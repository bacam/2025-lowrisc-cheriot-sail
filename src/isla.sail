/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

val isla_reset_registers = "reset_registers" : unit -> unit
val isla_footprint : forall 'n, 'n in {16, 32}. bits('n) -> bool
val sail_end_cycle = impure "cycle_count" : unit -> unit

val isla_footprint_no_init : forall 'n, 'n in {16, 32}. bits('n) -> bool effect {barr, eamem, escape, exmem, rmem, rmemt, rreg, undef, wmv, wmvt, wreg}

function isla_footprint_no_init(opcode) = {
  try {
    isla_reset_registers();

    sail_end_cycle();
    let ast: ast = if length(opcode) == 16 then {
      nextPC = PC + 2;
      ext_decode_compressed(opcode)
    } else {
      nextPC = PC + 4;
      ext_decode(opcode)
    };
    let _ = execute(ast);
    tick_pc();

    true
  } catch {
    _ => false
  }
}

val isla_footprint : forall 'n, 'n in {16, 32}. bits('n) -> bool effect {barr, eamem, escape, exmem, rmem, rmemt, rreg, undef, wmv, wmvt, wreg}

function isla_footprint(opcode) = {
  ext_init ();

  try {
    init_model();

    isla_footprint_no_init(opcode)
  } catch {
    _ => false
  }
}

function isla_init_cap_property(c : Capability) -> bool = {
  // Assert that the capability has some properties necessary for
  // derivability (ported from the formal proof work)
  let (base, top) = getCapBoundsBits(c);
/*
  let dti : bool =
    (unsigned(c.E) <= 14 | unsigned(c.E) == 24) &
    (not_bool(c.tag) | (
      (unsigned(top) <= unsigned(0x100000000)) &
      (not_bool(unsigned(c.E) == 24) | c.B[8] == bitzero) &
      (not_bool(unsigned(c.E) <= 14) | (unsigned(base) <= unsigned(top)))
    ));
*/

  let (_, c') = setCapBounds(max_bounds_cap, base, top[31..0]-base); 
  not_bool(c.tag) | c.reserved == 0b0 &
                    ((unsigned(base) + unsigned(top[31..0] - base) <= unsigned(0x100000000) &
                      unsigned(base) <= unsigned(top) &
                      unsigned(top) <= unsigned(0x100000000) &
                      c.E == c'.E & c.T == c'.T & c.B == c'.B) |
                     (c.E == 0b11000 & c.B == 0b000000000 & c.T == 0b100000000))
}

function isla_testgen_init() -> unit = {
  PC = 0x80000000;
  mstatus[MIE] = 0b0;
  init_model();
}

function isla_testgen_step() -> unit = {
  // nextPCC is usually only updated when the non-address parts of PCC might change.  The test
  // generator may have chosen a new PCC, so initialise nextPCC here.
  nextPCC = PCC;
  let f : FetchResult = ext_fetch_hook(fetch());
  let r : Retired = match f {
    F_Ext_Error(e)   => RETIRE_FAIL,
    F_Error(e, addr) => RETIRE_FAIL,
    F_RVC(h) => {
      let ast = ext_decode_compressed(h);
      nextPC = PC + 2;
      execute(ast)
    },
    F_Base(w) => {
      let ast = ext_decode(w);
      nextPC = PC + 4;
      execute(ast)
    }
  };
  match r {
    RETIRE_SUCCESS => (),
    RETIRE_FAIL => assert(false),
  };
  tick_pc();
  // Keep the address of the PCC up to date
  let (ok, newpcc) = setCapAddr(PCC, PC);
  assert(ok);

  // Make sure that the new PCC is good enough for the test exit instruction
  assert(not_bool(isCapSealed(newpcc)));
  assert(newpcc.permit_execute);
  assert(inCapBounds(newpcc, newpcc.address, 2));

  PCC = newpcc;
} 

$property
function isla_cap_encoding(c_tag : bool, c_bits : bits(64)) -> (option ((bool, Capability, CapAddrBits, CapLenBits))) = {
  let c = capBitsToCapability(c_tag, c_bits);
  let (base, top) = getCapBoundsBits(c);
  if ((unsigned(c.E) <= 14 | unsigned(c.E) == 24) &
   not_bool(c.tag) | (
     (unsigned(top) <= unsigned(0x100000000)) &
     (not_bool(unsigned(c.E) == 24) | base[8] == bitzero) &
     (not_bool(unsigned(c.E) <= 14) | (unsigned(base) <= unsigned(top)))
   )) then None() else Some(c_tag, c, base, top)
}

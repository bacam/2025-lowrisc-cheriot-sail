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
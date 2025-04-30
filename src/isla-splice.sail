
val __read_memt
  = impure { ocaml: "Platform.read_memt", c: "platform_read_memt", _: "read_memt" }
  : forall ('rk : Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
  ('rk, bits('addrsize), int('n)) -> (bits(8 * 'n), bit)


val __write_memt
  = impure { ocaml: "Platform.write_memt", c: "platform_write_memt", _: "write_memt" }
  : forall ('wk : Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
  ('wk, bits('addrsize), int('n), bits(8 * 'n), bit) -> bool

function write_ram(wk, addr, width, data, meta) = __write_memt(wk, addr, width, data, bool_to_bit(meta))
function read_ram(rk, addr, width, read_meta) =
  if read_meta then {
    let (v,t) = __read_memt(rk, addr, width);
    // We don't have a good way to assert derivability on the initial memory, so check it on
    // capability loads
    let t' = bit_to_bool(t);
    if t' & width == 8 then { assert(isla_init_cap_property(capBitsToCapability(true, v))) };
    (v,t')
  } else (__read_mem(rk, sizeof(xlen), addr, width), default_meta)

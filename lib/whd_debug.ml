module Profile = struct
  type t = {
    whd     : bool;
    ccnv    : bool;
    gen_conv: bool;
    eqappr  : bool;
  }
  let empty = { whd = false; ccnv = false; gen_conv = false; eqappr = false }
end

let profile = ref Profile.empty

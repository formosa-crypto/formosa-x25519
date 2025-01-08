require import List Int.

from Jasmin require import JModel.

require import Zp_25519.

import Zp.


op spec_decode_scalar_25519 (k:W256.t) =
  let k = k.[0   <- false] in
  let k = k.[1   <- false] in
  let k = k.[2   <- false] in
  let k = k.[255 <- false] in
  let k = k.[254 <- true ] in
      k.

op spec_decode_u_coordinate (u:W256.t) = let u = u.[255 <- false] in u.

op spec_add_and_double (qx : zp) (nqs : (zp * zp) * (zp * zp)) =
  let x_1 = qx in
  let (x_2, z_2) = nqs.`1 in
  let (x_3, z_3) = nqs.`2 in
  let a  = x_2 + z_2 in
  let aa = a * a in
  let b  = x_2 + (- z_2) in
  let bb = b*b in
  let e = aa + (- bb) in
  let c = x_3 + z_3 in
  let d = x_3 + (- z_3) in
  let da = d * a in
  let cb = c * b in
  let x_3 = (da + cb)*(da + cb) in
  let z_3 = x_1 * ((da + (- cb))*(da + (- cb))) in
  let x_2 = aa * bb in
  let z_2 = e * (aa + (inzp 121665 * e)) in
      ((x_2,z_2), (x_3,z_3)).

op spec_swap_tuple (t : ('a * 'a) * ('a * 'a)) = (t.`2, t.`1).

op spec_ith_bit(k : W256.t, i : int) = k.[i].

op spec_montgomery_ladder(init : zp, k : W256.t) =
  let nqs0 = ((Zp.one,Zp.zero),(init,Zp.one)) in
  foldl (fun (nqs : (zp * zp) * (zp * zp)) ctr =>
         if spec_ith_bit k ctr
         then spec_swap_tuple (spec_add_and_double init (spec_swap_tuple(nqs)))
         else spec_add_and_double init nqs) nqs0 (rev (iota_ 0 255)).

op spec_encode_point (q: zp * zp) : W256.t  =
    let q = q.`1 * (ZModpRing.exp q.`2 (p - 2)) in
        W256.of_int (asint q) axiomatized by spec_encode_pointE.

op spec_scalarmult_internal (k: zp) (u: W256.t) : W256.t =
   let r = spec_montgomery_ladder k u in
       spec_encode_point (r.`1) axiomatized by scalarmult_internalE.

op spec_scalarmult (k: W256.t) (u: W256.t) : W256.t =
    let k = spec_decode_scalar_25519 k in
    let u = spec_decode_u_coordinate u in
        spec_scalarmult_internal (inzp (to_uint u)) k axiomatized by spec_scalarmultE.

hint simplify spec_scalarmultE.

op spec_scalarmult_base (k:W256.t) : W256.t =
    spec_scalarmult (k) (W256.of_int(9%Int)).

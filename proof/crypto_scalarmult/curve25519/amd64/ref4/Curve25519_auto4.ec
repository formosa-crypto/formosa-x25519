require import AllCore StdOrder IntDiv Bool List BitEncoding StdRing Pervasive Logic StdBigop.
require import Zp_25519 W64limbs Zp_limbs Curve25519_Spec Curve25519_Procedures Scalarmult_s EClib.

from Jasmin require import JWord JWord_array JModel JUtils.

import Zp Curve25519_Procedures Scalarmult_s Array4 Array32 StdOrder.IntOrder Array4 BitEncoding.BS2Int EClib Ring.IntID StdBigop.Bigint.


lemma h_add_rrs_ref4 (_f _g: zp):
  hoare [M.__add4_rrs :
      inzpRep4 f = _f /\ inzpRep4 g = _g
      ==>
      inzpRep4 res = _f + _g
  ].
proof.
    proc.
    admit.
qed.

lemma h_sub_rrs_ref4 (_f _g: zp):
  hoare [M.__sub4_rrs :
      inzpRep4 f = _f /\ inzpRep4 gs = _g
      ==>
      inzpRep4 res = _f - _g
  ].
proof.
    proc.
    admit.
qed.

lemma h_mul_a24_ref4 (_f : zp, _a24: int):
  hoare [M.__mul4_a24_rs :
      inzpRep4 xa = _f /\  _a24 = to_uint a24
      ==>
      inzpRep4 res = _f * inzp _a24
  ].
proof.
    proc.
    admit.
qed.

lemma h_mul_rss_ref4 (_f _g: zp):
  hoare [M.__mul4_rss :
      inzpRep4 xa = _f /\  inzpRep4 ya = _g
      ==>
      inzpRep4 res = _f * _g
  ].
proof.
    proc.
    admit.
qed.


lemma h_mul_pp_ref4 (_f _g: zp):
  hoare [M._mul4_pp :
      inzpRep4 xa = _f /\  inzpRep4 ya = _g
      ==>
      inzpRep4 res = _f * _g
  ].
proof.
    proc.
    admit.
qed.

lemma h_sqr_rs_ref4 (_f: zp):
  hoare [M.__sqr4_rs :
      inzpRep4 xa = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2
  ].
proof.
    proc.
    admit.
qed.


lemma h_sqr_p_ref4 (_f: zp):
  hoare [M._sqr4_p :
      inzpRep4 xa = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2
  ].
proof.
    proc.
    admit.
qed.

lemma h_to_bytes_ref4 r:
  hoare [M.__tobytes4 :
      r = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 r)))
  ].
proof.
    proc.
    admit.
qed.

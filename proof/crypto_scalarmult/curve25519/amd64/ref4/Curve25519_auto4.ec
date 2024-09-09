require import AllCore StdOrder IntDiv Bool List BitEncoding StdRing Pervasive Logic StdBigop.
require import Zp_25519 W64limbs Zplimbs Curve25519_Spec Curve25519_Procedures EClib Scalarmult_s.

from Jasmin require import JWord JWord_array JModel JUtils.

import Zp Curve25519_Procedures Scalarmult_s Array4 Array32 StdOrder.IntOrder Array4 BitEncoding.BS2Int EClib Ring.IntID StdBigop.Bigint.

equiv eq_spec_impl_add_rrs_ref4 : CurveProcedures.add  ~ M.__add4_rrs:
    f{1} = inzpRep4 f{2} /\
    g{1} = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    admit.
qed.

equiv eq_spec_impl_sub_rrs_ref4 : CurveProcedures.sub ~ M.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl_sub_rsr_ref4 : CurveProcedures.sub ~ M.__sub4_rsr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_mul_a24_rs_ref4 : CurveProcedures.mul_a24 ~ M.__mul4_a24_rs:
    f{1}   = inzpRep4 xa{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl_mul_rss_ref4 : CurveProcedures.mul ~ M.__mul4_rss:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
   proc.
    admit.
qed.

equiv eq_spec_impl_mul_pp_ref4 : CurveProcedures.mul ~ M._mul4_pp:
    f{1}   = inzpRep4 xa{2} /\
    g{1}   = inzpRep4 ya{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_sqr_ref4 : CurveProcedures.sqr ~ M.__sqr4_rs:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl_sqr_ss__ref4 : CurveProcedures.sqr ~ M.__sqr4_ss:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.

    admit.
qed.

equiv eq_spec_impl_sqr_rs_ref4 : CurveProcedures.sqr ~ M.__sqr4_rs:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_sqr_p_ref4 : CurveProcedures.sqr ~ M._sqr4_p:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

(* asint already puts the range of its input between 0 and 2^255 - 19, no need for range post-conditions *)
lemma eq_to_bytes_ref4 r:
  hoare [M.__tobytes4 :
      r = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 r)))
  ].
proof.
    proc.
    admit.
qed.

lemma ill_eq_to_bytes_ref4 : islossless M.__tobytes4 by islossless.

lemma ph_eq_to_bytes_ref4 r:
  phoare [M.__tobytes4 :
      r = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 r)))
  ] = 1%r.
proof.
    by conseq ill_eq_to_bytes_ref4 (eq_to_bytes_ref4 r).
qed.

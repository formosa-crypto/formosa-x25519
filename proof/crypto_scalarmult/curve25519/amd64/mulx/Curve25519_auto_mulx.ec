require import Int StdOrder Ring IntDiv Bool List Real BitEncoding.
require import Zp_25519 W64limbs Zplimbs Curve25519_Spec Curve25519_Operations Curve25519_Procedures Scalarmult_s.

from Jasmin require import JWord JWord_array JModel JUtils.

import Zp Curve25519_Procedures Curve25519_Operations Scalarmult_s Array4 Array32 Ring.IntID StdOrder.IntOrder Array4.

(* Probably needs to be moved elsewhere, such as W64limbs *)

(** step 0 : add sub mul sqr - all done by auto **)

equiv eq_spec_impl_add_rrs_mulx : CurveProcedures.add ~ M.__add4_rrs:
    f{1}   = inzpRep4 f{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl_sub_rrs_mulx : CurveProcedures.sub ~ M.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.


equiv eq_spec_impl_sub_rsr_mulx : CurveProcedures.sub ~ M.__sub4_rsr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

(* inline mul4_c0 mul4_c1 mul4_c2 mul4_c3 *)

equiv eq_spec_impl_mul_a24_mulx : CurveProcedures.mul_a24 ~ M.__mul4_a24_rs:
    f{1}   = inzpRep4 fs{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_mul_rsr_mulx : CurveProcedures.mul ~ M.__mul4_rsr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc.
    admit.
qed.

equiv eq_spec_impl_mul__rpr_mulx : CurveProcedures.mul ~ M.__mul4_rpr:
    f{1}   = inzpRep4 fp{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl__sqr_rr_mulx : CurveProcedures.sqr ~ M.__sqr4_rr:
    f{1}   = inzpRep4 f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    admit.
qed.

equiv eq_spec_impl__sqr_rr_mulx_rev : M.__sqr4_rr ~ CurveProcedures.sqr:
    f{2}   = inzpRep4 f{1}
    ==>
    res{2} = inzpRep4 res{1}.
proof.
    proc *.
    admit.
qed.


lemma eq_to_bytes_mulx r:
  hoare [M.__tobytes4 :
      r = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 r)))
  ].
proof.
    proc.
    admit.
qed.

lemma ill_eq_to_bytes_mulx : islossless M.__tobytes4 by islossless.

lemma ph_eq_to_bytes_mulx r:
  phoare [M.__tobytes4 :
      r = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 r)))
  ] = 1%r.
proof.
    by conseq ill_eq_to_bytes_mulx (eq_to_bytes_mulx r).
qed.

require import Bool List Int IntDiv CoreMap Real Ring.
require import Zp_25519 Curve25519_Spec Curve25519_Operations Curve25519_Procedures.

from Jasmin require import JModel.

import Zp Ring.IntID Curve25519_Spec Curve25519_Procedures Curve25519_Operations.

lemma ill_decode_scalar_25519 : islossless CurveProcedures.decode_scalar by islossless.

lemma eq_ph_decode_scalar_25519 k:
    phoare [CurveProcedures.decode_scalar :
        k' = k
        ==>
        res = spec_decode_scalar_25519 k] = 1%r.
proof.
    by conseq ill_decode_scalar_25519 (eq_proc_op_decode_scalar k).
qed.

(** step 2 : decode_u_coordinate **)
lemma ill_decode_u_coordinate : islossless CurveProcedures.decode_u_coordinate by islossless.

lemma ill_decode_u_coordinate_base : islossless CurveProcedures.decode_u_coordinate_base by islossless.

lemma eq_ph_decode_u_coordinate u:
    phoare [CurveProcedures.decode_u_coordinate :
        u' = u
        ==>
        res = inzp (to_uint (spec_decode_u_coordinate u))] = 1%r.
proof.
    by conseq ill_decode_u_coordinate (eq_proc_op_decode_u_coordinate u).
qed.

lemma eq_ph_decode_u_coordinate_base:
    phoare [CurveProcedures.decode_u_coordinate_base :
        true
        ==>
        res = inzp (to_uint (spec_decode_u_coordinate (W256.of_int 9)))] = 1%r.
proof.
    by conseq ill_decode_u_coordinate_base (eq_proc_op_decode_u_coordinate_base).
qed.


(** step 3 : spec_ith_bit **)
lemma ill_ith_bit : islossless CurveProcedures.ith_bit by islossless.

lemma eq_ph_ith_bit (k : W256.t) i:
    phoare [CurveProcedures.ith_bit :
        k' = k /\
        ctr = i
        ==>
        res = spec_ith_bit k i] = 1%r.
proof.
    by conseq ill_ith_bit (eq_proc_op_ith_bit k i).
qed.

(** step 4 : cswap **)
lemma ill_cswap : islossless CurveProcedures.cswap by islossless.

lemma eq_ph_cswap (t : (zp * zp) * (zp * zp) )  b:
  phoare [CurveProcedures.cswap : x2 = (t.`1).`1 /\
                        z2 = (t.`1).`2 /\
                        x3 = (t.`2).`1 /\
                        z3 = (t.`2).`2 /\
                       toswap = b
          ==> ((res.`1, res.`2),(res.`3, res.`4)) = cswap t b] = 1%r.
proof.
    by conseq ill_cswap (eq_proc_op_cswap t b).
qed.

(** step 5 : add_and_double **)
lemma ill_add_and_double : islossless CurveProcedures.add_and_double by islossless.

lemma eq_ph_add_and_double (qx : zp) (nqs : (zp * zp) * (zp * zp)):
  phoare [CurveProcedures.add_and_double : init = qx /\
                                 x2 = nqs.`1.`1 /\
                                 z2 = nqs.`1.`2 /\
                                 x3 = nqs.`2.`1 /\
                                 z3 = nqs.`2.`2
          ==> ((res.`1, res.`2),(res.`3, res.`4)) = op_add_and_double qx nqs] = 1%r.
proof.
    by conseq ill_add_and_double (eq_proc_op_add_and_double qx nqs).
qed.

(** step 6 : montgomery_ladder_step **)
lemma ill_montgomery_ladder_step : islossless CurveProcedures.montgomery_ladder_step by islossless.

lemma eq_ph_montgomery_ladder_step (k : W256.t)
                                   (init : zp)
                                   (nqs : (zp * zp) * (zp * zp) * bool)
                                   (ctr : int) :
  phoare [CurveProcedures.montgomery_ladder_step : k' = k /\
                                         init' = init /\
                                         x2 = nqs.`1.`1 /\
                                         z2 = nqs.`1.`2 /\
                                         x3 = nqs.`2.`1 /\
                                         z3 = nqs.`2.`2 /\
                                         swapped = nqs.`3 /\
                                         ctr' = ctr
          ==> ((res.`1, res.`2),(res.`3, res.`4),res.`5) =
              op_montgomery_ladder3_step k init nqs ctr] = 1%r.
proof.
    by conseq ill_montgomery_ladder_step (eq_proc_op_montgomery_ladder_step k init nqs ctr).
qed.

(** step 7 : montgomery_ladder **)
lemma ill_montgomery_ladder : islossless CurveProcedures.montgomery_ladder.
proof.
    islossless. while true (ctr+1). move => ?. wp. simplify.
    call(_:true ==> true). islossless. sp.  skip; smt().
    skip; smt().
qed.

lemma eq_ph_montgomery_ladder (init : zp)
                              (k : W256.t) :
  phoare [CurveProcedures.montgomery_ladder : init' = init /\
                                    k.[0] = false /\
                                    k' = k
          ==> ((res.`1, res.`2),(res.`3,res.`4)) =
              select_double_from_triple (op_montgomery_ladder3 init k)] = 1%r.
proof.
    by conseq ill_montgomery_ladder (eq_proc_op_montgomery_ladder init k).
qed.

(** step 8 iterated square **)
lemma ill_it_sqr : islossless CurveProcedures.it_sqr.
proof.
    islossless.
    while true ii. move => ?. wp.
    inline CurveProcedures.sqr. wp. skip. move => &hr [H] H1. smt().
    skip. smt().
qed.

lemma eq_ph_it_sqr (e : int) (z : zp) :
    phoare[CurveProcedures.it_sqr :
        i = e && 1 <= i && f =  z
        ==>
        res = op_it_sqr1 e z] = 1%r.
proof.
    by conseq ill_it_sqr (eq_proc_op_it_sqr e z).
qed.

(** step 9 : invert **)
lemma ill_invert : islossless CurveProcedures.invert.
proof.
    proc.
    inline CurveProcedures.sqr CurveProcedures.mul.
    wp; sp. call(_: true ==> true). apply ill_it_sqr.
    wp; sp. call(_: true ==> true). apply ill_it_sqr.
    wp; sp. call(_: true ==> true). apply ill_it_sqr.
    wp; sp. call(_: true ==> true). apply ill_it_sqr.
    wp; sp. call(_: true ==> true). apply ill_it_sqr.
    wp; sp. call(_: true ==> true). apply ill_it_sqr.
    wp; sp. call(_: true ==> true). apply ill_it_sqr.
    wp; sp. call(_: true ==> true). apply ill_it_sqr.
    skip. trivial.
qed.

lemma eq_ph_invert (z : zp) :
  phoare[CurveProcedures.invert : fs =  z ==> res = op_invert2 z] = 1%r.
proof.
    conseq ill_invert (eq_proc_op_invert z). auto => />.
    smt().
qed.

(** step 10 : encode point **)
lemma ill_encode_point : islossless CurveProcedures.encode_point.
proof.
    proc. inline CurveProcedures.mul. wp; sp. call(_: true ==> true). apply ill_invert. trivial.
qed.

lemma eq_ph_encode_point (q : zp * zp) :
  phoare[CurveProcedures.encode_point : x2 =  q.`1 /\ z2 = q.`2 ==> res = op_encode_point q] = 1%r.
proof.
    conseq ill_encode_point (eq_proc_op_encode_point q). auto => />.
    smt().
qed.

(** step 11 : scalarmult **)
lemma ill_scalarmult_internal : islossless CurveProcedures.scalarmult_internal.
proof.
    proc. sp.
    call(_: true ==> true). apply ill_encode_point.
    call(_: true ==> true). apply ill_montgomery_ladder.
    skip. trivial.
qed.

(** step 11 : spec_scalarmult **)
lemma ill_scalarmult : islossless CurveProcedures.scalarmult.
proof.
    proc. sp.
    call(_: true ==> true). apply ill_scalarmult_internal.
    call(_: true ==> true). apply ill_decode_u_coordinate.
    call(_: true ==> true). apply ill_decode_scalar_25519.
    skip. trivial.
qed.

lemma ill_scalarmult_base : islossless CurveProcedures.scalarmult_base.
proof.
    proc. sp.
    call(_: true ==> true). apply ill_scalarmult_internal.
    call(_: true ==> true). apply ill_decode_u_coordinate_base.
    call(_: true ==> true). apply ill_decode_scalar_25519.
    skip. trivial.
qed.

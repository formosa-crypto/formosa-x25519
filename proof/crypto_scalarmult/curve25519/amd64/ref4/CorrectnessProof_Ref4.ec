require import Real Bool Int IntDiv List.
from Jasmin require import JModel.
require import  Add4Extracted Sub4Extracted Mul4RefExtracted Mul4_a24RefExtracted Sqr4RefExtracted. (* must be in this order so module names do not clash *)
require import Curve25519_Procedures Ref4_scalarmult_s CryptolineEquivs_Ref4 Zp_limbs Zp_25519 CommonCryptoline CorrectnessProof_ToBytes.

import Zp Ring.IntID.

require import Array4 Array32 WArray32.

(** hoares, lossless and phoares **)

lemma h_add_rrs_ref4 (_f _g: zp):
  hoare [M.__add4_rrs :
      inzpRep4 f = _f /\ inzpRep4 g = _g
      ==>
      inzpRep4 res = _f + _g
  ].
proof.
    exists* f, g.
    elim * => _ff _gg.
    conseq __add4_rrs_cryptoline_equiv_ref4 (: (((g = _gg) /\ (f = _ff)) /\ inzpRep4 _gg = _g /\ inzpRep4 _ff = _f) ==> inzpRep4 _gg = _g /\ inzpRep4 _ff = _f /\
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ff.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gg.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))) __add4_rrs_spec; 1:smt().
    rewrite -add4_equiv_contract 1:/#.
    proc *. call (__add4_rrs_spec _ff _gg).
    auto => />.
qed.

lemma h_sub_rrs_ref4 (_f _g: zp):
  hoare [M.__sub4_rrs :
      inzpRep4 f = _f /\ inzpRep4 gs = _g
      ==>
      inzpRep4 res = _f - _g
  ].
proof.
    exists* f, gs.
    elim * => _ff _gg.
    conseq __sub4_rss_cryptoline_equiv_ref4 (: (((gs = _gg) /\ (f = _ff)) /\ inzpRep4 _gg = _g /\ inzpRep4 _ff = _f) ==> inzpRep4 _gg = _g /\ inzpRep4 _ff = _f /\
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ff.[ii]))) (iota_ 0 4))) -
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gg.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))) __add4_rrs_spec; 1:smt().
    rewrite -sub4_equiv_contract 1:/#.
    proc *. call (__sub4_rrs_spec _ff _gg).
    auto => />.
qed.

lemma h_mul_a24_ref4 (_f : zp):
  hoare [M.__mul4_a24_rs :
      inzpRep4 xa = _f /\ W64.to_uint a24 = 121665
      ==>
      inzpRep4 res = _f * inzp 121665
  ].
proof.
    exists* xa.
    elim * => _ff.
   conseq __mul4_a24_rs_cryptoline_equiv_ref4 (: (((xa = _ff)) /\ inzpRep4 _ff = _f) ==> inzpRep4 _ff = _f /\
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ff.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19)))) __mul4_a24_rs_spec.
      auto => />. move => &1 H. exists(xa{1}). auto => />.
      smt(W64.to_uintK). rewrite -mul4_a24_equiv_contract. smt(inzpM).
      proc *. call (__mul4_a24_rs_spec _ff).
      auto => />.
qed.

lemma h_mul_rss_ref4 (_f _g: zp):
  hoare [M.__mul4_rss :
      inzpRep4 xa = _f /\  inzpRep4 ya = _g
      ==>
      inzpRep4 res = _f * _g
  ].
proof.
    exists* xa, ya.
    elim * => _ff _gg.
    conseq __mul4_rss_cryptoline_equiv_ref4 (: (((xa = _ff) /\ (ya = _gg)) /\ inzpRep4 _gg = _g /\ inzpRep4 _ff = _f) ==> inzpRep4 _gg = _g /\ inzpRep4 _ff = _f /\
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ff.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gg.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))) __mul4_rss_spec.
      smt(). rewrite -mul4_equiv_contract. smt(inzpM).
      proc *. call (__mul4_rss_spec _ff _gg).
      auto => />.
qed.

lemma h_sqr_rs_ref4 (_f: zp):
  hoare [M.__sqr4_rs :
      inzpRep4 xa = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2
  ].
proof.
    exists* xa.
    elim * => _ff.
    conseq __sqr4_rs_cryptoline_equiv_ref4 (: (((xa = _ff))  /\ inzpRep4 _ff = _f) ==> inzpRep4 _ff = _f /\
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ff.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ff.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))) __sqr4_rs_spec.
      smt(). rewrite -sqr4_equiv_contract. auto => />.
      move => &2 H. rewrite H /exp => />. rewrite /iterop => />.
       do 2! rewrite iteri_red //=. rewrite inzpRep4E inzpM //=.
      proc *. call (__sqr4_rs_spec _ff).
      auto => />.
qed.

lemma ill_add_rrs_ref4 : islossless M.__add4_rrs.
    by proc; do 2! unroll for ^while; islossless.
qed.

lemma ph_add_rrs_ref4 (_f _g: zp):
    phoare [M.__add4_rrs :
      inzpRep4 f = _f /\ inzpRep4 g = _g
      ==>
      inzpRep4 res = _f + _g
  ] = 1%r.
proof.
    by conseq ill_add_rrs_ref4 (h_add_rrs_ref4 _f _g).
qed.

lemma ill_sub_rrs_ref4 : islossless M.__sub4_rrs.
    by proc; do 2! unroll for ^while; islossless.
qed.

lemma ph_sub_rrs_ref4 (_f _g: zp):
    phoare [M.__sub4_rrs :
      inzpRep4 f = _f /\ inzpRep4 gs = _g
      ==>
      inzpRep4 res = _f - _g
  ] = 1%r.
proof.
    by conseq ill_sub_rrs_ref4 (h_sub_rrs_ref4 _f _g).
qed.

lemma ill_mul_a24_ref4 : islossless M.__mul4_a24_rs by islossless.

lemma ph_mul_a24_ref4 (_f: zp):
    phoare [M.__mul4_a24_rs :
      inzpRep4 xa = _f /\ W64.to_uint a24 =  121665
      ==>
      inzpRep4 res = _f * inzp 121665
  ] = 1%r.
proof.
    by conseq ill_mul_a24_ref4 (h_mul_a24_ref4 _f).
qed.

lemma ill_mul_rss_ref4 : islossless M.__mul4_rss.
proof.
    proc. inline *.
    do 8! unroll for ^while. islossless.
qed.

lemma ph_mul_rss_ref4 (_f _g : zp):
    phoare [M.__mul4_rss :
      inzpRep4 xa = _f /\  inzpRep4 ya = _g
      ==>
      inzpRep4 res = _f * _g] = 1%r.
proof.
    by conseq ill_mul_rss_ref4 (h_mul_rss_ref4 _f _g).
qed.

lemma ill_sqr_rs_ref4 : islossless M.__sqr4_rs
    by proc; inline *; do 2! unroll for ^while; islossless.

lemma ph_sqr_rs_ref4 (_f: zp):
    phoare [M.__sqr4_rs :
      inzpRep4 xa = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2] = 1%r.
proof.
    by conseq ill_sqr_rs_ref4 (h_sqr_rs_ref4 _f).
qed.

(** step 0 : add sub mul sqr **)
equiv eq_spec_impl_add_rrs_ref4 : CurveProcedures.add ~ M.__add4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_add_rrs_ref4 (inzpRep4 f{2}) (inzpRep4 g{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_sub_rrs_ref4 : CurveProcedures.sub ~ M.__sub4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_sub_rrs_ref4 (inzpRep4 f{2}) (inzpRep4 gs{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_mul_a24_rs_ref4 : CurveProcedures.mul_a24 ~ M.__mul4_a24_rs:
   f{1} = inzpRep4 xa{2} /\
   a24{1} = W64.to_uint a24{2} /\
   a24{1} = 121665
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_mul_a24_ref4 (inzpRep4 xa{2})).
    inline *; wp; skip => />.
    move => &2 H  => />.
    move => H0 H1; 1:smt().
qed.

equiv eq_spec_impl_mul_rss_ref4 : CurveProcedures.mul ~ M.__mul4_rss:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_mul_rss_ref4 (inzpRep4 xa{2}) (inzpRep4 ya{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_sqr_ref4 : CurveProcedures.sqr ~ M.__sqr4_rs:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_sqr_rs_ref4 (inzpRep4 xa{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

(** step 0.5 : transitivity stuff **)
equiv eq_spec_impl_add_ssr_ref4 : CurveProcedures.add ~ M.__add4_ssr:
   f{1} = inzpRep4 g{2} /\
   g{1} = inzpRep4 fs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call (eq_spec_impl_add_rrs_ref4). skip. auto => />.
qed.

equiv eq_spec_impl_add_sss_ref4 : CurveProcedures.add ~ M.__add4_sss:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_add_rrs_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_sub_sss_ref4 : CurveProcedures.sub ~ M.__sub4_sss:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sub_rrs_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_sub_rrs_rsr_ref4 : M.__sub4_rrs ~ M.__sub4_rsr:
   f{1}   =   fs{2} /\
   gs{1}   =  g{2}
   ==>
   res{1} = res{2}.
proof.
    proc.
    do 2! unroll for{1} ^while.
    do 2! unroll for{2} ^while.
    wp; skip => />.
qed.

equiv eq_spec_impl_sub_rsr_ref4 : CurveProcedures.sub ~ M.__sub4_rsr:
   f{1}   =   inzpRep4 fs{2} /\
   g{1}   =   inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    transitivity
    M.__sub4_rrs
    ( f{1} = inzpRep4 f{2} /\ g{1} = inzpRep4 gs{2} ==> res{1} = inzpRep4 res{2})
    ( f{1} = fs{2} /\ gs{1} = g{2} ==> res{1} = res{2}).
    move => &1 &2 [H] H0.
    exists(fs{2}, g{2}) => />.
    move => &1 &m &2 H H0. by rewrite -H0 H.
    proc *; call eq_spec_impl_sub_rrs_ref4.
    by skip => />.
    proc *; call eq_spec_impl_sub_rrs_rsr_ref4.
    by done.
qed.

equiv eq_spec_impl_sub_ssr_ref4 : CurveProcedures.sub ~ M.__sub4_ssr:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sub_rsr_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_mul_a24_ss_ref4 : CurveProcedures.mul_a24 ~ M.__mul4_a24_ss:
   f{1} = inzpRep4 xa{2} /\
   a24{1} = to_uint a24{2} /\
   a24{1} = 121665 /\
   a24{2} = W64.of_int 121665
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_a24_rs_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_mul_p_rss_ref4 : M._mul4_pp ~ M.__mul4_rss:
    xa{1} = xa{2} /\ ya{1} = ya{2}
    ==>
    res{1} = res{2}.
proof.
    proc.
    do 7! unroll for{1} ^while.
    do 6! unroll for{2} ^while.
    sim. simplify.
    inline __reduce4.
    do 2! unroll for{1} ^while.
    do 2! unroll for{2} ^while.    
    seq 172 172 : (#pre /\ ={r}). sim. auto => />.
    move => &2. apply Array4.ext_eq => i ib. smt(Array4.get_setE).
qed.

equiv eq_spec_impl_mul_pp_ref4 : CurveProcedures.mul ~ M._mul4_pp:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    transitivity
    M.__mul4_rss
    ( f{1} = inzpRep4 xa{2} /\ g{1} = inzpRep4 ya{2} ==> res{1} = inzpRep4 res{2})
    ( xa{1} = xa{2} /\ ya{1} = ya{2} ==> res{1} = res{2}).
    move => &1 &2 H.
    exists(xa{2}, ya{2}) => />.
    move => &1 &m &2 H H0. by rewrite -H0 H.
    proc *; call eq_spec_impl_mul_rss_ref4.
    by skip => />. symmetry.
    proc *; call eq_spec_impl_mul_p_rss_ref4.
    by done.
qed.

equiv eq_spec_impl_mul_ss_ref4 : CurveProcedures.mul ~ M._mul4_ss_:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_pp_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_mul_sss_ref4 : CurveProcedures.mul ~ M.__mul4_sss:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_rss_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_sqr_rs__ss_ref4 : M.__sqr4_ss ~ M.__sqr4_rs:
    xa{1} = xa{2}
    ==>
    res{1} = res{2}.
proof.
    proc *. inline {1} 1; sp; wp.
    conseq (_: r0{1} = r{2}).
    sim.
qed.

equiv eq_spec_impl_sqr_rs__p_ref4 : M._sqr4_p ~ M.__sqr4_rs:
    xa{1} = xa{2}
    ==>
    res{1} = res{2}.
proof.
    proc *. inline *.
    do 3! unroll for{1} ^while.
    do 2! unroll for{2} ^while.
    sim.
    seq 183 183 : (={r1}). by sim.
    wp. skip => />.
    move => &1 &2. apply Array4.ext_eq.
    smt(Array4.get_setE).
qed.

equiv eq_spec_impl_sqr__ss_ref4 : CurveProcedures.sqr ~ M.__sqr4_ss:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    transitivity
    M.__sqr4_rs
    ( f{1} = inzpRep4 xa{2} ==> res{1} = inzpRep4 res{2})
    ( xa{1} = xa{2} ==> res{1} = res{2}).
    move => &1 &2 H.
    exists(xa{2}) => />.
    move => &1 &m &2 H H0. by rewrite -H0 H.
    proc *; call eq_spec_impl_sqr_ref4.
    by skip => />. symmetry.
    proc *; call eq_spec_impl_sqr_rs__ss_ref4.
    by done.
qed.

equiv eq_spec_impl_sqr_p_ref4 : CurveProcedures.sqr ~ M._sqr4_p:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    transitivity
    M.__sqr4_rs
    ( f{1} = inzpRep4 xa{2} ==> res{1} = inzpRep4 res{2})
    ( xa{1} = xa{2} ==> res{1} = res{2}).
    move => &1 &2 H.
    exists(xa{2}) => />.
    move => &1 &m &2 H H0. by rewrite -H0 H.
    proc *; call eq_spec_impl_sqr_ref4.
    by skip => />. symmetry.
    proc *; call eq_spec_impl_sqr_rs__p_ref4.
    by done.
qed.

equiv eq_spec_impl_sqr_ss_ref4 : CurveProcedures.sqr ~ M._sqr4_ss_:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1).
    unroll for{2} ^while.
    wp. sp. simplify.
    call eq_spec_impl_sqr_p_ref4. skip. auto => />.
    move => &2.
    congr. apply Array4.ext_eq. move => H [H1] H2.
    smt(Array4.get_setE).
qed.

equiv eq_spec_impl_sqr_s_ref4 : CurveProcedures.sqr ~ M._sqr4_s_:
    f{1}   = inzpRep4 x{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sqr_p_ref4. skip. auto => />.
 qed.

(** setting last bit to 0 **)
lemma eq_set_last_bit_to_zero64_ref4 x :
  hoare [
      M.__decode_u_coordinate4 :
      u = x
      ==>
      res = Curve25519_Operations.last_bit_to_zero64 x
  ].
proof.
    proc; wp; skip => />.
    rewrite /last_bit_to_zero64 => />; congr.
    pose X := x.[3].
    rewrite /of_int /int2bs  /mkseq /to_list -iotaredE => />.
    rewrite andE  wordP => /> k K0 K1.
    rewrite  map2iE //  get_bits2w //.
    smt(W64.initE).
qed.

lemma ill_set_last_bit_to_zero64: islossless M.__decode_u_coordinate4 by islossless.

lemma eq_ph_set_last_bit_to_zero64 x:
  phoare [
    M.__decode_u_coordinate4 :
    u = x
    ==>
    res = Curve25519_Operations.last_bit_to_zero64 x
  ] = 1%r.
proof.
    by conseq ill_set_last_bit_to_zero64 (eq_set_last_bit_to_zero64_ref4 x).
qed.

lemma h_to_bytes_ref4 _f:
  hoare [M.__tobytes4 :
      _f = f 
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 _f)))
  ].
proof.
    have E: 0 <= valRep4 _f < W256.modulus. apply valRep4_cmp.
    have E0: to_uint (limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])) = valRep4 _f.
      + by rewrite valRep4ToPack /to_list /mkseq -iotaredE => />.     
    case (0 <= valRep4 _f < p) => C1.      
    exists* f.
    elim *=> _ff.
    conseq __tobytes_cryptoline_equiv_0p_ref4 (: (((f = _ff)) /\  0 <= valRep4 _ff && valRep4 _ff < p /\ _ff = _f) ==>  _ff = _f /\
      (((limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3])) \ult
       (W256.of_int
       57896044618658097711785492504343953926634992332820282019728792003956564819949
       )) /\
      (((W256.of_int 0) \ule
       (limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3]))) /\
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4)))
      (single ((pow 2 255) - 19)))))) CommonToBytes_0p.__tobytes4_spec; 1:smt().
    auto => />. move => &2 H. 
    rewrite tobytes_equiv_contract. smt(). 
    proc *. call (CommonToBytes_0p.__tobytes4_spec _ff). auto => />.    
    rewrite pVal. move => H H1.    
    do split. rewrite ultE E0 of_uintK pmod_small //=. rewrite uleE E0 of_uintK pmod_small //=.
    
    case (p <= valRep4 _f < pow 2 255) => C2.      
    exists* f.
    elim *=> _ff.
    conseq __tobytes_cryptoline_equiv_p2_255_ref4 (: (((f = _ff)) /\  p <= valRep4 _ff && valRep4 _ff < pow 2 255 /\ _ff = _f) ==>  _ff = _f /\
      (((((limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3])) \ult
       (W256.of_int
       57896044618658097711785492504343953926634992332820282019728792003956564819949
       )) /\
      (((W256.of_int 0) \ule
       (limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3]))) /\
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4)))
      (single ((pow 2 255) - 19)))))))) CommonToBytes_p2_255.__tobytes4_spec; 1:smt(pVal).
    auto => />. move => &2 H. 
    rewrite tobytes_equiv_contract. smt(). 
    proc *. call (CommonToBytes_p2_255.__tobytes4_spec _ff). auto => />.    
    rewrite pVal. move => H H1.    
    do split. rewrite ultE E0 of_uintK pmod_small //=. rewrite uleE E0 of_uintK pmod_small //=.

    case (pow 2 255 <= valRep4 _f < 2*p) => C3.      
    exists* f.
    elim *=> _ff.
    conseq __tobytes_cryptoline_equiv_2_2552p_ref4 (: (((f = _ff)) /\  pow 2 255 <= valRep4 _ff && valRep4 _ff < 2*p /\ _ff = _f) ==>  _ff = _f /\
      ((((limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3])) \ult
       (W256.of_int
       57896044618658097711785492504343953926634992332820282019728792003956564819949
       )) /\
      (((W256.of_int 0) \ule
       (limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3]))) /\
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4)))
      (single ((pow 2 255) - 19))))))) CommonToBytes_2_2552p.__tobytes4_spec; 1:smt(pVal).
    auto => />. move => &2 H. 
    rewrite tobytes_equiv_contract. smt(). 
    proc *. call (CommonToBytes_2_2552p.__tobytes4_spec _ff). auto => />.    
    rewrite pVal. move => H H1.    
    do split. rewrite ultE E0 of_uintK pmod_small //=. rewrite uleE E0 of_uintK pmod_small //=.
    
    case (2*p <= valRep4 _f < pow 2 256) => C4.      
    exists* f.
    elim *=> _ff.
    conseq __tobytes_cryptoline_equiv_2p2_256_ref4 (: (((f = _ff)) /\  2*p <= valRep4 _ff && valRep4 _ff < pow 2 256 /\ _ff = _f) ==>  _ff = _f /\
      ((((limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3])) \ult
       (W256.of_int
       57896044618658097711785492504343953926634992332820282019728792003956564819949
       )) /\
      (((W256.of_int 0) \ule
       (limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3]))) /\
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4)))
      (single ((pow 2 255) - 19))))))) CommonToBytes_2p2_256.__tobytes4_spec. 
    move => &1. auto => />. exists(arg{1}). auto => />.           
    rewrite tobytes_equiv_contract. auto => />.   
    proc *. call (CommonToBytes_2p2_256.__tobytes4_spec _ff). auto => />.    
    rewrite pVal. move => H H1.    
    do split. rewrite !uleE E0 of_uintK pmod_small //=. smt(). 
    rewrite !uleE E0 of_uintK pmod_small //=. smt().  
qed.

(*
lemma h_to_bytes_ref4 _f:
  hoare [M.__tobytes4 :
      _f = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 _f)))
  ].
proof.
    have E: 0 <= valRep4 _f < W256.modulus. apply valRep4_cmp.
    case (0 <= valRep4 _f < p) => C1.
    conseq equiv_to_bytes (: _f = arg /\ 0 <= valRep4 _f < p ==>
      (valRep4 res = asint (inzpRep4 _f))).
    move => &1 [#] H. smt().
    move => &1 &2 [#] H [#] H0.  move: H. rewrite !H0. move => H1.
    rewrite -H1 valRep4ToPack to_uintK //=.
    apply (h_to_bytes_no_reduction _f).

    case (p <= valRep4 _f < pow 2 255) => C2.
    conseq equiv_to_bytes (: _f = arg /\ p <= valRep4 _f < pow 2 255 ==>
      (valRep4 res = asint (inzpRep4 _f))).
    move => &1 [#] H. exists _f. move: C2. smt().
    move => &1 &2 [#] H [#] H0.  move: H. rewrite !H0. move => H1.
    rewrite -H1 valRep4ToPack to_uintK //=.
    apply (h_to_bytes_cminusP_part1 _f).

    case (pow 2 255 <= valRep4 _f < 2*p) => C3.
    conseq equiv_to_bytes (: _f = arg /\ pow 2 255 <= valRep4 _f < 2*p ==>
      (valRep4 res = asint (inzpRep4 _f))).
    move => &1 [#] H. exists _f. move: C3. smt().
    move => &1 &2 [#] H [#] H0.  move: H. rewrite !H0. move => H1.
    rewrite -H1 valRep4ToPack to_uintK //=.
    apply (h_to_bytes_cminusP_part2 _f).

    case (2*p <= valRep4 _f < W256.modulus) => C4.
    conseq equiv_to_bytes (: _f = arg /\ 2*p <= valRep4 _f < W256.modulus ==>
      (valRep4 res = asint (inzpRep4 _f))).
    move => &1 [#] H. exists _f. move: C4. smt().
    move => &1 &2 [#] H [#] H0.  move: H. rewrite !H0. move => H1.
    rewrite -H1 valRep4ToPack to_uintK //=.
    apply (h_to_bytes_cminus2P _f). smt().
qed.
*)

lemma ill_to_bytes_ref4 : islossless M.__tobytes4 by islossless.

lemma ph_to_bytes_ref4 r:
  phoare [M.__tobytes4 :
      r = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 r)))
  ] = 1%r.
proof.
    by conseq ill_to_bytes_ref4 (h_to_bytes_ref4 r).
qed.

(** step 1 : decode_scalar **)
equiv eq_spec_impl_decode_scalar_25519_ref4 : CurveProcedures.decode_scalar ~ M.__decode_scalar:
    k'{1}  = pack4 (to_list k{2})
    ==>
    res{1} = pack32 (to_list res{2}).
proof.
    proc; wp; auto => />.
    unroll for{2} ^while => />; wp; skip => /> &2.
    rewrite pack4E pack32E !/init8 !bits8E => />.
    rewrite !orE !andE !map2E //= wordP => i ib.
    rewrite !set64E !/get8 !/(\bits8) => />.
    rewrite !get_setE 1..5:/#; auto => />.
    rewrite !initiE 1:/# //= !of_listE !initiE 1,2:/# //=.
    rewrite !/to_list !/mkseq -!iotaredE => />. auto => />.
    rewrite !of_intE modz_small. apply bound_abs; 1:smt().
    rewrite !bits2wE !/int2bs !/mkseq -!iotaredE => />.
    smt(W8.initiE).
qed.

(** step 2 : decode_u_coordinate **)
equiv eq_spec_impl_decode_u_coordinate_ref4 : CurveProcedures.decode_u_coordinate ~ M.__decode_u_coordinate4:
    u'{1}                      =     pack4 (to_list u{2})
    ==>
    res{1}                     =     inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (eq_ph_set_last_bit_to_zero64 u{2}).
    inline *; wp; skip => /> &2.
    rewrite inzpRep4E. congr.
    rewrite to_uint_unpack4u64  valRep4E; congr; congr.
    rewrite /last_bit_to_zero64 => />.
    rewrite /to_list /mkseq /to_list -iotaredE => />.
    do split.
    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE 1:/# pack4E of_listE => />.
    + rewrite !initiE 1:/# //= !initiE 1:/# //= 1:/#.
    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE 1:/# pack4E of_listE => />.
    + rewrite !initiE 1:/# //= !initiE 1:/# //= 1:/#.
    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE 1:/# pack4E of_listE => />.
    + rewrite !initiE 1:/# //= !initiE 1:/# //= 1:/#.
    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite !setE !initiE 1,2:/# //=  pack4E of_listE => />.
    + rewrite !initiE 1:/# //= !initiE 1:/# //= 1:/#.
qed.

equiv eq_spec_impl_decode_u_coordinate_base_ref4 :
    CurveProcedures.decode_u_coordinate_base ~ M.__decode_u_coordinate_base4:
        true
        ==>
        res{1} = inzpRep4 res{2}.
proof.
            proc *.
    inline *; wp; skip => />.
    rewrite inzpRep4E. congr.
    rewrite to_uint_unpack4u64  valRep4E; congr; congr.
    rewrite /last_bit_to_zero64 => />.
    have !->: ((of_int 9))%W256.[255 <- false] = ((of_int 9))%W256.
    rewrite !of_intE !bits2wE !/int2bs !/mkseq -iotaredE => />.
    apply W256.ext_eq => />. move => X X0 X1.
    rewrite get_setE //. case (X = 255) => /> C.
    rewrite /to_list /mkseq /to_list -iotaredE => />.
 qed.

(** step 3 : ith_bit - quite slow, cryptoline candidate? **)
equiv eq_spec_impl_ith_bit_ref4 : CurveProcedures.ith_bit ~ M.__ith_bit :
    k'{1}                    = pack32 (to_list k{2}) /\
    ctr{1}                   = to_uint ctr{2} /\
    0 <= ctr{1} < 256
    ==>
    b2i res{1}                = to_uint res{2}.
proof.
proc; wp; skip => /> &2 H H0.
    rewrite (W64.and_mod 3 ctr{2}) //=  (W64.and_mod 6 (of_int (to_uint ctr{2} %% 8))%W64) //= !to_uint_shr //= !shr_shrw.
    smt(W64.to_uint_cmp  W64.of_uintK W64.to_uintK).
    rewrite /zeroextu64 /truncateu8 //=  !of_uintK => />.
    + rewrite  of_intE modz_small.  apply bound_abs. smt(W8.to_uint_cmp JUtils.powS_minus JUtils.pow2_0).
    rewrite bits2wE /int2bs /mkseq -iotaredE => />.
    auto => />.
    rewrite (modz_small (to_uint ctr{2} %% 8) W64.modulus). apply bound_abs. smt(W64.to_uint_cmp).
    rewrite (modz_small (to_uint ctr{2} %% 8) 64). apply bound_abs. smt(W64.to_uint_cmp).
    rewrite (modz_small (to_uint ctr{2} %% 8) W64.modulus). apply bound_abs. smt(W64.to_uint_cmp).
    pose ctr := to_uint ctr{2}.
    rewrite pack32E of_listE /to_list !/mkseq !initiE // -!iotaredE => />.
    rewrite !initiE //=. auto => />. smt().
    rewrite !/b2i !of_intE !bits2wE !/int2bs !/mkseq //=.
    rewrite -!iotaredE => />.
    rewrite !to_uintE !/bs2int !/w2bits !/mkseq /big /range !/predT -!iotaredE => />.
    rewrite !b2i0 => />.
    rewrite !initiE => />. smt(). auto => />.
    rewrite !/b2i => />.
    + case(ctr %/ 8 = 0) => /> *. smt().
    + case(ctr %/ 8 - 1 = 0) => /> *. smt().
    + case(ctr %/ 8 - 2 = 0) => /> *. smt().
    + case(ctr %/ 8 - 3 = 0) => /> *. smt().
    + case(ctr %/ 8 - 4 = 0) => /> *. smt().
    + case(ctr %/ 8 - 5 = 0) => /> *. smt().
    + case(ctr %/ 8 - 6 = 0) => /> *. smt().
    + case(ctr %/ 8 - 7 = 0) => /> *. smt().
    + case(ctr %/ 8 - 8 = 0) => /> *. smt().
    + case(ctr %/ 8 - 9 = 0) => /> *. smt().
    + case(ctr %/ 8 - 10 = 0) => /> *. smt().
    + case(ctr %/ 8 - 11 = 0) => /> *. smt().
    + case(ctr %/ 8 - 12 = 0) => /> *. smt().
    + case(ctr %/ 8 - 13 = 0) => /> *. smt().
    + case(ctr %/ 8 - 14 = 0) => /> *. smt().
    + case(ctr %/ 8 - 15 = 0) => /> *. smt().
    + case(ctr %/ 8 - 16 = 0) => /> *. smt().
    + case(ctr %/ 8 - 17 = 0) => /> *. smt().
    + case(ctr %/ 8 - 18 = 0) => /> *. smt().
    + case(ctr %/ 8 - 19 = 0) => /> *. smt().
    + case(ctr %/ 8 - 20 = 0) => /> *. smt().
    + case(ctr %/ 8 - 21 = 0) => /> *. smt().
    + case(ctr %/ 8 - 22 = 0) => /> *. smt().
    + case(ctr %/ 8 - 23 = 0) => /> *. smt().
    + case(ctr %/ 8 - 24 = 0) => /> *. smt().
    + case(ctr %/ 8 - 25 = 0) => /> *. smt().
    + case(ctr %/ 8 - 26 = 0) => /> *. smt().
    + case(ctr %/ 8 - 27 = 0) => /> *. smt().
    + case(ctr %/ 8 - 28 = 0) => /> *. smt().
    + case(ctr %/ 8 - 29 = 0) => /> *. smt().
    + case(ctr %/ 8 - 30 = 0) => /> *. smt().
    + case(ctr %/ 8 - 31 = 0) => /> *. smt(). smt().
qed.

equiv eq_spec_impl_init_points_ref4 :
    CurveProcedures.init_points ~ M.__init_points4 :
        init{1} = inzpRep4 initr{2}
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1 /\
        res{1}.`2 = inzpRep4 res{2}.`2 /\
        res{1}.`3 = inzpRep4 res{2}.`3 /\
        res{1}.`4 = inzpRep4 res{2}.`4.
proof.
    proc.
    wp. unroll for{2} ^while. wp. skip. move => &1 &2 H H0 H1 H2 H3 *.
    split; auto => />. rewrite /H4 /H0 /H2 /H3 /Zp.one /set0_64_ /inzpRep4 => />.
        rewrite /valRep4 /to_list /mkseq -iotaredE => />.
    split; auto => />. rewrite /H5  /H0 /H3 /H2 /Zp.zero /set0_64_ /inzpRep4 => />.
        rewrite /valRep4 /to_list /mkseq -iotaredE  => />.
    rewrite /H6  /H0 /H3 /H2 /Zp.zero /set0_64_ /inzpRep4 // /valRep4 /to_list /mkseq -iotaredE  => />.
qed.

(** step 4 : cswap **)
equiv eq_spec_impl_cswap_ref4 :
  CurveProcedures.cswap ~ M.__cswap4:
  x2{1}         = inzpRep4 x2{2}  /\
  z2{1}         = inzpRep4 z2r{2} /\
  x3{1}         = inzpRep4 x3{2}  /\
  z3{1}         = inzpRep4 z3{2}  /\
  b2i toswap{1} = to_uint toswap{2}
  ==>
  res{1}.`1     = inzpRep4 res{2}.`1  /\
  res{1}.`2     = inzpRep4 res{2}.`2  /\
  res{1}.`3     = inzpRep4 res{2}.`3  /\
  res{1}.`4     = inzpRep4 res{2}.`4.
proof.
proc.
do 4! unroll for{2} ^while.
case: (toswap{1}).
  rcondt {1} 1 => //. wp => /=. skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_set :  (set0_64.`6 - toswap{2}) = W64.onew. rewrite /set0_64_ /=.
    smt( W64.of_intN W64.to_uintN W64.WRingA.subr_eq0 W64.ofintS W64.of_int_modulus ).
    rewrite !mask_set /=.
   have lxor1 : forall (x1 x2:W64.t),  x1 `^` (x2 `^` x1) = x2.
      move=> *. rewrite xorwC -xorwA xorwK xorw0 //.
    have lxor2 : forall (x1 x2:W64.t),  x1 `^` (x1 `^` x2) = x2.
      move=> *. rewrite xorwA xorwK xor0w //.
  rewrite !lxor1 !lxor2.
      split. congr. apply Array4.ext_eq. smt(Array4.get_setE).
      split. congr. apply Array4.ext_eq. smt(Array4.get_setE).
      split. congr. apply Array4.ext_eq. smt(Array4.get_setE).
             congr. apply Array4.ext_eq. rewrite /copy_64 => />. smt(Array4.get_setE).
  rcondf {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_not_set :  (set0_64.`6 - toswap{2}) = W64.zero. rewrite /set0_64_ => />. smt().
    rewrite !mask_not_set !andw0 !xorw0 !/copy_64 => />.
    do split.
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
    congr. smt(Array4.initE Array4.ext_eq Array4.set_set_if).
qed.

(** step 5 : add_and_double **)
equiv eq_spec_impl_add_and_double_ref4 :
  CurveProcedures.add_and_double ~ M.__add_and_double4:
  init{1} = inzpRep4 init{2} /\
  x2{1}   = inzpRep4 x2{2}   /\
  z2{1}   = inzpRep4 z2r{2}  /\
  x3{1}   = inzpRep4 x3{2}   /\
  z3{1}   = inzpRep4 z3{2}
  ==>
  res{1}.`1 = inzpRep4 res{2}.`1 /\
  res{1}.`2 = inzpRep4 res{2}.`2 /\
  res{1}.`3 = inzpRep4 res{2}.`3 /\
  res{1}.`4 = inzpRep4 res{2}.`4.
proof.
  proc.
  call eq_spec_impl_mul_rss_ref4; wp.
  call eq_spec_impl_mul_sss_ref4; wp.
  call eq_spec_impl_add_sss_ref4; wp.
  call eq_spec_impl_sqr__ss_ref4; wp.
  call eq_spec_impl_mul_a24_ss_ref4;  wp.
  call eq_spec_impl_sqr__ss_ref4; wp.
  call eq_spec_impl_sub_sss_ref4; wp.
  call eq_spec_impl_mul_sss_ref4; wp.
  call eq_spec_impl_sub_sss_ref4; wp.
  call eq_spec_impl_add_sss_ref4; wp.
  call eq_spec_impl_sqr__ss_ref4; wp.
  call eq_spec_impl_sqr__ss_ref4; wp.
  call eq_spec_impl_mul_sss_ref4; wp.
  call eq_spec_impl_mul_sss_ref4; wp.
  call eq_spec_impl_add_sss_ref4; wp.
  call eq_spec_impl_sub_sss_ref4; wp.
  call eq_spec_impl_add_ssr_ref4; wp.
  call eq_spec_impl_sub_ssr_ref4; wp.
  done.
qed.

(** step 6 : montgomery_ladder_step **)
equiv eq_spec_impl_montgomery_ladder_step_ref4 :
 CurveProcedures.montgomery_ladder_step ~ M.__montgomery_ladder_step4:
        k'{1} =   pack32 (to_list k{2}) /\
        init'{1} = inzpRep4 init{2}             /\
        x2{1} = inzpRep4 x2{2}                  /\
        z2{1} = inzpRep4 z2r{2}                 /\
        x3{1} = inzpRep4 x3{2}                  /\
        z3{1} = inzpRep4 z3{2}                  /\
        b2i swapped{1} = to_uint swapped{2}     /\
        ctr'{1} = to_uint ctr{2}                /\
        0 <= ctr'{1} < 256
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1          /\
        res{1}.`2 = inzpRep4 res{2}.`2          /\
        res{1}.`3 = inzpRep4 res{2}.`3          /\
        res{1}.`4 = inzpRep4 res{2}.`4          /\
        b2i res{1}.`5 = to_uint res{2}.`5.
proof.
    proc => /=; wp.
    call eq_spec_impl_add_and_double_ref4. wp.
    call eq_spec_impl_cswap_ref4. wp.
    call eq_spec_impl_ith_bit_ref4. wp; skip.
    move => &1 &2 [H0] [H1] [H2] [H3] [H4] [H5] [H6] H7. split.
    auto => />. rewrite H0.
    move => [H8 H9] H10 H11 H12 H13 H14.
    split;  auto => />. rewrite /H14 /H13.
    rewrite /b2i.
    case: (swapped{1} ^^ H10).
    move => *. smt(W64.to_uintK W64.xorw0 W64.xorwC).
    move => *. smt(W64.ge2_modulus W64.to_uintK W64.of_uintK W64.xorwK).
qed.

(** step 7 : montgomery_ladder **)
equiv eq_spec_impl_montgomery_ladder_ref4 :
  CurveProcedures.montgomery_ladder ~ M.__montgomery_ladder4 :
        init'{1} = inzpRep4 u{2}                     /\
        k'{1} =  pack32 (to_list k{2})
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1               /\
        res{1}.`2 = inzpRep4 res{2}.`2.
proof.
    proc. wp. sp.
    unroll {1} 4.
    rcondt {1} 4. auto => />. inline CurveProcedures.init_points.
        wp. sp. skip. auto => />.
    while(
          k'{1} = pack32 (to_list  k{2})                   /\
          ctr{1} = to_uint ctr{2}                          /\
          -1 <= ctr{1} < 256                                /\
          init'{1} = inzpRep4 us{2}                        /\
          x2{1} = inzpRep4 x2{2}                           /\
          x3{1} = inzpRep4 x3{2}                           /\
          z2{1} = inzpRep4 z2r{2}                          /\
          z3{1} = inzpRep4 z3{2}                           /\
          b2i swapped{1} = to_uint swapped{2}).
        wp. sp. call eq_spec_impl_montgomery_ladder_step_ref4. skip. auto => />.
        move => &1 &2 ctrR H H0 H1 H2 E3. split.
        rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
        smt(W64.to_uint_cmp).
        move => H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. split. smt(W64.to_uint_cmp).
        rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
        rewrite to_uint1 to_uint0 //=. wp.
        call eq_spec_impl_montgomery_ladder_step_ref4. wp. call eq_spec_impl_init_points_ref4. skip. done.
qed.

(** step 8 : iterated square **)
equiv eq_spec_impl_it_sqr_ref4 :
 CurveProcedures.it_sqr ~ M._it_sqr4_p:
   f{1}            =    inzpRep4 x{2} /\
   i{1}            =    to_uint i{2}  /\
   i{1}            <=   W32.modulus   /\
    2              <=   to_uint i{2}  /\
    2             <=   i{1}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
proc. simplify. wp. sp.
  while (h{1}            =    inzpRep4 x{2}            /\
         ii{1}            =    to_uint i{2}              /\
         ii{1}            <=   W32.modulus               /\
         0                 <=   ii{1}
    ).
   wp. call eq_spec_impl_sqr_p_ref4. conseq(_: _ ==> h{1} = inzpRep4 x{2}).
    move => &1 &2 [[H][ H0] [H1] H2 [H3] H4 H5]. split. apply H5.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=.
    move => H6 H7 H8 H9. split. split. apply H9. split.
    rewrite to_uintB. rewrite  uleE => />. by smt(). rewrite to_uint1 H0 //.
    split. move: H1. smt(). move: H2. smt(). split. rewrite H0. move => H10.
    smt(@W32 W32.WRingA.subrK).
    smt(W32.to_uintK' W32.WRingA.subrr).
    skip. auto => />. wp.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w /ZF_of => /=.
    call eq_spec_impl_sqr_p_ref4.
    skip. auto => />. move => &2 H H0. split. split.
    rewrite to_uintB. rewrite uleE => />. move: H. smt().
    rewrite to_uint1 //. split. move: H0. smt(). move: H. smt().
    split. move => H1.
    smt(W32.ge2_modulus @W32 W32.WRingA.subrK).
    move => H1. move: H. smt().
qed.

equiv eq_spec_impl_it_sqr_s_ref4 :
    CurveProcedures.it_sqr ~ M._it_sqr4_s_:
        f{1}            =    inzpRep4 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2              <=   i{1}   ==>
        res{1} = inzpRep4 res{2}.
 proof.
    proc *. inline M._it_sqr4_s_. wp. sp.
    call eq_spec_impl_it_sqr_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_it_sqr_ss_ref4 :
        CurveProcedures.it_sqr ~ M._it_sqr4_ss_:
        f{1}            =    inzpRep4 x{2} /\
        i{1}            =    to_uint i{2}  /\
        2               <=   to_uint i{2}  /\
        i{1}            <=   W32.modulus   /\
        2               <=   i{1}
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M._it_sqr4_ss_.
    unroll for{2} ^while. wp. sp.
    call eq_spec_impl_it_sqr_ref4. skip. auto => />. move => &2 H H0. congr.
    apply Array4.ext_eq. move => H1 [H2] H3. smt(Array4.get_setE).
qed.


(** step 9 : invert **)
equiv eq_spec_impl_invert_ref4 :
  CurveProcedures.invert ~ M.__invert4 :
     fs{1} = inzpRep4 fs{2}
  ==> res{1} = inzpRep4 res{2}.
proof.
  transitivity
  CurveProcedures.invert_helper
  ( fs{1} = fs{2}          ==> res{1} = res{2})
  ( fs{1} = inzpRep4 fs{2} ==> res{1} = inzpRep4 res{2}).
  move => &1 &2 H; exists(fs{1}) => />.
  move => &1 &m &2 => />.
  proc *. symmetry; call eq_proc_proc_invert; skip => />.
  proc => /=; wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_sqr_s_ref4; wp.
  call (eq_spec_impl_it_sqr_s_ref4). wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_it_sqr_s_ref4; wp.
  call eq_spec_impl_mul_ss_ref4. wp.
  call eq_spec_impl_it_sqr_ss_ref4. wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_it_sqr_ss_ref4. wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_it_sqr_s_ref4. wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_it_sqr_ss_ref4. wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_it_sqr_ss_ref4. wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_it_sqr_s_ref4. wp.
  call eq_spec_impl_sqr_ss_ref4; wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_sqr_ss_ref4; wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_mul_ss_ref4; wp.
  call eq_spec_impl_sqr_s_ref4; wp.
  call eq_spec_impl_sqr_ss_ref4; wp.
  call eq_spec_impl_sqr_ss_ref4. wp. skip.
  done.
qed.

(** step 10 : encode point **)

equiv eq_spec_impl_encode_point_ref4 : CurveProcedures.encode_point ~ M.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    res{1} = pack4 (to_list  res{2}).
proof.
    proc => /=; wp.
     ecall {2} (ph_to_bytes_ref4 (r{2})). wp.
    call eq_spec_impl_mul_rss_ref4. wp.
    call eq_spec_impl_invert_ref4.
    wp; skip => /> &2 H H0 H1 H2.
    by rewrite -H2.
qed.
equiv eq_spec_impl_scalarmult_internal_ref4 :
    CurveProcedures.scalarmult_internal ~ M.__curve25519_internal_ref4:
        k'{1} = pack32 (to_list  k{2}) /\
        u''{1} = inzpRep4 u{2}
        ==>
        res{1} = pack4 (to_list res{2}).
proof.
    proc => /=; wp.
    call eq_spec_impl_encode_point_ref4; wp.
    call eq_spec_impl_montgomery_ladder_ref4. wp. skip.
    done.
qed.

(** step 11 : scalarmult **)
equiv eq_spec_impl_scalarmult_ref4 :
  CurveProcedures.scalarmult ~ M._curve25519_ref4:
        k'{1} = pack4 (to_list  _k{2}) /\
        u'{1} = pack4 (to_list _u{2})
        ==>
        res{1} = pack4 (to_list res{2}).
proof.
    proc => /=; wp.
    call eq_spec_impl_scalarmult_internal_ref4 => />; wp.
    call eq_spec_impl_decode_u_coordinate_ref4 => />; wp.
    call eq_spec_impl_decode_scalar_25519_ref4 => />.
    wp; skip => />.
qed.

equiv eq_spec_impl_scalarmult_base_ref4 :
    CurveProcedures.scalarmult_base ~ M._curve25519_ref4_base:
        k'{1} = pack4 (to_list _k{2})
        ==>
        res{1} = pack4 (to_list res{2}).
proof.
    proc => /=; wp.
    call eq_spec_impl_scalarmult_internal_ref4; wp.
    call eq_spec_impl_decode_u_coordinate_base_ref4; wp.
    call eq_spec_impl_decode_scalar_25519_ref4.
    wp. skip. move => *. smt(Zp_limbs.valRep4ToPack_xy).
qed.

lemma eq_spec_impl_scalarmult_jade_ref4 _qp _np _pp:
    equiv [CurveProcedures.scalarmult ~ M.jade_scalarmult_curve25519_amd64_ref4:
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        pp{2} = _pp                                                                              /\
        k'{1} = pack4 (to_list np{2}) /\
        u'{1} = pack4 (to_list pp{2})
        ==>
        res{1} = pack4 (to_list res{2}.`1) /\
        res{2}.`2 = W64.zero].
proof.
    proc *. inline M.jade_scalarmult_curve25519_amd64_ref4; wp.
    call (eq_spec_impl_scalarmult_ref4); wp; skip => />.
qed.

lemma eq_spec_impl_scalarmult_jade_base_ref4 _qp _np:
    equiv [CurveProcedures.scalarmult_base ~ M.jade_scalarmult_curve25519_amd64_ref4_base:
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        k'{1} = pack4 (to_list np{2})
        ==>
        res{1} = pack4 (to_list res{2}.`1)     /\
        res{2}.`2 = W64.zero].
proof.
    proc *. inline M.jade_scalarmult_curve25519_amd64_ref4_base. wp. sp.
    call (eq_spec_impl_scalarmult_base_ref4). skip. done.
qed.




(* Below are proofs for an older implementation that utilises ptrs *)
(*
lemma eq_spec_impl_scalarmult_ptr_ref4 mem _rp _kp _up :
    equiv [CurveProcedures.scalarmult ~ M.__curve25519_ref4_ptr:
        valid_ptr (W64.to_uint _up)  32                                                          /\
        valid_ptr (W64.to_uint _kp)  32                                                          /\
        valid_ptr (W64.to_uint _rp)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        rp{2} = _rp                                                                              /\
        kp{2} = _kp                                                                              /\
        up{2} = _up                                                                              /\
        u'{1} = pack4 (load_array4 (mem) (W64.to_uint _up))           /\
        k'{1} = pack4 (load_array4 (mem) (W64.to_uint _kp))
        ==>
        res{1} = pack4 (load_array4 Glob.mem{2} (W64.to_uint res{2}.`1))    /\
        res{2}.`2 = tt
    ].
proof.
    proc *.
    inline M.__curve25519_ref4_ptr. wp. sp.
    inline M.__load4 M.__store4.
    do 3! unroll for{2} ^while.
    sp. wp. auto => />.
    call eq_spec_impl_scalarmult_ref4. skip. auto => />.
    move => &2 H H0 H1 H2 H3 H4.
    do split.
    congr. congr.
    rewrite  /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr. congr. rewrite /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    move => H5 H6 H7.
    congr. congr. rewrite /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    apply (load_store_pos Glob.mem{2} rp{2} H7 0).
    rewrite /valid_ptr; split => />. done.
    apply (load_store_pos Glob.mem{2} rp{2} H7 8).
    rewrite /valid_ptr; split => />. done.
    apply (load_store_pos Glob.mem{2} rp{2} H7 16).
    rewrite /valid_ptr; split => />. done.
    apply (load_store_pos Glob.mem{2} rp{2} H7 24).
    rewrite /valid_ptr; split => />. done.
qed.
*)

(*
lemma eq_spec_impl_scalarmult_base_ptr_ref4 mem _rp _kp :
 equiv [CurveProcedures.scalarmult_base ~ M.__curve25519_ref4_base_ptr:
        valid_ptr (W64.to_uint _rp) 32 /\
        valid_ptr (W64.to_uint _kp) 32 /\
        Glob.mem{2} = mem /\
        rp{2} = _rp /\
        kp{2} = _kp /\
        k'{1} =  pack4 (load_array4 (Glob.mem{2}) (W64.to_uint _kp))
        ==>
        res{1} = pack4 (load_array4 Glob.mem{2} (W64.to_uint res{2}.`1)) /\ res{2}.`2 = tt].
proof.
    proc *. inline M.__curve25519_ref4_base_ptr M.__load4 M.__store4.
    do 2! unroll for{2} ^while.
    wp; call eq_spec_impl_scalarmult_base_ref4; wp; skip => />.
    move => H H0 H1 H2.
    do split.
    congr; congr.
    rewrite  /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    move => H3 H4.
    congr; congr.
    rewrite  /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    apply (load_store_pos mem _rp H4 0); rewrite /valid_ptr. smt(). smt().
    apply (load_store_pos mem _rp H4 8); rewrite /valid_ptr. smt(). smt().
    apply (load_store_pos mem _rp H4 16); rewrite /valid_ptr. smt(). smt().
    apply (load_store_pos mem _rp H4 24); rewrite /valid_ptr. smt(). smt().
qed.
*)

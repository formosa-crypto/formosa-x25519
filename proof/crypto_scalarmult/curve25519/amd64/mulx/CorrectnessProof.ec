require import AllCore Bool List Int IntDiv StdOrder CoreMap Real Ring Distr.

from Jasmin require import JModel JMemory JWord.

require import Curve25519_Procedures Curve25519_Operations Curve25519_auto_mulx Scalarmult_s W64limbs Zp_25519 Zp_limbs EClib.

import Zp Curve25519_auto_mulx Curve25519_Operations Curve25519_Procedures Scalarmult_s Array4 Array8 Array32 StdOrder.IntOrder EClib.

abbrev zexp = ZModpRing.exp.

(* additions, substractions and powers *)

lemma ill_add_rrs_mulx : islossless M.__add4_rrs.
    by proc; do 2! unroll for ^while; islossless.
qed.

lemma ph_add_rrs_mulx (_f _g: zp):
    phoare [M.__add4_rrs :
      inzpRep4 f = _f /\ inzpRep4 g = _g
      ==>
      inzpRep4 res = _f + _g
  ] = 1%r.
proof.
    by conseq ill_add_rrs_mulx (h_add_rrs_mulx _f _g).
qed.

equiv eq_spec_impl_add_rrs_mulx : CurveProcedures.add ~ M.__add4_rrs:
    f{1}   = inzpRep4 f{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_add_rrs_mulx (inzpRep4 f{2}) (inzpRep4 g{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.


lemma ill_sub_rrs_mulx : islossless M.__sub4_rrs.
    by proc; do 2! unroll for ^while; islossless.
qed.

lemma ph_sub_rrs_mulx (_f _g: zp):
    phoare [M.__sub4_rrs :
      inzpRep4 f = _f /\ inzpRep4 gs = _g
      ==>
      inzpRep4 res = _f - _g
  ] = 1%r.
proof.
    by conseq ill_sub_rrs_mulx (h_sub_rrs_mulx _f _g).
qed.

equiv eq_spec_impl_sub_rrs_mulx : CurveProcedures.sub ~ M.__sub4_rrs:
   f{1}   = inzpRep4 f{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_sub_rrs_mulx (inzpRep4 f{2}) (inzpRep4 gs{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

lemma ill_mul_a24_mulx : islossless M.__mul4_a24_rs by islossless.

lemma ph_mul_a24_mulx (_f: zp, _a24: int):
    phoare [M.__mul4_a24_rs :
      inzpRep4 fs = _f /\  _a24 = to_uint a24
      ==>
      inzpRep4 res = _f * inzp _a24
  ] = 1%r.
proof.
    by conseq ill_mul_a24_mulx (h_mul_a24_mulx _f _a24).
qed.

equiv eq_spec_impl_mul_a24_mulx : CurveProcedures.mul_a24 ~ M.__mul4_a24_rs:
    f{1}   = inzpRep4 fs{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_mul_a24_mulx (inzpRep4 fs{2}) (to_uint a24{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.


lemma ill_mul_rsr_mulx : islossless M.__mul4_rsr by islossless.


lemma ph_mul_rsr_mulx (_f _g : zp):
    phoare [M.__mul4_rsr :
      inzpRep4 fs = _f /\  inzpRep4 g = _g
      ==>
      inzpRep4 res = _f * _g] = 1%r.
proof.
    by conseq ill_mul_rsr_mulx (h_mul_rsr_mulx _f _g).
qed.

equiv eq_spec_impl_mul_rsr_mulx : CurveProcedures.mul ~ M.__mul4_rsr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_mul_rsr_mulx (inzpRep4 fs{2}) (inzpRep4 g{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_mul_rsr__rpr_mulx : M.__mul4_rsr ~ M.__mul4_rpr:
    fs{1}   = fp{2} /\
    g{1}   =  g{2}
    ==>
    res{1} = res{2}.
proof.
    by sim.
qed.

equiv eq_spec_impl_mul__rpr_mulx : CurveProcedures.mul ~ M.__mul4_rpr:
   f{1}   = inzpRep4 fp{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    transitivity
    M.__mul4_rsr
    ( f{1} = inzpRep4 fs{2} /\ g{1} = inzpRep4 g{2} ==> res{1} = inzpRep4 res{2})
    ( fs{1} = fp{2} /\ g{1} = g{2} ==> res{1} = res{2}).
    move => &1 &2 [H] H0.
    exists(fp{2}, g{2}) => />.
    move => &1 &m &2 => H H0. by rewrite -H0 H.
    proc *; call eq_spec_impl_mul_rsr_mulx.
    by skip => />.
    proc *; call eq_spec_impl_mul_rsr__rpr_mulx.
    by done.
qed.


equiv eq_spec_impl_sub_rrs_rsr_mulx : M.__sub4_rrs ~ M.__sub4_rsr:
    f{1} = fs{2} /\ gs{1} = g{2} ==> ={res}.
proof.
    proc.
    do 2! unroll for{1} ^while.
    do 2! unroll for{2} ^while.
    wp; skip => />.
qed.

equiv eq_spec_impl_sub_rsr_mulx : CurveProcedures.sub ~ M.__sub4_rsr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
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
    proc *; call eq_spec_impl_sub_rrs_mulx.
    by skip => />.
    proc *; call eq_spec_impl_sub_rrs_rsr_mulx.
    by done.
qed.


lemma ill_sqr_rr_mulx : islossless M.__sqr4_rr
    by islossless.

lemma ph_sqr_rr_mulx (_f: zp):
    phoare [M.__sqr4_rr :
      inzpRep4 f = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2] = 1%r.
proof.
    by conseq ill_sqr_rr_mulx (h_sqr_rr_mulx _f).
qed.

equiv eq_spec_impl__sqr_rr_mulx : CurveProcedures.sqr ~ M.__sqr4_rr:
    f{1}   = inzpRep4 f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_sqr_rr_mulx (inzpRep4 f{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_add_sss_mulx : CurveProcedures.add ~ M.__add4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M.__add4_sss. wp. sp.
    call eq_spec_impl_add_rrs_mulx. skip. auto => />.
qed.

equiv eq_spec_impl_add_ssr_mulx : CurveProcedures.add ~ M.__add4_ssr:
    g{1}   = inzpRep4 fs{2} /\
    f{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M.__add4_ssr. wp. sp.
    call eq_spec_impl_add_rrs_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sub_sss_mulx : CurveProcedures.sub ~ M.__sub4_sss:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 gs{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M.__sub4_sss. wp. sp.
    call eq_spec_impl_sub_rrs_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sub_ssr_mulx : CurveProcedures.sub ~ M.__sub4_ssr:
   f{1}   = inzpRep4 fs{2} /\
   g{1}   = inzpRep4 g{2}
   ==>
       res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M.__sub4_ssr. wp. sp.
    call eq_spec_impl_sub_rsr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_mul_a24_ss_mulx : CurveProcedures.mul_a24 ~ M.__mul4_a24_ss:
    f{1}   = inzpRep4 fs{2} /\
    a24{1} = to_uint a24{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M.__mul4_a24_ss. wp. sp.
    call eq_spec_impl_mul_a24_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_mul_rpr_mulx : CurveProcedures.mul ~ M._mul4_rpr:
    f{1}   = inzpRep4 fp{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M._mul4_rpr. wp. sp.
    call eq_spec_impl_mul__rpr_mulx. skip. auto => />.
qed.

equiv eq_spec_impl_mul_rsr__mulx : CurveProcedures.mul ~ M._mul4_rsr_:
    f{1}   = inzpRep4 _fs{2} /\
    g{1}   = inzpRep4 _g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M._mul4_rsr_. wp. sp.
    call eq_spec_impl_mul_rpr_mulx. skip. auto => />.
qed.

equiv eq_spec_impl_mul_ssr_mulx : CurveProcedures.mul ~ M.__mul4_ssr:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 g{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M.__mul4_ssr. wp. sp.
    call eq_spec_impl_mul_rsr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_mul_sss_mulx : CurveProcedures.mul ~ M.__mul4_sss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M.__mul4_sss. wp. sp.
    call eq_spec_impl_mul_rsr_mulx. skip. auto => />.
qed.

equiv eq_spec_impl_mul_rss_mulx : CurveProcedures.mul ~ M.__mul4_rss:
    f{1}   = inzpRep4 fs{2} /\
    g{1}   = inzpRep4 gs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M.__mul4_rss. wp. sp.
    call eq_spec_impl_mul_rsr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sqr_rr_mulx : CurveProcedures.sqr ~ M._sqr4_rr:
    f{1}   = inzpRep4 f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M._sqr4_rr. wp. sp.
    call (eq_spec_impl__sqr_rr_mulx) . skip. auto => />.
qed.


equiv eq_spec_impl_sqr_rr__mulx : CurveProcedures.sqr ~ M._sqr4_rr_:
    f{1}   = inzpRep4 _f{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline M._sqr4_rr_. wp. sp. rewrite /copy_64 => />.
    call eq_spec_impl_sqr_rr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sqr_ss_mulx : CurveProcedures.sqr ~ M.__sqr4_ss:
    f{1}   = inzpRep4 fs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M.__sqr4_ss. wp. sp.
    call eq_spec_impl__sqr_rr_mulx. skip. auto => />.
qed.


equiv eq_spec_impl_sqr_rs_mulx : CurveProcedures.sqr ~ M.__sqr4_rs:
    f{1}   = inzpRep4 fs{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.  inline M.__sqr4_rs. wp. sp.
    call eq_spec_impl__sqr_rr_mulx. skip. auto => />.
qed.

(** tp bytes **)

lemma ill_to_bytes_mulx : islossless M.__tobytes4 by islossless.

lemma ph_to_bytes_mulx r:
  phoare [M.__tobytes4 :
      r = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 r)))
  ] = 1%r.
proof.
    by conseq ill_to_bytes_mulx (eq_to_bytes_mulx r).
qed.

equiv eq_spec_impl_init_points_mulx :
    CurveProcedures.init_points ~ M.__init_points4 :
        init{1} = inzpRep4 initr{2}
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1 /\
        res{1}.`2 = inzpRep4 res{2}.`2 /\
        res{1}.`3 = inzpRep4 res{2}.`3 /\
        res{1}.`4 = inzpRep4 res{2}.`4.
proof.
    proc.
    wp. unroll for{2} ^while. wp. skip. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6.
    split; auto => />. rewrite /H4 /H0 /H2 /H3 /Zp.one /set0_64_ /inzpRep4 => />.
        rewrite /valRep4 /to_list /mkseq -iotaredE => />.
    split; auto => />. rewrite /H5  /H0 /H3 /H2 /Zp.zero /set0_64_ /inzpRep4 => />.
        rewrite /valRep4 /to_list /mkseq -iotaredE  => />.
    rewrite /H6  /H0 /H3 /H2 /Zp.zero /set0_64_ /inzpRep4 // /valRep4 /to_list /mkseq -iotaredE  => />.
qed.

equiv eq_spec_impl_ith_bit_mulx : CurveProcedures.ith_bit ~ M.__ith_bit :
    k'{1} =     pack32 (to_list k{2}) /\
    ctr{1}                   = to_uint ctr{2} /\
    0 <= ctr{1} < 256
    ==>
    b2i res{1}                = to_uint res{2}.
proof.
    proc; wp; skip => /> &2 H H0.
    rewrite (W64.and_mod 3 ctr{2}) //=  (W64.and_mod 6 (of_int (to_uint ctr{2} %% 8))%W64) //= !to_uint_shr //= !shr_shrw.
    smt(W64.to_uint_cmp  W64.of_uintK W64.to_uintK).
    rewrite /zeroextu64 /truncateu8 //=  !of_uintK => />.
    + rewrite  of_intE modz_small.  apply bound_abs. smt(W8.to_uint_cmp  @JUtils).
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
    + case(ctr %/ 8 - 31 = 0) => /> *. smt().
    + case(ctr %/ 8 - 32 = 0) => /> *. smt().
    smt().
qed.


equiv eq_spec_impl_decode_scalar_25519_mulx : CurveProcedures.decode_scalar ~ M.__decode_scalar:
    k'{1}  = pack4 (to_list k{2})
    ==>
    res{1} = pack32 (to_list res{2}).
proof.
    proc; wp; auto => />.
    unroll for{2} ^while => />; wp; skip => /> &2.
    rewrite !/set64_direct !/get8 !/init8 => />.
    rewrite pack4E pack32E.
    rewrite !/to_list /mkseq -!iotaredE => /> .
    rewrite !of_intE modz_small. by apply bound_abs. rewrite !bits2wE /int2bs /mkseq -!iotaredE => />.
    rewrite wordP => i rgi />.
    rewrite !of_listE !bits8E //= => />.
    rewrite !get_setE //= !orE !andE !map2E //=.
    rewrite !initiE => />.
    rewrite !initiE => />. smt(). smt().
    + case(i = 0) => /> *; case(i = 1) => /> *; case(i = 2) => /> *; case(i = 254) => /> *; case(i = 255) => /> *.
    + case(i %/ 8 = 0) => /> *.
    + rewrite initiE => /> . smt(). rewrite initiE => />. smt(). rewrite initiE => />. smt(). smt().
    + case(i %/ 8 - 1 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 2 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 3 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 4 = 0) => /> *.
    rewrite initiE => /> /#.
    + case(i %/ 8 - 5 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 6 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 7 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 8 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 9 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 10 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 11 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 12 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 13 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 14 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 15 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 16 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 17 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 18 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 19 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 20 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 21 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 22 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 23 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 24 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 25 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 26 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 27 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 28 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 29 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 30 = 0) => /> *.
    + rewrite initiE => /> /#.
    + case(i %/ 8 - 31 = 0) => /> *.
    + rewrite !initiE => />. smt().
    + rewrite !initiE => />. smt().
    case(i %/ 64 = 0) => /> *. smt(). smt().
    + rewrite !initiE => /> /#. smt().
qed.


lemma eq_set_last_bit_to_zero64_mulx x :
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

lemma ill_set_last_bit_to_zero64_mulx: islossless M.__decode_u_coordinate4 by islossless.

lemma eq_ph_set_last_bit_to_zero64_mulx x:
  phoare [
    M.__decode_u_coordinate4 :
    u = x
    ==>
    res = Curve25519_Operations.last_bit_to_zero64 x
  ] = 1%r.
proof.
    by conseq ill_set_last_bit_to_zero64_mulx (eq_set_last_bit_to_zero64_mulx x).
qed.

equiv eq_spec_impl_decode_u_coordinate_mulx : CurveProcedures.decode_u_coordinate ~ M.__decode_u_coordinate4:
    u'{1}                      =     pack4 (to_list u{2})
    ==>
    res{1}                     =     inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (eq_ph_set_last_bit_to_zero64_mulx u{2}).
    inline *; wp; skip => /> &2.
    rewrite inzpRep4E. congr.
    rewrite to_uint_unpack4u64  valRep4E; congr; congr.
    rewrite /last_bit_to_zero64 => />.
    rewrite /to_list /mkseq /to_list -iotaredE => />.
    do split.
    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE. smt().
    + rewrite pack4E => />. rewrite of_listE => />.
    + rewrite initE => />.
    + have ->: (0 <= i && i < 256) by smt(). auto => />.
    + rewrite initE => />. have ->: 0 <= i %/ 64 by smt(). auto => />.
    + case(i %/ 64 < 4) => /> *. smt(). smt().

    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE. smt().
    + rewrite pack4E => />. rewrite of_listE => />.
    + rewrite initE => />.
    + have ->: (0 <= 64 + i && 64 + i < 256) by smt(). auto => />.
    + rewrite initE => />. have ->: 0 <= (64 + i) %/ 64 by smt(). auto => />.
    + case((64 + i) %/ 64 < 4) => /> *. smt(). smt().

    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.
    + rewrite set_neqiE. smt().
    + rewrite pack4E => />. rewrite of_listE => />.
    + rewrite initE => />.
    + have ->: (0 <= 128 + i && 128 + i < 256) by smt(). auto => />.
    + rewrite initE => />. have ->: 0 <= (128 + i) %/ 64 by smt(). auto => />.
    + case((128 + i) %/ 64 < 4) => /> *. smt(). smt().
    + rewrite !wordP => /> i I I0. rewrite !bits64iE => />.

    rewrite pack4E => />. rewrite of_listE => />.
    rewrite !setE => />. rewrite initE => />.
    have ->: (0 <= 192 + i && 192 + i < 256) by smt(). auto => />.
    rewrite !initE => />.
    have ->: (0 <= i && i < 64) by smt().
    have ->: (0 <= 192 + i && 192 + i < 256) by smt().
    auto => />.
    case (i <> 63) => /> C.
    have ->: 192 + i <> 255 by smt().
    auto => />. rewrite !initE. smt().
qed.


equiv eq_spec_impl_decode_u_coordinate_base_mulx :
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


equiv eq_spec_impl_cswap_mulx :
    CurveProcedures.cswap ~ M.__cswap4:
        x2{1}         = inzpRep4 x2{2}      /\
        z2{1}         = inzpRep4 z2r{2}     /\
        x3{1}         = inzpRep4 x3{2}      /\
        z3{1}         = inzpRep4 z3{2}      /\
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
        have mask_set :  (set0_64.`6 - toswap{2}) = W64.onew. rewrite /set0_64_ /=. smt().
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

equiv eq_spec_impl_add_and_double_mulx :
    CurveProcedures.add_and_double ~ M.__add_and_double4:
        init{1} = inzpRep4 init{2}     /\
        x2{1}   = inzpRep4 x2{2}       /\
        z2{1}   = inzpRep4 z2r{2}      /\
        x3{1}   = inzpRep4 x3{2}       /\
        z3{1}   = inzpRep4 z3{2}
        ==>
        res{1}.`1 = inzpRep4 res{2}.`1 /\
        res{1}.`2 = inzpRep4 res{2}.`2 /\
        res{1}.`3 = inzpRep4 res{2}.`3 /\
        res{1}.`4 = inzpRep4 res{2}.`4.
proof.
    proc => /=; wp.
    call eq_spec_impl_mul_rss_mulx; wp.
    call eq_spec_impl_mul_sss_mulx; wp.
    call eq_spec_impl_add_sss_mulx; wp.
    call eq_spec_impl_sqr_ss_mulx;  wp.
    call eq_spec_impl_mul_a24_ss_mulx; wp.
    call eq_spec_impl_sqr_ss_mulx; wp.
    swap{1} 14 1.
    call eq_spec_impl_mul_ssr_mulx; wp.
    call eq_spec_impl_sub_ssr_mulx; wp.
    call eq_spec_impl_sub_sss_mulx; wp.
    call eq_spec_impl_add_sss_mulx; wp.
    call eq_spec_impl_sqr_rs_mulx; wp.
    call eq_spec_impl_sqr_ss_mulx; wp.
    call eq_spec_impl_mul_sss_mulx; wp.
    call eq_spec_impl_mul_sss_mulx; wp.
    call eq_spec_impl_add_sss_mulx; wp.
    call eq_spec_impl_sub_sss_mulx; wp.
    call eq_spec_impl_add_ssr_mulx; wp.
    call eq_spec_impl_sub_ssr_mulx; wp.
    skip. by done.
qed.

equiv eq_spec_impl_montgomery_ladder_step_mulx :
    CurveProcedures.montgomery_ladder_step ~ M.__montgomery_ladder_step4:
        k'{1} =   pack32 (to_list k{2})         /\
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
    call eq_spec_impl_add_and_double_mulx. wp.
    call eq_spec_impl_cswap_mulx. wp.
    call eq_spec_impl_ith_bit_mulx. wp. skip.
    move => &1 &2 [H0] [H1] [H2] [H3] [H4] [H5] [H6] H7. split.
    auto => />. rewrite H0.
    move => [H8 H9] H10 H11 H12 H13 H14.
    split;  auto => />. rewrite /H14 /H13.
    rewrite /b2i.
    case: (swapped{1} ^^ H10).
    move => *. smt(W64.to_uintK W64.xorw0 W64.xorwC).
    move => *. smt(W64.ge2_modulus W64.to_uintK W64.of_uintK W64.xorwK).
qed.

equiv eq_spec_impl_montgomery_ladder_mulx :
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
        wp. sp. call eq_spec_impl_montgomery_ladder_step_mulx. skip. auto => />.
        move => &1 &2 ctrR H H0 H1 H2 E3. split.
        rewrite to_uintB. rewrite uleE to_uint1 => />. smt(). rewrite to_uint1 => />.
        smt(W64.to_uint_cmp).
        move => H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. split. smt(W64.to_uint_cmp).
        rewrite ultE to_uintB. rewrite uleE to_uint1. smt().
        rewrite to_uint1 to_uint0 //=. wp.
        call eq_spec_impl_montgomery_ladder_step_mulx. wp. call eq_spec_impl_init_points_mulx. skip. done.
qed.


equiv eq_spec_impl_it_sqr_aux_mulx :
        M.__it_sqr4_x2 ~ CurveProcedures.it_sqr_aux:
        inzpRep4 f{1} = a{2} /\
        W32.to_uint i{1} = l{2} /\
        0 < l{2}
        ==>
        inzpRep4 res{1} = res{2}.
proof.
    proc; simplify.
    while(
        0 <= ii{2} /\ 0 <= W32.to_uint i{1} /\ ii{2} = W32.to_uint i{1} /\
        f{2} = inzpRep4 f{1}  /\ zf{1} = (0 = W32.to_uint i{1})
    ).
    wp.
    symmetry.
    call eq_spec_impl__sqr_rr_mulx. wp. call eq_spec_impl__sqr_rr_mulx. wp. symmetry.
    skip => />.
    move => &1 *. do split. smt().
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />.
    + rewrite to_uintB. rewrite uleE to_uint1; smt(). rewrite to_uint1. smt(W32.to_uint_cmp).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite to_uintB.
    + rewrite uleE to_uint1; smt(). rewrite to_uint1 //.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of to_uintB.
    + rewrite uleE to_uint1. smt(). rewrite -to_uintB. rewrite uleE. smt(W32.to_uint_cmp).
    + rewrite to_uintB. rewrite uleE to_uint1; smt(). rewrite to_uint1.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    wp. symmetry. call eq_spec_impl__sqr_rr_mulx. wp. call eq_spec_impl__sqr_rr_mulx. wp.
    symmetry.
    skip => />. move => &1 H.
    do split. smt().
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    rewrite to_uintB. rewrite uleE to_uint1. smt(W32.to_uint_cmp). rewrite to_uint1 //.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
qed.

equiv eq_spec_impl_it_sqr_aux_mulx_test :
        CurveProcedures.it_sqr_aux ~ M.__it_sqr4_x2:
        a{1} = inzpRep4 f{2} /\
        l{1} = W32.to_uint i{2} /\
        0 < l{1}
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc; simplify.
    while(
        0 <= ii{1} /\ 0 <= W32.to_uint i{2} /\ ii{1} = W32.to_uint i{2} /\
        f{1} = inzpRep4 f{2}  /\ zf{2} = (0 = W32.to_uint i{2})
    ).
    wp. call eq_spec_impl__sqr_rr_mulx. wp. call eq_spec_impl__sqr_rr_mulx. wp.
    skip => />.
    move => &1 *. do split. smt().
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />.
    + rewrite to_uintB. rewrite uleE to_uint1; smt(). rewrite to_uint1. smt(W32.to_uint_cmp).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite to_uintB.
    + rewrite uleE to_uint1; smt(). rewrite to_uint1 //.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of to_uintB.
    + rewrite uleE to_uint1. smt(). rewrite -to_uintB. rewrite uleE. smt(W32.to_uint_cmp).
    + rewrite to_uintB. rewrite uleE to_uint1; smt(). rewrite to_uint1.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    wp. call eq_spec_impl__sqr_rr_mulx. wp. call eq_spec_impl__sqr_rr_mulx. wp.
    skip => />. move => &1 H.
    do split. smt().
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    rewrite to_uintB. rewrite uleE to_uint1. smt(W32.to_uint_cmp). rewrite to_uint1 //.
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
    rewrite /DEC_32 /rflags_of_aluop_nocf_w => />. rewrite /ZF_of => *.
    smt(W32.ge2_modulus W32.of_uintK W32.to_uintK W32.to_uintN W32.of_intD).
qed.


lemma eq_spec_impl__it_sqr_mulx (i1: int) (i2: int):
    i1 = i2 => 2 <= i1  =>
equiv[
        M.__it_sqr4_x2 ~ CurveProcedures.it_sqr:
        i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        W32.to_uint i{1} = i{2} /\
        inzpRep4 f{1} = f{2}
        ==>
        inzpRep4 res{1} = zexp res{2} (exp 2 i1)
    ].
proof.
    move => I I0.
    transitivity
     CurveProcedures.it_sqr_aux
     (
       l{2} = W32.to_uint i{1}  /\
       a{2} = inzpRep4 f{1} /\
       1 < l{2}
        ==>
        inzpRep4 res{1} = res{2})
     (  a{1} = f{2} /\
        l{1} = i{2} /\
        l{1} = i1 /\
        l{1} = i2 /\
        2 <= i{2}
        ==>
        res{1} = zexp res{2} (exp 2 i1)).
    auto => />.
    move => &1 &2 *.
    exists(f{2}, i{2}) => />. smt().
    move => &1 &m &2 H H0. rewrite -H0. assumption.
    proc *.
    call eq_spec_impl_it_sqr_aux_mulx. skip => />. smt(W32.to_uint_cmp).

    proc; inline *; simplify.
    seq 7 6 : (ii{1} = l{1} - 1 /\
        h{2} = (zexp a{1} 2) /\
        0 <= ii{2} /\
        0 <= ii{1} /\
        ii{1} = ii{2} /\
        1 <= counter{2} <= i1 /\
        counter{2} = i1 - ii{2} /\
        f{1} = zexp h{2} (exp 2 counter{2})).
        wp; skip. auto => />. move => *.  smt().

    while(
        0 <= ii{1} /\
        0 <= ii{2} /\
        ii{1} = ii{2} /\
        1 <= counter{2} /\
        counter{2} = i1 - ii{2} /\
        f{1} = zexp h{2} (exp 2 (counter{2}))).
    wp; skip. auto => />.
    move => &1 &2 H H0 H1.
    smt( ZModpRing.exprM IntID.exprN IntID.exprN1 IntID.exprD_nneg).
    skip => />. move => &1 &2 H H1 H2 H3 H4 H5 H6 H7 H8 H9.
    have H10: H4 = 0. smt(). rewrite H10 => />.
qed.

lemma eq_spec_impl__it_sqr_mulx_x2 (i1: int) (i2: int):
    2*i1 = i2 => 2 <= i1 => 4 <= i2 => i2 %% 2 = 0 =>
equiv[
        M.__it_sqr4_x2 ~ CurveProcedures.it_sqr:
        i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        2*W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 f{1} = f{2}
        ==>
        inzpRep4 res{1} = res{2}
    ].
proof.
    move => I I0 I1 I2;
     transitivity
     CurveProcedures.it_sqr_aux
     (
       l{2} = W32.to_uint i{1}  /\
       a{2} = inzpRep4 f{1} /\
       1 < l{2}
        ==>
        inzpRep4 res{1} = res{2})
     (  a{1} = f{2} /\
        2*l{1} = i{2} /\
        l{1} = i1 /\
        i{2} = i2  /\
        4 <= i{2}  /\
        2 <= l{1}
        ==>
        res{1} = res{2}).
    auto => />. move => &1 &2 *.
    exists(f{2}, i1) => />. smt(). smt().
    proc *.
    call eq_spec_impl_it_sqr_aux_mulx. skip => />. smt(W32.to_uint_cmp).
     proc; simplify. inline *.
     seq 7 6 : (
        i2 = 2*l{1} /\
        ii{1} = l{1} - counter{2} /\
        ii{2} = i2 - counter{2} /\
        h{2} = (zexp a{1} 2) /\
        0 <= ii{2} /\
        0 <= ii{1} /\
        1 <= counter{2} <= i1 /\
        f{1} = zexp h{2} (exp 2 counter{2})).
    wp; skip. auto => />.
    move => *. smt().
      async while
      [ (fun r => 0%r < ii%r), (ii{1} - 1)%r ]
      [ (fun r => 0%r < ii%r), (ii{1} - 1)%r ]
        (0 < ii{1} /\ 0 < ii{2}) (!(0 < ii{1}))
      :
      (
        (ii{2} %% 2 = 0   => 2*ii{1} - 1 = ii{2})  /\
        (ii{2} %% 2 <> 0  => 2*ii{1}     = ii{2})  /\
        0 <= ii{1} /\
        0 <= ii{2}
      ).
    auto => />;  move => &1 &2 * /#.
    auto => />;  move => &1 &2 * /#.
    auto => />;  move => &1 &2 * /#.
    auto => />;  move => &2 * /#.
    move => &1; auto => />.
    move => v1 v2; auto => />.
    while(
        0 <= ii{1} /\
        0 <= ii{2} /\
        (ii{2} %% 2 = 0   => 2*ii{1} - 1 = ii{2})  /\
        (ii{2} %% 2 <> 0  => 2*ii{1}     = ii{2})  /\
        1 <= counter{2} /\
        f{1} = zexp h{2} (exp 2 counter{2})
    ) => //=.
   auto => />; move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7.
   smt( ZModpRing.exprM IntID.exprN IntID.exprN1 IntID.exprD_nneg).
   auto => />; move => &1 &2 H H0 H1 H2 H3 H4 H5.
   smt( ZModpRing.exprM IntID.exprN IntID.exprN1 IntID.exprD_nneg).
    while true (ii) => //.
    move => H; auto => />. skip => />; move => &hr H0 H1 H2 H3 H4 H5 /#.
    while true (ii) => //. move => H; auto => /> /#. skip => /> /#.
    skip => />. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 /#.
qed.


lemma eq_spec_impl_it_sqr_x2_mulx (i1: int) (i2: int):
    i1 = i2 => 2 <= i1 => i2 %% 2 = 0 =>
equiv[
        M._it_sqr4_x2 ~ CurveProcedures.it_sqr:
        i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 f{1} = f{2}
        ==>
        inzpRep4 res{1} = zexp res{2} (exp 2 i1)
    ].
    move => *; proc *.
    inline {1} 1. sp; wp.
    call (eq_spec_impl__it_sqr_mulx i1 i2). skip => />.
qed.


lemma  eq_spec_impl_it_sqr_x2__mulx  (i1: int) (i2: int):
    i1 = i2 => 2 <= i1 => i2 %% 2 = 0 =>
    equiv[
        M._it_sqr4_x2_ ~ CurveProcedures.it_sqr:
        i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 _f{1} = f{2}
        ==>
        inzpRep4 res{1} = zexp res{2} (exp 2 i1)
    ].
proof.
    move => *; proc *.
    inline{1} 1. inline{1} 5. wp; sp.
    call (eq_spec_impl__it_sqr_mulx i1 i2). skip => />.
qed.


lemma eq_spec_impl_it_sqr_x2_mulx_x2 (i1: int) (i2: int):
    2*i1 = i2 => 2 <= i1 => 4 <= i2 => i2 %% 2 = 0 =>
equiv[
        M._it_sqr4_x2 ~ CurveProcedures.it_sqr:
       i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        2*W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 f{1} = f{2}
        ==>
        inzpRep4 res{1} = res{2}
    ].
    move => *; proc *.
    inline {1} 1. sp; wp.
    call (eq_spec_impl__it_sqr_mulx_x2 i1 i2). skip => />.
qed.


lemma  eq_spec_impl_it_sqr_x2__mulx_x2  (i1: int) (i2: int):
    2*i1 = i2 => 2 <= i1 => 4 <= i2 => i2 %% 2 = 0 =>
        equiv[
        M._it_sqr4_x2_ ~ CurveProcedures.it_sqr:
         i1 = W32.to_uint i{1} /\
        i2 = i{2}   /\
        2*W32.to_uint i{1} = i{2} /\
        i{2} %% 2 = 0 /\
        inzpRep4 _f{1} = f{2}
        ==>
        inzpRep4 res{1} = res{2}
    ].
proof.
    move => *; proc *.
    inline{1} 1. inline{1} 5. wp; sp.
    call (eq_spec_impl__it_sqr_mulx_x2 i1 i2). skip => />.
qed.

equiv eq_spec_impl_invert_mulx :
    CurveProcedures.invert ~ M.__invert4 :
        fs{1} = inzpRep4 f{2}
        ==>
        res{1} = inzpRep4 res{2}.
proof.
    proc. sp.
    auto => />.
    call eq_spec_impl_mul_rsr__mulx. wp.
    call eq_spec_impl_sqr_rr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 2 4); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 25 50); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 50 100); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 25 50); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 5 10); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 10 20); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 5 10); wp; symmetry.
    call eq_spec_impl_mul_rsr__mulx. wp.
    symmetry;  call (eq_spec_impl_it_sqr_x2__mulx_x2 2 4); wp; symmetry.
    call eq_spec_impl_sqr_rr__mulx. wp.
    call eq_spec_impl_mul_rsr__mulx. wp.
    call eq_spec_impl_sqr_rr__mulx.  wp.
    call eq_spec_impl_mul_rsr__mulx. wp.
    call eq_spec_impl_mul_rsr__mulx. wp.
    call eq_spec_impl_sqr_rr__mulx. wp.
    call eq_spec_impl_sqr_rr__mulx. wp.
    call eq_spec_impl_sqr_rr__mulx. wp.
    skip.  done.
qed.


equiv eq_spec_impl_encode_point_mulx : CurveProcedures.encode_point ~ M.__encode_point4:
    x2{1}                 = inzpRep4 x2{2} /\
    z2{1}                 = inzpRep4 z2r{2}
    ==>
    res{1} = pack4 (to_list  res{2}).
proof.
    proc. wp.
    ecall {2} (ph_to_bytes_mulx (r{2})). wp.
    call eq_spec_impl_mul_rsr_mulx. wp.
    call eq_spec_impl_invert_mulx.
    wp; skip => />. move => H H0 H1.
    by rewrite -H1.
qed.

equiv eq_spec_impl_scalarmult_internal_mulx :
    CurveProcedures.scalarmult_internal ~ M.__curve25519_internal_mulx:
        k'{1} = pack32 (to_list  k{2}) /\
        u''{1} = inzpRep4 u{2}
        ==>
        res{1} = pack4 (to_list res{2}).
proof.
    proc => /=. wp.
    call eq_spec_impl_encode_point_mulx. wp.
    call eq_spec_impl_montgomery_ladder_mulx. wp. skip.
    done.
qed.

equiv eq_spec_impl_scalarmult_mulx :
    CurveProcedures.scalarmult ~ M.__curve25519_mulx:
        k'{1} = pack4 (to_list  _k{2}) /\
        u'{1} = pack4 (to_list _u{2})
        ==>
        res{1} = pack4 (to_list res{2}).
proof.
    proc => /=. wp.
    call eq_spec_impl_scalarmult_internal_mulx => />. wp.
    call eq_spec_impl_decode_u_coordinate_mulx => />. wp.
    call eq_spec_impl_decode_scalar_25519_mulx => />.
    wp; skip => />.
qed.

equiv eq_spec_impl_scalarmult_base_mulx :
    CurveProcedures.scalarmult_base ~ M.__curve25519_mulx_base:
    k'{1} = pack4 (to_list  _k{2})
    ==>
    res{1} = pack4 (to_list res{2}).
proof.
    proc => /=; wp.
    call eq_spec_impl_scalarmult_internal_mulx => />; wp.
    call eq_spec_impl_decode_u_coordinate_base_mulx => />; wp.
    call eq_spec_impl_decode_scalar_25519_mulx.
    wp. skip => />.
qed.

lemma eq_spec_impl_scalarmult_jade_mulx _qp _np _pp:
    equiv [CurveProcedures.scalarmult ~ M.jade_scalarmult_curve25519_amd64_mulx:
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        pp{2} = _pp                                                                              /\
        k'{1} = pack4 (to_list np{2}) /\
        u'{1} = pack4 (to_list  pp{2})
        ==>
        res{1} = pack4 (to_list res{2}.`1)     /\
        res{2}.`2 = W64.zero].
proof.
    proc *. inline M.jade_scalarmult_curve25519_amd64_mulx; wp; sp.
    call eq_spec_impl_scalarmult_mulx. skip => />.
qed.

lemma eq_spec_impl_scalarmult_jade_base  _qp _np:
    equiv [CurveProcedures.scalarmult_base ~ M.jade_scalarmult_curve25519_amd64_mulx_base:
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        k'{1} = pack4 (to_list np{2})
        ==>
        res{1} = pack4 (to_list res{2}.`1)     /\
        res{2}.`2 = W64.zero].
proof.
    proc *. inline M.jade_scalarmult_curve25519_amd64_mulx_base; wp; sp.
    call eq_spec_impl_scalarmult_base_mulx. skip => />.
qed.

(* Proofs for older implementation *)
(*
lemma eq_spec_impl_scalarmult_jade_mulx mem _qp _np _pp:
    equiv [CurveProcedures.scalarmult ~ M.jade_scalarmult_curve25519_amd64_mulx:
        valid_ptr (W64.to_uint _qp)  32                                                          /\
        valid_ptr (W64.to_uint _np)  32                                                          /\
        valid_ptr (W64.to_uint _pp)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        pp{2} = _pp                                                                              /\
        k'{1} = pack4 (load_array4 (Glob.mem{2}) (W64.to_uint np{2})) /\
        u'{1} = pack4 (load_array4 (Glob.mem{2}) (W64.to_uint pp{2}))
        ==>
        res{1} = pack4 (load_array4 Glob.mem{2} (W64.to_uint res{2}.`1))     /\
        res{2}.`2 = W64.zero].
proof.
    proc *. inline M.jade_scalarmult_curve25519_amd64_mulx; wp; sp.
    inline M.__load4 M.__store4.
    do 3! unroll for{2} ^while. wp. sp.
    call eq_spec_impl_scalarmult_mulx. skip => />.
    move => &2 H H0 H1 H2 H3 H4.
    do split.
    congr; congr; rewrite  /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; congr; rewrite /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    move => H5 H6 H7.
    congr; rewrite /load_array4 /to_list /mkseq -iotaredE => />.
    congr; congr.
    apply (load_store_pos Glob.mem{2} qp{2} H7 0). rewrite /valid_ptr; by do split => /> //=. done.
    congr.
    apply (load_store_pos Glob.mem{2} qp{2} H7 8). rewrite /valid_ptr; by do split => /> //=. done.
    congr.
    apply (load_store_pos Glob.mem{2} qp{2} H7 16). rewrite /valid_ptr; by do split => /> //=. done.
    congr.
    apply (load_store_pos Glob.mem{2} qp{2} H7 24). rewrite /valid_ptr; by do split => /> //=. done.
qed.
*)

(*
lemma eq_spec_impl_scalarmult_jade_base  mem _qp _np:
    equiv [CurveProcedures.scalarmult_base ~ M.jade_scalarmult_curve25519_amd64_mulx_base:
        valid_ptr (W64.to_uint _qp)  32                                                          /\
        valid_ptr (W64.to_uint _np)  32                                                          /\
        Glob.mem{2} = mem                                                                        /\
        qp{2} = _qp                                                                              /\
        np{2} = _np                                                                              /\
        k'{1} = pack4 (load_array4 (Glob.mem{2}) (W64.to_uint np{2}))
        ==>
        res{1} = pack4 (load_array4 Glob.mem{2} (W64.to_uint res{2}.`1))     /\
        res{2}.`2 = W64.zero].
proof.
    proc *. inline M.jade_scalarmult_curve25519_amd64_mulx_base. wp. sp.
    inline M.__load4 M.__store4.
    do 2! unroll for{2} ^while. wp; sp.
    call eq_spec_impl_scalarmult_base_mulx. skip  => />.
    move => &2 H H0 H1 H2. do split.
    congr; congr; rewrite  /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    congr; rewrite !to_uintD_small !to_uint_small => />. smt().
    move => H3 H4.
    congr; congr; rewrite /load_array4 /to_list /mkseq -iotaredE => />.
    do split.
    apply (load_store_pos Glob.mem{2} qp{2} H4 0). rewrite /valid_ptr; by do split => /> //=. done.
    apply (load_store_pos Glob.mem{2} qp{2} H4 8). rewrite /valid_ptr; by do split => /> //=. done.
    apply (load_store_pos Glob.mem{2} qp{2} H4 16). rewrite /valid_ptr; by do split => /> //=. done.
    apply (load_store_pos Glob.mem{2} qp{2} H4 24). rewrite /valid_ptr; by do split => /> //=. done.
qed.
*)

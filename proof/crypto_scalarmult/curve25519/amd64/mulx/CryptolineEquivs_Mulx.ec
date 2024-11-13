require import Int Mulx_scalarmult_s Jcheck Mul4_a24MulxExtracted Mul4MulxExtracted Sqr4MulxExtracted.

from Jasmin require import JWord.

require import Array8.

lemma __mul4_a24_rs_cryptoline_equiv_mulx  :
      equiv [Mulx_scalarmult_s.M.__mul4_a24_rs ~ Mul4_a24MulxExtracted.M.__mul4_a24_rs : ={fs} /\ a24{1} = W64.of_int 121665 ==> res{1} = res{2}.`1].
proof.
    proc. 
    seq 36 53 : (={h, c, fs, r0}). auto => />.
    seq 2 12 : (={h, c, fs}). auto => />.
    move => &2. rewrite !addcE !/carry_add => />.  
    auto => />.  

qed.

lemma __reduce_cryptoline_equiv_mul_mulx  :
      equiv [Mulx_scalarmult_s.M.__reduce4 ~ Mul4MulxExtracted.M.__reduce4 : h{1} = x{2} /\ ={r, cf, of_0} /\ z{1} = W64.zero /\ _38{1} = W64.of_int 38  ==> res{1} = res{2}.`1].
proof.
    proc => //=.
    seq 46 64 : (r{1} = h0{2} /\ ={h, z, _38, of_0, cf, hi, lo} ). sim; auto => />.
    seq 2 7 : (_5{1} = cf{2} /\ ={h, z, _38, of_0, hi, lo}). auto => />.
    seq 1 7 : (={h, z, _38, of_0, hi, lo}). auto => />.
    rewrite !addcE !/carry_add !b2i0 => />. 
    auto => />.
qed.

lemma __reduce_cryptoline_equiv_sqr_mulx  :
      equiv [Mulx_scalarmult_s.M.__reduce4 ~ Sqr4MulxExtracted.M.__reduce4 : h{1} = x{2} /\ ={r, cf, of_0} /\ z{1} = W64.zero /\ _38{1} = W64.of_int 38  ==> res{1} = res{2}.`1].
proof.
    proc => //=.
    seq 46 64 : (r{1} = h0{2} /\ ={h, z, _38, of_0, cf, hi, lo} ). sim; auto => />.
    seq 2 7 : (_5{1} = cf{2} /\ ={h, z, _38, of_0, hi, lo}). auto => />.
    seq 1 7 : (={h, z, _38, of_0, hi, lo}). auto => />.
    rewrite !addcE !/carry_add !b2i0 => />. 
    auto => />.
qed.


lemma __mul4_cryptoline_equiv_mulx  :
      equiv [Mulx_scalarmult_s.M.__mul4_rsr ~ Mul4MulxExtracted.M.__mul4_rsr : ={fs, g} ==> res{1} = res{2}.`1].
proof.
     proc => //=. 
    seq 4 8 : (={fs, g, h, r, of_0, cf, _1, _2, z, f} /\ z{1} = W64.zero /\ z{2} = W64.zero ). auto => />.
    inline{1} 1. inline{2} 1.
    seq 33 47 : (={fs, g, h, r, of_0, cf, _1, _2, z, f, f0, g0, z0, cf0, of_00, h0, r0, lo} /\ z{1} = W64.zero /\ z{2} = W64.zero ). auto => />.
    inline{1} 1. inline{2} 1.
    seq 42 60 : (={fs, g, h, r, of_0, cf, _1, _2, z, f, f0, g0, z0, cf0, of_00, h0, r0, lo, h1, r1, f1, g1, z1, cf1, of_01, hi, lo0} /\ z{1} = W64.zero /\ z{2} = W64.zero). auto => />.
    inline{1} 1. inline{2} 1.
    seq 42 60 : (={fs, g, h, r, of_0, cf, _1, _2, z, f, f0, g0, z0, cf0, of_00, h0, r0, lo, h1, r1, f1, g1, z1, cf1, of_01, hi, lo0, h2, r2, f2, g2, z2, cf2, of_02, hi0, lo1} /\ z{1} = W64.zero /\ z{2} = W64.zero ). auto => />.
    inline{1} 1. inline{2} 1.
    seq 42 60 : (={fs, g, h, r, of_0, cf, _1, _2, f, f0, g0, z0, cf0, of_00, h0, r0, lo, h1, r1, f1, g1, z1, cf1, of_01, hi, lo0, h2, r2, f2, g2, z2, cf2, of_02, hi0, lo1, h3, r3, f3, g3, z3, cf3, of_03, hi1, lo2, _38} /\ _38{1} = W64.of_int 38 /\ z{1} = W64.zero). 
    auto => />.  
    wp. call __reduce_cryptoline_equiv_mul_mulx. auto => />.
qed.

lemma __sqr4_cryptoline_equiv_mulx  :
      equiv [Mulx_scalarmult_s.M.__sqr4_rr ~ Sqr4MulxExtracted.M.__sqr4_rr : ={f} ==> res{1} = res{2}.`1].
proof.
     proc => //=. 
     wp. call __reduce_cryptoline_equiv_sqr_mulx. 
    seq 108 128 : (={f, h, r, of_0, cf, _1, _2, z, f, aux_1, aux_0, t, fx, _38} /\ z{1} = W64.zero /\ z{2} = W64.zero /\ _38{1} = W64.of_int 38). auto => />. auto => />.
qed.



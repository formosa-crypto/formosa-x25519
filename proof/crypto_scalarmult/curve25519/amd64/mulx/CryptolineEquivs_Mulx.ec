require import Int Mulx_scalarmult_s Mul4_a24MulxExtracted Mul4MulxExtracted Sqr4MulxExtracted.

from Jasmin require import JWord Jcheck.

require import Array8.

lemma __mul4_a24_rs_cryptoline_equiv_mulx  :
      equiv [Mulx_scalarmult_s.M.__mul4_a24_rs ~ Mul4_a24MulxExtracted.M.__mul4_a24_rs : ={fs} /\ a24{1} = W64.of_int 121665 ==> res{1} = res{2}.`1].
proof.
    proc. auto => />.    
    move => &2. rewrite !addcE !/carry_add => />.      
qed.

lemma __reduce_cryptoline_equiv_mul_mulx  :
      equiv [Mulx_scalarmult_s.M.__reduce4 ~ Mul4MulxExtracted.M.__reduce4 : h{1} = x{2} /\ ={r, cf, of_0} /\ z{1} = W64.zero /\ _38{1} = W64.of_int 38  ==> res{1} = res{2}.`1].
proof.
    proc => //=. auto => />.    
    rewrite !addcE !/carry_add !b2i0 => />. 
qed.

lemma __reduce_cryptoline_equiv_sqr_mulx  :
      equiv [Mulx_scalarmult_s.M.__reduce4 ~ Sqr4MulxExtracted.M.__reduce4 : h{1} = x{2} /\ ={r, cf, of_0} /\ z{1} = W64.zero /\ _38{1} = W64.of_int 38  ==> res{1} = res{2}.`1].
proof.
    proc => //=. auto => />.    
    rewrite !addcE !/carry_add !b2i0 => />.
qed.


lemma __mul4_cryptoline_equiv_mulx  :
      equiv [Mulx_scalarmult_s.M.__mul4_rsr ~ Mul4MulxExtracted.M.__mul4_rsr : ={fs, g} ==> res{1} = res{2}.`1].
proof.
     proc => //=. wp. call __reduce_cryptoline_equiv_mul_mulx. auto => />.     
     inline *. auto => />.
qed.

lemma __sqr4_cryptoline_equiv_mulx  :
      equiv [Mulx_scalarmult_s.M.__sqr4_rr ~ Sqr4MulxExtracted.M.__sqr4_rr : ={f} ==> res{1} = res{2}.`1].
proof.
     proc => //=. 
     wp. call __reduce_cryptoline_equiv_sqr_mulx.
     auto => />. 
qed.



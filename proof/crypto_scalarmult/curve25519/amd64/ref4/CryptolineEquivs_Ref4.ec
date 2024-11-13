require import Int Ref4_scalarmult_s Jcheck Add4Extracted Sub4Extracted Mul4RefExtracted Mul4_a24RefExtracted Int Sqr4RefExtracted.

from Jasmin require import JWord.

require import Array8.

lemma __add4_rrs_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__add4_rrs ~ Add4Extracted.M.__add4_rrs : ={f, g} ==> res{1} = res{2}.`1].
proof.
    proc. 
    seq 9 14 : (={f, g, h, z} /\  _1{1} = cf{2}). by sim.
    seq 7 20 : (={f, g, h, z} /\ _2{1} = cf{2}). by sim.
    sim : (={f, g, h, z}). auto => />. 
    rewrite addcE /carry_add b2i0 => />. 
qed.

lemma __sub4_rss_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__sub4_rrs ~ Sub4Extracted.M.__sub4_rrs : ={f, gs} ==> res{1} = res{2}.`1].
proof.
    proc.  
    seq 9 14 : (={f, gs, h, z} /\  _1{1} = cf{2}). by sim.
    seq 7 16 : (={f, gs, h, z} /\ _2{1} = cf{2}). by sim.
    sim : (={f, gs, h, z}). auto => />.
    rewrite subcE /borrow_sub b2i0 => />. 
qed.

lemma __reduce_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__reduce4 ~ Mul4RefExtracted.M.__reduce4 : ={z} ==> res{1} = res{2}.`1].
proof.
    proc.
    seq 36 52 : (={r, r38, rax, h, l, i, z, z8, cf}). by sim. 
    seq 6 14 : (={r, r38, rax, h, l, i, z, z8, r0, cf}). auto => />.
    rewrite !addcE !/carry_add !muluE !/mulhi => />. 
    seq 2 2 : (={r, r38, rax, h, l, i, z8, z, r0, cf}). by sim.
    sim : (={r, r38, rax, h, l, i, z8, r0, z}). auto => />.
    move => *. do split. 
    rewrite !/mulhi !/mulu !addcE !/carry_add => />. 
    rewrite !/mulhi !/mulu !addcE !/carry_add => />. 
qed.

lemma __reduce_cryptoline_equiv_sqr_ref4  :
      equiv [Ref4_scalarmult_s.M.__reduce4 ~ Sqr4RefExtracted.M.__reduce4 : ={z} ==> res{1} = res{2}.`1].
proof.
    proc.
    seq 36 52 : (={r, r38, rax, h, l, i, z, z8, cf}). by sim. 
    seq 6 14 : (={r, r38, rax, h, l, i, z, z8, r0, cf}). auto => />.
    rewrite !addcE !/carry_add !muluE !/mulhi => />. 
    seq 2 2 : (={r, r38, rax, h, l, i, z8, z, r0, cf}). by sim.
    sim : (={r, r38, rax, h, l, i, z8, r0, z}). auto => />.
    move => *. do split. 
    rewrite !/mulhi !/mulu !addcE !/carry_add => />. 
    rewrite !/mulhi !/mulu !addcE !/carry_add => />. 
qed.


lemma __mul4_rss_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__mul4_rss ~ Mul4RefExtracted.M.__mul4_rss : ={xa, ya} ==> res{1} = res{2}.`1].
proof.
    proc.     
    wp. call __reduce_cryptoline_equiv_ref4.
    seq 9 13 : (={x, y, z, r, xa, ya}). by sim.
    unroll for{1} ^while. unroll for{2} ^while.
    seq 4 4 : (={x, y, z, r, xa, ya, hprev, i}).  
    unroll for{1} ^while. unroll for{2} ^while.
    rcondt{1} ^if. auto => />. rcondt{2} ^if. auto => />. sim.
    seq 4 4 : (={x, y, z, r, xa, ya, hprev, i}).  
    unroll for{1} ^while. unroll for{2} ^while.
    rcondt{1} ^if. auto => />. rcondt{2} ^if. auto => />. sim.
    seq 4 4 : (={x, y, z, r, xa, ya, hprev, i}).  
    unroll for{1} ^while. unroll for{2} ^while.
    rcondt{1} ^if. auto => />. rcondt{2} ^if. auto => />. sim.
    wp. skip. auto => />.
qed.

lemma __mul4_a24_rs_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__mul4_a24_rs ~ Mul4_a24RefExtracted.M.__mul4_a24_rs : ={xa} /\ a24{1} = W64.of_int 121665 ==> res{1} = res{2}.`1].
proof.
    proc. 
    seq 4 12 : (={r, c, rax, rdx, xa}). auto => />.
    seq 39 47 : (={r, c, rax, rdx, xa, t1, t2, t3, t4, cf}). auto => />.
    sim : (={r, c, rax, rdx, xa, t1, t2, t3, t4}). auto => />.
    move => &2. rewrite !addcE !/carry_add !b2i0  => />.  
qed.

lemma __sqr4_rs_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__sqr4_rs ~ Sqr4RefExtracted.M.__sqr4_rs : ={xa} ==> res{1} = res{2}.`1].
proof.
    proc. 
    wp. call __reduce_cryptoline_equiv_sqr_ref4.
    sim : (={zero, xa, r, t, z, rax, rdx, aux, aux_0}). 
qed.



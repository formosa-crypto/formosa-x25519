require import Int Ref4_scalarmult_s Add4Extracted Sub4Extracted Mul4RefExtracted Mul4_a24RefExtracted Int Sqr4RefExtracted CommonToBytes_0p CommonToBytes_p2_255 CommonToBytes_2p2_256 CommonToBytes_2_2552p.

from Jasmin require import JWord Jcheck.

require import Array4 Array8.

lemma __add4_rrs_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__add4_rrs ~ Add4Extracted.M.__add4_rrs : ={f, g} ==> res{1} = res{2}.`1].
proof.
    proc. 
    unroll for{1} ^while.
    unroll for{1} ^while.
    unroll for{2} ^while.
    unroll for{2} ^while. auto => />.
    move => *. rewrite !/copy_64 !/set0_64_ => />. 
    apply Array4.ext_eq. move => i ib. rewrite !get_setE 1..18://=.
    case (i = 0) => I0. smt(W64.of_intN' W64.of_intS).
    case (i = 1) => I1. smt(W64.of_intN' W64.of_intS).
    case (i = 2) => I2. smt(W64.of_intN' W64.of_intS).
    case (i = 3) => I3. smt(W64.of_intN' W64.of_intS). smt().      
qed.

lemma __sub4_rss_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__sub4_rrs ~ Sub4Extracted.M.__sub4_rrs : ={f, gs} ==> res{1} = res{2}.`1].
proof.
    proc.     
    unroll for{1} ^while.
    unroll for{1} ^while.
    unroll for{2} ^while.
    unroll for{2} ^while. auto => />.
    move => *. rewrite !/copy_64 !/set0_64_ => />. 
    apply Array4.ext_eq. move => i ib. rewrite !get_setE 1..18://=.
    case (i = 0) => I0. smt(W64.WRingA.oppr0  W64.WRingA.subr0).
    case (i = 1) => I1. smt(W64.WRingA.oppr0  W64.WRingA.subr0).
    case (i = 2) => I2. smt(W64.WRingA.oppr0  W64.WRingA.subr0).
    case (i = 3) => I3. smt(W64.WRingA.oppr0  W64.WRingA.subr0). smt().  
qed.

lemma __reduce_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__reduce4 ~ Mul4RefExtracted.M.__reduce4 : ={z} ==> res{1} = res{2}.`1].
proof.
    proc.     
    unroll for{1} ^while.
    unroll for{1} ^while.
    unroll for{2} ^while.
    unroll for{2} ^while. auto => />.
    move => *. rewrite !/copy_64 !/set0_64_ => />. 
    apply Array4.ext_eq. move => i ib. rewrite !get_setE 1..26://=.
    case (i = 0) => I0. smt(W64.of_intN' W64.of_intS).
    case (i = 1) => I1. smt(W64.of_intN' W64.of_intS).
    case (i = 2) => I2. smt(W64.of_intN' W64.of_intS).
    case (i = 3) => I3. smt(W64.of_intN' W64.of_intS). smt().    
qed.

lemma __reduce_cryptoline_equiv_sqr_ref4  :
      equiv [Ref4_scalarmult_s.M.__reduce4 ~ Sqr4RefExtracted.M.__reduce4 : ={z} ==> res{1} = res{2}.`1].
proof.
    proc.     
    unroll for{1} ^while.
    unroll for{1} ^while.
    unroll for{2} ^while.
    unroll for{2} ^while. auto => />.
    move => *. rewrite !/copy_64 !/set0_64_ => />. 
    apply Array4.ext_eq. move => i ib. rewrite !get_setE 1..26://=.
    case (i = 0) => I0. smt(W64.of_intN' W64.of_intS).
    case (i = 1) => I1. smt(W64.of_intN' W64.of_intS).
    case (i = 2) => I2. smt(W64.of_intN' W64.of_intS).
    case (i = 3) => I3. smt(W64.of_intN' W64.of_intS). smt(). 
qed.

lemma __mul4_rss_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__mul4_rss ~ Mul4RefExtracted.M.__mul4_rss : ={xa, ya} ==> res{1} = res{2}.`1].
proof.
    proc. wp.       
    unroll for{1} ^while.     
    unroll for{1} ^while.
    unroll for{2} ^while.
    unroll for{2} ^while. 
    unroll for{2} ^while. 
    unroll for{2} ^while. 
    unroll for{2} ^while. 
    unroll for{2} ^while. 
    unroll for{1} ^while. 
    unroll for{1} ^while. 
    unroll for{1} ^while. 
    unroll for{1} ^while.
    call __reduce_cryptoline_equiv_ref4.
    simplify. sim.      
qed.

lemma __mul4_a24_rs_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__mul4_a24_rs ~ Mul4_a24RefExtracted.M.__mul4_a24_rs : ={xa} /\ a24{1} = W64.of_int 121665 ==> res{1} = res{2}.`1].
proof.
    proc. auto => />.
    move => *. rewrite !/copy_64 !/set0_64_ => />. 
    apply Array4.ext_eq. move => i ib. rewrite !get_setE 1..24://=.
    case (i = 0) => I0. smt(W64.of_intN' W64.of_intS).
    case (i = 1) => I1. smt(W64.of_intN' W64.of_intS).
    case (i = 2) => I2. smt(W64.of_intN' W64.of_intS).
    case (i = 3) => I3. smt(W64.of_intN' W64.of_intS). smt().  
qed.

lemma __sqr4_rs_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__sqr4_rs ~ Sqr4RefExtracted.M.__sqr4_rs : ={xa} ==> res{1} = res{2}.`1].
proof.
    proc. 
    wp. call __reduce_cryptoline_equiv_sqr_ref4.
    sim : (={zero, xa, r, t, z, rax, rdx, aux, aux_0}). 
qed.

lemma __tobytes_cryptoline_equiv_0p_ref4  :
      equiv [Ref4_scalarmult_s.M.__tobytes4 ~ CommonToBytes_0p.M.__tobytes4 : ={f} ==> res{1} = res{2}.`1].
proof.
    proc. auto => />.    
qed.

lemma __tobytes_cryptoline_equiv_p2_255_ref4  :
      equiv [Ref4_scalarmult_s.M.__tobytes4 ~ CommonToBytes_p2_255.M.__tobytes4 : ={f} ==> res{1} = res{2}.`1].
proof.
    proc. auto => />.    
qed.

lemma __tobytes_cryptoline_equiv_2p2_256_ref4  :
      equiv [Ref4_scalarmult_s.M.__tobytes4 ~ CommonToBytes_2p2_256.M.__tobytes4 : ={f} ==> res{1} = res{2}.`1].
proof.
    proc. auto => />.    
qed.

lemma __tobytes_cryptoline_equiv_2_2552p_ref4  :
      equiv [Ref4_scalarmult_s.M.__tobytes4 ~ CommonToBytes_2_2552p.M.__tobytes4 : ={f} ==> res{1} = res{2}.`1].
proof.
    proc. auto => />.    
qed.


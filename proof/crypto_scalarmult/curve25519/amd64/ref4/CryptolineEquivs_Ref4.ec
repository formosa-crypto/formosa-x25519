require import Ref4_scalarmult_s Jcheck Add4Extracted Sub4Extracted Int.

from Jasmin require import JWord.

lemma __add4_rrs_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__add4_rrs ~ Add4Extracted.M.__add4_rrs : ={f, g} ==> res{1} = res{2}.`1].
proof.
    proc. 
    seq 9 14 : (={f, g, h, z} /\  _1{1} = cf{2}). by sim.
    seq 7 20 : (={f, g, h, z} /\ _2{1} = cf{2}). by sim.
    seq 1 5 : (={f, g, h, z}). by sim. 
    wp; skip; auto => />.
    rewrite addcE /carry_add b2i0 => />. 
qed.

lemma __sub4_rss_cryptoline_equiv_ref4  :
      equiv [Ref4_scalarmult_s.M.__sub4_rrs ~ Sub4Extracted.M.__sub4_rrs : ={f, gs} ==> res{1} = res{2}.`1].
proof.
    proc.  
    seq 9 14 : (={f, gs, h, z} /\  _1{1} = cf{2}). by sim.
    seq 7 16 : (={f, gs, h, z} /\ _2{1} = cf{2}). by sim.
    seq 1 5 : (={f, gs, h, z}). by sim. 
    wp; skip; auto => />.
    rewrite subcE /borrow_sub b2i0 => />. 
qed.

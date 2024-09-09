require import Bool List Int IntDiv CoreMap Real Ring StdOrder.
require import Zp_25519 Zplimbs Curve25519_Spec EClib.
import Zp StdOrder.IntOrder Ring.IntID Array4 EClib.

from Jasmin require import JModel.

(* sets last bit to 0 *)
op last_bit_to_zero64 (x: Rep4) : Rep4 = let x = x.[3 <- x.[3].[63 <- false]] in x.

(* returns the first 2 elements of the input triple *)
op select_double_from_triple (t : ('a * 'a) * ('a * 'a) * 'c) : ('a * 'a) * ('a * 'a) = (t.`1, t.`2).

(* if the third element is true then the first 2 elements are swapped
  - this op returns the first 2 elements in the correct order      *)
op reconstruct_triple (t : ('a * 'a) * ('a * 'a) * bool) : ('a * 'a) * ('a * 'a)  =
    if t.`3
    then spec_swap_tuple (select_double_from_triple t)
    else select_double_from_triple t.

(* given that t.`3 is false, we can convert from a "list" with two elems
   to a ""list"" with three elements, whereby the last element is false *)
lemma eq_reconstruct_select_triple (t : (('a * 'a) * ('a * 'a) * bool)) :
    t.`3 = false =>
    select_double_from_triple t = reconstruct_triple t.
proof.
    rewrite /reconstruct_triple /select_double_from_triple.
    by move => ? /#.
qed.


(* step 1: spec_add_and_double = op_add_and_double : reordered to match
    implementation *)
op op_add_and_double (qx : zp, nqs : (zp * zp) * (zp * zp)) : (zp * zp) * (zp * zp)  =
    let x_1 = qx                                   in
    let (x_2, z_2) = nqs.`1                        in
    let (x_3, z_3) = nqs.`2                        in
    let a          = x_2 + z_2                     in
    let aa         = a * a                         in
    let b          = x_2 - z_2                     in
    let bb         = b *  b                        in
    let e          = aa - bb                       in
    let c          = x_3 + z_3                     in
    let d          = x_3 - z_3                     in
    let da         = d * a                         in
    let cb         = c * b                         in
    let x_3        = (da + cb) * (da + cb)         in
    let z_3        = x_1 * ((da - cb) * (da - cb)) in
    let x_2        = aa * bb                       in
    let z_2        = e * (aa + (inzp 121665 * e))  in
        ((x_2, z_2), (x_3, z_3)).

(* lemma: spec_add_and_double = op_add_and_double *)
lemma eq_op_add_and_double (qx : zp, nqs : (zp * zp) * (zp * zp)) :
    spec_add_and_double qx nqs = op_add_and_double qx nqs.
proof.
    rewrite /spec_add_and_double /op_add_and_double.
    auto => />.
qed.

(** step 2: montgomery ladder and isolate foldl function and introduce reconstruct tuple * *)
op op_montgomery_ladder1 (init : zp, k : W256.t) : (zp * zp) * (zp * zp) =
    let nqs0 = ((Zp.one,Zp.zero),(init,Zp.one)) in
    foldl (fun (nqs : (zp * zp) * (zp * zp)) ctr =>
         if spec_ith_bit k ctr
         then spec_swap_tuple (op_add_and_double init (spec_swap_tuple(nqs)))
         else op_add_and_double init nqs) nqs0 (rev (iota_ 0 255)).

op op_montgomery_ladder2_step(k : W256.t, init : zp, nqs : (zp * zp) * (zp * zp), ctr : int) : (zp * zp) * (zp * zp)=
    if spec_ith_bit k ctr
    then spec_swap_tuple(op_add_and_double init (spec_swap_tuple(nqs)))
    else op_add_and_double init nqs.

op op_montgomery_ladder2(init : zp, k : W256.t) : (zp * zp) * (zp * zp) =
    let nqs0 = reconstruct_triple ((Zp.one,Zp.zero),(init,Zp.one),false) in
    foldl (op_montgomery_ladder2_step k init) nqs0 (rev (iota_ 0 255)).

(* lemma: spec_montgomery_ladder = op_montgomery_ladder1 *)
lemma eq_op_montgomery_ladder1 (init : zp) (k : W256.t) :
    spec_montgomery_ladder init k = op_montgomery_ladder1 init k.
proof.
    rewrite /spec_montgomery_ladder /op_montgomery_ladder1 /=.
    apply foldl_in_eq.
    move => nqs ctr inlist => /=.
    case (spec_ith_bit k ctr).
        by move => ?; rewrite /spec_swap_tuple /#.
    by move => ?; rewrite /spec_swap_tuple /#.
qed.

(* lemma: op_montgomery_ladder1 = op_montgomery_ladder2 *)
lemma eq_op_montgomery_ladder2 (init : zp) (k : W256.t) :
    op_montgomery_ladder1 init k = op_montgomery_ladder2 init k.
proof.
    rewrite /op_montgomery_ladder1 /op_montgomery_ladder2 /reconstruct_triple /select_double_from_triple.
    rewrite /op_montgomery_ladder2_step.
    by simplify.
qed.


(** step 3: extend the state to contain an additional bit stating if the state is swapped * *)
op cswap (t : ('a * 'a) * ('a * 'a), b : bool) : ('a * 'a) * ('a * 'a)  =
    if b
    then spec_swap_tuple t
    else t.

op op_montgomery_ladder3_step(k : W256.t, init : zp, nqs : (zp * zp) * (zp * zp) * bool, ctr : int) : (zp * zp) * (zp * zp) * bool =
    let nqs = cswap (select_double_from_triple nqs) (nqs.`3 ^^ (spec_ith_bit k ctr)) in
    let nqs = op_add_and_double init nqs in
    (nqs.`1, nqs.`2, (spec_ith_bit k ctr)).

op op_montgomery_ladder3(init : zp, k : W256.t) : (zp * zp) * (zp * zp) * bool =
    let nqs0 = ((Zp.one, Zp.zero),(init, Zp.one),false) in
    foldl (op_montgomery_ladder3_step k init) nqs0 (rev (iota_ 0 255)).

(* lemma: op_montgomery_ladder2 = op_reconstruct_triple(op_montgomery_ladder3 ) *)
lemma eq_op_montgomery_ladder3_reconstruct (init : zp) (k: W256.t) :
    op_montgomery_ladder2 init k = reconstruct_triple (op_montgomery_ladder3 init k).
proof.
    rewrite /op_montgomery_ladder2 /op_montgomery_ladder3 //=.
    apply foldl_in_eq_r.
    move => ? ? ?.
    rewrite /reconstruct_triple /op_montgomery_ladder2_step /op_montgomery_ladder3_step.
    rewrite /spec_swap_tuple /select_double_from_triple /cswap.
    simplify => /#.
qed.

(* lemma: if the first bit of k is 0, which will be because of spec_decode_scalar_25519
   then op_montgomery_ladder2 = select_double_from_triple op_montgomery_ladder3 *)
lemma eq_op_montgomery_ladder3 (init : zp, k: W256.t) :
    k.[0] = false =>
    op_montgomery_ladder2 init k = select_double_from_triple (op_montgomery_ladder3 init k).
proof.
    move => hkf.
    have tbf : (op_montgomery_ladder3 init k).`3 = false. (*third bit false *)
    rewrite /op_montgomery_ladder3 /op_montgomery_ladder3_step /select_double_from_triple /cswap /spec_ith_bit /spec_swap_tuple => />.
    rewrite foldl_rev; auto => />; rewrite -iotaredE => />.
    have seqr : select_double_from_triple (op_montgomery_ladder3 init k) = reconstruct_triple (op_montgomery_ladder3 init k).
        by apply /eq_reconstruct_select_triple /tbf.
    rewrite seqr.
    by apply eq_op_montgomery_ladder3_reconstruct.
qed.

(** step 4: spec_montgomery_ladder = select_double_from_triple op_montgomery_ladder3 * *)
lemma eq_op_montgomery_ladder123 (init : zp, k: W256.t) :
    k.[0] = false => spec_montgomery_ladder init k = select_double_from_triple (op_montgomery_ladder3 init k).
proof.
    move => H.
    rewrite eq_op_montgomery_ladder1 eq_op_montgomery_ladder2 eq_op_montgomery_ladder3. apply H.
    trivial.
qed.

(* step 5: introduce reordering in encode point *)
(*  - we split invert in 3 parts to make the proof faster *)
op op_invert_p_p1 (z1 : zp) : (zp * zp) =
    let z2    = ZModpRing.exp z1 2     in
    let z8    = ZModpRing.exp z2 (2*2) in
    let z9    = z1 * z8                in
    let z11   = z2 * z9                in
    let z22   = ZModpRing.exp z11 2    in
    let z_5_0 = z9 * z22               in
        (z_5_0, z11).

op op_invert_p_p2(z_5_0 : zp) : zp =
    let z_10_5  = ZModpRing.exp z_5_0 (2^5)   in
    let z_10_0  =  z_10_5 * z_5_0             in
    let z_20_10 = ZModpRing.exp z_10_0 (2^10) in
    let z_20_0  = z_20_10 * z_10_0            in
    let z_40_20 = ZModpRing.exp z_20_0 (2^20) in
    let z_40_0  = z_40_20 * z_20_0            in
    let z_50_10 = ZModpRing.exp z_40_0 (2^10) in
    let z_50_0  = z_50_10 * z_10_0 in
        z_50_0.

op op_invert_p_p3(z_50_0 z11 : zp) : zp =
    let z_100_50  = ZModpRing.exp z_50_0 (2^50)   in
    let z_100_0   =  z_100_50 * z_50_0            in
    let z_200_100 = ZModpRing.exp z_100_0 (2^100) in
    let z_200_0   = z_200_100 * z_100_0           in
    let z_250_50  = ZModpRing.exp z_200_0 (2^50)  in
    let z_250_0   = z_250_50 * z_50_0             in
    let z_255_5   = ZModpRing.exp z_250_0 (2^5)   in
    let z_255_21  = z_255_5 *  z11                in
        z_255_21.

op op_invert_p(z1 : zp) : zp =
    let (z_5_0, z11) = op_invert_p_p1 z1         in
    let z_50_0       = op_invert_p_p2 z_5_0      in
    let z_255_21     = op_invert_p_p3 z_50_0 z11 in
    z_255_21 axiomatized by op_invert_pE.

(* lemma: invert is the same as z1^(p-2) from fermat's little theorem *)
lemma eq_op_invert_p (z1: zp) :
    op_invert_p z1 = ZModpRing.exp z1 (p-2).
proof.
    rewrite op_invert_pE.
    rewrite /op_invert_p_p1 /= expE //= /op_invert_p_p3 /op_invert_p_p2 => />.
    rewrite -!ZModpRing.exprS => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite -!ZModpRing.exprM => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite -!ZModpRing.exprM => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite -!ZModpRing.exprM => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite -!ZModpRing.exprM => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite -!ZModpRing.exprM => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite -!ZModpRing.exprM => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite -!ZModpRing.exprM => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite -!ZModpRing.exprM => />.
    rewrite -ZModpRing.exprD_nneg => />.
    rewrite -ZModpRing.exprM => />.
    rewrite -!ZModpRing.exprD_nneg => />.
    rewrite pE => />.
qed. (* there must be a faster and elegant way of doing this *)

(* now we define invert as one op and prove it equiv to exp z1 (p-2) *)
op op_invert0(z1 : zp) : zp =
    let z2        = ZModpRing.exp z1 2            in
    let z8        = ZModpRing.exp z2 (2*2)        in
    let z9        = z1 * z8                       in
    let z11       = z2 * z9                       in
    let z22       = ZModpRing.exp z11 2           in
    let z_5_0     = z9 * z22                      in
    let z_10_5    = ZModpRing.exp z_5_0 (2^5)     in
    let z_10_0    = z_10_5 * z_5_0                in
    let z_20_10   = ZModpRing.exp z_10_0 (2^10)   in
    let z_20_0    = z_20_10 * z_10_0              in
    let z_40_20   = ZModpRing.exp z_20_0 (2^20)   in
    let z_40_0    = z_40_20 * z_20_0              in
    let z_50_10   = ZModpRing.exp z_40_0 (2^10)   in
    let z_50_0    = z_50_10 * z_10_0              in
    let z_100_50  = ZModpRing.exp z_50_0 (2^50)   in
    let z_100_0   = z_100_50 * z_50_0             in
    let z_200_100 = ZModpRing.exp z_100_0 (2^100) in
    let z_200_0   = z_200_100 * z_100_0           in
    let z_250_50  = ZModpRing.exp z_200_0 (2^50)  in
    let z_250_0   = z_250_50 * z_50_0             in
    let z_255_5   = ZModpRing.exp z_250_0 (2^5)   in
    let z_255_21  = z_255_5 * z11                 in
        z_255_21 axiomatized by op_invert0E.

(* lemma: op_invert0 = op_invert_p *)
lemma eq_op_invert0 (z1 : zp) :
    op_invert0 z1 = op_invert_p z1.
proof.
    rewrite op_invert0E op_invert_pE /op_invert_p_p1 /op_invert_p_p2 /op_invert_p_p3 //.
qed.

(* lemma: hence, op_invert0 is equal to z1^(p-1) *)
lemma eq_op_invert0p (z1 : zp) :
    op_invert0 z1 = ZModpRing.exp z1 (p-2).
proof.
    rewrite eq_op_invert0 eq_op_invert_p //.
qed.

(* we now need to define various iterated sqaure operations and lemmas *)
op op_sqr(z : zp) : zp =
    ZModpRing.exp z 2.

op op_it_sqr(e : int, z : zp) : zp =
    ZModpRing.exp z (2^e).

op op_it_sqr1(e : int, z : zp) : zp =
    foldl (fun (z' : zp) _ => ZModpRing.exp z' 2) z (iota_ 0 e).

op op_it_sqr_x2(e : int, z : zp) : zp =
    ZModpRing.exp z (4^e).

op op_it_sqr1_x2(e : int, z : zp) : zp =
    foldl (fun (z' : zp) _ => ZModpRing.exp z' 4) z (iota_ 0 e).

(* lemma: op_it_sqr1 = op_itr_sqr *)
lemma eq_op_it_sqr1 (e : int, z : zp) :
    0 <= e  =>
    op_it_sqr1 e z = op_it_sqr e z.
proof.
    move : e.
    rewrite /op_it_sqr1 /op_it_sqr. elim. simplify. rewrite -iotaredE ZModpRing.expr1 //.
    move => i ige0 hin.
    rewrite iotaSr // -cats1 foldl_cat hin /= expE /=.  smt(gt0_pow2).
    congr. clear hin.
    rewrite exprS // mulzC //.
qed.

(* lemma: op_it_sqr1_x2 = op_itr_sqr_x2 *)
lemma eq_op_it_sqr1_x2 (e : int, z : zp) :
    0 <= e  =>
    op_it_sqr1_x2 e z = op_it_sqr_x2 e z.
proof.
    move : e.
    rewrite /op_it_sqr1_x2 /op_it_sqr_x2. elim. simplify. rewrite -iotaredE ZModpRing.expr1 //.
    move => i ige0 hin.
    rewrite iotaSr // -cats1 foldl_cat hin /= expE /=.
    have ->: 4^i = 2^2^i. rewrite expr2 //.
    rewrite -exprM. smt(gt0_pow2).
    congr. clear hin.
    rewrite exprS // mulzC //.
qed.

(* lemma: op_it_sqr = op_itr_sqr_x2 *)
lemma eq_op_it_sqr_x2_4 (e : int, z : zp) :
    0 <= e  => e %% 2 = 0 =>
    op_it_sqr e z = op_it_sqr_x2 (e%/2) z.
proof.
    move => e1 e2.
    rewrite /op_it_sqr /op_it_sqr_x2.
    congr.
    have ->: 4 ^ (e %/ 2) = 2 ^ 2 ^ (e %/ 2). rewrite expr2 => />.
    rewrite -exprM => />. smt().
qed.

(* lemma: op_it_sqr1 = op_itr1_sqr_x2 *)
lemma eq_op_it_sqr1_x2_4 (e : int, z : zp) :
    0 <= e  => e %% 2 = 0 =>
    op_it_sqr1 e z = op_it_sqr1_x2 (e%/2) z.
proof.
    move => H H0.
    rewrite eq_op_it_sqr1 // eq_op_it_sqr1_x2. smt().
    apply eq_op_it_sqr_x2_4; trivial.
qed.

(* lemma: op_it_sqr1 = op_itr_sqr_x2, other perspective *)
lemma eq_op_it_sqr1_x2_4_twice (e : int, z : zp) :
    0 <= e  => e %% 2 = 0 =>
    op_it_sqr1 (2*e) z = op_it_sqr1_x2 e z.
proof.
    move => H H0.
    rewrite eq_op_it_sqr1 //. smt(). rewrite eq_op_it_sqr1_x2. smt().
    rewrite /op_it_sqr /op_it_sqr_x2 => />.
    have ->: 4 ^ e = 2 ^ 2 ^ e. rewrite expr2 => />.
    rewrite -exprM => />.
qed.

(* lemma: op_it_sqr1 with arg 0 *)
lemma op_it_sqr1_0 (e : int) (z : zp) :
     0 = e => op_it_sqr1 e z = z.
proof.
    move => ?.
    rewrite eq_op_it_sqr1. smt().
    rewrite /op_it_sqr. subst. simplify.
    rewrite ZModpRing.expr1 //.
qed.

(* lemma: op_it_sqr1_x2 with arg 0 *)
lemma op_it_sqr1_x2_0 (e : int) (z : zp) :
     0 = e => op_it_sqr1_x2 e z = z.
proof.
    move => ?.
    rewrite eq_op_it_sqr1_x2. smt().
    rewrite /op_it_sqr_x2. subst. simplify.
    rewrite ZModpRing.expr1 //.
qed.

(* lemma: "decomposing" op_it_sqr1 with e-2 *)
lemma op_it_sqr1_m2_exp4 (e : int) (z : zp) :
     0 <= e - 2 => op_it_sqr1 e z = op_it_sqr1 (e-2) (ZModpRing.exp (ZModpRing.exp z 2) 2).
proof.
    rewrite expE // /= => ?.
    rewrite !eq_op_it_sqr1. smt(). trivial.
    rewrite /op_it_sqr (*expE *).
    (* directly rewriting expE takes too long *)
    have ee :  ZModpRing.exp (ZModpRing.exp z 4) (2 ^ (e - 2)) =  ZModpRing.exp z (2^2 * 2 ^ (e - 2)). smt(expE).
    rewrite ee. congr.
    rewrite -exprD_nneg //.
qed.

(* lemma: "decomposing" op_it_sqr1 witg arg e-1 *)
lemma op_it_sqr1_m2_exp1 (e : int) (z : zp) :
     0 <= e - 1 => op_it_sqr1 e z = op_it_sqr1 (e-1) (ZModpRing.exp z  2).
proof.
    have ->: ZModpRing.exp z 2 = ZModpRing.exp (ZModpRing.exp z 1) 2. rewrite expE. smt(). trivial.
    rewrite expE // /= => ?.
    rewrite !eq_op_it_sqr1. smt(). smt().
    rewrite /op_it_sqr (*expE *). rewrite expE. split. smt().
    rewrite expr_ge0 //. congr. have ->: 2 * 2^(e-1) = 2^1 * 2^(e-1). rewrite expr1 //.
    rewrite -exprD_nneg //.
qed.

(* lemma: "decomposing" op_it_sqr1_x2 with arg e-2 *)
lemma op_it_sqr1_m2_exp4_x2 (e : int) (z : zp) :
     0 <= e - 2 => op_it_sqr1_x2 e z = op_it_sqr1_x2 (e-2) (ZModpRing.exp (ZModpRing.exp z 4) 4).
proof.
    have E: 4^(e-2) = 2^(2*(e-2)) by rewrite exprM => />.
    rewrite expE // /= => H.
    rewrite !eq_op_it_sqr1_x2. smt(). trivial.
    rewrite /op_it_sqr_x2.
    rewrite expE. rewrite E. smt(gt0_pow2).
    congr => />.  have ->: 16 = 4^2 by rewrite expr2.
    rewrite -exprD_nneg //.
qed.

(* lemma: "decomposing" op_it_sqr1_x2 with arg e-1 *)
lemma op_it_sqr1_m2_exp1_x2 (e : int) (z : zp) :
     0 <= e - 1 => op_it_sqr1_x2 e z = op_it_sqr1_x2 (e-1) (ZModpRing.exp z 4).
proof.
    have ->: ZModpRing.exp z 4 = ZModpRing.exp (ZModpRing.exp z 1) 4. rewrite expE. smt(). trivial.
    rewrite expE // /= => ?.
    rewrite !eq_op_it_sqr1_x2. smt(). smt().
    rewrite /op_it_sqr_x2 (*expE *). rewrite expE. split. smt().
    rewrite expr_ge0 //. congr. have ->: 4 * 4^(e-1) = 4^1 * 4^(e-1). rewrite expr1 //.
    rewrite -exprD_nneg //.
qed.

op op_invert1(z1 : zp) : zp =
    let t0 = op_sqr z1        in   (* z1^2  *)
    let t1 = op_sqr t0        in   (* z1^4  *)
    let t1 = op_sqr t1        in   (* z1^8  *)
    let t1 = z1 * t1          in   (* z1^9  *)
    let t0 = t0 * t1          in   (* z1^11 *)
    let t2 = op_sqr t0        in   (* z1^22 *)
    let t1 = t1 * t2          in   (* z_5_0  *)
    let t2 = op_sqr t1        in   (* z_10_5 *)
    let t2 = op_it_sqr 4 t2   in
    let t1 = t1 * t2          in   (* z_10_0 *)
    let t2 = op_it_sqr 10 t1  in   (* z_20_10 *)
    let t2 = t1 * t2          in   (* z_20_0 *)
    let t3 = op_it_sqr 20 t2  in   (* z_40_20 *)
    let t2 = t2 * t3          in   (* z_40_0 *)
    let t2 = op_it_sqr 10 t2  in   (* z_50_10 *)
    let t1 = t1 * t2          in   (* z_50_0 *)
    let t2 = op_it_sqr 50 t1  in   (* z_100_50 *)
    let t2 = t1 * t2          in   (* z_100_0 *)
    let t3 = op_it_sqr 100 t2 in   (* z_200_100 *)
    let t2 = t2 * t3          in   (* z_200_0 *)
    let t2 = op_it_sqr 50 t2  in   (* z_250_50 *)
    let t1 = t1 * t2          in   (* z_250_0 *)
    let t1 = op_it_sqr 4 t1   in   (* z_255_5 *)
    let t1 = op_sqr t1        in
    let t1 = t0 * t1          in
        t1 axiomatized by op_invert1E.

(* lemma: op_invert1 = op_invert0 *)
lemma eq_op_invert1 (z1: zp) :
    op_invert1 z1 = op_invert0 z1.
proof.
    rewrite op_invert1E op_invert0E /= /op_it_sqr /op_sqr /=.
    smt(exprS exprD expE).
qed.

(* split op_invert2 in 3 parts : jump from op_it_sqr to op_it_sqr1 *)
op op_invert2(z1 : zp) : zp =
    let t0 = op_sqr z1         in  (* z1^2  *)
    let t1 = op_sqr t0         in  (* z1^4  *)
    let t1 = op_sqr t1         in  (* z1^8  *)
    let t1 = z1 * t1           in  (* z1^9  *)
    let t0 = t0 * t1           in  (* z1^11 *)
    let t2 = op_sqr t0         in  (* z1^22 *)
    let t1 = t1 * t2           in  (* z_5_0  *)
    let t2 = op_sqr t1         in  (* z_10_5 *)
    let t2 = op_it_sqr1 4 t2   in
    let t1 = t1 * t2           in  (* z_10_0 *)
    let t2 = op_it_sqr1 10 t1  in  (* z_20_10 *)
    let t2 = t1 * t2           in  (* z_20_0 *)
    let t3 = op_it_sqr1 20 t2  in  (* z_40_20 *)
    let t2 = t2 * t3           in  (* z_40_0 *)
    let t2 = op_it_sqr1 10 t2  in  (* z_50_10 *)
    let t1 = t1 * t2           in  (* z_50_0 *)
    let t2 = op_it_sqr1 50 t1  in  (* z_100_50 *)
    let t2 = t1 * t2           in  (* z_100_0 *)
    let t3 = op_it_sqr1 100 t2 in  (* z_200_100 *)
    let t2 = t2 * t3           in  (* z_200_0 *)
    let t2 = op_it_sqr1 50 t2  in  (* z_250_50 *)
    let t1 = t1 * t2           in  (* z_250_0 *)
    let t1 = op_it_sqr1 4 t1   in  (* z_255_5 *)
    let t1 = op_sqr t1         in
    let t1 = t0 * t1           in
        t1 axiomatized by op_invert2E.

(* lemma: op_invert2 = op_invert 1 *)
lemma eq_op_invert2 (z1: zp) :
    op_invert2 z1 = op_invert1 z1.
proof.
    rewrite op_invert2E op_invert1E. smt(eq_op_it_sqr1).
qed.

(* lemma: op_invert2 returns the inverse of its arg *)
lemma eq_op_invert210p (z1: zp) :
    op_invert2 z1 = ZModpRing.exp z1 (p-2).
proof.
    rewrite eq_op_invert2 eq_op_invert1 eq_op_invert0p //.
qed.

(* now we define an alternative version of spec_encode_point *)
op op_encode_point (q: zp * zp) : W256.t =
    let qi = op_invert2 q.`2 in
    let q =  q.`1 * qi       in
        W256.of_int (asint q) axiomatized by op_encode_pointE.

(* lemma: op_encode_point = spec_encode_point *)
lemma eq_op_encode_point (q: zp * zp) :
    op_encode_point q = spec_encode_point q.
proof.
    rewrite op_encode_pointE spec_encode_pointE. simplify. congr.
    rewrite eq_op_invert210p //.
qed.

(* step 6: spec_scalarmult with updated op_montgomery_ladder3 *)

op op_scalarmult_internal(u: zp, k:W256.t) : W256.t =
    let r = op_montgomery_ladder3 u  k in
        op_encode_point (r.`1) axiomatized by op_scalarmult_internalE.

(* lemma: spec_scalarmult = op_scalarmult *)
lemma eq_op_scalarmult_internal (u:zp) (k:W256.t) :
    k.[0] = false => op_scalarmult_internal u k = spec_scalarmult_internal u k.
proof.
    rewrite /op_scalarmult_internal. simplify.
    rewrite eq_op_encode_point /spec_scalarmult_internal.
    simplify. move => H.
    congr.
    have ml123 : spec_montgomery_ladder u k = select_double_from_triple (op_montgomery_ladder3 u k).
        apply eq_op_montgomery_ladder123. apply H.
    rewrite ml123 /select_double_from_triple //.
qed.

hint simplify op_scalarmult_internalE.

op op_scalarmult (k:W256.t) (u:W256.t) : W256.t =
    let k = spec_decode_scalar_25519 k in
    let u = spec_decode_u_coordinate u in
    op_scalarmult_internal (inzp (to_uint u)) k axiomatized by op_scalarmultE.

hint simplify op_scalarmultE.

op op_scalarmult_base(k:W256.t) : W256.t =
    op_scalarmult (k) (W256.of_int(9%Int)).

(* lemma: spec_scalarmult = op_scalarmult *)
lemma eq_op_scalarmult (k:W256.t) (u:W256.t) :
    op_scalarmult k u = spec_scalarmult k u.
proof.
    simplify.
    pose du := spec_decode_u_coordinate u.
    pose dk := spec_decode_scalar_25519 k.
    rewrite eq_op_encode_point /spec_scalarmult_internal. simplify.
    congr.
    have kb0f  : (dk).[0] = false. (* k bit 0 false *)
        rewrite /dk /spec_decode_scalar_25519 //.
    have ml123 : spec_montgomery_ladder (inzp (to_uint du)) dk = select_double_from_triple (op_montgomery_ladder3 (inzp (to_uint du)) dk).
        move : kb0f. apply eq_op_montgomery_ladder123.
    rewrite ml123 /select_double_from_triple //.
qed.

(* lemma: spec_ op_scalarmult_base = spec_scalarmult_base *)
lemma eq_op_scalarmult_base (k:W256.t) :
    op_scalarmult_base k = spec_scalarmult_base k.
proof.
    apply eq_op_scalarmult.
qed.

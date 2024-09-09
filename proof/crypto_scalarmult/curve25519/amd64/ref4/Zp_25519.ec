require import List Int IntDiv Ring CoreMap StdOrder.
require import EClib W64limbs Array4 Array5 Array32.

from Jasmin require import JModel.

import Ring.IntID IntOrder.

require ZModP.

(* modular operations modulo P *)
op p = 2^255 - 19 axiomatized by pE.

lemma two_pow255E: 2^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 by done.

lemma pVal: p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 by smt(pE two_pow255E).

(* Embedding into ring theory *)
clone import ZModP.ZModRing as Zp with
    op p <- p
    rename "zmod" as "zp"
    proof ge2_p by rewrite pE.

(* congruence "mod p" *)

lemma zpcgr_over a b:
    Zp.zpcgr (a + 57896044618658097711785492504343953926634992332820282019728792003956564819968 * b) (a + 19 * b).
proof.
    have /= ->: (2^ 255) = 19 + p by rewrite pE.
    by rewrite (mulzC _ b) mulzDr addzA modzMDr mulzC.
qed.

lemma inzp_over x:
    Zp.inzp (57896044618658097711785492504343953926634992332820282019728792003956564819968 * x) = Zp.inzp (19*x).
proof.
    by have /= := zpcgr_over 0 x; rewrite -eq_inzp.
qed.

lemma zp_over_lt2p_red x:
    p <= x < 2*p =>
    x %% p = (x + 19) %% 2^255.
proof.
    move=> *.
    rewrite modz_minus. split; smt().
    have ->: x-p = x+19-2^255.
      by rewrite pE.
    rewrite modz_minus. split.
    apply (lez_trans (p+19) (2^255) (x+19)).
    rewrite pE. trivial. smt().
    move => *. apply (ltz_trans (2*p+19) (x+19) (2*2^255)). smt().
    simplify. rewrite pE; trivial.
    smt().
qed.


lemma twop255_cgr : 2^255 %% p = 19 by smt(powS_minus  pow2_256).
lemma twop256_cgr : 2^256 %% p = 38 by smt(powS_minus  pow2_256).
lemma twop256_cgr2 : 2^256 * 2  %% p = 76 by smt(powS_minus  pow2_256).

lemma ltP_overflow x:
    (x + 2^255 + 19 < 2^256) = (x < p).
proof.
    have ->: 2^255 = p + 19 by rewrite pE /#.
    have ->: 2^256 = p + p + 19 + 19 by rewrite !pE /#.
smt().
qed.

op red x = if x + 2^255 + 19 < 2^256 then x else (x + 2^255 + 19) %% 2^256.

lemma redE x:
    p <= x < 2^256 =>
    (x + 2^255 + 19) %% 2^256 = x - p.
proof.
    move=> [H1 H2].
    pose y := x-p.
    rewrite (_: x= y+p) 1:/# (_:2^255 = p+19) 1:pE 1:/#.
    rewrite -addrA -addrA (_:p + (p + 19 + 19) = 2^256) 1:pE 1:/#.
    rewrite modzDr modz_small; last reflexivity.
    apply bound_abs.
    move: H2; have ->: 2^256 = p + p + 19 + 19 by rewrite !pE /#.
    smt(pVal).
qed.

lemma redP x:
    0 <= x < 2^256 =>
    x %% p = red (red x).
proof.
    move=> [H1 H2].
    rewrite /red !ltP_overflow.
    case: (x < p) => Hx1.
    rewrite Hx1 /= modz_small; last done.
        by apply bound_abs => /#.
    rewrite redE.
        split => *; [smt() | assumption].
    case: (x - p < p) => Hx2.
        rewrite {1}(_: x = x - p + p) 1:/# modzDr modz_small; last reflexivity.
    by apply bound_abs => /#.
    rewrite redE.
    split => *; first smt().
    rewrite (_:W256.modulus = W256.modulus-0) 1:/#.
    apply (ltr_le_sub); first assumption.
    smt(pVal).
    rewrite (_: x = x - p - p + p + p) 1:/#.
    rewrite modzDr modzDr modz_small.
    apply bound_abs; split => *; first smt().
    move: H2; have ->: 2^256 = p + p + 19 + 19 by     rewrite !pE /#.
    smt(pVal).
    smt().
qed.

op bezout_coef256 (x : int) : int * int = (x %/ W256.modulus, x %% W256.modulus).

op red256 (x: int) : int =
    (bezout_coef256 x).`2 + 38 * (bezout_coef256 x).`1.

lemma red256P x: Zp.zpcgr x (red256 x).
proof.
    by rewrite {1}(divz_eq x (2^256)) -modzDml -modzMmr twop256_cgr
    modzDml /red256 /split256 /= addrC mulrC.
qed.


lemma red256_bnd B x:
    0 <= x < W256.modulus * B =>
    0 <= red256 x < W256.modulus + 38*B.
proof.
    move=> [Hx1 Hx2]; rewrite /red256 /bezout_coef256 /=; split => *.
    apply addz_ge0; first smt(modz_cmp).
    apply mulr_ge0; first done.
    apply divz_ge0; smt().
    have H1: x %/ W256.modulus < B by smt(pow2_256).
    have H2: x %% W256.modulus < W256.modulus by smt(modz_cmp).
    smt(pow2_256).
qed.

lemma red256_once x:
    0 <= x < W256.modulus * W256.modulus =>
    0 <= red256 x < W256.modulus*39.
proof.
    have ->: W256.modulus*39 = W256.modulus + 38*W256.modulus by ring.
    exact red256_bnd.
qed.

lemma red256_twice x:
    0 <= x < W256.modulus*W256.modulus =>
    0 <= red256 (red256 x) < W256.modulus*2.
proof.
    move=> Hx; split => *.
    smt(red256_once).
    move: (red256_once x Hx).
    move => Hy.
    move: (red256_bnd 39 _ Hy); smt().
qed.

lemma red256_twiceP x a b:
    0 <= x < W256.modulus*W256.modulus =>
    (a,b) = bezout_coef256 (red256 (red256 x)) =>
    (* 0 <= a < 2 /\ (a=0 \/ b <= 38*38).*)
    a=0 \/ a=1 /\ b <= 38*38.
proof.
    move=> Hx Hab.
    have Ha: 0 <= a < 2.
    have H := (red256_twice x Hx).
    move: Hab; rewrite /split256.
    move => [-> _]. smt(pow2_256).
    case: (a=0) => Ea /=; first done.
    have {Ea} Ea: a=1 by smt().
    rewrite Ea /=.
    move: Hab; pose y := red256 x.
    rewrite /red256 /bezout_coef256 /=.
    pose yL := y%%W256.modulus.
    pose yH := y%/W256.modulus.
    have Hy := red256_once x Hx.
    have HyH : 0 <= yH <= 38 by smt().
    move => [Hab1 Hab2].
    have E: W256.modulus + b = yL + 38 * yH.
    by move: (divz_eq (yL + 38 * yH) W256.modulus); smt(pow2_256).
    smt(modz_cmp).
qed.

lemma red256_thrice x:
    0 <= x < W256.modulus*W256.modulus =>
    0 <= red256 (red256 (red256 x)) < W256.modulus.
proof.
    move=> Hx; pose y:= red256 (red256 x).
    rewrite /red256.
    have := (red256_twiceP x (bezout_coef256 y).`1 (bezout_coef256 y).`2 _ _).
    smt(pow2_256).
    smt(red256_twice).
    move=> [->|[-> H2]] /=.
    rewrite /bezout_coef256; smt(modz_cmp).
    split.
    rewrite /bezout_coef256; smt(modz_cmp).
    smt().
qed.

op reduce x = red256 (red256 (red256 x)).

lemma reduceP x:
    0 <= x < W256.modulus * W256.modulus =>
    Zp.zpcgr x (reduce x) /\ 0 <= reduce x < W256.modulus.
proof.
    rewrite /reduce => H; split; first smt(red256P).
    smt(pow2_256 red256_thrice).
qed.

lemma expE (z : zp) (e1 e2 : int) : 0 <= e1 /\ 0 <= e2 =>
    ZModpRing.exp (ZModpRing.exp z e1) e2 =
    ZModpRing.exp z (e1*e2).
proof.
    rewrite -ZModpRing.exprM => />.
qed.

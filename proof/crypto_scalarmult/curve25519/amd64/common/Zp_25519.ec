require import Core Int Ring IntDiv StdOrder List.

from Jasmin require import JModel.

import Ring.IntID StdOrder.IntOrder.

(* modular operations modulo P *)
op p = 2^255 - 19 axiomatized by pE.

(* Embedding into ring theory *)
lemma two_pow255E: 2^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 by done.

lemma pVal: p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 by smt(pE two_pow255E).

require ZModP.

clone import ZModP.ZModRing as Zp with
        op p <- p
        rename "zmod" as "zp"
        proof ge2_p by rewrite pE.

lemma expE (z : zp) (e1 e2 : int) : 0 <= e1 /\ 0 <= e2 =>
    ZModpRing.exp (ZModpRing.exp z e1) e2 =
    ZModpRing.exp z (e1*e2).
proof.
    rewrite -ZModpRing.exprM => />.
qed.

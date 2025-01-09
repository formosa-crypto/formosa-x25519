require import List Int IntDiv Ring.

from Jasmin require import JModel JWord.
require import Zp_25519 EClib Array4.

import Zp Ring.IntID.

require import Array4.

op val_digits (base: int) (x: int list) =
 foldr (fun w r => w + base * r) 0 x.

abbrev digits64 = List.map W64.to_uint.
abbrev val_limbs base l = val_digits base (digits64 l).

abbrev val_digits64 = val_digits (2^64).
abbrev val_limbs64 x = val_digits64 (digits64 x).

type Rep4 = W64.t Array4.t.
op valRep4       (x : Rep4)           : int   = val_limbs64 (Array4.to_list x) axiomatized by valRep4E.
op valRep4List   (x : W64.t list)     : int   = val_limbs64 x       axiomatized by valRep4ListE.
op inzpRep4      (x : Rep4)           : zp    = inzp (valRep4 x)     axiomatized by inzpRep4E.
op inzpRep4List  (x: W64.t list)      : zp    = inzp (valRep4List x) axiomatized by inzpRep4ListE.

lemma to_uint_unpack4u64 w:
    W256.to_uint w = val_digits W64.modulus (map W64.to_uint (W4u64.to_list w)).
proof.
    have [? /= ?]:= W256.to_uint_cmp w.
    rewrite /val_digits /=.
    do 4! (rewrite bits64_div 1:// /=).
    rewrite !of_uintK /=.
    have P: forall x, x = x %% 18446744073709551616 + 18446744073709551616 * (x %/ 18446744073709551616).
        by move=> x; rewrite {1}(divz_eq x 18446744073709551616) /=; ring.
    rewrite {1}(P (to_uint w)) {1}(P (to_uint w %/ 18446744073709551616)) divz_div 1..2:/# /=
            {1}(P (to_uint w)) {1}(P (to_uint w %/  340282366920938463463374607431768211456)) divz_div 1..2:/# /=
            {1}(P (to_uint w)) {1}(P (to_uint w %/ 6277101735386680763835789423207666416102355444464034512896)) divz_div 1..2:/# /=.
     by ring; smt().
qed.

lemma valRep4ToPack x:  valRep4 x = W256.to_uint (W4u64.pack4 (Array4.to_list x)).
proof.
    rewrite valRep4E. rewrite to_uint_unpack4u64.
     auto => />.
    have E: forall k, 0 <= k < 4 => nth W64.zero (to_list x) k = x.[k].
    + move => H H0. rewrite /to_list /mkseq -iotaredE => />. smt().
    rewrite !E; trivial. rewrite /to_list /mkseq -iotaredE => />.
qed.

lemma valRep4ToPack_xy (x: W256.t, y):
    W256.to_uint x =  valRep4 y => x  = W4u64.pack4 (Array4.to_list y).
    rewrite valRep4ToPack. move => H.
    smt(@W256).
qed.

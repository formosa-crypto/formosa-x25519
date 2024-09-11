require import List Int IntDiv Ring CoreMap StdOrder.
require import Zp_25519 EClib W64limbs Array4 Array32.

from Jasmin require import JModel JWord.

import Zp Ring.IntID Array4 Array32 IntOrder JWord.W8 JWord.W64.


op inzp_limbs base l = inzp (val_limbs base l).

type Rep4 = W64.t Array4.t.
type Rep32 = W8.t Array32.t.

op valRep4       (x : Rep4)           : int   = val_limbs64 (Array4.to_list x) axiomatized by valRep4E.
op valRep4List   (x : W64.t list)     : int   = val_limbs64 x       axiomatized by valRep4ListE.
op inzpRep4      (x : Rep4)           : zp    = inzp (valRep4 x)     axiomatized by inzpRep4E.
op inzpRep4List  (x: W64.t list)      : zp    = inzp (valRep4List x) axiomatized by inzpRep4ListE.

op valRep32List  (x : W8.t list)      : int    = val_limbs8 x axiomatized by valRep32ListE.
op valRep32      (x : Rep32)          : int    = val_limbs8 (Array32.to_list x) axiomatized by valRep32E.
op inzpRep32     (x : Rep32)          : zp     = inzp (valRep32 x) axiomatized by inzpRep32E.
op inzpRep32List (x : W8.t list)      : zp     = inzp (valRep32List x) axiomatized by inzpRep32ListE.

lemma val_limbs64_div2255 x0 x1 x2 x3:
    val_limbs64 [x0; x1; x2; x3] %/ 2^255 = to_uint x3 %/ 9223372036854775808.
proof.
    rewrite /val_digits /=.
    have := (divz_eq (to_uint x3) 9223372036854775808).
    rewrite addzC mulzC => {1}->.
    rewrite !mulzDr -!mulzA /=.
    have /= ? := W64.to_uint_cmp x0.
    have /= ? := W64.to_uint_cmp x1.
    have /= ? := W64.to_uint_cmp x2.
    have /= ? := W64.to_uint_cmp x3.
    have ? : 0 <= to_uint x3 %% 9223372036854775808 < 9223372036854775808 by smt().
    rewrite !addzA (mulzC 57896044618658097711785492504343953926634992332820282019728792003956564819968) divzMDr //.
    have ->: (to_uint x0 + 18446744073709551616 * to_uint x1 +
             340282366920938463463374607431768211456 * to_uint x2 +
             6277101735386680763835789423207666416102355444464034512896 * (to_uint x3 %% 9223372036854775808)) %/
             57896044618658097711785492504343953926634992332820282019728792003956564819968 = 0.
        by rewrite -divz_eq0 /#.
    by ring.
qed.


lemma val_limbs64_div2256 x0 x1 x2 x3:
    val_limbs64 [x0; x1; x2; x3] %/ 2^256 = to_uint x3 %/ 2^64.
proof.
    rewrite /val_digits /=.
    have := (divz_eq (to_uint x3) 18446744073709551616).
    rewrite addzC mulzC => {1}->.
    rewrite !mulzDr -!mulzA /=.
    have /= ? := W64.to_uint_cmp x0.
    have /= ? := W64.to_uint_cmp x1.
    have /= ? := W64.to_uint_cmp x2.
    have /= ? := W64.to_uint_cmp x3.
    have ? : 0 <= to_uint x3 %% 18446744073709551616 < 18446744073709551616 by smt().
    rewrite !addzA (mulzC 115792089237316195423570985008687907853269984665640564039457584007913129639936) divzMDr //.
    have ->: (to_uint x0 + 18446744073709551616 * to_uint x1 +
             340282366920938463463374607431768211456 * to_uint x2 +
             6277101735386680763835789423207666416102355444464034512896 * (to_uint x3 %% W64.modulus)) %/
             115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0.
        by rewrite -divz_eq0 /#.
    by ring.
qed.


op valid_ptr(p : int, o : int) = 0 <= o => 0 <= p /\ p + o < W64.modulus.

op load_array4 (m : global_mem_t, p : address) : W64.t list =
    [loadW64 m p; loadW64 m (p+8); loadW64 m (p+16); loadW64 m (p+24)].

op load_array32(m : global_mem_t, p : address) : W8.t Array32.t =
      Array32.init (fun i => m.[p + i]).

lemma valRep4ToPack x:  valRep4 x = W256.to_uint (W4u64.pack4 (Array4.to_list x)).
proof.
    rewrite valRep4E. rewrite to_uint_unpack4u64.
    congr. congr. auto => />.
    have E: forall k, 0 <= k < 4 => nth W64.zero (to_list x) k = x.[k].
    + move => H H0. rewrite /to_list /mkseq -iotaredE => />. smt().
    rewrite !E; trivial. rewrite /to_list /mkseq -iotaredE => />.
qed.

lemma inzpRep4ToPack x:  inzpRep4 x = inzp (W256.to_uint (W4u64.pack4 (Array4.to_list x))).
proof.
    rewrite inzpRep4E. congr. apply valRep4ToPack.
qed.

lemma valRep4ToPack_xy (x: W256.t, y):
    W256.to_uint x =  valRep4 y => x  = W4u64.pack4 (Array4.to_list y).
    rewrite valRep4ToPack. move => H.
    smt(W256.to_uintK).
qed.


lemma load_store_pos (mem: global_mem_t, p: W64.t, w: Rep4, i: int) :
    valid_ptr (to_uint p) 32 => (i = 0 \/ i = 8 \/ i = 16 \/ i = 24) =>
    w.[i %/ 8] =
        loadW64
            (storeW64
                (storeW64
                    (storeW64
                        (storeW64 mem (W64.to_uint p) w.[0])
                        (W64.to_uint (p + (W64.of_int 8)%W64)) w.[1])
                    (W64.to_uint (p + (W64.of_int 16)%W64)) w.[2])
                (W64.to_uint (p + (W64.of_int 24)%W64)) w.[3])
            (W64.to_uint p + i).
proof.
    move => V0 I.
    rewrite /load_array4 !/storeW64 !/stores /= load8u8' /mkseq -iotaredE => />.
    rewrite wordP => V1 V2. rewrite !to_uintD_small !to_uint_small => />.
    move: V0. rewrite /valid_ptr. smt().
    move: V0. rewrite /valid_ptr. smt().
    move: V0. rewrite /valid_ptr. smt().
    rewrite pack8wE => />. rewrite get_of_list. smt().
    rewrite !bits8E !get_setE. auto => />.
    case: (i = 0). auto => />.
    case: (V1 %/ 8 = 0). move => V3.
    do 31! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 1 = 0). move => *.
    do 30! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 2 = 0). move => *.
    do 29! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 3 = 0). move => *.
    do 28! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 27! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 26! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 25! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 24! (rewrite ifF 1:/#). smt(W8.initE).
    move => *. smt(W8.initE).
    case: (i = 8). auto => />.
    case: (V1 %/ 8 = 0). move => V3.
    do 23! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 1 = 0). move => *.
    do 22! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 2 = 0). move => *.
    do 21! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 3 = 0). move => *.
    do 20! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 19! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 18! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 17! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 16! (rewrite ifF 1:/#). smt(W8.initE).
    move => *. smt(W8.initE).
    case: (i = 16). auto => />.
    case: (V1 %/ 8 = 0). move => V3.
    do 15! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 1 = 0). move => *.
    do 14! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 2 = 0). move => *.
    do 13! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 3 = 0). move => *.
    do 12! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 11! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 10! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 9! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 8! (rewrite ifF 1:/#). smt(W8.initE).
    move => *. smt(W8.initE).
    case: (i = 24). auto => />.
    case: (V1 %/ 8 = 0). move => V3.
    do 7! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 1 = 0). move => *.
    do 6! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 2 = 0). move => *.
    do 5! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 3 = 0). move => *.
    do 4! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 4 = 0). move => *.
    do 3! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 5 = 0). move => *.
    do 2! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 6 = 0). move => *.
    do 1! (rewrite ifF 1:/#). smt(W8.initE).
    case: (V1 %/ 8 - 7 = 0). move => *.
    do 0! (rewrite ifF 1:/#). smt(W8.initE).
    move => *. smt(W8.initE).  move => *.
    smt(W8.initE).
qed.

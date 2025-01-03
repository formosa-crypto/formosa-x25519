require import Real Bool Int IntDiv List StdOrder BitEncoding.
from Jasmin require import JModel JUtils.
require import  Add4Extracted Sub4Extracted Mul4RefExtracted Mul4_a24RefExtracted Sqr4RefExtracted. (* must be in this order so module names do not clash *)
require import Curve25519_Procedures Ref4_scalarmult_s CryptolineEquivs_Ref4 Zp_limbs Zp_25519 CommonCryptoline Jcheck.

import Zp Ring.IntID IntOrder BS2Int.

require import Array4 Array32 WArray32.

(* Spec to prove smaller parts of ToBytes and then compose the, *)
module ToBytesSpec = {

 proc extract_msb(f3: W64.t) : W64.t = {
    var _of_, _cf_, _sf_, _zf_, _0, aux_3, aux_2, aux_1, aux_0, aux : bool;
    var aux_4: W64.t;

    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- SAR_64 f3 ((of_int 63))%W8;
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
    _0 <- aux_0;
    _zf_ <- aux;
    f3 <- aux_4;
    return f3;
 }

 proc remove_msb_if_set(f3: W64.t) : W64.t = {
    var _of_, _cf_, _sf_, _zf_, _0, aux_3, aux_2, aux_1, aux_0, aux : bool;
    var t: W64.t;

    t <- LEA_64 (f3 + f3);
    t <- t `>>` W8.one;

    return t;
 }

 proc to_0_or_19 (t: W64.t) : W64.t = {
    var _of_, _cf_, _sf_, _2, _zf_ : bool;
    var _tt, tt0, tt1 : W64.t;

    (_of_, _cf_, _sf_, _2, _zf_, _tt) <- SAR_64 t ((of_int 63))%W8;
    tt0 <- invw _tt;
    tt1 <- tt0 `&` (of_int 19)%W64;
    return tt1;
 }

 proc to_19_or_38(t: W64.t) : W64.t = {

    t <- t `&` (of_int 19)%W64;
    t <- t + (of_int 19)%W64;

    return t;
 }

 proc addition(f: Rep4, _tt: W64.t, operand2: W64.t) : Rep4 = {
  var aux_4, tt0 : W64.t;
  var cf, cf0, cf1, aux_3, _1 : bool;
  var ff : Rep4; (* we don't change the value of f, easier proofs *)

  (aux_3, aux_4) <- addc f.[0] operand2 false;
  cf <- aux_3;
  ff <- ff.[0 <- aux_4];
  (aux_3, aux_4) <- addc f.[1] W64.zero cf;
  cf0 <- aux_3;
  ff <- ff.[1 <- aux_4];
  (aux_3, aux_4) <- addc f.[2] W64.zero cf0;
  cf1 <- aux_3;
  ff <- ff.[2 <- aux_4];
  (_1, tt0) <- addc _tt W64.zero cf1;
  ff <- ff.[3 <- tt0];

  return ff;
 }

 proc subtraction(f: Rep4, operand2: W64.t) : Rep4 = {
  var aux_4 : W64.t;
  var cf, cf0, cf1, _3, aux_3 : bool;
  var ff : Rep4; (* we don't change the value of f, easier proofs *)


  (aux_3, aux_4) <- subc f.[0] operand2 false;
  cf <- aux_3;
  ff <- ff.[0 <- aux_4];
  (aux_3, aux_4) <- subc f.[1] W64.zero cf;
  cf0 <- aux_3;
  ff <- ff.[1 <- aux_4];
  (aux_3, aux_4) <- subc f.[2] W64.zero cf0;
  cf1 <- aux_3;
  ff <- ff.[2 <- aux_4];
  (aux_3, aux_4) <- subc f.[3] W64.zero cf1;
  _3 <- aux_3;
  ff <- ff.[3 <- aux_4];

  return ff;
 }


 proc to_bytes(f: Rep4) : Rep4 = {
     var msb1, _tt, _tt0, msb2, _f3, _tt2  : W64.t;
     var ff, ff2, ff3 : Rep4; (* we don't change the value of f, easier proofs *)

     msb1 <@ extract_msb (f.[3]);
     _tt  <@ remove_msb_if_set (f.[3]);
     _tt0 <@ to_19_or_38 (msb1);
     ff   <@ addition(f, _tt, _tt0);
     _f3  <@ remove_msb_if_set (ff.[3]);
     ff2 <- ff.[3 <- _f3];
     _tt2 <@ to_0_or_19(ff.[3]);
     ff3  <@ subtraction(ff2, _tt2);
     return ff3;
 }
}.

(* Helper lemmas *)
lemma cminusP0 r: 0 <= r < p => r = asint (inzp r).
proof. move => H. rewrite inzpK pE => />. by rewrite pmod_small; 1:smt(pVal). qed.

lemma cminusP1 r: p <= r < 2*p => r - p = asint (inzp r).
proof. rewrite inzpK => />. move => [#] H H0. smt(pE pVal). qed.

lemma cminusP2 r: 2*p <= r < W256.modulus => r - p - p = asint (inzp r).
proof. rewrite inzpK => />. move => [#] H H0. smt(pE pVal). qed.

(** Range lemmas **)
lemma valRep4_cmp f: 0 <= valRep4 f < W256.modulus.
proof. rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />. move: W64.to_uint_cmp. smt(). qed.

lemma limb4_ltP_cmp r: 0 <= valRep4 r < p => 0 <= (to_uint r.[3]) < pow 2 63.
proof. rewrite valRep4E pE /to_list /val_digits /mkseq -iotaredE => />. smt(W64.to_uint_cmp). qed.

lemma limb4_lt_2_255_cmp r: 0 <= valRep4 r < pow 2 255 => 0 <= (to_uint r.[3]) < pow 2 63.
proof. rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />. smt(W64.to_uint_cmp). qed.

lemma limb4_gtP_cmp r: p < valRep4 r < W64.modulus => pow 2 63 <= (to_uint r.[3]) < W64.modulus.
proof. rewrite valRep4E pE /to_list /val_digits /mkseq -iotaredE => />. smt(W64.to_uint_cmp). qed.

lemma limb4_geq_2_255_cmp r: pow 2 255 <= valRep4 r < W256.modulus =>
           pow 2 63 <= (to_uint r.[3]) < W64.modulus.
proof. rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />.
       move => H H0. do split. move: W64.to_uint_cmp. smt(). move: W64.to_uint_cmp. smt(). qed.

(** MSB lemmas **)
lemma limb4_msbw0 r: 0 <=  W64.to_uint r < pow 2 63 => r.[63] = false.
proof. move => H. have E: b2i r.[63] = 0.
       rewrite b2i_get //=. move: H. smt(). smt(). qed.

lemma limb4_msbw1 r: pow 2 63 <= W64.to_uint r < W64.modulus => r.[63] = true.
proof. move => H. have E: b2i r.[63] = 1.
       rewrite b2i_get //=. move: H. smt(). smt(). qed.

lemma limb4_ltP_msb r: 0 <= valRep4 r < p => r.[3].[63] = false.
proof. move => H. have E: b2i r.[3].[63] = 0.
       rewrite b2i_get //=. move: limb4_ltP_cmp W64.to_uint_cmp; 1:smt(). smt(). qed.

lemma limb4_gtP_msb r: p < valRep4 r < W64.modulus => r.[3].[63] = true.
proof. move => H. have E: b2i r.[3].[63] = 1.
       rewrite b2i_get //=. move: H.
       rewrite valRep4E pE /to_list /val_digits /mkseq -iotaredE => />. smt(W64.to_uint_cmp).
       smt().
qed.

(** Helper lemmas **)
lemma helper_lemma_msb_is_not_set (f: W64.t):
    0 <= W64.to_uint f < pow 2 63 => LEA_64 (f + f) `>>` W8.one = f.
proof.
    auto => />. rewrite /LEA_64 => *.
    have E: W64.to_uint (f + f `>>` W8.of_int 1) = W64.to_uint f.
    rewrite to_uint_shr //= !to_uintD !modz_small /absz //=.
    smt(). smt(). smt(@W64).
qed.

lemma helper_lemma_extract_msb_0 (f: W64.t) : 0 <= W64.to_uint f < pow 2 63 => (SAR_64 f ((of_int 63))%W8).`6 = W64.zerow.
proof.
    auto => />. move => H H0. rewrite /SAR_64 /shift_mask /rflags_OF //= sarE.
    rewrite init_bits2w bits2wE -iotaredE /min //=.
    rewrite limb4_msbw0 //=.
    + rewrite /W64.zerow /W64.zero bits2wE /int2bs /mkseq -iotaredE => />.
qed.

lemma helper_lemma_extract_msb_1 (f: W64.t) : pow 2 63 <= W64.to_uint f < pow 2 64 => (SAR_64 f ((of_int 63))%W8).`6 = W64.onew.
proof.
    auto => />. move => H H0. rewrite /SAR_64 /shift_mask /rflags_OF //= sarE.
    rewrite init_bits2w bits2wE -iotaredE /min //=.
    rewrite limb4_msbw1 //=.
    + rewrite /W64.onew of_intE  bits2wE /int2bs /mkseq -iotaredE => />.
qed.

lemma helper_lemma_remove_msb (f: W64.t):
    pow 2 63 <= W64.to_uint f < pow 2 64 => LEA_64 (f + f) `>>` W8.one = f - W64.of_int (pow 2 63).
proof.
    auto => />. rewrite /LEA_64 => *.
    rewrite shr_shrw //= addE !/ulift2 of_intE => />. rewrite of_intE.
    have !->: (u64i f + u64i f) %% 18446744073709551616 = (u64i f + u64i f) - 18446744073709551616. smt().
    rewrite !to_uintN !of_uintK.
    have !->: - 9223372036854775808 %% pow 2 64 =
                9223372036854775808 - pow 2 64. smt(). auto => />.
    have !->: (u64i f + 9223372036854775808) %% 18446744073709551616 =
              (u64i f + 9223372036854775808) - 18446744073709551616.
    move: W64.to_uint_cmp. smt(). auto => />.
    rewrite wlsrE init_bits2w. congr. rewrite /int2bs /mkseq -!iotaredE => />.
    do split; 1..63:smt().
    rewrite get_out /#.
qed.

lemma helper_lemma_to_19 (t: W64.t) : 0 <= u64i t && u64i t < pow 2 63 => invw (SAR_64 t ((of_int 63))%W8).`6 `&` (of_int 19)%W64 = (of_int 19)%W64.
proof.
    auto => />. move => H H0.
    have ->: (SAR_64 t ((of_int 63))%W8).`6 = W64.zerow.
    + rewrite /SAR_64 /shift_mask /rflags_OF //= sarE /min => />.
    rewrite init_bits2w bits2wE -iotaredE /min //=.
    rewrite limb4_msbw0 //=.
    + rewrite /W64.zerow /W64.zero bits2wE /int2bs /mkseq -iotaredE => />.
    have ->: invw W64.zerow = W64.onew.
    + rewrite /invw mapE /W64.zerow /W64.zero bits2wE /int2bs /mkseq -iotaredE => />.
    + rewrite /W64.onew of_intE bits2wE /int2bs /mkseq -iotaredE => />.
    + rewrite wordP => i ib. rewrite !initiE 1,2:/# //= initiE 1:/# //= 1:/#.
    rewrite wordP => i ib.
    rewrite /W64.onew !of_intE !bits2wE !/int2bs !/mkseq -!iotaredE => />.
    rewrite !initiE 1,2:/# //= /#.
qed.

lemma helper_lemma_to_0 (t: W64.t) : pow 2 63 <= u64i t && u64i t < pow 2 64 => invw (SAR_64 t ((of_int 63))%W8).`6 `&` (of_int 19)%W64 = (of_int 0)%W64.
proof.
    auto => />. move => H H0.
    have ->: (SAR_64 t ((of_int 63))%W8).`6 = W64.onew.
    + rewrite /SAR_64 /shift_mask /rflags_OF //= sarE /min => />.
    rewrite init_bits2w bits2wE -iotaredE /min //=.
    rewrite limb4_msbw1 //=.
    + rewrite /W64.onew of_intE bits2wE /int2bs /mkseq -iotaredE => />.
    have ->: invw W64.onew = W64.zerow.
    + rewrite /invw mapE /W64.zerow /W64.zero bits2wE /int2bs /mkseq -iotaredE => />.
    + rewrite wordP => i ib. rewrite !initiE 1,2:/# //=. smt().
    rewrite wordP => i ib.
    rewrite /W64.onew !of_intE !bits2wE !/int2bs !/mkseq -!iotaredE => />.
    rewrite !initiE 1,2:/# //= /#.
qed.

lemma not_false_to_true bst: (bst <> false) = (bst = true) by smt().

lemma valRep4_equiv_representation (r: Rep4): r = (of_list witness [r.[0]; r.[1]; r.[2]; r.[3]])%Array4.
proof.
    auto => />. apply Array4.ext_eq => i ib.
    case (i = 3) => I. rewrite I => />.
    case (i = 2) => I0. rewrite I0 => />.
    case (i = 1) => I1. rewrite I1 => />.
    case (i = 0) => I2. rewrite I2 => />. rewrite get_out /#.
qed.

lemma valRep4_remove_limb4_ltP r: 0 <= valRep4 r < p => valRep4 r.[3 <- W64.zerow] < p - u64i r.[3].
proof.
    auto => />.
    rewrite !valRep4E !pE !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite to_uint0 => />. smt(W64.to_uint_cmp).
qed.

lemma valRep4_remove_limb4_geP_lt_2_255 r: p <= valRep4 r < pow 2 255 => valRep4 r.[3 <- W64.zerow] < pow 2 255 - u64i r.[3].
proof.
    auto => />.
    rewrite !valRep4E !pE !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite to_uint0 => />. smt(W64.to_uint_cmp).
qed.

lemma valRep4_remove_limb4_ltP_structure r: 0 <= valRep4 r < p => r.[3 <- W64.zerow] = (of_list witness [r.[0]; r.[1]; r.[2]; W64.zerow])%Array4.
proof.
    auto => />. move => H H0. apply Array4.ext_eq => i ib.
    rewrite !get_setE 1:/#.
    case (i = 3) => I. rewrite I => />.
    case (i = 2) => I0. rewrite I0 => />.
    case (i = 1) => I1. rewrite I1 => />.
    case (i = 0) => I2. rewrite I2 => />. rewrite get_out /#.
qed.

lemma valRep4_remove_limb4_ltP_structure_2 r: p <= valRep4 r < pow 2 255 => r.[3 <- W64.zerow] = (of_list witness [r.[0]; r.[1]; r.[2]; W64.zerow])%Array4.
proof.
    auto => />. move => H H0. apply Array4.ext_eq => i ib.
    rewrite !get_setE 1:/#.
    case (i = 3) => I. rewrite I => />.
    case (i = 2) => I0. rewrite I0 => />.
    case (i = 1) => I1. rewrite I1 => />.
    case (i = 0) => I2. rewrite I2 => />. rewrite get_out /#.
qed.

abbrev add_l1 (r: Rep4, i: int) = (addc r.[0] ((of_int i))%W64 false).`2.
abbrev add_l2 (r: Rep4, i: int) = (addc r.[1] W64.zero (addc_carry r.[0] ((of_int i))%W64 false)).`2.
abbrev add_l3 (r: Rep4, i: int) = (addc r.[2] W64.zero (addc_carry r.[1] W64.zero (addc_carry r.[0] ((of_int i))%W64 false))).`2.
abbrev add_l4 (r: Rep4, __tt: W64.t, i: int) = (addc __tt W64.zero (addc_carry r.[2] W64.zero (addc_carry r.[1] W64.zero (addc_carry r.[0] ((of_int i))%W64 false)))).`2.

abbrev add_to_limb (r: Rep4, __tt: W64.t, i: int) = Array4.of_list witness [add_l1 r i; add_l2 r i; add_l3 r i; add_l4 r __tt i ].

abbrev sub_l1 (r: Rep4, i: int) = (subc r.[0] ((of_int i))%W64 false).`2.
abbrev sub_l2 (r: Rep4, i: int) = (subc r.[1] W64.zero (subc_borrow r.[0] ((of_int i))%W64 false)).`2.
abbrev sub_l3 (r: Rep4, i: int) = (subc r.[2] W64.zero (subc_borrow r.[1] W64.zero (subc_borrow r.[0] ((of_int i))%W64 false))).`2.
abbrev sub_l4 (r: Rep4, i: int) = (subc r.[3] W64.zero (subc_borrow r.[2] W64.zero (subc_borrow r.[1] W64.zero (subc_borrow r.[0] ((of_int i))%W64 false)))).`2.

abbrev sub_from_limb (r: Rep4, i: int) = Array4.of_list witness [sub_l1 r i; sub_l2 r i; sub_l3 r i; sub_l4 r i ].

lemma limb4_valRep4_add19_cmp f __tt: valRep4 (add_to_limb f __tt 19) < p + 19 => 0 <= u64i (add_l4 f __tt 19) => u64i (add_l4 f __tt 19) < 9223372036854775808.
proof.
   + rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + rewrite !addcE !/carry_add !b2i0 => />.
   + case (18446744073709551616 <= u64i f.[0] + 19 = false) => C. rewrite !C !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f.[1] = false. move: W64.to_uint_cmp. smt().
   + have !->: 18446744073709551616 <= u64i f.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C. rewrite not_false_to_true. move => C. rewrite !C !b2i1 => />.
   + case (18446744073709551616 <= u64i f.[1] + 1 = false) => C1. rewrite !C1 !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1 => />.
   + case (18446744073709551616 <= u64i f.[2] + 1 = false) => C2. rewrite !C2 !b2i0 => />.
   + smt(W64.to_uint_cmp).
   + move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1 => />.
   + rewrite !to_uintD of_uintK. smt(W64.to_uint_cmp).
qed.

lemma limb4_add19_range_l4_ltP r __tt: 0 <= valRep4 r =>
  valRep4 r < p =>
  valRep4 r + 19 = valRep4 (add_to_limb r __tt 19) =>
  0 <= u64i (add_l4 r __tt 19) /\
  (0 <= u64i (add_l4 r __tt 19) => u64i (add_l4 r __tt 19) < 9223372036854775808).
proof.
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !of_uintK (modz_small 19 (pow 2 64)) 1:/# => />.
    move: (limb4_ltP_cmp r) W64.to_uint_cmp. smt().
qed.

lemma limb4_add_equiv_ltP r:
0 <= valRep4 r =>
valRep4 r < p =>
u64i r.[3] < 18446744073709551597 /\
(u64i r.[3] < 18446744073709551597 =>
 valRep4 ((of_list witness [r.[0]; r.[1]; r.[2]; r.[3]]))%Array4 + 19 =
 valRep4 (add_to_limb r r.[3] 19) =>
 valRep4 r + 19 = valRep4 (add_to_limb r r.[3] 19)).
proof.
  rewrite pVal -valRep4_equiv_representation.
  rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />. smt(W64.to_uint_cmp).
qed.

lemma limb4_add_equiv_geqP_lt_2p r:
p <= valRep4 r =>
valRep4 r <
57896044618658097711785492504343953926634992332820282019728792003956564819968 =>
u64i r.[3] < 18446744073709551597 /\
(u64i r.[3] < 18446744073709551597 =>
 valRep4 ((of_list witness [r.[0]; r.[1]; r.[2]; r.[3]]))%Array4 + 19 =
 valRep4 (add_to_limb r r.[3] 19) =>
 valRep4 r + 19 = valRep4 (add_to_limb r r.[3] 19)).
proof.
  rewrite pVal -valRep4_equiv_representation.
  rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />. smt(W64.to_uint_cmp).
qed.

lemma limb4_add_sub_equiv_geq2P r:
2 * p <= valRep4 r =>
valRep4 r <
115792089237316195423570985008687907853269984665640564039457584007913129639936 =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) =
u64i r.[3] - 9223372036854775808 =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) < 18446744073709551578 /\
(u64i (r.[3] - (of_int 9223372036854775808)%W64) < 18446744073709551578 =>
 valRep4
   ((of_list witness
       [r.[0]; r.[1]; r.[2]; r.[3] - (of_int 9223372036854775808)%W64]))%Array4 +
 38 = valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
 valRep4 r -
 57896044618658097711785492504343953926634992332820282019728792003956564819930 =
 valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38)).
proof.
    rewrite !pVal.
    move => H H0 H1.
    do split. rewrite H1. move: W64.to_uint_cmp. smt().
    move => H2 H3. rewrite -H3.
    move: H H0 H1 H2 H3. rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + move: W64.to_uint_cmp. smt(@W64).
qed.

lemma limb4_add_sub_equiv_geqP_lt_2p r:
57896044618658097711785492504343953926634992332820282019728792003956564819968 <=
valRep4 r =>
valRep4 r < 2 * p =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) =
u64i r.[3] - 9223372036854775808 =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) < 18446744073709551578 /\
(u64i (r.[3] - (of_int 9223372036854775808)%W64) < 18446744073709551578 =>
 valRep4
   ((of_list witness
       [r.[0]; r.[1]; r.[2]; r.[3] - (of_int 9223372036854775808)%W64]))%Array4 +
 38 = valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
 valRep4 r -
 57896044618658097711785492504343953926634992332820282019728792003956564819930 =
 valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38)).
proof.
    move: (limb4_geq_2_255_cmp r) W64.to_uint_cmp.
    rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />. smt().
qed.

lemma limb4_add_range_ltP r:
0 <= valRep4 r =>
valRep4 r < p =>
valRep4 r + 19 = valRep4 (add_to_limb r r.[3] 19) =>
0 <= u64i (add_l4 r r.[3] 19) /\
(0 <= u64i (add_l4 r r.[3] 19) =>
 u64i (add_l4 r r.[3] 19) < 9223372036854775808).
proof.
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !of_uintK (modz_small 19 (pow 2 64)) 1:/# => />.
    move: W64.to_uint_cmp limb4_gtP_cmp. smt().
qed.

lemma limb4_add_range_geqP_lt_2_255 r:
p <= valRep4 r =>
valRep4 r <
pow 2 255 =>
valRep4 r + 19 = valRep4 (add_to_limb r r.[3] 19) =>
9223372036854775808 <= u64i (add_l4 r r.[3] 19) /\
(9223372036854775808 <= u64i (add_l4 r r.[3] 19) =>
 u64i (add_l4 r r.[3] 19) < 18446744073709551616).
proof.
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !of_uintK (modz_small 19 (pow 2 64)) 1:/# => />.
    move: W64.to_uint_cmp limb4_gtP_cmp. smt().
qed.

lemma limb4_add_range_geq_2_255_lt_2p r:
57896044618658097711785492504343953926634992332820282019728792003956564819968 <=
valRep4 r =>
valRep4 r < 2 * p =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) =
u64i r.[3] - 9223372036854775808 =>
valRep4 r -
57896044618658097711785492504343953926634992332820282019728792003956564819930 =
valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
0 <= u64i (add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38) /\
(0 <= u64i (add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
 u64i (add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38) <
 9223372036854775808).
proof.
    move => H H0 H1 H2.
    do split. smt(W64.to_uint_cmp). move => H3. rewrite !addcE !/carry_add !b2i0 => />.
    + rewrite to_uintD. rewrite !H1.
    + move: H H0 H1 H2 H3. rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + move: W64.to_uint_cmp. smt(@W64).
qed.

lemma limb4_add_range_geq2P r:
2 * p <= valRep4 r =>
valRep4 r <
115792089237316195423570985008687907853269984665640564039457584007913129639936 =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) =
u64i r.[3] - 9223372036854775808 =>
valRep4 r -
57896044618658097711785492504343953926634992332820282019728792003956564819930 =
valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
9223372036854775808 <=
u64i (add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38) /\
(9223372036854775808 <=
 u64i (add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
 u64i (add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38) <
 18446744073709551616).
proof.
    move => H H0 H1 H2.
    do split. rewrite !addcE !/carry_add !b2i0 => />.
    rewrite to_uintD. rewrite H1.
    + move: H H1 H2 pVal W64.to_uint_cmp.
    + rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />. smt(@W64).
    move => H3.
    + move: H H1 H2 pVal W64.to_uint_cmp.
    + rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />. smt(@W64).
qed.

lemma limb4_set_f3_geq_2_255_lt_2p r:
p <= valRep4 r =>
valRep4 r <
57896044618658097711785492504343953926634992332820282019728792003956564819968 =>
valRep4 r + 19 = valRep4 (add_to_limb r r.[3] 19) =>
valRep4
  (add_to_limb r r.[3] 19).[3 <-
    add_l4 r r.[3] 19 - (of_int 9223372036854775808)%W64] =
valRep4 (add_to_limb r r.[3] 19) -
57896044618658097711785492504343953926634992332820282019728792003956564819968.
proof.
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !of_uintK (modz_small 19 (pow 2 64)) 1:/# => />.
    case (18446744073709551616 <= u64i r.[0] + 19 = false) => C. rewrite !C !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i r.[1] = false. move: W64.to_uint_cmp. smt().
   + have !->: 18446744073709551616 <= u64i r.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C. rewrite not_false_to_true. move => C. rewrite !C !b2i1 => />.
   + case (18446744073709551616 <= u64i r.[1] + 1 = false) => C1. rewrite !C1 !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i r.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1 => />.
   + case (18446744073709551616 <= u64i r.[2] + 1 = false) => C2. rewrite !C2 !b2i0 => />.
   + smt(W64.to_uint_cmp).
   + move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1 => />.
   + rewrite !to_uintN. smt().
qed.

lemma limb4_set_f3_gtP_lt_2p r:
57896044618658097711785492504343953926634992332820282019728792003956564819968 <=
valRep4 r =>
valRep4 r < 2 * p =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) =
u64i r.[3] - 9223372036854775808 =>
valRep4 r -
57896044618658097711785492504343953926634992332820282019728792003956564819930 =
valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
valRep4
  (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38).[3 <-
    add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38] =
valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38).
proof.
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
qed.

lemma limb4_set_f3_gt2P r:
2 * p <= valRep4 r =>
valRep4 r <
115792089237316195423570985008687907853269984665640564039457584007913129639936 =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) =
u64i r.[3] - 9223372036854775808 =>
valRep4 r -
57896044618658097711785492504343953926634992332820282019728792003956564819930 =
valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
valRep4
  (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38).[3 <-
    add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38 -
    (of_int 9223372036854775808)%W64] =
valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) -
57896044618658097711785492504343953926634992332820282019728792003956564819968.
proof.
    move => H H0 H1 H2. rewrite -H2 => />.
    move: H H0 H1 H2.
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    move: W64.to_uint_cmp. smt(@W64).
qed.

lemma limb4_minus_2_63_equiv r:
57896044618658097711785492504343953926634992332820282019728792003956564819968 <=
valRep4 r =>
valRep4 r < 2 * p =>
u64i (r.[3] - (of_int (pow 2 63))%W64) = u64i r.[3] - 9223372036854775808.
proof.
move: (limb4_geq_2_255_cmp r) W64.to_uint_cmp.
rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />. smt(@W64).
qed.

lemma limb4_minus_2_63_add38_equiv (r: Rep4):
57896044618658097711785492504343953926634992332820282019728792003956564819968 <=
valRep4 r =>
valRep4 r < 2 * p =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) =
u64i r.[3] - 9223372036854775808 =>
valRep4 r -
57896044618658097711785492504343953926634992332820282019728792003956564819930 =
valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
LEA_64
  (add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38 +
   add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38) `>>`
W8.one = add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38.
proof.
    move => H H0 H1 H2. rewrite helper_lemma_msb_is_not_set.
    do split. move: W64.to_uint_cmp. smt(). move => H3.
    + rewrite !addcE !/carry_add !b2i0 => />.
    + rewrite to_uintD. rewrite !H1.
    + move: H H0 H1 H2 H3. rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + move: W64.to_uint_cmp. smt(@W64). auto.
qed.

lemma limb4_minus_2_63_add38_equiv_2 (r: Rep4):
2 * p <= valRep4 r =>
valRep4 r <
115792089237316195423570985008687907853269984665640564039457584007913129639936 =>
u64i (r.[3] - (of_int 9223372036854775808)%W64) =
u64i r.[3] - 9223372036854775808 =>
valRep4 r -
57896044618658097711785492504343953926634992332820282019728792003956564819930 =
valRep4 (add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38) =>
LEA_64
  (add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38 +
   add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38) `>>`
W8.one =
add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38 -
(of_int 9223372036854775808)%W64.
proof.
    move => H H0 H1 H2. rewrite helper_lemma_remove_msb.
    + rewrite !addcE !/carry_add !b2i0 => />.
    + rewrite to_uintD. rewrite !H1.
    + move: H H0 H1 H2. rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + move: W64.to_uint_cmp. smt(@W64). auto.
qed.


lemma limb4_minus_2_63_equiv_2 r:
2 * p <= valRep4 r =>
valRep4 r <
115792089237316195423570985008687907853269984665640564039457584007913129639936 =>
u64i (r.[3] - (of_int (pow 2 63))%W64) = u64i r.[3] - 9223372036854775808.
proof.
move: (limb4_geq_2_255_cmp r) W64.to_uint_cmp.
rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />. smt(@W64).
qed.


(** Lossless lemmas **)
lemma ill_to_0_or_19: islossless ToBytesSpec.to_0_or_19 by proc; wp; skip => />.
lemma ill_remove_msb_if_set: islossless ToBytesSpec.remove_msb_if_set by proc; wp; skip => />.
lemma ill_extract_msb: islossless ToBytesSpec.extract_msb by proc; wp; skip => />.
lemma ill_to_19_or_38: islossless ToBytesSpec.to_19_or_38 by proc; wp; skip => />.
lemma ill_addition: islossless ToBytesSpec.addition by proc; wp; skip => />.
lemma ill_subtraction: islossless ToBytesSpec.subtraction by proc; wp; skip => />.
lemma ill_tobytes: islossless ToBytesSpec.to_bytes by proc; inline *; wp; skip => />.

(** Word to 19 or 0 by using invw **)
lemma h_to_19_by_invw:
  hoare [ToBytesSpec.to_0_or_19 :
  0 <= W64.to_uint t < pow 2 63 ==> res = W64.of_int 19].
proof. proc => />. auto => />. move => &h H H0. rewrite helper_lemma_to_19. smt(). auto. qed.

lemma ph_to_19_by_invw:
  phoare [ToBytesSpec.to_0_or_19 : 0 <= W64.to_uint t < pow 2 63 ==> res = W64.of_int 19] = 1%r.
proof. by conseq ill_to_0_or_19 (h_to_19_by_invw). qed.

lemma h_to_0_by_invw:
  hoare [ToBytesSpec.to_0_or_19 :
      pow 2 63  <= W64.to_uint t < pow 2 64 ==> res = W64.of_int 0].
proof. proc => />. auto => />. move => &h H H0. rewrite helper_lemma_to_0. smt(). auto. qed.

lemma ph_to_0_by_invw:
  phoare [ToBytesSpec.to_0_or_19 : pow 2 63  <= W64.to_uint t < pow 2 64 ==> res = W64.of_int 0] = 1%r.
proof. by conseq ill_to_0_or_19 (h_to_0_by_invw). qed.

(** Remove MSB if it is set **)
lemma h_msb_not_set (r: W64.t):
  hoare [ToBytesSpec.remove_msb_if_set : r = f3 /\ 0 <= W64.to_uint r < pow 2 63 ==> r = res].
proof. proc => />. wp; skip => />. move => *. rewrite helper_lemma_msb_is_not_set /#. qed.

lemma ph_msb_not_set (r: W64.t):
  phoare [ToBytesSpec.remove_msb_if_set : r = f3 /\ 0 <= W64.to_uint r < pow 2 63 ==> r = res] = 1%r.
proof. by conseq ill_remove_msb_if_set (h_msb_not_set r). qed.

lemma h_remove_msb (r: W64.t):
  hoare [ToBytesSpec.remove_msb_if_set :
      r = f3 /\ pow 2 63 <= W64.to_uint r < pow 2 64 ==> r = res - W64.of_int (pow 2 63)].
proof. proc => />. wp; skip => />. move => *. rewrite helper_lemma_remove_msb. auto => />. ring. qed.

lemma ph_remove_msb (r: W64.t):
  phoare [ToBytesSpec.remove_msb_if_set : r = f3 /\ pow 2 63 <= W64.to_uint r < pow 2 64 ==>
      r = res - W64.of_int (pow 2 63)] = 1%r.
proof. by conseq ill_remove_msb_if_set (h_remove_msb r). qed.

(** Extracts MSB **)
lemma h_extract_msb0:
  hoare [ToBytesSpec.extract_msb : 0 <= W64.to_uint f3 < pow 2 63 ==> res = W64.zerow].
proof. proc => />. wp; skip => /> &hr H H0. rewrite helper_lemma_extract_msb_0 /#. qed.

lemma ph_extract_msb0:
  phoare [ToBytesSpec.extract_msb : 0 <= W64.to_uint f3 < pow 2 63 ==> res = W64.zerow] = 1%r.
proof. by conseq ill_extract_msb (h_extract_msb0). qed.

lemma h_extract_msb1:
  hoare [ToBytesSpec.extract_msb : pow 2 63 <= W64.to_uint f3 < pow 2 64 ==> res = W64.onew].
proof. proc => />. wp; skip => /> &hr H H0. rewrite helper_lemma_extract_msb_1. smt(). auto. qed.

lemma ph_extract_msb1:
  phoare [ToBytesSpec.extract_msb : pow 2 63 <= W64.to_uint f3 < pow 2 64 ==> res = W64.onew] = 1%r.
proof. by conseq ill_extract_msb (h_extract_msb1). qed.

(** Sets word to 19 if word = 0 and 38 if word = 1 **)
lemma h_to_19:
  hoare [ToBytesSpec.to_19_or_38 : t = W64.zerow ==> res = W64.of_int 19].
proof. proc => />. wp; skip => /> &hr H H0. qed.

lemma ph_to_19:
  phoare [ToBytesSpec.to_19_or_38 : t = W64.zerow ==> res = W64.of_int 19] = 1%r.
proof. by conseq ill_to_19_or_38 (h_to_19). qed.

lemma h_to_38:
  hoare [ToBytesSpec.to_19_or_38 : t = W64.onew ==> res = W64.of_int 38 ].
proof. proc => />. wp; skip => /> &hr H H0. qed.

lemma ph_to_38:
  phoare [ToBytesSpec.to_19_or_38 : t = W64.onew ==> res = W64.of_int 38] = 1%r.
proof. by conseq ill_to_19_or_38 (h_to_38). qed.

(** Adding 19 or 38 to a Rep4 **)
lemma h_addition (r: Rep4, _tt1: W64.t, n : int):
  hoare [ToBytesSpec.addition :
      r = f /\ _tt1 = _tt /\ operand2 = W64.of_int n /\ 19 <= n <= 38 /\ W64.to_uint _tt1 < pow 2 64-n
      ==>
      res = add_to_limb r _tt1 n /\
      valRep4 (Array4.of_list witness [r.[0]; r.[1]; r.[2]; _tt1]) + n = valRep4 res
  ].
proof.
    proc. auto => />. move => &hr H H0 H1. do split.
    + apply Array4.ext_eq => i ib. rewrite !addcE. rewrite !get_setE 1..4:/#.
    + case(i = 3) => C. rewrite C => />.
    + case(i = 2) => C0. rewrite C0 => />.
    + case(i = 1) => C1. rewrite C1 => />.
    + case(i = 0) => C2. rewrite C2 => />. smt().
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !of_uintK (modz_small n (pow 2 64)) 1:/# => />.
    case((18446744073709551616 <= u64i r.[0] + n) = false) => C1. rewrite C1 !b2i0 => />.
    + rewrite pmod_small. move: C1 W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + have ->: (18446744073709551616 <= u64i r.[1] = false). move: W64.to_uint_cmp => />. smt().
    + have ->: (18446744073709551616 <= u64i r.[2] = false). move: W64.to_uint_cmp => />. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt(). ring.

    move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1.
    case(18446744073709551616 <= u64i r.[1] + 1 = false) => C2. rewrite !C2 !b2i0.
    + rewrite (pmod_small (u64i r.[1] + 1 %% 18446744073709551616) 18446744073709551616).
    + move :W64.to_uint_cmp. smt(). auto => />.
    + rewrite (pmod_small (u64i r.[2]) 18446744073709551616). move: C1 W64.to_uint_cmp. smt().
    + have ->: (u64i r.[0] + n) %% 18446744073709551616 = (u64i r.[0] + n) - 18446744073709551616.
    + move :W64.to_uint_cmp. smt(). move: W64.to_uint_cmp. smt().

    move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1.
    + rewrite (pmod_small 1 18446744073709551616). auto => />.
    + have ->: (u64i r.[1] + 1) %% 18446744073709551616 = (u64i r.[1] + 1) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt().
    + have ->: (u64i r.[0] + n) %% 18446744073709551616 = (u64i r.[0] + n) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt().

    case(18446744073709551616 <= u64i r.[2] + 1 = false) => C3. rewrite C3 b2i0 => />.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt(). ring.

    move: C3. rewrite not_false_to_true. move => C3. rewrite !C3 !b2i1 => />.

    + have ->: (u64i r.[2] + 1) %% 18446744073709551616 = (u64i r.[2] + 1) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt().
    + have E: 0 <= u64i _tt1 && u64i _tt1 < pow 2 64.
    + move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: E. smt().
    ring.
qed.

lemma ph_addition (r: Rep4, _tt1: W64.t, n : int):
  phoare [ToBytesSpec.addition :
      r = f /\ _tt1 = _tt /\ operand2 = W64.of_int n /\ 19 <= n <= 38  /\ W64.to_uint _tt1 < pow 2 64 - n
      ==>
      res = add_to_limb r _tt1 n /\
      valRep4 (Array4.of_list witness [r.[0]; r.[1]; r.[2]; _tt1]) + n = valRep4 res
  ] = 1%r.
proof. by conseq ill_addition (h_addition r _tt1 n). qed.

(** Substraction of 0, 19 or 38 to a Rep4 **)
lemma h_subtraction (r: Rep4, n: int):
  hoare [ToBytesSpec.subtraction :
      r = f /\ operand2 = W64.of_int n /\ 19 <= n <= 38 /\ n <= valRep4 r < W256.modulus
      ==>
      res = sub_from_limb r n /\ valRep4 r - n = valRep4 res
  ].
proof.
    proc. auto => />. move => &hr H H0 H1 H2.
    do split.
    + apply Array4.ext_eq => i ib. rewrite !subcE. rewrite !get_setE 1..4:/#.
    + case(i = 3) => C. rewrite C => />.
    + case(i = 2) => C0. rewrite C0 => />.
    + case(i = 1) => C1. rewrite C1 => />.
    + case(i = 0) => C2. rewrite C2 => />. smt().

    rewrite !subcE !/borrow_sub !b2i0 => />.
    rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !to_uintN !of_uintK (modz_small n (pow 2 64)) 1:/# => />.

    case ((u64i r.[0] < n) = false) => C1. rewrite !C1 !b2i0 => />.
    have ->: u64i r.[1] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    have ->: u64i r.[2] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    rewrite !b2i0 => />.
    + have ->: (u64i r.[0] + (-n) %% 18446744073709551616) %% 18446744073709551616 =
               (u64i r.[0] + (-n) %% 18446744073709551616) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt(). auto => />. rewrite !modNz 1,2:/#.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + ring.

    move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1 => />.
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    case ((u64i r.[1] < 1) = false) => C2. rewrite !C2 !b2i0  => />.
    + have ->: u64i r.[2] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    + rewrite !b2i0 => />.
    + have ->: (u64i r.[1] + 18446744073709551615) %% 18446744073709551616 =
               (u64i r.[1] + 18446744073709551615) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt(). auto => />.
    + rewrite !modNz 1,2:/#.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + ring.

    move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1 => />.
    + rewrite modNz 1,2:/#.
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    case ((u64i r.[2] < 1) = false) => C3. rewrite !C3 !b2i0  => />.
    + have ->: (u64i r.[2] + 18446744073709551615) %% 18446744073709551616 =
               (u64i r.[2] + 18446744073709551615) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt(). auto => />.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + ring.

    move: C3. rewrite not_false_to_true. move => C3. rewrite !C3 !b2i1 => />.
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    have E: ((u64i r.[3] < 1) = false).
    + move: (W64.to_uint_cmp r.[3])  (limb4_ltP_cmp r) H H0 H2 H1.
    + rewrite !valRep4E !pE !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + rewrite !mulzDr -!mulzA   (pmod_small 0 (pow 2 64)) 1:/# => />. smt().
    + have ->: (u64i r.[3] + 18446744073709551615) %% 18446744073709551616 =
               (u64i r.[3] + 18446744073709551615) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt(). auto => />.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt(). ring.
qed.

lemma h_subtraction0 (r: Rep4, n: int):
  hoare [ToBytesSpec.subtraction :
      r = f /\ operand2 = W64.of_int n /\ n = 0 /\ n <= valRep4 r < W256.modulus
      ==>
      res = sub_from_limb r n /\ valRep4 r - n = valRep4 res
  ].
proof.
    proc. auto => />. move => &hr H H0.
    do split.
    + apply Array4.ext_eq => i ib. rewrite !subcE. rewrite !get_setE 1..4:/#.
    + case(i = 3) => C. rewrite C => />.
    + case(i = 2) => C0. rewrite C0 => />.
    + case(i = 1) => C1. rewrite C1 => />.
    + case(i = 0) => C2. rewrite C2 => />. smt().

    rewrite !subcE !/borrow_sub !b2i0 => />.
    rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !to_uintN !of_uintK.
    have ->: u64i r.[0] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    have ->: u64i r.[1] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    have ->: u64i r.[2] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    rewrite !b2i0. auto => />.
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    ring.
qed.


lemma ph_subtraction (r: Rep4, n: int):
  phoare [ToBytesSpec.subtraction :
      r = f /\ operand2 = W64.of_int n /\ 19 <= n <= 38 /\ n <= valRep4 r < W256.modulus
      ==>
      res = sub_from_limb r n /\ valRep4 r - n = valRep4 res
  ] = 1%r.
proof. by conseq ill_subtraction (h_subtraction r n). qed.

lemma ph_subtraction0 (r: Rep4, n: int):
  phoare [ToBytesSpec.subtraction :
      r = f /\ operand2 = W64.of_int n /\ n = 0 /\ n <= valRep4 r < W256.modulus
      ==>
      res = sub_from_limb r n /\ valRep4 r - n = valRep4 res
  ] = 1%r.
proof. by conseq ill_subtraction (h_subtraction0 r n). qed.


(** To Bytes **)
lemma h_to_bytes_no_reduction (r: Rep4):
  hoare [ToBytesSpec.to_bytes :
      r = f /\ 0 <= valRep4 r < p
      ==>
      valRep4 res = asint (inzpRep4 r)
  ].
proof.
    proc.
    seq 9: (#pre /\ valRep4 ff3 = valRep4 r).
    seq 1 : (#pre /\ msb1 = W64.zerow). call h_extract_msb0. auto => />.
    + move: (limb4_ltP_cmp r). smt(limb4_ltP_cmp).
    seq 1 : (#pre /\ _tt = f.[3]). call (h_msb_not_set (r.[3])). auto => />.
    + move: (limb4_ltP_cmp r). smt().
    seq 1 : (#pre /\ _tt0 = W64.of_int 19). call h_to_19. auto => />.
    seq 1 : (#pre /\ valRep4 r + 19 = valRep4 ff
                  /\ (add_to_limb r _tt 19) = ff). call (h_addition r r.[3] 19). auto => />.
    + apply limb4_add_equiv_ltP.
    seq 1 : (#pre /\ _f3 = ff.[3]). call (h_msb_not_set (add_to_limb r r.[3] 19).[3]). auto => />.
    + apply limb4_add19_range_l4_ltP. sp.
    seq 1 : (#pre /\ _tt2 = W64.of_int 19). auto => />. call h_to_19_by_invw.
    + auto => />. apply limb4_add19_range_l4_ltP.
    call (h_subtraction (add_to_limb r r.[3] 19) 19). auto => />.
    move => &hr [#] H H0. do split.
    + apply Array4.ext_eq => i ib. rewrite !get_setE 1:/#.
    + case(i = 3) => C. rewrite C => />.
    + case(i = 2) => C0. rewrite C0 => />.
    + case(i = 1) => C1. rewrite C1 => />.
    + case(i = 0) => C2. rewrite C2 => />. smt().
    + rewrite -H0. move: valRep4_cmp. smt(). move => H2.
    + rewrite -H0. move: valRep4_cmp. smt(). move => H3 H4 H5 H6. smt().
    auto => />. smt(cminusP0).
qed.

(** To Bytes **)
lemma h_to_bytes_cminusP_part1 (r: Rep4):
  hoare [ToBytesSpec.to_bytes :
      r = f /\ p <= valRep4 r < pow 2 255
      ==>
      valRep4 res = asint (inzpRep4 r)
      (* valRep4 r - p = valRep4 res *)
  ].
proof.
    proc.
    seq 9: (#pre /\ valRep4 ff3 = valRep4 r - p).
    seq 1 : (#pre /\ msb1 = W64.zerow). call h_extract_msb0. auto => />.
    + move: (limb4_lt_2_255_cmp r) pVal. smt().
    seq 1 : (#pre /\ _tt = f.[3]). call (h_msb_not_set (r.[3])). auto => />.
    + move: (limb4_lt_2_255_cmp r) pVal. smt().
    seq 1 : (#pre /\ _tt0 = W64.of_int 19). call h_to_19. auto => />.
    seq 1 : (#pre /\ valRep4 r + 19 = valRep4 ff
                  /\ (add_to_limb r _tt 19) = ff). call (h_addition r r.[3] 19). auto => />.
    + apply limb4_add_equiv_geqP_lt_2p. swap 2 1.
    seq 1 : (#pre /\ _f3 = ff.[3] - W64.of_int (pow 2 63)). inline 1. auto => />.
    + move => H H0 H1. rewrite helper_lemma_remove_msb.
    + move: limb4_add_range_geqP_lt_2_255. smt(). auto.
    seq 1 : (#pre /\ _tt2 = W64.of_int 0). call h_to_0_by_invw. auto => />.
    + apply limb4_add_range_geqP_lt_2_255.
    seq 1 : (#pre /\ valRep4 ff2 = valRep4 ff - (pow 2 255) /\ ff2 = ff.[3 <- _f3]).
    auto => />. apply limb4_set_f3_geq_2_255_lt_2p.
    call (h_subtraction0 (add_to_limb r r.[3] 19).[3 <-
            (add_to_limb r r.[3] 19).[3] - (of_int (pow 2 63))%W64] 0). auto => />.
    move => [#] H H0 H1 H2. do split.
    + move: valRep4_cmp. smt(). move => H3.
    + move: valRep4_cmp. smt(). move => H4 H5 H6.
    + rewrite -H6. move : H H0 H1 H2 H4 H5 H6.
    + rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + move: W64.to_uint_cmp. rewrite !addcE !/carry_add !b2i0 => />. smt().
    auto => />. smt(pVal cminusP1).
qed.


lemma h_to_bytes_cminusP_part2 (r: Rep4):
  hoare [ToBytesSpec.to_bytes :
      r = f /\ pow 2 255 <= valRep4 r < 2*p
      ==>
      valRep4 res = asint (inzpRep4 r)
      (* valRep4 r - p = valRep4 res *)
  ].
proof.
    proc.
    seq 9: (#pre /\ valRep4 ff3 = valRep4 r - p).
    seq 1 : (#pre /\ msb1 = W64.onew). call h_extract_msb1. auto => />.
    + move => H H0. move: (limb4_geq_2_255_cmp r) pVal. smt().
    seq 1 : (#pre /\ _tt = f.[3] - W64.of_int (pow 2 63)
                  /\ W64.to_uint _tt = W64.to_uint f.[3] - (pow 2 63)).
    + inline 1. auto => />. move => H H0. rewrite helper_lemma_remove_msb.
    + move: limb4_geq_2_255_cmp W64.to_uint_cmp H H0 pVal. smt(). do split.
    + move: H H0. apply limb4_minus_2_63_equiv.
    seq 1 : (#pre /\ _tt0 = W64.of_int 38). call h_to_38. auto => />.
    seq 1 : (#pre /\ valRep4 r - pow 2 255 + 38 = valRep4 ff /\ (add_to_limb r _tt 38) = ff).
    + call (h_addition r (r.[3] - W64.of_int (pow 2 63)) 38). auto => />.
    + apply limb4_add_sub_equiv_geqP_lt_2p. swap 3 -1.
    seq 1 : (#pre /\ _f3 = ff.[3]). inline 1. auto => />.
    + apply limb4_minus_2_63_add38_equiv.
    seq 1 : (#pre /\ _tt2 = W64.of_int 19). call h_to_19_by_invw. auto => />.
    + apply limb4_add_range_geq_2_255_lt_2p.
    seq 1 : (#pre /\ valRep4 ff2 = valRep4 ff /\ ff2 = ff.[3 <- _f3]). auto => />.
    + apply limb4_set_f3_gtP_lt_2p.
    call (h_subtraction ((add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38).[3 <-
            add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38]) 19). auto => />.
    move => [#] H H0 H1 H2 H3. do split.
    + move: valRep4_cmp. smt(). move => H4.
    + move: valRep4_cmp. smt(). move => H4 H5 H6.
    + rewrite -H6. move : H H0 H1 H2 H4 H5 H6.
    + rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + move: W64.to_uint_cmp. rewrite !addcE !/carry_add !b2i0 => />. smt().
    + auto => />. smt(pVal cminusP1).
qed.

lemma h_to_bytes_cminus2P (r: Rep4):
  hoare [ToBytesSpec.to_bytes :
      r = f /\ 2*p <= valRep4 r < W256.modulus
      ==>
      valRep4 res = asint (inzpRep4 r)
      (* valRep4 r - p - p = valRep4 res *)
  ].
proof.
    proc.
    seq 9: (#pre /\ valRep4 ff3 = valRep4 r - p - p).
    seq 1 : (#pre /\ msb1 = W64.onew). call h_extract_msb1. auto => />.
    + move => H H0. move: (limb4_geq_2_255_cmp r) pVal. smt().
    seq 1 : (#pre /\ _tt = f.[3] - W64.of_int (pow 2 63)
                  /\ W64.to_uint _tt = W64.to_uint f.[3] - (pow 2 63)).
    + inline 1. auto => />. move => H H0. rewrite helper_lemma_remove_msb.
    + move: limb4_geq_2_255_cmp W64.to_uint_cmp H H0 pVal. smt(). do split.
    + move: H H0. apply limb4_minus_2_63_equiv_2.
    seq 1 : (#pre /\ _tt0 = W64.of_int 38). call h_to_38. auto => />.
    seq 1 : (#pre /\ valRep4 r - pow 2 255 + 38 = valRep4 ff /\ (add_to_limb r _tt 38) = ff).
    + call (h_addition r (r.[3] - W64.of_int (pow 2 63)) 38). auto => />.
    + apply limb4_add_sub_equiv_geq2P.
    seq 1 : (#pre /\ _f3 = ff.[3] - W64.of_int (pow 2 63)). inline 1. auto => />.
    + apply limb4_minus_2_63_add38_equiv_2. swap 1 1.
    seq 1 : (#pre /\ _tt2 = W64.of_int 0). call h_to_0_by_invw. auto => />.
    + apply limb4_add_range_geq2P.
    seq 1 : (#pre /\ valRep4 ff2 = valRep4 ff - (pow 2 255) /\ ff2 = ff.[3 <- _f3]). auto => />.
    + apply limb4_set_f3_gt2P.
    call (h_subtraction0 ((add_to_limb r (r.[3] - (of_int 9223372036854775808)%W64) 38).[3 <-
        add_l4 r (r.[3] - (of_int 9223372036854775808)%W64) 38
            - (of_int 9223372036854775808)%W64]) 0). auto => />.
    move => &hr [#] H H0 H1 H2. do split.
    + move: valRep4_cmp. smt(). move => H3.
    + move: valRep4_cmp. smt(). move => H4 H5 H6.
    + rewrite -H6 H2 -H1 !pVal. smt().
    auto => />. move => &hr. move => H H1 H2. rewrite H2 cminusP2. move: H valRep4_cmp. smt().
    by rewrite inzpRep4E.
qed.


lemma equiv_to_bytes:
    equiv[M.__tobytes4 ~ ToBytesSpec.to_bytes :
      f{1} = f{2}
      ==>
      valRep4 res{1} = valRep4 res{2}
    ].
proof.
    proc => />.
    swap {2} 2 -1. swap{1} 9 -7. swap {1} 24 -1.
    inline {2} 1.
    seq 2 4 : (#pre /\ _tt{2} = t{1}
                    /\ _tt{2} = (f.[3]{2} + f.[3]{2}) `>>` W8.one). auto => />.
    inline {2} 1.
    seq  7 9 : (_tt{2} = t{1} /\
                _tt{2} = (f.[3]{2} + f.[3]{2}) `>>` W8.one /\
                f.[0]{1} = f.[0]{2} /\
                f.[1]{1} = f.[1]{2} /\
                f.[2]{1} = f.[2]{2} /\
                msb1{2} = f.[3]{1} /\
                msb1{2} = (SAR_64 f{2}.[3] ((of_int 63))%W8).`6). auto => />.
    inline {2} 1.
    seq  2 4 : (_tt{2} = t{1} /\
                _tt{2} = (f.[3]{2} + f.[3]{2}) `>>` W8.one /\
                f.[0]{1} = f.[0]{2} /\
                f.[1]{1} = f.[1]{2} /\
                f.[2]{1} = f.[2]{2} /\
                msb1{2} = (SAR_64 f{2}.[3] ((of_int 63))%W8).`6 /\
                _tt0{2} = f.[3]{1} /\
                _tt0{2} = msb1{2} `&` W64.of_int 19 + W64.of_int 19). auto => />.
    inline {2} 1.
    seq  10 15 : (tt0{2} = t{1} /\
                  _tt{2} = (f.[3]{2} + f.[3]{2}) `>>` W8.one /\
                  msb1{2} = (SAR_64 f{2}.[3] ((of_int 63))%W8).`6 /\
                  _tt0{2} = f.[3]{1} /\
                  _tt0{2} = msb1{2} `&` W64.of_int 19 + W64.of_int 19 /\
                  f0{2} = f{2} /\
                  ff0{2}.[0] = add_l1 f0{2} (W64.to_uint _tt0{2}) /\
                  ff0{2}.[1] = add_l2 f0{2} (W64.to_uint _tt0{2}) /\
                  ff0{2}.[2] = add_l3 f0{2} (W64.to_uint _tt0{2}) /\
                  ff0{2}.[3] = add_l4 f0{2} _tt{2} (W64.to_uint _tt0{2}) /\
                  f.[0]{1} = ff0.[0]{2} /\
                  f.[1]{1} = ff0.[1]{2} /\
                  f.[2]{1} = ff0.[2]{2} /\
                  ff{2} = ff0{2} /\
                  ff{2}.[3] = t{1}). auto => />.
    move => &1 &2 [#] H H0 H1 H2. do split. rewrite H H0 H1 //=. rewrite H //=.
    rewrite H H0 //=. rewrite H H0 H1 H2 //=. rewrite H H0 H1 //=.

    inline {2} 1.
    seq  2 5 : ( _tt{2} = (f.[3]{2} + f.[3]{2}) `>>` W8.one /\
                 msb1{2} = (SAR_64 f{2}.[3] ((of_int 63))%W8).`6 /\
                 _tt0{2} = msb1{2} `&` W64.of_int 19 + W64.of_int 19 /\
                 f0{2} = f{2} /\
                 ff0{2}.[0] = add_l1 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[1] = add_l2 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[2] = add_l3 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[3] = add_l4 f0{2} _tt{2} (W64.to_uint _tt0{2}) /\
                 f.[0]{1} = ff0.[0]{2} /\
                 f.[1]{1} = ff0.[1]{2} /\
                 f.[2]{1} = ff0.[2]{2} /\
                 f.[3]{1} = _f3{2} /\
                 _f3{2} = (ff.[3]{2} + ff.[3]{2}) `>>` W8.one /\
                 ff2{2} = ff{2}.[3 <- _f3{2}] /\
                 ff2{2}.[3] = f{1}.[3] /\
                 ff{2} = ff0{2} /\
                 ff{2}.[3] = t{1}). auto => />.

    inline {2} 1.
    seq 3 5 : (  _tt{2} = (f.[3]{2} + f.[3]{2}) `>>` W8.one /\
                 msb1{2} = (SAR_64 f{2}.[3] ((of_int 63))%W8).`6 /\
                 _tt0{2} = msb1{2} `&` W64.of_int 19 + W64.of_int 19 /\
                 f0{2} = f{2} /\
                 ff0{2}.[0] = add_l1 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[1] = add_l2 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[2] = add_l3 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[3] = add_l4 f0{2} _tt{2} (W64.to_uint _tt0{2}) /\
                 f.[0]{1} = ff0.[0]{2} /\
                 f.[1]{1} = ff0.[1]{2} /\
                 f.[2]{1} = ff0.[2]{2} /\
                 f.[3]{1} = _f3{2} /\
                 ff{2} = ff0{2} /\
                 _f3{2} = (ff.[3]{2} + ff.[3]{2}) `>>` W8.one /\
                 ff2{2} = ff{2}.[3 <- _f3{2}] /\
                 ff2{2}.[3] = f{1}.[3] /\
                 _tt2{2} = t{1}
                 ). auto => />.

    inline {2} 1.
    seq 12 14: (
                 _tt{2} = (f.[3]{2} + f.[3]{2}) `>>` W8.one /\
                 msb1{2} = (SAR_64 f{2}.[3] ((of_int 63))%W8).`6 /\
                 _tt0{2} = msb1{2} `&` W64.of_int 19 + W64.of_int 19 /\
                 f0{2} = f{2} /\
                 ff0{2}.[0] = add_l1 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[1] = add_l2 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[2] = add_l3 f0{2} (W64.to_uint _tt0{2}) /\
                 ff0{2}.[3] = add_l4 f0{2} _tt{2} (W64.to_uint _tt0{2}) /\
                 ff1{2}.[0] = sub_l1 f1{2} (W64.to_uint _tt2{2}) /\
                 ff1{2}.[1] = sub_l2 f1{2} (W64.to_uint _tt2{2}) /\
                 ff1{2}.[2] = sub_l3 f1{2} (W64.to_uint _tt2{2}) /\
                 ff1{2}.[3] = sub_l4 f1{2} (W64.to_uint _tt2{2}) /\
                 f1{2} = ff2{2} /\
                 operand20{2} = _tt2{2} /\
                 _tt2{2} = t{1} /\
                 f.[0]{1} = ff1.[0]{2} /\
                 f.[0]{1} = ff1.[0]{2} /\
                 f.[1]{1} = ff1.[1]{2} /\
                 f.[2]{1} = ff1.[2]{2} /\
                 f.[3]{1} = ff1.[3]{2} /\
                 ff{2} = ff0{2} /\
                 _f3{2} = (ff.[3]{2} + ff.[3]{2}) `>>` W8.one /\
                 ff2{2} = ff{2}.[3 <- _f3{2}]). auto => />.
    + move => &1 &2 H H0 H1 H2 H3 H4 H5 H6. do split.
    rewrite -H3 //=. rewrite -H3 //=. rewrite -H3 //=.
    rewrite -H4 //=. rewrite -H3 -H4 -H5 //=. rewrite -H3 -H4 -H5 //=.
    seq 0 1: (#pre /\ ff3{2} = ff1{2}). auto => />.
    auto => />.
    move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
    rewrite valRep4_equiv_representation.  rewrite H7 H8 H9 H10.
    by rewrite -valRep4_equiv_representation.
qed.

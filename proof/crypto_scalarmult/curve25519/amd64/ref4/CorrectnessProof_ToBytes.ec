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

 proc sar_inv_t (t: W64.t) : W64.t = {
    var _of_, _cf_, _sf_, _2, _zf_ : bool;
    var tt, tt0, tt1 : W64.t;

    (_of_, _cf_, _sf_, _2, _zf_, tt) <- SAR_64 t ((of_int 63))%W8;
    tt0 <- invw tt;
    tt1 <- tt0 `&` (of_int 19)%W64;
    return tt1;
 }

 proc to19(t: W64.t) : W64.t = {

    t <- t `&` (of_int 19)%W64;
    t <- t + (of_int 19)%W64;

    return t;
 }

 proc addition(f: Rep4, operand2: W64.t) : Rep4 = {
  var aux_4, tt, tt0 : W64.t;
  var _of_, _cf_, _sf_, _zf_, cf, _0, _1, _2, aux_3 : bool;
  var ff : Rep4; (* we don't change the value of f, easier proofs *)
  tt <- f.[3];

  (aux_3, aux_4) <- addc f.[0] operand2 false;
  cf <- aux_3;
  ff <- ff.[0 <- aux_4];
  (aux_3, aux_4) <- addc f.[1] W64.zero cf;
  cf <- aux_3;
  ff <- ff.[1 <- aux_4];
  (aux_3, aux_4) <- addc f.[2] W64.zero cf;
  cf <- aux_3;
  ff <- ff.[2 <- aux_4];
  (_1, tt0) <- addc tt W64.zero cf;
  ff <- ff.[3 <- tt0];

  return ff;
 }

 proc subtraction(f: Rep4, operand2: W64.t) : Rep4 = {
  var aux_4 : W64.t;
  var _of_, _cf_, _sf_, _zf_, cf, _0, _1, _2, _3, aux_3 : bool;
  var ff : Rep4; (* we don't change the value of f, easier proofs *)


  (aux_3, aux_4) <- subc f.[0] operand2 false;
  cf <- aux_3;
  ff <- ff.[0 <- aux_4];
  (aux_3, aux_4) <- subc f.[1] W64.zero cf;
  cf <- aux_3;
  ff <- ff.[1 <- aux_4];
  (aux_3, aux_4) <- subc f.[2] W64.zero cf;
  cf <- aux_3;
  ff <- ff.[2 <- aux_4];
  (aux_3, aux_4) <- subc f.[3] W64.zero cf;
  _3 <- aux_3;
  ff <- ff.[3 <- aux_4];

  return ff;
 }

 (* We show that for 0 <= valrep4 f < 2^255, the first three calls essentially do nothing *)
 proc addition_calls(f: Rep4) : Rep4 = {
   var tt, tt0, extracted_msbw : W64.t;
   var ff : Rep4; (* we don't change the value of f, easier proofs *)
   ff <- witness;
   extracted_msbw <@ extract_msb (f.[3]);
   tt  <@ remove_msb_if_set (f.[3]);
   tt0 <@ to19 (extracted_msbw);
   ff <@ addition(f, tt0);
   return ff;
 }

 proc tobytes_no_reduction(f: Rep4) : Rep4 = {
     var tt, tt0, f3, extracted_msbw : W64.t;
     var ff, ff2: Rep4; (* we don't change the value of f, easier proofs *)

     ff <@ addition_calls(f);              (* ff = f + 19 *)
     f3 <@ sar_inv_t(ff.[3]);              (* f3 = 19 *)
     ff2  <@ subtraction(ff, f3);          (* ff2 = ff - 19 = f + 19 - 19 = f *)
     return ff2;
 }


}.

(* Helper lemmas *)
lemma cminusP0 r: 0 <= r < p => r = asint (inzp r).
proof. move => H. rewrite inzpK pE => />. rewrite modz_small. apply bound_abs. smt(pVal). auto. qed.

lemma cminusP1 r: p <= r < 2*p => r - p = asint (inzp r).
proof. rewrite inzpK => />. move => [#] H H0. smt(pE pVal). qed.

lemma cminusP2 r: 2*p <= r < W256.modulus => r - p - p = asint (inzp r).
proof. rewrite inzpK => />. move => [#] H H0. smt(pE pVal). qed.

lemma upper_limb4_lt_2_255_range r: 0 <= valRep4 r < pow 2 255 => 0 <= (to_uint r.[3]) < pow 2 63.
proof. rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />. smt(W64.to_uint_cmp). qed.

lemma upper_limb4_ltP_range r: 0 <= valRep4 r < p => 0 <= (to_uint r.[3]) < pow 2 63.
proof. rewrite valRep4E pE /to_list /val_digits /mkseq -iotaredE => />. smt(W64.to_uint_cmp). qed.

lemma upper_limb4_ltP_msb r: 0 <= valRep4 r < p => r.[3].[63] = false.
proof. move => H. have E: b2i r.[3].[63] = 0.
       rewrite b2i_get //=. move: upper_limb4_ltP_range W64.to_uint_cmp; 1:smt(). smt(). qed.

lemma upper_limb4_ltP_msbw r: 0 <=  W64.to_uint r < pow 2 63 => r.[63] = false.
proof. move => H. have E: b2i r.[63] = 0.
       rewrite b2i_get //=. move: H. smt(). smt(). qed.

lemma upper_limb4_geq_2_255_range r: pow 2 255 <= valRep4 r < W256.modulus =>
           pow 2 63 <= (to_uint r.[3]) < W64.modulus.
proof. rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />.
       move => H H0. do split. move: W64.to_uint_cmp. smt(). move: W64.to_uint_cmp. smt(). qed.

lemma upper_limb4_p_2_255_range r: p <= valRep4 r < pow 2 255 =>
           pow 2 63 - 1 <= (to_uint r.[3]) < W64.modulus.
proof. rewrite valRep4E pE /to_list /val_digits /mkseq -iotaredE => />.
       move => H H0. do split. move: W64.to_uint_cmp. smt(). move: W64.to_uint_cmp. smt(). qed.

lemma upper_limb4_geqP_range r: p <= valRep4 r < W256.modulus =>
           (pow 2 63) - 1 <= (to_uint r.[3]) < W64.modulus.
proof. rewrite valRep4E pE /to_list /val_digits /mkseq -iotaredE => />.
       move => H H0. do split. move: W64.to_uint_cmp. smt(). move: W64.to_uint_cmp. smt(). qed.

lemma upper_limb4_geq_2_255_msb r: pow 2 255 <= valRep4 r < W256.modulus => r.[3].[63] = true.
proof. move => H. have E: b2i r.[3].[63] = 1.
       rewrite b2i_get //=. move: H upper_limb4_geq_2_255_range W64.to_uint_cmp; 1:smt(). smt(). qed.

lemma upper_limb4_geqP_msbw r: pow 2 63  <=  W64.to_uint r < W64.modulus => r.[63] = true.
proof. move => H. have E: b2i r.[63] = 1.
       rewrite b2i_get //=. move: H upper_limb4_geq_2_255_range W64.to_uint_cmp; 1:smt(). smt(). qed.

lemma helper_remove_msb_if_set (f: W64.t):
    0 <= W64.to_uint f < pow 2 63 => LEA_64 (f + f) `>>` W8.one = f.
proof.
    auto => />. rewrite /LEA_64 => *.
    have E: W64.to_uint (f + f `>>` W8.of_int 1) = W64.to_uint f.
    rewrite to_uint_shr //= !to_uintD !modz_small /absz //=.
    smt(). smt(). smt(@W64).
qed.

lemma helper_sar_inv_t (t: W64.t) : 0 <= u64i t && u64i t < pow 2 63 => invw (SAR_64 t ((of_int 63))%W8).`6 `&` (of_int 19)%W64 = (of_int 19)%W64.
proof.
    auto => />. move => H H0.
    have ->: (SAR_64 t ((of_int 63))%W8).`6 = W64.zerow.
    + rewrite /SAR_64 /shift_mask /rflags_OF //= sarE /min => />.
    rewrite init_bits2w bits2wE -iotaredE /min //=.
    rewrite upper_limb4_ltP_msbw //=.
    + rewrite /W64.zerow /W64.zero bits2wE /int2bs /mkseq -iotaredE => />.
    have ->: invw W64.zerow = W64.onew.
    + rewrite /invw mapE /W64.zerow /W64.zero bits2wE /int2bs /mkseq -iotaredE => />.
    + rewrite /W64.onew of_intE bits2wE /int2bs /mkseq -iotaredE => />.
    + rewrite wordP => i ib. rewrite !initiE 1,2:/# //= initiE 1:/# //= 1:/#.
    rewrite wordP => i ib.
    rewrite /W64.onew !of_intE !bits2wE !/int2bs !/mkseq -!iotaredE => />.
    rewrite !initiE 1,2:/# //= /#.
qed.

lemma not_false_to_true bst: (bst <> false) = (bst = true) by smt().


(** Lossless lemmas **)

lemma ill_sar_inv_t: islossless ToBytesSpec.sar_inv_t by proc; wp; skip => />.
lemma ill_remove_msb_if_set_lt_2_255: islossless ToBytesSpec.remove_msb_if_set by proc; wp; skip => />.
lemma ill_extract_msb_lt_2_255: islossless ToBytesSpec.extract_msb by proc; wp; skip => />.
lemma ill_to19: islossless ToBytesSpec.to19 by proc; wp; skip => />.
lemma ill_addition: islossless ToBytesSpec.addition by proc; wp; skip => />.
lemma ill_subtraction: islossless ToBytesSpec.subtraction by proc; wp; skip => />.

(** Case: 0 <= valRep4 f < p (some lemmas can be till < 2 255) **)

(** SAR+INV+AND **)
lemma h_sar_inv_t:
  hoare [ToBytesSpec.sar_inv_t :
      0 <= W64.to_uint t < pow 2 63
      ==>
      res = W64.of_int 19].
    proc => />. auto => />.
    move => &h H H0. rewrite helper_sar_inv_t. smt(). auto.
qed.

lemma ph_sar_inv_t:
  phoare [ToBytesSpec.sar_inv_t :
      0 <= W64.to_uint t < pow 2 63
      ==>
      res = W64.of_int 19] = 1%r.
proof.
    by conseq ill_sar_inv_t (h_sar_inv_t).
qed.

(** Remove MSB if it is set **)
lemma h_remove_msb_if_set_lt_2_255 (r: W64.t):
  hoare [ToBytesSpec.remove_msb_if_set :
      r = f3 /\ 0 <= W64.to_uint r < pow 2 63
      ==>
      r = res
  ].
    proc => />. wp; skip => />. move => *.
    rewrite helper_remove_msb_if_set /#.
qed.

lemma ph_remove_msb_if_set_lt_2_255 (r: W64.t):
  phoare [ToBytesSpec.remove_msb_if_set :
      r = f3 /\ 0 <= W64.to_uint r < pow 2 63
      ==>
      r = res] = 1%r.
proof.
    by conseq ill_remove_msb_if_set_lt_2_255 (h_remove_msb_if_set_lt_2_255 r).
qed.

(** Extracts MSB **)
lemma h_extract_msb_lt_2_255:
  hoare [ToBytesSpec.extract_msb :
      0 <= W64.to_uint f3 < pow 2 63
      ==>
      res = W64.zerow
  ].
    proc => />. wp; skip => /> &hr H H0.
    rewrite /SAR_64 /shift_mask /rflags_OF //= sarE.
    rewrite init_bits2w bits2wE -iotaredE /min //=.
    rewrite upper_limb4_ltP_msbw //=.
    + rewrite /W64.zerow /W64.zero bits2wE /int2bs /mkseq -iotaredE => />.
qed.

lemma ph_extract_msb_lt_2_255:
  phoare [ToBytesSpec.extract_msb :
      0 <= W64.to_uint f3 < pow 2 63
      ==>
      res = W64.zerow] = 1%r.
proof.
    by conseq ill_extract_msb_lt_2_255 (h_extract_msb_lt_2_255).
qed.

(** Sets word to 19 if word = 0 **)
lemma h_to19:
  hoare [ToBytesSpec.to19 :
      t = W64.zerow
      ==>
      res = W64.of_int 19
  ].
    proc => />. wp; skip => /> &hr H H0.
qed.


lemma ph_to19:
  phoare [ToBytesSpec.to19 :
      t = W64.zerow
      ==>
      res = W64.of_int 19] = 1%r.
proof.
    by conseq ill_to19 (h_to19).
qed.

(** Adding 19 to a Rep4 **)

abbrev add19_l1 (r: Rep4) = (addc r.[0] ((of_int 19))%W64 false).`2.
abbrev add19_l2 (r: Rep4) = (addc r.[1] W64.zero (addc_carry r.[0] ((of_int 19))%W64 false)).`2.
abbrev add19_l3 (r: Rep4) = (addc r.[2] W64.zero (addc_carry r.[1] W64.zero (addc_carry r.[0] ((of_int 19))%W64 false))).`2.
abbrev add19_l4 (r: Rep4) = (addc r.[3] W64.zero (addc_carry r.[2] W64.zero (addc_carry r.[1] W64.zero (addc_carry r.[0] ((of_int 19))%W64 false)))).`2.

abbrev add19 (r: Rep4) = Array4.of_list witness [add19_l1 r; add19_l2 r ; add19_l3 r ; add19_l4 r].

lemma h_addition19 (r: Rep4):
  hoare [ToBytesSpec.addition :
      r = f /\ operand2 = W64.of_int 19 /\  0 <= valRep4 r < p
      ==>
      res = add19 r /\ valRep4 r + 19 = valRep4 res
  ].
proof.
    proc. auto => />. move => &hr H H0. do split.
    + apply Array4.ext_eq => i ib. rewrite !addcE. rewrite !get_setE 1..4:/#.
    + case(i = 3) => C. rewrite C => />.
    + case(i = 2) => C0. rewrite C0 => />.
    + case(i = 1) => C1. rewrite C1 => />.
    + case(i = 0) => C2. rewrite C2 => />. smt().
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !of_uintK (modz_small 19 (pow 2 64)) 1:/# => />.
    case((18446744073709551616 <= u64i r.[0] + 19) = false) => C1. rewrite C1 !b2i0 => />.
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
    + have ->: (u64i r.[0] + 19) %% 18446744073709551616 = (u64i r.[0] + 19) - 18446744073709551616.
    + move :W64.to_uint_cmp. smt(). move: W64.to_uint_cmp. smt().

    move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1.
    + rewrite (pmod_small 1 18446744073709551616). auto => />.
    + have ->: (u64i r.[1] + 1) %% 18446744073709551616 = (u64i r.[1] + 1) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt().
    + have ->: (u64i r.[0] + 19) %% 18446744073709551616 = (u64i r.[0] + 19) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt().

    case(18446744073709551616 <= u64i r.[2] + 1 = false) => C3. rewrite C3 b2i0 => />.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt(). ring.

    move: C3. rewrite not_false_to_true. move => C3. rewrite !C3 !b2i1 => />.
    + have ->: (u64i r.[2] + 1) %% 18446744073709551616 = (u64i r.[2] + 1) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt().
    + have E: 0 <= u64i r.[3] && u64i r.[3] < pow 2 63.
    + apply upper_limb4_ltP_range. smt().
    + rewrite pmod_small. move: E. smt().
    ring.
qed.

lemma ph_addition19 (r: Rep4):
  phoare [ToBytesSpec.addition :
      r = f /\ operand2 = W64.of_int 19 /\  0 <= valRep4 r < p
      ==>
      res = add19 r /\ valRep4 r + 19 = valRep4 res
  ] = 1%r.
proof.
    by conseq ill_addition (h_addition19 r).
qed.

lemma h_addition19_calls (r: Rep4):
  equiv [ToBytesSpec.addition_calls ~ ToBytesSpec.addition :
      0 <= valRep4 f{1} < p /\ ={f} /\ operand2{2} = W64.of_int 19
      ==>
       valRep4 res{1} = valRep4 res{2}
  ].
proof.
    proc *. auto => />. inline {1} 1.
    seq 3 0 : (#pre /\ f0{1} = f{2} /\ ff{1} = witness /\ extracted_msbw{1} = W64.zerow).
    + ecall {1} (ph_extract_msb_lt_2_255). auto => />.
    + move => &2 H H0.
    + move: upper_limb4_ltP_range r. smt().
    seq 1 0 : (#pre /\ tt{1} = f0{1}.[3]).
    + ecall {1} (ph_remove_msb_if_set_lt_2_255 (f0{1}.[3])).
    + auto => />. move => &1 &2 [#] H. do split.
    + move: (upper_limb4_ltP_range (f{1})) (W64.to_uint_cmp f{1}.[3]). auto => />.
    + move: (upper_limb4_ltP_range (f{1})) (W64.to_uint_cmp f{1}.[3]). auto => />. smt().
    seq 1 0 : (#pre /\ tt0{1} = W64.of_int 19).
    + ecall {1} (ph_to19). auto => />. wp.
    ecall {1} (ph_addition19 (f0{1})).
    ecall {2} (ph_addition19 (f{2})).
    auto => />.
qed.

(** Substraction **)
lemma h_subtraction19 (r: Rep4):
  hoare [ToBytesSpec.subtraction :
      r = f /\ operand2 = W64.of_int 19 /\ 19 <= valRep4 r < W256.modulus
      ==>
      valRep4 r - 19 = valRep4 res
  ].
proof.
    proc. auto => />. move => &hr H H0.
    rewrite !subcE !/borrow_sub !b2i0 => />.
    rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !to_uintN (modz_small 19 (pow 2 64)) 1:/# => />.

    case ((u64i r.[0] < 19) = false) => C1. rewrite !C1 !b2i0 !to_uint0 => />.
    have ->: u64i r.[1] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    have ->: u64i r.[2] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    rewrite !b2i0 => />.
    + have ->: (u64i r.[0] + 18446744073709551597) %% 18446744073709551616 =
               (u64i r.[0] + 18446744073709551597) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt(). auto => />.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + ring.

    move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1 !to_uint1 => />.
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    case ((u64i r.[1] < 1) = false) => C2. rewrite !C2 !b2i0 !to_uint0 => />.
    + have ->: u64i r.[2] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    + rewrite !b2i0 => />.
    + have ->: (u64i r.[1] + 18446744073709551615) %% 18446744073709551616 =
               (u64i r.[1] + 18446744073709551615) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt(). auto => />.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + ring.

    move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1 !to_uint1 => />.
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    case ((u64i r.[2] < 1) = false) => C3. rewrite !C3 !b2i0 !to_uint0 => />.
    + have ->: (u64i r.[2] + 18446744073709551615) %% 18446744073709551616 =
               (u64i r.[2] + 18446744073709551615) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt(). auto => />.
    + rewrite pmod_small. move: W64.to_uint_cmp. smt().
    + ring.

    move: C3. rewrite not_false_to_true. move => C3. rewrite !C3 !b2i1 !to_uint1 => />.
    rewrite pmod_small. move: W64.to_uint_cmp. smt().
    have E: ((u64i r.[3] < 1) = false).
    + move: (W64.to_uint_cmp r.[3])  (upper_limb4_ltP_range r) H H0.
    + rewrite !valRep4E !pE !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + rewrite !mulzDr -!mulzA   (modz_small 0 (pow 2 64)) 1:/# => />; 1:smt().
    + have ->: (u64i r.[3] + 18446744073709551615) %% 18446744073709551616 =
               (u64i r.[3] + 18446744073709551615) - 18446744073709551616.
    + move: W64.to_uint_cmp. smt(). auto => />. ring.
qed.

lemma ph_subtraction19 (r: Rep4):
  phoare [ToBytesSpec.subtraction :
       r = f /\ operand2 = W64.of_int 19 /\ 19 <= valRep4 r < W256.modulus
      ==>
      valRep4 r - 19 = valRep4 res
  ] = 1%r.
proof.
    by conseq ill_subtraction (h_subtraction19 r).
qed.

(** To Bytes **)
lemma h_tobytes_no_reduction (r: Rep4):
  hoare [ToBytesSpec.tobytes_no_reduction :
      r = f /\ 0 <= valRep4 r < p
      ==>
      valRep4 r = valRep4 res
  ].
proof.
    proc. inline 1.
    seq 3 : (#pre /\ extracted_msbw0 = W64.zerow /\ f0 = f).
    + call h_extract_msb_lt_2_255. auto => />.
    + move => H H0. move: (upper_limb4_ltP_range r). smt().
    seq 1 : (#pre /\ tt1 = f.[3]).
    + call (h_remove_msb_if_set_lt_2_255 (r.[3])). auto => />.
    + move: (upper_limb4_ltP_range r). smt().
    seq 1 : (#pre /\ tt00 = W64.of_int 19).
    + call h_to19. auto => />.
    + seq 1 : (#pre /\ valRep4 r + 19 = valRep4 ff0 /\ add19 r = ff0).
    + call (h_addition19 r). auto => />.
    seq 2 : (#pre /\ f3 = W64.of_int 19 /\ ff = ff0).
    + call h_sar_inv_t. auto => />.
    + move => &hr.
    rewrite !addcE !/add_carry !/carry_add !b2i0 => />.
    rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !of_uintK (modz_small 19 (pow 2 64)) 1:/# => />.
    + move: (upper_limb4_ltP_range r).
    + move: (W64.to_uint_cmp (add19_l4 r)). smt().
    call (h_subtraction19 (add19 r)). auto => />.
    move => &hr [#] H H0. do split;1:smt(). move: H.
    rewrite pVal 1:/#. smt().
qed.

lemma equiv_to_bytes_no_reduction:
    equiv[M.__tobytes4 ~ ToBytesSpec.tobytes_no_reduction :
      f{1} = f{2} /\ 0 <= valRep4 f{1} < p
      ==>
      valRep4 res{1} = valRep4 res{2}
    ].
proof.
    proc => />.
    inline {2} 1. swap {2} 4 -1. swap{1} 9 -7.
    seq 2 3: (#pre /\ t{1} = tt1{2} /\ tt1{2} = f0.[3]{2} /\ 0 <= valRep4 f0{2} < p /\ f0{2} = f{2}).
    + wp; sp. ecall {2} (ph_remove_msb_if_set_lt_2_255 f0.[3]{2}). auto => />.
    + move => &2 [#] H H0. do split. smt(W64.to_uint_cmp).
    + move: H H0 upper_limb4_lt_2_255_range W64.to_uint_cmp pVal; 1:smt().
    + move => H1 H2. rewrite helper_remove_msb_if_set /#.

    seq 6 1 : (#pre /\ extracted_msbw0{2} = W64.zerow /\ aux_4{1} = extracted_msbw0{2}).
    + auto => />.
    + ecall {2} (ph_extract_msb_lt_2_255). auto => />.
    + move => &2 H H0 H1 H2. do split. smt(W64.to_uint_cmp).
    + move: H1 H2. rewrite valRep4E pE /to_list /val_digits /mkseq -iotaredE => />.
    + smt(W64.to_uint_cmp). move => H3 H4.
    + rewrite /SAR_64 /shift_mask /rflags_OF //= sarE /min => />.
    + rewrite init_bits2w bits2wE -iotaredE /min //= upper_limb4_ltP_msbw.
    + move: H H0. rewrite valRep4E pE /to_list /val_digits /mkseq -iotaredE => />.
    + rewrite /W64.zerow of_intE bits2wE /int2bs /mkseq -iotaredE => />.

    seq 1 0 : (0 <= valRep4 f{1} && valRep4 f{1} < p - W64.to_uint (f.[3]{2}) /\ t{1} = tt1{2}
               /\ tt1{2} = f0{2}.[3] /\
               0 <= valRep4 f0{2} && valRep4 f0{2} < p /\ extracted_msbw0{2} = W64.zerow /\
               aux_4{1} = extracted_msbw0{2} /\ f0{2} = f{2} /\
               f{1} = Array4.of_list witness [f.[0]{2}; f.[1]{2}; f.[2]{2}; extracted_msbw0{2}]).
    + auto => />. move => &2 H H0 H1 H2. do split.
    + rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />. smt(W64.to_uint_cmp).
    + move => H3. do split.
    + move: H H0. rewrite !valRep4E !pE !/to_list !/val_digits !/mkseq -!iotaredE => />.
    + rewrite to_uint0 => />. smt(W64.to_uint_cmp). apply Array4.ext_eq => i ib.
    + rewrite !get_setE 1:/#.
    + case (i = 3) => I. rewrite I => />.
    + case (i = 2) => I0. rewrite I0 => />.
    + case (i = 1) => I1. rewrite I1 => />.
    + case (i = 0) => I2. rewrite I2 => />. rewrite get_out /#.

    seq 2 1 : (0 <= valRep4 f{1} && valRep4 f{1} < p - (W64.to_uint f.[3]{2}) + 19 * pow 2 196 /\
               t{1} = tt1{2} /\ tt1{2} = f0{2}.[3] /\ 0 <= valRep4 f0{2} && valRep4 f0{2} < p
               /\ extracted_msbw0{2} = W64.zerow /\ f0{2} = f{2}
               /\ tt00{2} = W64.of_int 19 /\ f.[0]{1} = f.[0]{2} /\ f.[1]{1} = f.[1]{2} /\
               f.[2]{1} = f.[2]{2} /\  f.[3]{1} = tt00{2}).
   + ecall {2} (ph_to19). wp. auto => />. move => &2 [#] H H0 H1 H2. do split.
   + move: H. rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + rewrite to_uint0 => />. smt(W64.to_uint_cmp). move => H3.
   + have !->: W64.zerow `&` (of_int 19)%W64 + (of_int 19)%W64 = W64.of_int 19. smt(@W64).
   + move: H0. rewrite !valRep4E pE !/to_list !/val_digits !/mkseq -!iotaredE => />. rewrite to_uint0 //=.
   + smt(W64.to_uint_cmp).

   seq 0 0 : (#pre /\ f{1} = Array4.of_list witness [f.[0]{2}; f.[1]{2}; f.[2]{2}; tt00{2}]).
   + skip. move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
   + auto => />. move => *. auto => />. rewrite -H8 -H9 -H10 H7.
   + apply Array4.ext_eq => i ib.
    + case (i = 3) => I. rewrite I => />.
    + case (i = 2) => I0. rewrite I0 => />.
    + case (i = 1) => I1. rewrite I1 => />.
    + case (i = 0) => I2. rewrite I2 => />. rewrite get_out /#.

    seq 10 1 : (0 <= valRep4 f0{2} && valRep4 f0{2} < p
               /\ extracted_msbw0{2} = W64.zerow /\ f0{2} = f{2}
               /\ tt00{2} = W64.of_int 19 /\ 19 <= valRep4 ff0{2} && valRep4 ff0{2} < p+19 /\
               ff0{2} = add19 f0{2} /\ f{1}.[0] = add19_l1 f{2} /\ f{1}.[1] = add19_l2 f{2} /\
               f{1}.[2] = add19_l3 f{2} /\ f{1}.[3] = W64.of_int 19 /\ t{1} = add19_l4 f0{2}
               /\ t{1} = add19_l4 f{2}).
   + ecall {2} (ph_addition19 f0{2}). auto => />. move => &1 [#] H H0 H1 H2 H3.
   + do split. rewrite -H3 1:/#. move => H4.  rewrite -H3 1:/#.

   seq 0 1 : (#pre /\ ff{2} = ff0{2}). auto => />.

   swap{1} 3 -1.
   seq 2 0 : (ff{2} = ff0{2} /\ 0 <= valRep4 f0{2} && valRep4 f0{2} < p /\ t{1} = add19_l4 f{2} /\
               0 <= valRep4 f{1} && valRep4 f{1} < p + 19
               /\ extracted_msbw0{2} = W64.zerow /\ f0{2} = f{2}
               /\ tt00{2} = W64.of_int 19 /\ 19 <= valRep4 ff0{2} && valRep4 ff0{2} < p+19 /\
               ff0{2} = add19 f0{2} /\ f{1}.[0] = add19_l1 f{2} /\ f{1}.[1] = add19_l2 f{2} /\
               f{1}.[2] = add19_l3 f{2} /\ f{1}.[3] = ff0.[3]{2}).
   + auto => />. move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6. do split.
   + rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />. smt(W64.to_uint_cmp). move => H7.
   + do split. move: H2. rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + have ->: LEA_64 (add19_l4 f{2} + add19_l4 f{2}) `>>` W8.one = add19_l4 f{2}.
   + rewrite helper_remove_msb_if_set. move: H0.
   + rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + rewrite !addcE !/carry_add !b2i0 => />.
   + case (18446744073709551616 <= u64i f{2}.[0] + 19 = false) => C. rewrite !C !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f{2}.[1] = false. move: W64.to_uint_cmp. smt().
   + have !->: 18446744073709551616 <= u64i f{2}.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C. rewrite not_false_to_true. move => C. rewrite !C !b2i1 => />.
   + case (18446744073709551616 <= u64i f{2}.[1] + 1 = false) => C1. rewrite !C1 !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f{2}.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1 => />.
   + case (18446744073709551616 <= u64i f{2}.[2] + 1 = false) => C2. rewrite !C2 !b2i0 => />.
   + smt(W64.to_uint_cmp).
   + move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1 => />.
   + rewrite !to_uintD of_uintK. smt(W64.to_uint_cmp).
   + auto => />. move => H8. smt().
   + have ->: LEA_64 (add19_l4 f{2} + add19_l4 f{2}) `>>` W8.one = add19_l4 f{2}.
   + rewrite helper_remove_msb_if_set. move: H0.
   + rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + rewrite !addcE !/carry_add !b2i0 => />.
   + case (18446744073709551616 <= u64i f{2}.[0] + 19 = false) => C. rewrite !C !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f{2}.[1] = false. move: W64.to_uint_cmp. smt().
   + have !->: 18446744073709551616 <= u64i f{2}.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C. rewrite not_false_to_true. move => C. rewrite !C !b2i1 => />.
   + case (18446744073709551616 <= u64i f{2}.[1] + 1 = false) => C1. rewrite !C1 !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f{2}.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1 => />.
   + case (18446744073709551616 <= u64i f{2}.[2] + 1 = false) => C2. rewrite !C2 !b2i0 => />.
   + smt(W64.to_uint_cmp).
   + move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1 => />.
   + rewrite !to_uintD of_uintK. smt(W64.to_uint_cmp). auto => />. auto => />.

   seq 3 1 : (ff{2} = ff0{2} /\ 0 <= valRep4 f0{2} && valRep4 f0{2} < p /\
               0 <= valRep4 f{1} && valRep4 f{1} < p + 19
               /\ extracted_msbw0{2} = W64.zerow /\ f0{2} = f{2}
               /\ tt00{2} = W64.of_int 19 /\ 19 <= valRep4 ff0{2} && valRep4 ff0{2} < p+19 /\
               ff0{2} = add19 f0{2} /\ f{1}.[0] = add19_l1 f{2} /\ f{1}.[1] = add19_l2 f{2} /\
               f{1}.[2] = add19_l3 f{2} /\ f{1}.[3] = ff0.[3]{2} /\ f3{2} = W64.of_int 19 /\
               t{1} = W64.of_int 19).
   + ecall {2} (ph_sar_inv_t). auto => />. move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8.
   + do split. smt(W64.to_uint_cmp). move: H4.
   + rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + rewrite !addcE !/carry_add !b2i0 => />.
   + case (18446744073709551616 <= u64i f{2}.[0] + 19 = false) => C. rewrite !C !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f{2}.[1] = false. move: W64.to_uint_cmp. smt().
   + have !->: 18446744073709551616 <= u64i f{2}.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C. rewrite not_false_to_true. move => C. rewrite !C !b2i1 => />.
   + case (18446744073709551616 <= u64i f{2}.[1] + 1 = false) => C1. rewrite !C1 !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f{2}.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1 => />.
   + case (18446744073709551616 <= u64i f{2}.[2] + 1 = false) => C2. rewrite !C2 !b2i0 => />.
   + smt(W64.to_uint_cmp).
   + move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1 => />.
   + rewrite !to_uintD of_uintK. smt(W64.to_uint_cmp).
   + auto => />. move => H9 H10.
   + rewrite helper_sar_inv_t 1:/#. auto.
   ecall {2} (ph_subtraction19 ff{2}). auto => />.
   + move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8. do split.
   + move: H4. rewrite !valRep4E !pVal !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + rewrite !addcE !/carry_add !b2i0 => />.
   + case (18446744073709551616 <= u64i f{2}.[0] + 19 = false) => C. rewrite !C !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f{2}.[1] = false. move: W64.to_uint_cmp. smt().
   + have !->: 18446744073709551616 <= u64i f{2}.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C. rewrite not_false_to_true. move => C. rewrite !C !b2i1 => />.
   + case (18446744073709551616 <= u64i f{2}.[1] + 1 = false) => C1. rewrite !C1 !b2i0 => />.
   + have !->: 18446744073709551616 <= u64i f{2}.[2] = false. move: W64.to_uint_cmp. smt().
   + rewrite !b2i0 => />. smt(W64.to_uint_cmp).
   + move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1 => />.
   + case (18446744073709551616 <= u64i f{2}.[2] + 1 = false) => C2. rewrite !C2 !b2i0 => />.
   + smt(W64.to_uint_cmp).
   + move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1 => />.
   + rewrite !to_uintD of_uintK. smt(W64.to_uint_cmp).
   + move => H9 H10 H11. rewrite -H11 H5 H6 H7 H8.
   + rewrite !addcE !/carry_add !b2i0 => />.
   + rewrite !subcE !/borrow_sub !b2i0 => />.
   + rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + rewrite !mulzDr -!mulzA !to_uintD !to_uintN (modz_small 19 (pow 2 64)) 1:/# => />.
   + rewrite !of_uintK => />.
   + case (18446744073709551616 <= u64i f{2}.[0] + 19 = false) => C. rewrite !C !b2i0 => />.
   + have ->: (18446744073709551616 <= u64i f{2}.[1] = false). move: W64.to_uint_cmp => />. smt().
   + have ->: (18446744073709551616 <= u64i f{2}.[2] = false). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[3]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[2]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[1]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[0] + 19) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have ->: u64i f{2}.[0] + 19 < 19 = false. move: W64.to_uint_cmp => />. smt().
   + have ->: u64i f{2}.[1] < 0 = false. move: W64.to_uint_cmp => />. smt().
   + have ->: u64i f{2}.[2] < 0 = false. move: W64.to_uint_cmp => />. smt().
   + rewrite !b2i0 => />.
   + rewrite (pmod_small (u64i f{2}.[3]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[2]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[1]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have ->: (u64i f{2}.[0] + 18446744073709551616) %% 18446744073709551616 = (u64i f{2}.[0] + 18446744073709551616) - 18446744073709551616. move: W64.to_uint_cmp. smt().
   + ring.

   move: C. rewrite not_false_to_true. move => C. rewrite !C !b2i1.
   case(18446744073709551616 <= u64i f{2}.[1] + 1 = false) => C1. rewrite !C1 !b2i0 => />.
   + have ->: (18446744073709551616 <= u64i f{2}.[2] = false). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[3]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[2]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have ->: ((u64i f{2}.[0] + 19) %% 18446744073709551616 < 19) = true. move: W64.to_uint_cmp => />. smt().
   + have ->: ((u64i f{2}.[1] + 1) %% 18446744073709551616 < 1) = false. move: W64.to_uint_cmp => />. smt().
   + have ->: ((u64i f{2}.[2] < 0)) = false. move: W64.to_uint_cmp => />. smt().
   + rewrite !b2i0 !b2i1 => />.
   + rewrite (pmod_small (u64i f{2}.[3]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[2]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have ->: (u64i f{2}.[0] + 19) %% 18446744073709551616 = (u64i f{2}.[0] + 19) - 18446744073709551616. move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[1] + 1) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have ->: (u64i f{2}.[1] + 1 + 18446744073709551615) %% 18446744073709551616 = (u64i f{2}.[1] + 1 + 18446744073709551615) - 18446744073709551616. move: W64.to_uint_cmp => />. smt(). auto => />.
   + rewrite (pmod_small (u64i f{2}.[0]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + ring.

   move: C1. rewrite not_false_to_true. move => C1. rewrite !C1 !b2i1.
   case(18446744073709551616 <= u64i f{2}.[2] + 1 = false) => C2. rewrite !C2 !b2i0 => />.
   + rewrite (pmod_small (u64i f{2}.[3]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have ->: ((u64i f{2}.[0] + 19) %% 18446744073709551616 < 19) = true. move: W64.to_uint_cmp => />. smt().
   + have ->: ((u64i f{2}.[1] + 1) %% 18446744073709551616 < 1) = true. move: W64.to_uint_cmp => />. smt().
   + rewrite  !b2i1 => />.
   + have ->: (u64i f{2}.[0] + 19) %% 18446744073709551616 = (u64i f{2}.[0] + 19) - 18446744073709551616. move: W64.to_uint_cmp => />. smt().
   + have ->: (u64i f{2}.[2] + 1) %% 18446744073709551616 < 1 = false. move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[0]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[2] + 1) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have ->: (u64i f{2}.[2] + 1 + 18446744073709551615) %% 18446744073709551616 = (u64i f{2}.[2] + 1 + 18446744073709551615) - 18446744073709551616. move: W64.to_uint_cmp => />. smt(). auto => />.
   + have ->: (u64i f{2}.[1] + 1) %% 18446744073709551616 = (u64i f{2}.[1] + 1 - 18446744073709551616). move: W64.to_uint_cmp => />. smt(). rewrite !b2i0 => />.
   + rewrite (pmod_small (u64i f{2}.[3]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[1]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + ring.

   move: C2. rewrite not_false_to_true. move => C2. rewrite !C2 !b2i1.
   have E: (18446744073709551616 <= u64i f{2}.[3] + 1 = false).
   + move: (W64.to_uint_cmp f{2}.[3])  (upper_limb4_ltP_range f{2}) H H0 H1 H2 H3 H4 H9.
   + rewrite !valRep4E !pE !/to_list !/val_digits !/mkseq -!iotaredE => />.
   + rewrite !mulzDr -!mulzA   (modz_small 0 (pow 2 64)) 1:/# => />; 1:smt().

   + have ->: ((u64i f{2}.[0] + 19) %% 18446744073709551616 < 19) = true. move: W64.to_uint_cmp => />. smt().
   + have ->: ((u64i f{2}.[1] + 1) %% 18446744073709551616 < 1) = true. move: W64.to_uint_cmp => />. smt().
   + rewrite  !b2i1 => />.
   + have !->: (u64i f{2}.[0] + 19) %% 18446744073709551616 = (u64i f{2}.[0] + 19) - 18446744073709551616. move: W64.to_uint_cmp => />. smt().
   + have ->: (u64i f{2}.[2] + 1) %% 18446744073709551616 < 1 = true. move: W64.to_uint_cmp => />. smt().
   + rewrite (pmod_small (u64i f{2}.[0]) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have !->: (u64i f{2}.[2] + 1) %% 18446744073709551616 = (u64i f{2}.[2] + 1) - 18446744073709551616. move: W64.to_uint_cmp => />. smt(). auto => />.
   + have !->: (u64i f{2}.[1] + 1) %% 18446744073709551616 = (u64i f{2}.[1] + 1) - 18446744073709551616. move: W64.to_uint_cmp => />. smt(). auto => />.
   + rewrite pmod_small. move: W64.to_uint_cmp => />. smt().
   + rewrite pmod_small. move: W64.to_uint_cmp => />. smt().
   + rewrite !b2i1 => />.
   + rewrite (pmod_small (u64i f{2}.[3] + 1) 18446744073709551616). move: W64.to_uint_cmp => />. smt().
   + have !->: (u64i f{2}.[3] + 1 + 18446744073709551615) %% 18446744073709551616 = (u64i f{2}.[3] + 1 + 18446744073709551615) - 18446744073709551616. move: W64.to_uint_cmp => />. smt().
   + ring.
qed.

(** Case p <= valRep4 < 2*p (some lemmas extend to 2**256)**)

lemma h_sar_inv_t_of:
  hoare [ToBytesSpec.sar_inv_t :
      pow 2 63 <= W64.to_uint t < W64.modulus
      ==>
      res = W64.zerow].
    proc => />. auto => />.
    move => &hr H H0.
    have ->: (SAR_64 t{hr} ((of_int 63))%W8).`6 = W64.onew.
    + rewrite /SAR_64 /shift_mask /rflags_OF //= sarE /min => />.
    rewrite init_bits2w bits2wE -iotaredE /min //= upper_limb4_geqP_msbw.
    move: H upper_limb4_geq_2_255_range W64.to_uint_cmp; 1:smt().
    + rewrite /W64.onew of_intE bits2wE /int2bs /mkseq -iotaredE => />.
    have ->: invw W64.onew = W64.zerow.
    + rewrite /invw mapE /W64.zerow /W64.zero bits2wE /int2bs /mkseq -iotaredE => />.
    + rewrite wordP => i ib. rewrite !initiE 1,2,3:/# //=.
    rewrite wordP => i ib.
    rewrite /W64.zerow /W64.zero !bits2wE !/int2bs !/mkseq -!iotaredE => />.
    rewrite !initiE 1,2:/# //= /#.
qed.

lemma ph_sar_inv_t_of:
  phoare [ToBytesSpec.sar_inv_t :
      pow 2 63 <= W64.to_uint t < W64.modulus
      ==>
      res = W64.zerow] = 1%r.
proof.
    by conseq ill_sar_inv_t (h_sar_inv_t_of).
qed.

(** Subtraction **)

lemma h_subtraction0 (r: Rep4):
  hoare [ToBytesSpec.subtraction :
      r = f /\ operand2 = W64.of_int 0
      ==>
      valRep4 r = valRep4 res
  ].
proof.
    proc. auto => />. move => &hr.
    rewrite !subcE !/borrow_sub !b2i0 => />.
    rewrite !valRep4E !/to_list !/val_digits !/mkseq -!iotaredE => />.
    rewrite !mulzDr -!mulzA !to_uintD !to_uintN (modz_small 0 (pow 2 64)) 1:/# => />.
    have ->: u64i r.[0] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    have ->: u64i r.[1] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    have ->: u64i r.[2] < 0 = false. move: W64.to_uint_cmp; 1:smt().
    rewrite pmod_small. move: W64.to_uint_cmp; 1:smt().
    rewrite !b2i0 => />.
    rewrite pmod_small. move: W64.to_uint_cmp; 1:smt().
    rewrite pmod_small. move: W64.to_uint_cmp; 1:smt().
    rewrite pmod_small. move: W64.to_uint_cmp; 1:smt().
    auto.
qed.

lemma ph_subtraction0 (r: Rep4):
  phoare [ToBytesSpec.subtraction :
      r = f /\ operand2 = W64.of_int 0
      ==>
      valRep4 r = valRep4 res
  ] = 1%r.
proof.
    by conseq ill_subtraction (h_subtraction0 r).
qed.

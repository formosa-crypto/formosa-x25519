require import AllCore IntDiv CoreMap List Distr StdOrder.

from Jasmin require import JModel_x86.

import SLH64 IntOrder.

from Jasmin require import Jcheck.

require import Array4.

require import WArray32.

require import Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.

module M = {
  var tmp__trace : trace
  var tmp__data___tobytes4 : (W64.t Array4.t)
  var tmp____tobytes4 : W64.t Array4.t
  proc __tobytes4 (f:W64.t Array4.t) : ((W64.t Array4.t) * trace) = {
    var aux_3:bool;
    var aux_2:bool;
    var aux_1:bool;
    var aux_0:bool;
    var aux:bool;
    var aux_4:W64.t;
    var t:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    var old_f:W64.t Array4.t;
    var trace___tobytes4:trace;
    old_f <- f;
    trace___tobytes4 <- [];
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assume,
     ((W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639898
      ) \ule
     (limbs_4u64 (quad f.[0] f.[1] f.[2] f.[3]))))]);
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assume,
     ((limbs_4u64 (quad f.[0] f.[1] f.[2] f.[3])) \ule
     (W256.of_int
     115792089237316195423570985008687907853269984665640564039457584007913129639935
     )))]);
    t <- (f.[3] + f.[3]);
    t <- (t `>>` (W8.of_int 1));
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assert, (t = (f.[3] - (W64.of_int 9223372036854775808))))]);
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assume, ((u64i t) = ((u64i f.[3]) - (pow 2 63))))]);
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <-
    (SAR_64 f.[3] (W8.of_int 63));
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
     _0 <- aux_0;
    _zf_ <- aux;
    f.[3] <- aux_4;
    f.[3] <- (f.[3] `&` (W64.of_int 19));
    f.[3] <- (f.[3] + (W64.of_int 19));
    trace___tobytes4 <-
    (trace___tobytes4 ++ [(Assert, (f.[3] = (W64.of_int 38)))]);
    trace___tobytes4 <-
    (trace___tobytes4 ++ [(Assume, ((u64i f.[3]) = 38))]);
    (aux_3, aux_4) <- (adc_64 f.[0] f.[3] false);
    cf <- aux_3;
    f.[0] <- aux_4;
    (aux_3, aux_4) <- (adc_64 f.[1] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[1] <- aux_4;
    (aux_3, aux_4) <- (adc_64 f.[2] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[2] <- aux_4;
    (cf, t) <- (adc_64 t (W64.of_int 0) cf);
    trace___tobytes4 <- (trace___tobytes4 ++ [(Assert, (! cf))]);
    trace___tobytes4 <- (trace___tobytes4 ++ [(Assume, ((b2i cf) = 0))]);
    f.[3] <- (t + t);
    f.[3] <- (f.[3] `>>` (W8.of_int 1));
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assert, (f.[3] = (t - (W64.of_int (- 9223372036854775808)))))]);
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assume, ((u64i f.[3]) = ((u64i t) - (pow 2 63))))]);
    (_of_, _cf_, _sf_,  _1, _zf_, t) <- (SAR_64 t (W8.of_int 63));
    t <- (invw t);
    t <- (t `&` (W64.of_int 19));
    trace___tobytes4 <-
    (trace___tobytes4 ++ [(Assert, (t = (W64.of_int 0)))]);
    trace___tobytes4 <- (trace___tobytes4 ++ [(Assume, ((u64i t) = 0))]);
    (aux_3, aux_4) <- (sbb_64 f.[0] t false);
    cf <- aux_3;
    f.[0] <- aux_4;
    (aux_3, aux_4) <- (sbb_64 f.[1] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[1] <- aux_4;
    (aux_3, aux_4) <- (sbb_64 f.[2] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[2] <- aux_4;
    (aux_3, aux_4) <- (sbb_64 f.[3] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[3] <- aux_4;
    trace___tobytes4 <- (trace___tobytes4 ++ [(Assert, (! cf))]);
    trace___tobytes4 <- (trace___tobytes4 ++ [(Assume, ((b2i cf) = 0))]);
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i f.[ii]))) (iota_ 0 4)))
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_f.[ii]))) (iota_ 0 4)))
     (single ((pow 2 255) - 19))))]);
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assert,
     ((W256.of_int 0) \ule (limbs_4u64 (quad f.[0] f.[1] f.[2] f.[3]))))]);
    trace___tobytes4 <-
    (trace___tobytes4 ++
    [(Assert,
     ((limbs_4u64 (quad f.[0] f.[1] f.[2] f.[3])) \ult
     (W256.of_int
     57896044618658097711785492504343953926634992332820282019728792003956564819949
     )))]);
    return (f, trace___tobytes4);
  }
}.

(* The post is in the trace. *)

lemma __tobytes4_valid_post _f :
      hoare [M.__tobytes4 :
      (_f = f) ==>
      ((valid (trace res)) =>
      (((limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3])) \ult
       (W256.of_int
       57896044618658097711785492504343953926634992332820282019728792003956564819949
       )) /\
      (((W256.of_int 0) \ule
       (limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3]))) /\
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4)))
      (single ((pow 2 255) - 19))))))].
proof.
proc . auto => />.
qed .

(* The post is in the trace and all assumes are valid. *)
lemma limb4_geq2p_cmp r: 2*p <= valRep4 r < W256.modulus =>
           (to_uint r.[3]) = W64.modulus-1.
proof. rewrite valRep4E !pE /to_list /val_digits /mkseq -iotaredE => />.
       move => H H0. move: W64.to_uint_cmp. smt().
qed.

lemma __tobytes4_assume_ _f :
      hoare [M.__tobytes4 :
      (_f = f) ==>
      ((((limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])) \ule
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        )) /\
       ((W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639898
        ) \ule
       (limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])))) =>
      (validk Assume (trace res)))].
proof.
    proc. auto => />. 
    move => H H0 H1. 
    do split. rewrite H1.
    have E: to_uint (limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])) = valRep4 _f.
    + by rewrite valRep4ToPack /to_list /mkseq -iotaredE => />.
    have E0: 2*p <= valRep4 _f < W256.modulus.
    + rewrite -E pVal => />. move: H H0. rewrite !uleE. smt().
    rewrite to_uintB. rewrite uleE of_uintK pmod_small //=. 
    rewrite limb4_geq2p_cmp. by rewrite E0. auto. rewrite of_uintK //=.
    move => H2. do split. by rewrite H2. move => H3 H4. do split. 
    rewrite H4 H2 H1. rewrite to_uintB. rewrite uleE of_uintK pmod_small //=.
    have E: to_uint (limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])) = valRep4 _f.
    + by rewrite valRep4ToPack /to_list /mkseq -iotaredE => />.
    have E0: 2*p <= valRep4 _f < W256.modulus.
    + rewrite -E pVal => />. move: H H0. rewrite !uleE. smt().
    rewrite !addcE !/carry_add !b2i0 => />.
    move: E0 pVal (W64.to_uint_cmp _f.[3]) (limb4_geq2p_cmp _f). rewrite !pVal => />. 
    move => L L0 L1 L2 L3. 
    have L4: _f.[3] = W64.of_int 18446744073709551615. smt(W64.to_uintK).
    rewrite L4 //=.
    have ->:  18446744073709551616 <= u64i _f.[0] + 38 = true.
    + move: L L0. rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />.
    + move => L L0. move: W64.to_uint_cmp. smt().
    rewrite !b2i1 => />.
    have ->:  18446744073709551616 <= u64i _f.[1] + 1 = true.
    + move: L L0. rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />.
    + move => L L0. move: W64.to_uint_cmp. smt().
    rewrite !b2i1 => />.
    have ->:  18446744073709551616 <= u64i _f.[2] + 1 = true.
    + move: L L0. rewrite valRep4E /to_list /val_digits /mkseq -iotaredE => />.
    + move => L L0. move: W64.to_uint_cmp. smt().
    rewrite !b2i1 => />.
    rewrite of_uintK pmod_small //=.
    smt(W64.to_uint_cmp W64.of_uintK).
qed.

lemma __tobytes4_assume _f :
      hoare [M.__tobytes4 :
      (_f = f) ==>
      (((valid (trace res)) =>
       (((limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3])) \ult
        (W256.of_int
        57896044618658097711785492504343953926634992332820282019728792003956564819949
        )) /\
       (((W256.of_int 0) \ule
        (limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3]))) /\
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4)))
       (single ((pow 2 255) - 19)))))) /\
      ((((limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])) \ule
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        )) /\
       ((W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639898
        ) \ule
       (limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])))) =>
      (validk Assume (trace res))))].
proof.
conseq (__tobytes4_assume_ _f) (__tobytes4_valid_post _f) => />.
qed .

(* All assert are valid. *)

lemma __tobytes4_assert _f :
      hoare [M.__tobytes4 :
      ((_f = f) /\
      (((limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])) \ule
       (W256.of_int
       115792089237316195423570985008687907853269984665640564039457584007913129639935
       )) /\
      ((W256.of_int
       115792089237316195423570985008687907853269984665640564039457584007913129639898
       ) \ule
      (limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3]))))) ==>
      (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __tobytes4_spec _f :
      hoare [M.__tobytes4 :
      ((_f = f) /\
      (((limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])) \ule
       (W256.of_int
       115792089237316195423570985008687907853269984665640564039457584007913129639935
       )) /\
      ((W256.of_int
       115792089237316195423570985008687907853269984665640564039457584007913129639898
       ) \ule
      (limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3]))))) ==>
      (((limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3])) \ult
       (W256.of_int
       57896044618658097711785492504343953926634992332820282019728792003956564819949
       )) /\
      (((W256.of_int 0) \ule
       (limbs_4u64 (quad res.`1.[0] res.`1.[1] res.`1.[2] res.`1.[3]))) /\
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4)))
      (single ((pow 2 255) - 19)))))].
proof.
conseq (__tobytes4_assume _f) (__tobytes4_assert _f) => />.
smt (all_validk_valid).
qed .


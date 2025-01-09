require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck.

require import Array4 Array8.

require import WArray32 WArray64.

require import Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.

module M = {
  var tmp__trace : trace
  var tmp__data___reduce4 : (W64.t Array4.t)
  var tmp____reduce4 : W64.t Array4.t
  var tmp__data___sqr4_rr : (W64.t Array4.t)
  var tmp____sqr4_rr : W64.t Array4.t
  proc __reduce4 (x:W64.t Array4.t, r:W64.t Array4.t, _38:W64.t, z:W64.t,
                  cf:bool, of_0:bool) : ((W64.t Array4.t) * trace) = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var h:W64.t Array4.t;
    var h0:W64.t Array4.t;
    var hi:W64.t;
    var lo:W64.t;
    var carryo:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var old_of:bool;
    var old_cf:bool;
    var old_z:W64.t;
    var old__38:W64.t;
    var old_r:W64.t Array4.t;
    var old_x:W64.t Array4.t;
    var trace___reduce4:trace;
    old_x <- x;
    old_r <- r;
    old__38 <- _38;
    old_z <- z;
    old_cf <- cf;
    old_of <- of_0;
    trace___reduce4 <- [];
    h <- witness;
    h0 <- witness;
    z <- (W64.of_int 0);
    _38 <- (W64.of_int 38);
    h <- (copy_64 x);
    h0 <- (copy_64 r);
    (hi, lo) <- (MULX_64 _38 h0.[0]);
    (aux, aux_1) <- (ADOX_64 h.[0] lo of_0);
    of_0 <- aux;
    h.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[1] hi cf);
    cf <- aux;
    h.[1] <- aux_1;
    (hi, lo) <- (MULX_64 _38 h0.[1]);
    (aux, aux_1) <- (ADOX_64 h.[1] lo of_0);
    of_0 <- aux;
    h.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[2] hi cf);
    cf <- aux;
    h.[2] <- aux_1;
    (hi, lo) <- (MULX_64 _38 h0.[2]);
    (aux, aux_1) <- (ADOX_64 h.[2] lo of_0);
    of_0 <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[3] hi cf);
    cf <- aux;
    h.[3] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 _38 h0.[3]);
    h0.[0] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h0.[0] z cf);
    cf <- aux;
    h0.[0] <- aux_1;
    (aux, aux_1) <- (ADOX_64 h0.[0] z of_0);
    of_0 <- aux;
    h0.[0] <- aux_1;
    ( _0,  _1,  _2,  _3,  _4, lo) <- (IMULri_64 h0.[0] (W64.of_int 38));
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! of_0))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i of_0) = 0))]);
    (aux, aux_1) <- (adc_64 h.[0] lo false);
    cf <- aux;
    h.[0] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[1] z cf);
    cf <- aux;
    h.[1] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[2] z cf);
    cf <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[3] z cf);
    cf <- aux;
    h.[3] <- aux_1;
    carryo <- cf;
    (cf, z) <- (sbb_64 z z cf);
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (cf = carryo))]);
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assume, ((b2i cf) = (b2i carryo)))]);
    z <- (z `&` (W64.of_int 38));
    trace___reduce4 <-
    (trace___reduce4 ++
    [(Assert,
     (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))))]);
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assume, ((u64i z) = ((b2i cf) * 38)))]);
    (aux, aux_1) <- (adc_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_1;
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    trace___reduce4 <-
    (trace___reduce4 ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_x.[ii]))) (iota_ 0 4))) +
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i old_r.[ii])))
     (iota_ 0 4)))) (single ((pow 2 255) - 19))))]);
    return (h, trace___reduce4);
  }
  proc __sqr4_rr (f:W64.t Array4.t) : ((W64.t Array4.t) * trace) = {
    var aux_1:bool;
    var aux_0:W64.t;
    var aux:W64.t;
    var h:W64.t Array4.t;
    var of_0:bool;
    var cf:bool;
    var z:W64.t;
    var fx:W64.t;
    var t:W64.t Array8.t;
    var r:W64.t Array4.t;
    var _38:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var old_f:W64.t Array4.t;
    var trace___sqr4_rr:trace;
    old_f <- f;
    trace___sqr4_rr <- [];
    h <- witness;
    r <- witness;
    t <- witness;
    (of_0, cf,  _0,  _1,  _2, z) <- (set0_64);
    fx <- f.[0];
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[1] <- aux_0;
    h.[0] <- aux;
    (aux_0, aux) <- (MULX_64 fx f.[1]);
    h.[2] <- aux_0;
    h.[1] <- aux;
    (aux_0, aux) <- (MULX_64 fx f.[2]);
    h.[3] <- aux_0;
    t.[2] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[2] t.[2] cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[0] <- aux_0;
    t.[3] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[3] t.[3] cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    fx <- f.[1];
    (aux_0, aux) <- (MULX_64 fx f.[2]);
    t.[4] <- aux_0;
    t.[3] <- aux;
    (aux_1, aux_0) <- (ADOX_64 h.[3] t.[3] of_0);
    of_0 <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[0] t.[4] cf);
    cf <- aux_1;
    r.[0] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[1] <- aux_0;
    t.[4] <- aux;
    (aux_1, aux_0) <- (ADOX_64 r.[0] t.[4] of_0);
    of_0 <- aux_1;
    r.[0] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[3] <- aux_0;
    t.[2] <- aux;
    fx <- f.[2];
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[2] <- aux_0;
    t.[5] <- aux;
    (aux_1, aux_0) <- (ADCX_64 r.[1] t.[5] cf);
    cf <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[1] z of_0);
    of_0 <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[2] z cf);
    cf <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[2] z of_0);
    of_0 <- aux_1;
    r.[2] <- aux_0;
    trace___sqr4_rr <- (trace___sqr4_rr ++ [(Assert, (! cf))]);
    trace___sqr4_rr <- (trace___sqr4_rr ++ [(Assume, ((b2i cf) = 0))]);
    trace___sqr4_rr <- (trace___sqr4_rr ++ [(Assert, (! of_0))]);
    trace___sqr4_rr <- (trace___sqr4_rr ++ [(Assume, ((b2i of_0) = 0))]);
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[5] <- aux_0;
    t.[4] <- aux;
    fx <- f.[3];
    (aux_0, aux) <- (MULX_64 fx fx);
    r.[3] <- aux_0;
    t.[6] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[1] h.[1] cf);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[1] t.[1] of_0);
    of_0 <- aux_1;
    h.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 h.[2] h.[2] cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[2] t.[2] of_0);
    of_0 <- aux_1;
    h.[2] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 h.[3] h.[3] cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[3] t.[3] of_0);
    of_0 <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[0] r.[0] cf);
    cf <- aux_1;
    r.[0] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[0] t.[4] of_0);
    of_0 <- aux_1;
    r.[0] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[1] r.[1] cf);
    cf <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[1] t.[5] of_0);
    of_0 <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[2] r.[2] cf);
    cf <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[2] t.[6] of_0);
    of_0 <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[3] z cf);
    cf <- aux_1;
    r.[3] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[3] z of_0);
    of_0 <- aux_1;
    r.[3] <- aux_0;
    trace___sqr4_rr <- (trace___sqr4_rr ++ [(Assert, (! cf))]);
    trace___sqr4_rr <- (trace___sqr4_rr ++ [(Assume, ((b2i cf) = 0))]);
    trace___sqr4_rr <- (trace___sqr4_rr ++ [(Assert, (! of_0))]);
    trace___sqr4_rr <- (trace___sqr4_rr ++ [(Assume, ((b2i of_0) = 0))]);
    _38 <- (W64.of_int 38);
    (tmp__data___reduce4, tmp__trace) <@ __reduce4 (h, r, _38, z, cf, of_0);
    tmp____reduce4 <- tmp__data___reduce4;
    trace___sqr4_rr <- (trace___sqr4_rr ++ tmp__trace);
    trace___sqr4_rr <-
    (trace___sqr4_rr ++
    [(Assume,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
     (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4))) +
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i r.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))]);
    h <- tmp____reduce4;
    trace___sqr4_rr <-
    (trace___sqr4_rr ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_f.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_f.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))]);
    return (h, trace___sqr4_rr);
  }
}.

(* The post is in the trace. *)

lemma __reduce4_valid_post _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      ((_of = of_0) /\
      ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii]))) (iota_ 0 4)
      ))) (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=. auto => />.
qed .

lemma __sqr4_rr_valid_post _f :
      hoare [M.__sqr4_rr :
      (_f = f) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> (_f = old_f)).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 1 : ((_f = old_f)).
by auto .
by conseq  />.
qed .

(* The post is in the trace and all assumes are valid. *)

lemma __reduce4_assume_ _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      ((_of = of_0) /\
      ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) ==>
      (true => (validk Assume (trace res)))].
proof.
    proc. auto => />. move => H H0 H1. 
    smt(JUtils.pow2_64 W64.to_uint_small).
qed.

lemma __reduce4_assume _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      ((_of = of_0) /\
      ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii])))
       (iota_ 0 4)))) (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__reduce4_assume_ _x _r __38 _z _cf _of) (__reduce4_valid_post 
                                                  _x _r __38 _z _cf _of) 
       => />.
qed .

lemma __sqr4_rr_assume_ _f :
      hoare [M.__sqr4_rr :
      (_f = f) ==> (true => (validk Assume (trace res)))].
proof.
    proc. auto => />.
    ecall (__reduce4_assume h r _38 z cf of_0).     
    seq 2: (#pre /\ validk Assume trace___sqr4_rr). auto.
    seq 62: (#pre). auto => />.
    + move => &hr H. rewrite !/trace //= !validk_cat //=; 1,2:smt(valid_cat).
    seq 53: (#pre). auto => />.
    + move => &hr H. rewrite !/trace //= !validk_cat //=; 1,2:smt(valid_cat).
    auto => />.
    move => &hr H H0 H1 H2.
    rewrite !/trace //= !validk_cat //=; 1:smt(valid_cat).
qed.

lemma __sqr4_rr_assume _f :
      hoare [M.__sqr4_rr :
      (_f = f) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) *
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))))
       (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__sqr4_rr_assume_ _f) (__sqr4_rr_valid_post _f) => />.
qed .

(* All assert are valid. *)

lemma __reduce4_assert _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      (((_of = of_0) /\
       ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) /\
      true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

lemma __sqr4_rr_assert _f :
      hoare [M.__sqr4_rr :
      ((_f = f) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __reduce4_spec _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      (((_of = of_0) /\
       ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) /\
      true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii]))) (iota_ 0 4)
      ))) (single ((pow 2 255) - 19)))].
proof.
conseq (__reduce4_assume _x _r __38 _z _cf _of) (__reduce4_assert _x 
                                                 _r __38 _z _cf _of) 
       => />.
smt (all_validk_valid).
qed .

lemma __sqr4_rr_spec _f :
      hoare [M.__sqr4_rr :
      ((_f = f) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
conseq (__sqr4_rr_assume _f) (__sqr4_rr_assert _f) => />.
smt (all_validk_valid).
qed .


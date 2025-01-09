require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck.

require import Array4 Array5 Array8.

require import WArray32 WArray40 WArray64.

require import Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.

module M = {
  var tmp__trace : trace
  var tmp__data___reduce4 : (W64.t Array4.t)
  var tmp____reduce4 : W64.t Array4.t
  var tmp__data___sqr4_rs : (W64.t Array4.t)
  var tmp____sqr4_rs : W64.t Array4.t
  proc __reduce4 (z:W64.t Array8.t) : ((W64.t Array4.t) * trace) = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var r:W64.t Array4.t;
    var cf:bool;
    var r38:W64.t;
    var rax:W64.t;
    var h:W64.t;
    var l:W64.t;
    var z8:W64.t;
    var i:int;
    var dc:W64.t;
    var r0:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    var old_z:W64.t Array8.t;
    var trace___reduce4:trace;
    old_z <- z;
    trace___reduce4 <- [];
    r <- witness;
    ( _0, cf,  _1,  _2,  _3,  _4) <- (set0_64);
    r38 <- (W64.of_int 38);
    rax <- z.[4];
    (h, l) <- (mulu_64 rax r38);
    r.[0] <- l;
    r.[1] <- h;
    rax <- z.[5];
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[1] l false);
    cf <- aux;
    r.[1] <- aux_0;
    r.[2] <- (MOV_64 (W64.of_int 0));
    rax <- z.[6];
    (aux, aux_0) <- (adc_64 r.[2] h cf);
    cf <- aux;
    r.[2] <- aux_0;
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[2] l false);
    cf <- aux;
    r.[2] <- aux_0;
    r.[3] <- (MOV_64 (W64.of_int 0));
    rax <- z.[7];
    (aux, aux_0) <- (adc_64 r.[3] h cf);
    cf <- aux;
    r.[3] <- aux_0;
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[3] l false);
    cf <- aux;
    r.[3] <- aux_0;
    z8 <- (MOV_64 (W64.of_int 0));
    (cf, z8) <- (adc_64 z8 h cf);
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (aux, aux_0) <- (adc_64 r.[0] z.[0] false);
    cf <- aux;
    r.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (adc_64 r.[i] z.[i] cf);
      cf <- aux;
      r.[i] <- aux_0;
      i <- (i + 1);
    }
    (cf, z8) <- (adc_64 z8 (W64.of_int 0) cf);
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (dc, z8) <- (mulu_64 z8 (W64.of_int 38));
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assert, (dc = (W64.of_int 0)))]);
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assume, (dc = (W64.of_int 0)))]);
    r0 <- (MOV_64 (W64.of_int 0));
    (aux, aux_0) <- (adc_64 r.[0] z8 false);
    cf <- aux;
    r.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (adc_64 r.[i] r0 cf);
      cf <- aux;
      r.[i] <- aux_0;
      i <- (i + 1);
    }
    (cf, r0) <- (adc_64 r0 r0 cf);
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (dc, r0) <- (mulu_64 r0 (W64.of_int 38));
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assert, (dc = (W64.of_int 0)))]);
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assume, (dc = (W64.of_int 0)))]);
    (aux, aux_0) <- (adc_64 r.[0] r0 false);
    cf <- aux;
    r.[0] <- aux_0;
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    trace___reduce4 <-
    (trace___reduce4 ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i r.[ii]))) (iota_ 0 4)))
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_z.[ii]))) (iota_ 0 8)))
     (single ((pow 2 255) - 19))))]);
    return (r, trace___reduce4);
  }
  proc __sqr4_rs (xa:W64.t Array4.t) : ((W64.t Array4.t) * trace) = {
    var aux:bool;
    var aux_0:W64.t;
    var r:W64.t Array4.t;
    var z:W64.t Array8.t;
    var zero:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var cf:bool;
    var t:W64.t Array5.t;
    var old_xa:W64.t Array4.t;
    var trace___sqr4_rs:trace;
    old_xa <- xa;
    trace___sqr4_rs <- [];
    r <- witness;
    t <- witness;
    z <- witness;
    z.[7] <- (MOV_64 (W64.of_int 0));
    zero <- (MOV_64 (W64.of_int 0));
    rax <- xa.[1];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    z.[1] <- rax;
    z.[2] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    z.[3] <- rax;
    z.[4] <- rdx;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[2]);
    z.[5] <- rax;
    z.[6] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    (aux, aux_0) <- (adc_64 z.[2] rax false);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] rdx cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] zero cf);
    cf <- aux;
    z.[4] <- aux_0;
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assert, (! cf))]);
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assume, ((b2i cf) = 0))]);
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    (aux, aux_0) <- (adc_64 z.[4] rax false);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] rdx cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] zero cf);
    cf <- aux;
    z.[6] <- aux_0;
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assert, (! cf))]);
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assume, ((b2i cf) = 0))]);
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    (aux, aux_0) <- (adc_64 z.[3] rax false);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] rdx cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] zero cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] zero cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] zero cf);
    cf <- aux;
    z.[7] <- aux_0;
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assert, (! cf))]);
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assume, ((b2i cf) = 0))]);
    (aux, aux_0) <- (adc_64 z.[1] z.[1] false);
    cf <- aux;
    z.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[2] z.[2] cf);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] z.[3] cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] z.[4] cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] z.[5] cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] z.[6] cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] z.[7] cf);
    cf <- aux;
    z.[7] <- aux_0;
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assert, (! cf))]);
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assume, ((b2i cf) = 0))]);
    rax <- xa.[0];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    z.[0] <- rax;
    t.[0] <- rdx;
    rax <- xa.[1];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    t.[1] <- rax;
    t.[2] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[2]);
    t.[3] <- rax;
    t.[4] <- rdx;
    (aux, aux_0) <- (adc_64 z.[1] t.[0] false);
    cf <- aux;
    z.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[2] t.[1] cf);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] t.[2] cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] t.[3] cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] t.[4] cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] (W64.of_int 0) cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] (W64.of_int 0) cf);
    cf <- aux;
    z.[7] <- aux_0;
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assert, (! cf))]);
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assume, ((b2i cf) = 0))]);
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[3]);
    (aux, aux_0) <- (adc_64 z.[6] rax false);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] rdx cf);
    cf <- aux;
    z.[7] <- aux_0;
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assert, (! cf))]);
    trace___sqr4_rs <- (trace___sqr4_rs ++ [(Assume, ((b2i cf) = 0))]);
    (tmp__data___reduce4, tmp__trace) <@ __reduce4 (z);
    tmp____reduce4 <- tmp__data___reduce4;
    trace___sqr4_rs <- (trace___sqr4_rs ++ tmp__trace);
    trace___sqr4_rs <-
    (trace___sqr4_rs ++
    [(Assume,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
     (iota_ 0 4)))
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i z.[ii]))) (iota_ 0 8)))
     (single ((pow 2 255) - 19))))]);
    r <- tmp____reduce4;
    trace___sqr4_rs <-
    (trace___sqr4_rs ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i r.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_xa.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_xa.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))]);
    return (r, trace___sqr4_rs);
  }
}.

(* The post is in the trace. *)

lemma __reduce4_valid_post _z :
      hoare [M.__reduce4 :
      (_z = z) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
      (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> (_z = old_z)).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 1 : ((_z = old_z)).
by auto .
by conseq  />.
qed .

lemma __sqr4_rs_valid_post _xa :
      hoare [M.__sqr4_rs :
      (_xa = xa) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> (_xa = old_xa)).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 1 : ((_xa = old_xa)).
by auto .
by conseq  />.
qed .

(* The post is in the trace and all assumes are valid. *)

lemma __reduce4_assume_ _z :
      hoare [M.__reduce4 :
      (_z = z) ==> (true => (validk Assume (trace res)))].
proof.
    proc. do 2! unroll for ^while. auto => />.
qed.

lemma __reduce4_assume _z :
      hoare [M.__reduce4 :
      (_z = z) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
       (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__reduce4_assume_ _z) (__reduce4_valid_post _z) => />.
qed .

lemma __sqr4_rs_assume_ _xa :
      hoare [M.__sqr4_rs :
      (_xa = xa) ==> (true => (validk Assume (trace res)))].
proof.
    proc. wp.
    seq 2: (#pre /\ validk Assume (trace___sqr4_rs)). auto => />.
    seq 30: (#pre). auto => />. move => &hr H. rewrite !validk_cat //=; 1:smt(@Jcheck @W64 @JUtils).  
    seq 13: (#pre). auto => />. move => &hr H. rewrite !validk_cat //=; 1:smt(@Jcheck @W64 @JUtils).  
    seq 19: (#pre). auto => />. move => &hr H. rewrite !validk_cat //=; 1:smt(@Jcheck @W64 @JUtils).  
    seq 23: (#pre). auto => />. move => &hr H. rewrite !validk_cat //=; 1:smt(@Jcheck @W64 @JUtils).  
    seq 35: (#pre). auto => />. move => &hr H. rewrite !validk_cat //=; 1:smt(@Jcheck @W64 @JUtils).  
    seq 10: (#pre). auto => />. move => &hr H. rewrite !validk_cat //=; 1:smt(@Jcheck @W64 @JUtils).  
    inline M.__reduce4. do 2! unroll for ^while. auto => />.
    move => &hr H. rewrite !/trace //= !validk_cat //=. move => H0 H1.
    rewrite !H1 !b2i0 => />. rewrite !valid_cat //=. smt(forall_validk_valid).
qed.

lemma __sqr4_rs_assume _xa :
      hoare [M.__sqr4_rs :
      (_xa = xa) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))))
       (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__sqr4_rs_assume_ _xa) (__sqr4_rs_valid_post _xa) => />.
qed .

(* All assert are valid. *)

lemma __reduce4_assert _z :
      hoare [M.__reduce4 :
      ((_z = z) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

lemma __sqr4_rs_assert _xa :
      hoare [M.__sqr4_rs :
      ((_xa = xa) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __reduce4_spec _z :
      hoare [M.__reduce4 :
      ((_z = z) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
      (single ((pow 2 255) - 19)))].
proof.
conseq (__reduce4_assume _z) (__reduce4_assert _z) => />.
smt (all_validk_valid).
qed .

lemma __sqr4_rs_spec _xa :
      hoare [M.__sqr4_rs :
      ((_xa = xa) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
conseq (__sqr4_rs_assume _xa) (__sqr4_rs_assert _xa) => />.
smt (all_validk_valid).
qed .

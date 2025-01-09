require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck.

from JazzEC require import Array4.

from JazzEC require import WArray32.

require import Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.

module M = {
  var tmp__trace : trace
  var tmp__data___add4_rrs : (W64.t Array4.t)
  var tmp____add4_rrs : W64.t Array4.t
  proc __add4_rrs (f:W64.t Array4.t, g:W64.t Array4.t) : ((W64.t Array4.t) *
                                                         trace) = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var h:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var z:W64.t;
    var cf:bool;
    var i:int;
    var carryo:bool;
    var  _0:bool;
    var old_g:W64.t Array4.t;
    var old_f:W64.t Array4.t;
    var trace___add4_rrs:trace;
    old_f <- f;
    old_g <- g;
    trace___add4_rrs <- [];
    h <- witness;
    (_of_, _cf_, _sf_,  _0, _zf_, z) <- (set0_64);
    h <- (copy_64 f);
    (aux, aux_0) <- (adc_64 h.[0] g.[0] false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (adc_64 h.[i] g.[i] cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    carryo <- cf;
    (cf, z) <- (sbb_64 z z cf);
    trace___add4_rrs <- (trace___add4_rrs ++ [(Assert, (cf = carryo))]);
    trace___add4_rrs <-
    (trace___add4_rrs ++ [(Assume, ((b2i cf) = (b2i carryo)))]);
    z <- (z `&` (W64.of_int 38));
    trace___add4_rrs <-
    (trace___add4_rrs ++
    [(Assert,
     (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))))]);
    trace___add4_rrs <-
    (trace___add4_rrs ++ [(Assume, ((u64i z) = ((b2i cf) * 38)))]);
    (aux, aux_0) <- (adc_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (adc_64 h.[i] (W64.of_int 0) cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    carryo <- cf;
    (cf, z) <- (sbb_64 z z cf);
    trace___add4_rrs <- (trace___add4_rrs ++ [(Assert, (cf = carryo))]);
    trace___add4_rrs <-
    (trace___add4_rrs ++ [(Assume, ((b2i cf) = (b2i carryo)))]);
    z <- (z `&` (W64.of_int 38));
    trace___add4_rrs <-
    (trace___add4_rrs ++
    [(Assert,
     (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))))]);
    trace___add4_rrs <-
    (trace___add4_rrs ++ [(Assume, ((u64i z) = ((b2i cf) * 38)))]);
    (aux, aux_0) <- (adc_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    trace___add4_rrs <- (trace___add4_rrs ++ [(Assert, (! cf))]);
    trace___add4_rrs <- (trace___add4_rrs ++ [(Assume, ((b2i cf) = 0))]);
    trace___add4_rrs <-
    (trace___add4_rrs ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_f.[ii]))) (iota_ 0 4))) +
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_g.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))]);
    return (h, trace___add4_rrs);
  }
}.

(* The post is in the trace. *)

lemma __add4_rrs_valid_post _f _g :
      hoare [M.__add4_rrs :
      ((_g = g) /\ (_f = f)) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> ((_g = old_g) /\ (_f = old_f))).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 4 : (((_g = old_g) /\ (_f = old_f))).
by auto.
do 2! unroll for ^while.
by conseq  />.
qed .

(* The post is in the trace and all assumes are valid. *)

lemma __add4_rrs_assume_ _f _g :
      hoare [M.__add4_rrs :
      ((_g = g) /\ (_f = f)) ==> (true => (validk Assume (trace res)))].
proof.
    proc. 
    wp -1 => /=. do 2! unroll for ^while. wp; skip => />. move => H. 
    do split. by rewrite H. move => H1. 
    do split. rewrite H. smt(JUtils.pow2_64 W64.to_uint_small). move => H2. 
    do split. rewrite H2. smt(JUtils.pow2_64 W64.to_uint_small). move => H3.
    smt(JUtils.pow2_64 W64.to_uint_small).
qed.

lemma __add4_rrs_assume _f _g :
      hoare [M.__add4_rrs :
      ((_g = g) /\ (_f = f)) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) +
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
       (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__add4_rrs_assume_ _f _g) (__add4_rrs_valid_post _f _g) => />.
qed .

(* All assert are valid. *)

lemma __add4_rrs_assert _f _g :
      hoare [M.__add4_rrs :
      (((_g = g) /\ (_f = f)) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __add4_rrs_spec _f _g :
      hoare [M.__add4_rrs :
      (((_g = g) /\ (_f = f)) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
conseq (__add4_rrs_assume _f _g) (__add4_rrs_assert _f _g) => />.
smt (all_validk_valid).
qed .


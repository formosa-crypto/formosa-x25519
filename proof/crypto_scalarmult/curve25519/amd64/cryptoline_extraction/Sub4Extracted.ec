require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck.

require import Array4.

require import WArray32.

require import Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.

module M = {
  var tmp__trace : trace
  var tmp__data___sub4_rrs : (W64.t Array4.t)
  var tmp____sub4_rrs : W64.t Array4.t
  proc __sub4_rrs (f:W64.t Array4.t, gs:W64.t Array4.t) : ((W64.t Array4.t) *
                                                          trace) = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var h:W64.t Array4.t;
    var z:W64.t;
    var cf:bool;
    var i:int;
    var borrowo:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var old_gs:W64.t Array4.t;
    var old_f:W64.t Array4.t;
    var trace___sub4_rrs:trace;
    old_f <- f;
    old_gs <- gs;
    trace___sub4_rrs <- [];
    h <- witness;
    ( _0,  _1,  _2,  _3,  _4, z) <- (set0_64);
    h <- (copy_64 f);
    (aux, aux_0) <- (sbb_64 h.[0] gs.[0] false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (sbb_64 h.[i] gs.[i] cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    borrowo <- cf;
    (cf, z) <- (sbb_64 z z cf);
    trace___sub4_rrs <- (trace___sub4_rrs ++ [(Assert, (cf = borrowo))]);
    trace___sub4_rrs <-
    (trace___sub4_rrs ++ [(Assume, ((b2i cf) = (b2i borrowo)))]);
    z <- (z `&` (W64.of_int 38));
    trace___sub4_rrs <-
    (trace___sub4_rrs ++
    [(Assert,
     (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))))]);
    trace___sub4_rrs <-
    (trace___sub4_rrs ++ [(Assume, ((u64i z) = ((b2i cf) * 38)))]);
    (aux, aux_0) <- (sbb_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (sbb_64 h.[i] (W64.of_int 0) cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    borrowo <- cf;
    (cf, z) <- (sbb_64 z z cf);
    trace___sub4_rrs <- (trace___sub4_rrs ++ [(Assert, (cf = borrowo))]);
    trace___sub4_rrs <-
    (trace___sub4_rrs ++ [(Assume, ((b2i cf) = (b2i borrowo)))]);
    z <- (z `&` (W64.of_int 38));
    trace___sub4_rrs <-
    (trace___sub4_rrs ++
    [(Assert,
     (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))))]);
    trace___sub4_rrs <-
    (trace___sub4_rrs ++ [(Assume, ((u64i z) = ((b2i cf) * 38)))]);
    (aux, aux_0) <- (sbb_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    trace___sub4_rrs <- (trace___sub4_rrs ++ [(Assert, (! cf))]);
    trace___sub4_rrs <- (trace___sub4_rrs ++ [(Assume, ((b2i cf) = 0))]);
    trace___sub4_rrs <-
    (trace___sub4_rrs ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_f.[ii]))) (iota_ 0 4))) -
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_gs.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))]);
    return (h, trace___sub4_rrs);
  }
}.

(* The post is in the trace. *)

lemma __sub4_rrs_valid_post _f _gs :
      hoare [M.__sub4_rrs :
      ((_gs = gs) /\ (_f = f)) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) -
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gs.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> ((_gs = old_gs) /\ (_f = old_f))).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 4 : (((_gs = old_gs) /\ (_f = old_f))).
by auto . 
do 2! unroll for ^while.
by conseq  />.
qed .

(* The post is in the trace and all assumes are valid. *)

lemma __sub4_rrs_assume_ _f _gs :
      hoare [M.__sub4_rrs :
      ((_gs = gs) /\ (_f = f)) ==> (true => (validk Assume (trace res)))].
proof.
    proc. 
    wp -1 => /=. do 2! unroll for ^while. wp; skip => />. move => H. 
    do split. by rewrite H. move => H1. 
    do split. rewrite H. smt(@W64 @JUtils). move => H2. 
    do split. rewrite H2. smt(@W64 @JUtils). move => H3.
    smt(@W64 @JUtils).
qed.

lemma __sub4_rrs_assume _f _gs :
      hoare [M.__sub4_rrs :
      ((_gs = gs) /\ (_f = f)) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) -
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gs.[ii]))) (iota_ 0 4))))
       (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__sub4_rrs_assume_ _f _gs) (__sub4_rrs_valid_post _f _gs) => />.
qed .

(* All assert are valid. *)

lemma __sub4_rrs_assert _f _gs :
      hoare [M.__sub4_rrs :
      (((_gs = gs) /\ (_f = f)) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __sub4_rrs_spec _f _gs :
      hoare [M.__sub4_rrs :
      (((_gs = gs) /\ (_f = f)) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) -
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gs.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
conseq (__sub4_rrs_assume _f _gs) (__sub4_rrs_assert _f _gs) => />.
smt (all_validk_valid).
qed .


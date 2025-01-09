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
  var tmp__data___mul4_a24_rs : (W64.t Array4.t)
  var tmp____mul4_a24_rs : W64.t Array4.t
  proc __mul4_a24_rs (xa:W64.t Array4.t) : ((W64.t Array4.t) * trace) = {
    var aux:bool;
    var aux_0:W64.t;
    var r:W64.t Array4.t;
    var c:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var t4:W64.t;
    var cf:bool;
    var dc:W64.t;
    var old_xa:W64.t Array4.t;
    var trace___mul4_a24_rs:trace;
    old_xa <- xa;
    trace___mul4_a24_rs <- [];
    r <- witness;
    c <- (W64.of_int 121665);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assert, (c = (W64.of_int 121665)))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, ((u64i c) = 121665))]);
    rax <- xa.[0];
    (rdx, rax) <- (mulu_64 rax c);
    r.[0] <- rax;
    r.[1] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax c);
    r.[2] <- rax;
    r.[3] <- rdx;
    rax <- xa.[1];
    (rdx, rax) <- (mulu_64 rax c);
    t1 <- rax;
    t2 <- rdx;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax c);
    t3 <- rax;
    t4 <- rdx;
    (aux, aux_0) <- (adc_64 r.[1] t1 false);
    cf <- aux;
    r.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[2] t2 cf);
    cf <- aux;
    r.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[3] t3 cf);
    cf <- aux;
    r.[3] <- aux_0;
    (cf, t4) <- (adc_64 t4 (W64.of_int 0) cf);
    trace___mul4_a24_rs <- (trace___mul4_a24_rs ++ [(Assert, (! cf))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, ((b2i cf) = 0))]);
    (dc, t4) <- (mulu_64 t4 (W64.of_int 38));
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assert, (dc = (W64.of_int 0)))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, (dc = (W64.of_int 0)))]);
    (aux, aux_0) <- (adc_64 r.[0] t4 false);
    cf <- aux;
    r.[0] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[1] (W64.of_int 0) cf);
    cf <- aux;
    r.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[2] (W64.of_int 0) cf);
    cf <- aux;
    r.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[3] (W64.of_int 0) cf);
    cf <- aux;
    r.[3] <- aux_0;
    t1 <- (W64.of_int 38);
    t2 <- (MOV_64 (W64.of_int 0));
    t1 <- ((! cf) ? t2 : t1);
    (aux, aux_0) <- (adc_64 r.[0] t1 false);
    cf <- aux;
    r.[0] <- aux_0;
    trace___mul4_a24_rs <- (trace___mul4_a24_rs ++ [(Assert, (! cf))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, ((b2i cf) = 0))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i r.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_xa.[ii]))) (iota_ 0 4))) *
     121665) (single ((pow 2 255) - 19))))]);
    return (r, trace___mul4_a24_rs);
  }
}.

(* The post is in the trace. *)

lemma __mul4_a24_rs_valid_post _xa :
      hoare [M.__mul4_a24_rs :
      (_xa = xa) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19))))].
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

lemma __mul4_a24_rs_assume_ _xa :
      hoare [M.__mul4_a24_rs :
      (_xa = xa) ==> (true => (validk Assume (trace res)))].
proof.
    proc. auto => />.
qed.

lemma __mul4_a24_rs_assume _xa :
      hoare [M.__mul4_a24_rs :
      (_xa = xa) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
       121665) (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__mul4_a24_rs_assume_ _xa) (__mul4_a24_rs_valid_post _xa) => />.
qed .

(* All assert are valid. *)

lemma __mul4_a24_rs_assert _xa :
      hoare [M.__mul4_a24_rs :
      ((_xa = xa) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __mul4_a24_rs_spec _xa :
      hoare [M.__mul4_a24_rs :
      ((_xa = xa) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19)))].
proof.
conseq (__mul4_a24_rs_assume _xa) (__mul4_a24_rs_assert _xa) => />.
smt (all_validk_valid).
qed .


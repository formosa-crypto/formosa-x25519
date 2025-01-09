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
  proc __mul4_a24_rs (fs:W64.t Array4.t) : ((W64.t Array4.t) * trace) = {
    var aux_1:bool;
    var aux_0:W64.t;
    var aux:W64.t;
    var h:W64.t Array4.t;
    var c:W64.t;
    var lo:W64.t;
    var cf:bool;
    var r0:W64.t;
    var carryo:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var old_fs:W64.t Array4.t;
    var trace___mul4_a24_rs:trace;
    old_fs <- fs;
    trace___mul4_a24_rs <- [];
    h <- witness;
    c <- (W64.of_int 121665);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assert, (c = (W64.of_int 121665)))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, ((u64i c) = 121665))]);
    (aux_0, aux) <- (MULX_64 c fs.[0]);
    h.[1] <- aux_0;
    h.[0] <- aux;
    (aux_0, aux) <- (MULX_64 c fs.[1]);
    h.[2] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (adc_64 h.[1] lo false);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_0, aux) <- (MULX_64 c fs.[2]);
    h.[3] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (adc_64 h.[2] lo cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (r0, lo) <- (MULX_64 c fs.[3]);
    (aux_1, aux_0) <- (adc_64 h.[3] lo cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    (cf, r0) <- (adc_64 r0 (W64.of_int 0) cf);
    ( _0,  _1,  _2,  _3,  _4, r0) <- (IMULri_64 r0 (W64.of_int 38));
    trace___mul4_a24_rs <- (trace___mul4_a24_rs ++ [(Assert, (! cf))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, ((b2i cf) = 0))]);
    (aux_1, aux_0) <- (adc_64 h.[0] r0 false);
    cf <- aux_1;
    h.[0] <- aux_0;
    (aux_1, aux_0) <- (adc_64 h.[1] (W64.of_int 0) cf);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_1, aux_0) <- (adc_64 h.[2] (W64.of_int 0) cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_1, aux_0) <- (adc_64 h.[3] (W64.of_int 0) cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    carryo <- cf;
    (cf, c) <- (sbb_64 c c cf);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assert, (cf = carryo))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, ((b2i cf) = (b2i carryo)))]);
    c <- (c `&` (W64.of_int 38));
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++
    [(Assert,
     (((! cf) /\ (c = (W64.of_int 0))) \/ (cf /\ (c = (W64.of_int 38)))))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, ((u64i c) = ((b2i cf) * 38)))]);
    (aux_1, aux_0) <- (adc_64 h.[0] c false);
    cf <- aux_1;
    h.[0] <- aux_0;
    trace___mul4_a24_rs <- (trace___mul4_a24_rs ++ [(Assert, (! cf))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++ [(Assume, ((b2i cf) = 0))]);
    trace___mul4_a24_rs <-
    (trace___mul4_a24_rs ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_fs.[ii]))) (iota_ 0 4))) *
     121665) (single ((pow 2 255) - 19))))]);
    return (h, trace___mul4_a24_rs);
  }
}.

(* The post is in the trace. *)

lemma __mul4_a24_rs_valid_post _fs :
      hoare [M.__mul4_a24_rs :
      (_fs = fs) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> (_fs = old_fs)).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 1 : ((_fs = old_fs)).
by auto .
by conseq  />.
qed .

(* The post is in the trace and all assumes are valid. *)

lemma __mul4_a24_rs_assume_ _fs :
      hoare [M.__mul4_a24_rs :
      (_fs = fs) ==> (true => (validk Assume (trace res)))].
proof.
    proc. auto => />. smt(@Zp_25519 @JUtils @W64 @Jcheck).
qed.

lemma __mul4_a24_rs_assume _fs :
      hoare [M.__mul4_a24_rs :
      (_fs = fs) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
       121665) (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__mul4_a24_rs_assume_ _fs) (__mul4_a24_rs_valid_post _fs) => />.
qed .

(* All assert are valid. *)

lemma __mul4_a24_rs_assert _fs :
      hoare [M.__mul4_a24_rs :
      ((_fs = fs) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __mul4_a24_rs_spec _fs :
      hoare [M.__mul4_a24_rs :
      ((_fs = fs) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19)))].
proof.
conseq (__mul4_a24_rs_assume _fs) (__mul4_a24_rs_assert _fs) => />.
smt (all_validk_valid).
qed .


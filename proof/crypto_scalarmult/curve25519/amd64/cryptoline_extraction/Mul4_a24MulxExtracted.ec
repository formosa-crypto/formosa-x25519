require import Int AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Jcheck.

require import Array4.

require import WArray32.

require import Jcheck Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.

module M = {
  var tmp__check : to_check
  var tmp__data___mul4_a24_rs : (W64.t Array4.t)
  var tmp____mul4_a24_rs : W64.t Array4.t
  proc __mul4_a24_rs (fs:W64.t Array4.t) : ((W64.t Array4.t) * to_check) = {
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
    var assume___mul4_a24_rs:bool;
    var assert___mul4_a24_rs:bool;
    var assume_proof___mul4_a24_rs:bool;
    var assert_proof___mul4_a24_rs:bool;
    assume___mul4_a24_rs <- true;
    assert___mul4_a24_rs <- true;
    assume_proof___mul4_a24_rs <- true;
    assert_proof___mul4_a24_rs <- assert___mul4_a24_rs;
    h <- witness;
    c <- (W64.of_int 121665);
    assert_proof___mul4_a24_rs <-
    (assert_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) =>
    (c = (W64.of_int 121665))));
    assert___mul4_a24_rs <-
    (assert___mul4_a24_rs /\ (c = (W64.of_int 121665)));
    assume_proof___mul4_a24_rs <-
    (assume_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => ((u64i c) = 121665)));
    assume___mul4_a24_rs <- (assume___mul4_a24_rs /\ ((u64i c) = 121665));
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
    assert_proof___mul4_a24_rs <-
    (assert_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => (! cf)));
    assert___mul4_a24_rs <- (assert___mul4_a24_rs /\ (! cf));
    assume_proof___mul4_a24_rs <-
    (assume_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => ((b2i cf) = 0)));
    assume___mul4_a24_rs <- (assume___mul4_a24_rs /\ ((b2i cf) = 0));
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
    assert_proof___mul4_a24_rs <-
    (assert_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => (cf = carryo)));
    assert___mul4_a24_rs <- (assert___mul4_a24_rs /\ (cf = carryo));
    assume_proof___mul4_a24_rs <-
    (assume_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) =>
    ((b2i cf) = (b2i carryo))));
    assume___mul4_a24_rs <-
    (assume___mul4_a24_rs /\ ((b2i cf) = (b2i carryo)));
    c <- (c `&` (W64.of_int 38));
    assert_proof___mul4_a24_rs <-
    (assert_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) =>
    (((! cf) /\ (c = (W64.of_int 0))) \/ (cf /\ (c = (W64.of_int 38))))));
    assert___mul4_a24_rs <-
    (assert___mul4_a24_rs /\
    (((! cf) /\ (c = (W64.of_int 0))) \/ (cf /\ (c = (W64.of_int 38)))));
    assume_proof___mul4_a24_rs <-
    (assume_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) =>
    ((u64i c) = ((b2i cf) * 38))));
    assume___mul4_a24_rs <-
    (assume___mul4_a24_rs /\ ((u64i c) = ((b2i cf) * 38)));
    (aux_1, aux_0) <- (adc_64 h.[0] c false);
    cf <- aux_1;
    h.[0] <- aux_0;
    assert_proof___mul4_a24_rs <-
    (assert_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => (! cf)));
    assert___mul4_a24_rs <- (assert___mul4_a24_rs /\ (! cf));
    assume_proof___mul4_a24_rs <-
    (assume_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => ((b2i cf) = 0)));
    assume___mul4_a24_rs <- (assume___mul4_a24_rs /\ ((b2i cf) = 0));
    return (h,
           (assume___mul4_a24_rs, assert___mul4_a24_rs,
           assume_proof___mul4_a24_rs, assert_proof___mul4_a24_rs));
  }
}.

(* All assume are valid. *)

lemma __mul4_a24_rs_assume  :
      hoare [M.__mul4_a24_rs : true ==> (assume_proof_ res)].
proof.
    proc. 
    seq 32 : (assume_proof__ (assume___mul4_a24_rs, assert___mul4_a24_rs, assume_proof___mul4_a24_rs, assert_proof___mul4_a24_rs)). auto => />. 
    seq 18 : (assume_proof__ (assume___mul4_a24_rs, assert___mul4_a24_rs, assume_proof___mul4_a24_rs, assert_proof___mul4_a24_rs)). auto => />.
    auto => />. move => &hr H H0 H1 H2.
    smt(@W64 @JUtils).
qed.

(* Soundness of assert/assume. *)

lemma __mul4_a24_rs_assert_assume_sound  :
      hoare [M.__mul4_a24_rs : true ==> (soundness_ res)].
proof.
    proc.
    seq 10 : (soundness__ (assume___mul4_a24_rs, assert___mul4_a24_rs, assume_proof___mul4_a24_rs, assert_proof___mul4_a24_rs)). auto => />. 
    seq 25 : (soundness__ (assume___mul4_a24_rs, assert___mul4_a24_rs, assume_proof___mul4_a24_rs, assert_proof___mul4_a24_rs)). auto => />. smt().
    seq 23 : (soundness__ (assume___mul4_a24_rs, assert___mul4_a24_rs, assume_proof___mul4_a24_rs, assert_proof___mul4_a24_rs)). auto => />. smt().
    auto => />. smt(). 
qed.

(* Lemmas proved by cryptoline. *)

axiom __mul4_a24_rs_assert _fs :
      hoare [M.__mul4_a24_rs :
      ((_fs = fs) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19))))].

(* Final specification for the functions. *)

lemma __mul4_a24_rs_spec  :
      forall _fs,
      hoare [M.__mul4_a24_rs :
      ((_fs = fs) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19)))].
proof.
move => _fs.
have h  :
     hoare [M.__mul4_a24_rs :
     ((_fs = fs) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
     121665) (single ((pow 2 255) - 19))))].
by conseq __mul4_a24_rs_assume (__mul4_a24_rs_assert _fs).
conseq h __mul4_a24_rs_assert_assume_sound => // ; smt ().
qed .


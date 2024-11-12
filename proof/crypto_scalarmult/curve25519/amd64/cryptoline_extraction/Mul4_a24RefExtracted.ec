require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Jcheck.

require import Array4.

require import WArray32.


require import WArray32 WArray64.
require import Jcheck Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.


module M = {
  var tmp__check : to_check
  var tmp__data___mul4_a24_rs : (W64.t Array4.t)
  var tmp____mul4_a24_rs : W64.t Array4.t
  proc __mul4_a24_rs (xa:W64.t Array4.t) : ((W64.t Array4.t) * to_check) = {
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
    var assume___mul4_a24_rs:bool;
    var assert___mul4_a24_rs:bool;
    var assume_proof___mul4_a24_rs:bool;
    var assert_proof___mul4_a24_rs:bool;
    assume___mul4_a24_rs <- true;
    assert___mul4_a24_rs <- true;
    assume_proof___mul4_a24_rs <- true;
    assert_proof___mul4_a24_rs <- assert___mul4_a24_rs;
    r <- witness;
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
    assert_proof___mul4_a24_rs <-
    (assert_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => (! cf)));
    assert___mul4_a24_rs <- (assert___mul4_a24_rs /\ (! cf));
    assume_proof___mul4_a24_rs <-
    (assume_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => ((b2i cf) = 0)));
    assume___mul4_a24_rs <- (assume___mul4_a24_rs /\ ((b2i cf) = 0));
    (dc, t4) <- (mulu_64 t4 (W64.of_int 38));
    assert_proof___mul4_a24_rs <-
    (assert_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => (dc = (W64.of_int 0))));
    assert___mul4_a24_rs <- (assert___mul4_a24_rs /\ (dc = (W64.of_int 0)));
    assume_proof___mul4_a24_rs <-
    (assume_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => (dc = (W64.of_int 0))));
    assume___mul4_a24_rs <- (assume___mul4_a24_rs /\ (dc = (W64.of_int 0)));
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
    assert_proof___mul4_a24_rs <-
    (assert_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => (! cf)));
    assert___mul4_a24_rs <- (assert___mul4_a24_rs /\ (! cf));
    assume_proof___mul4_a24_rs <-
    (assume_proof___mul4_a24_rs /\
    ((assert___mul4_a24_rs /\ assume___mul4_a24_rs) => ((b2i cf) = 0)));
    assume___mul4_a24_rs <- (assume___mul4_a24_rs /\ ((b2i cf) = 0));
    return (r,
           (assume___mul4_a24_rs, assert___mul4_a24_rs,
           assume_proof___mul4_a24_rs, assert_proof___mul4_a24_rs));
  }
}.

(* All assume are valid. *)

lemma __mul4_a24_rs_assume  :
      hoare [M.__mul4_a24_rs : true ==> (assume_proof_ res)].
proof.
    proc. auto => />.
qed.

(* Soundness of assert/assume. *)

lemma __mul4_a24_rs_assert_assume_sound  :
      hoare [M.__mul4_a24_rs : true ==> (soundness_ res)].
proof.
    proc. auto => />. smt(@W64 @Zp_25519).
qed.

(* Lemmas proved by cryptoline. *)

axiom __mul4_a24_rs_assert _xa :
      hoare [M.__mul4_a24_rs :
      ((_xa = xa) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19))))].

(* Final specification for the functions. *)

lemma __mul4_a24_rs_spec  :
      forall _xa,
      hoare [M.__mul4_a24_rs :
      ((_xa = xa) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      121665) (single ((pow 2 255) - 19)))].
proof.
move => _xa.
have h  :
     hoare [M.__mul4_a24_rs :
     ((_xa = xa) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
     121665) (single ((pow 2 255) - 19))))].
by conseq __mul4_a24_rs_assume (__mul4_a24_rs_assert _xa).
conseq h __mul4_a24_rs_assert_assume_sound => // ; smt ().
qed .


lemma mul4_a24_equiv_contract (xa h: Rep4) :
      inzpRep4 h = inzp (valRep4 xa * 121665) <=>       
       (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i xa.[ii]))) (iota_ 0 4))) *
     121665) (single ((pow 2 255) - 19))).
proof.      
      rewrite -!limbs_are_same.
      rewrite !inzpRep4E !/inzp. smt(@Zp_25519).      
qed.

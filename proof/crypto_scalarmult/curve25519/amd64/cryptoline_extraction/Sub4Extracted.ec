require import AllCore Int IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

require import Jcheck Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.


import SLH64.

require import Jcheck.

require import Array4.

require import WArray32.

module M = {
  var tmp__check : to_check
  var tmp__data___sub4_rrs : (W64.t Array4.t)
  var tmp____sub4_rrs : W64.t Array4.t
  proc __sub4_rrs (f:W64.t Array4.t, gs:W64.t Array4.t) : ((W64.t Array4.t) *
                                                          to_check) = {
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
    var assume___sub4_rrs:bool;
    var assert___sub4_rrs:bool;
    var assume_proof___sub4_rrs:bool;
    var assert_proof___sub4_rrs:bool;
    assume___sub4_rrs <- true;
    assert___sub4_rrs <- true;
    assume_proof___sub4_rrs <- true;
    assert_proof___sub4_rrs <- assert___sub4_rrs;
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
    assert_proof___sub4_rrs <-
    (assert_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) => (cf = borrowo)));
    assert___sub4_rrs <- (assert___sub4_rrs /\ (cf = borrowo));
    assume_proof___sub4_rrs <-
    (assume_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) => ((b2i cf) = (b2i borrowo))));
    assume___sub4_rrs <- (assume___sub4_rrs /\ ((b2i cf) = (b2i borrowo)));
    z <- (z `&` (W64.of_int 38));
    assert_proof___sub4_rrs <-
    (assert_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) =>
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38))))));
    assert___sub4_rrs <-
    (assert___sub4_rrs /\
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))));
    assume_proof___sub4_rrs <-
    (assume_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) =>
    ((u64i z) = ((b2i cf) * 38))));
    assume___sub4_rrs <- (assume___sub4_rrs /\ ((u64i z) = ((b2i cf) * 38)));
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
    assert_proof___sub4_rrs <-
    (assert_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) => (cf = borrowo)));
    assert___sub4_rrs <- (assert___sub4_rrs /\ (cf = borrowo));
    assume_proof___sub4_rrs <-
    (assume_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) => ((b2i cf) = (b2i borrowo))));
    assume___sub4_rrs <- (assume___sub4_rrs /\ ((b2i cf) = (b2i borrowo)));
    z <- (z `&` (W64.of_int 38));
    assert_proof___sub4_rrs <-
    (assert_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) =>
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38))))));
    assert___sub4_rrs <-
    (assert___sub4_rrs /\
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))));
    assume_proof___sub4_rrs <-
    (assume_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) =>
    ((u64i z) = ((b2i cf) * 38))));
    assume___sub4_rrs <- (assume___sub4_rrs /\ ((u64i z) = ((b2i cf) * 38)));
    (aux, aux_0) <- (sbb_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    assert_proof___sub4_rrs <-
    (assert_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) => (! cf)));
    assert___sub4_rrs <- (assert___sub4_rrs /\ (! cf));
    assume_proof___sub4_rrs <-
    (assume_proof___sub4_rrs /\
    ((assert___sub4_rrs /\ assume___sub4_rrs) => ((b2i cf) = 0)));
    assume___sub4_rrs <- (assume___sub4_rrs /\ ((b2i cf) = 0));
    return (h, (assume___sub4_rrs, assert___sub4_rrs, assume_proof___sub4_rrs, assert_proof___sub4_rrs));
  }
}.


(* All assume are valid. *)

lemma __sub4_rrs_assume  :
      hoare [M.__sub4_rrs : true ==> (assume_proof_ res)].
proof.
    proc. do 2! unroll for ^while.
    wp; skip => />. move => &hr.
    smt(@W64 @JUtils).
qed.

(* Soundness of assert/assume. *)

lemma __sub4_rrs_assert_assume_sound  :
      hoare [M.__sub4_rrs : true ==> (soundness_ res)].
proof.
    proc. do 2! unroll for ^while.
    wp; skip => />. move => &hr.
    smt(@W64 @JUtils). 
qed.

(* Lemmas proved by cryptoline. *)

axiom __sub4_rrs_assert _f _gs :
      hoare [M.__sub4_rrs :
      (((_gs = gs) /\ (_f = f)) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) -
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gs.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].

(* Final specification for the functions. *)

lemma __sub4_rrs_spec  :
      forall _f _gs,
      hoare [M.__sub4_rrs :
      (((_gs = gs) /\ (_f = f)) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) -
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gs.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
move => _f _gs.
have h  :
     hoare [M.__sub4_rrs :
     (((_gs = gs) /\ (_f = f)) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) -
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i _gs.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))].
by conseq __sub4_rrs_assume (__sub4_rrs_assert _f _gs).
conseq h __sub4_rrs_assert_assume_sound => // ; smt ().
qed .


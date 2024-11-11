require import AllCore Int IntDiv CoreMap List Distr. (* useful to include Int import *)

from Jasmin require import JModel_x86.

import SLH64.

require import Jcheck Ref4_scalarmult_s Zp_limbs Zp_25519.
import Zp_25519 Zp Zp_limbs EClib.

require import WArray32.

require import Array4.

(* Need to be put into the Jcheck file *)

(* Includes add4.jazz formosa-25519 extraction *)

module MAdd = {

  var tmp__check : to_check
  var tmp__data___add4_rrs : (W64.t Array4.t)
  var tmp____add4_rrs : W64.t Array4.t
  proc __add4_rrs (f:W64.t Array4.t, g:W64.t Array4.t) : ((W64.t Array4.t) *
                                                         to_check) = {
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
    var assume___add4_rrs:bool;
    var assert___add4_rrs:bool;
    var assume_proof___add4_rrs:bool;
    var assert_proof___add4_rrs:bool;
    assume___add4_rrs <- true;
    assert___add4_rrs <- true;
    assume_proof___add4_rrs <- true;
    assert_proof___add4_rrs <- assert___add4_rrs;
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
    assert_proof___add4_rrs <-
    (assert_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) => (cf = carryo)));
    assert___add4_rrs <- (assert___add4_rrs /\ (cf = carryo));
    assume_proof___add4_rrs <-
    (assume_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) => ((b2i cf) = (b2i carryo))));
    assume___add4_rrs <- (assume___add4_rrs /\ ((b2i cf) = (b2i carryo)));
    z <- (z `&` (W64.of_int 38));
    assert_proof___add4_rrs <-
    (assert_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) =>
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38))))));
    assert___add4_rrs <-
    (assert___add4_rrs /\
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))));
    assume_proof___add4_rrs <-
    (assume_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) =>
    ((u64i z) = ((b2i cf) * 38))));
    assume___add4_rrs <- (assume___add4_rrs /\ ((u64i z) = ((b2i cf) * 38)));
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
    assert_proof___add4_rrs <-
    (assert_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) => (cf = carryo)));
    assert___add4_rrs <- (assert___add4_rrs /\ (cf = carryo));
    assume_proof___add4_rrs <-
    (assume_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) => ((b2i cf) = (b2i carryo))));
    assume___add4_rrs <- (assume___add4_rrs /\ ((b2i cf) = (b2i carryo)));
    z <- (z `&` (W64.of_int 38));
    assert_proof___add4_rrs <-
    (assert_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) =>
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38))))));
    assert___add4_rrs <-
    (assert___add4_rrs /\
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))));
    assume_proof___add4_rrs <-
    (assume_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) =>
    ((u64i z) = ((b2i cf) * 38))));
    assume___add4_rrs <- (assume___add4_rrs /\ ((u64i z) = ((b2i cf) * 38)));
    (aux, aux_0) <- (adc_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    assert_proof___add4_rrs <-
    (assert_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) => (! cf)));
    assert___add4_rrs <- (assert___add4_rrs /\ (! cf));
    assume_proof___add4_rrs <-
    (assume_proof___add4_rrs /\
    ((assert___add4_rrs /\ assume___add4_rrs) => ((b2i cf) = 0)));
    assume___add4_rrs <- (assume___add4_rrs /\ ((b2i cf) = 0));
    return (h, (assume___add4_rrs, assert___add4_rrs, assume_proof___add4_rrs, assert_proof___add4_rrs));
  }
}.

(* All assume are valid. *)

lemma __add4_rrs_assume  :
      hoare [MAdd.__add4_rrs : true ==> (assume_proof_ res)].
proof.
    proc. do 2! unroll for ^while.
    wp; skip => />. move => &hr.
    smt(@W64 @JUtils).
qed.

(* Soundness of assert/assume. *)

lemma __add4_rrs_assert_assume_sound  :
      hoare [MAdd.__add4_rrs : true ==> (soundness_ res)].
proof.
    proc.
    do 2! unroll for ^while.
    wp; skip => />. move => &hr.
    smt(@W64 @JUtils).
qed.

(* Lemmas proved by cryptoline. *)

axiom __add4_rrs_assert (_f  _g: W64.t Array4.t ) :
      hoare [MAdd.__add4_rrs :
      (((_g = g) /\ (_f = f)) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0 (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].

(* Final specification for the functions. *)

lemma __add4_rrs_spec  :
      forall _f _g, hoare [MAdd.__add4_rrs :
      (((_g = g) /\ (_f = f)) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.                     
move => _f _g.
have h  :
     hoare [MAdd.__add4_rrs :
     (((_g = g) /\ (_f = f)) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) +
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))].
by conseq __add4_rrs_assume (__add4_rrs_assert _f _g).
conseq h __add4_rrs_assert_assume_sound => // ; smt ().
qed.

lemma limbs_are_same (f : Rep4) :
    valRep4 f = (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i f.[ii]))) (iota_ 0 4))).
proof.
    rewrite valRep4E /val_digits. 
    rewrite /to_list /mkseq -iotaredE => />. 
    smt().
qed.

lemma inzp_limbs_are_same (f : Rep4) :
    inzpRep4 f = inzp (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i f.[ii]))) (iota_ 0 4))).
proof.
    rewrite inzpRep4E; congr. apply limbs_are_same. 
qed.

lemma add4_equiv_contract (f g h: Rep4) :
      inzpRep4 h = inzpRep4 f + inzpRep4 g <=>       
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i f.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))).
proof.
      split.
      rewrite -!limbs_are_same.
      rewrite inzpRep4E /inzp. smt(@Zp_25519).
      rewrite -!limbs_are_same.
      rewrite inzpRep4E /inzp. smt(@Zp_25519).
qed.


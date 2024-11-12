require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Jcheck.

require import Array4 Array5 Array8.

require import WArray32 WArray40 WArray64.


require import WArray32 WArray64.
require import Jcheck Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.

module M = {
  var tmp__check : to_check
  var tmp__data___reduce4 : (W64.t Array4.t)
  var tmp____reduce4 : W64.t Array4.t
  var tmp__data___sqr4_rs : (W64.t Array4.t)
  var tmp____sqr4_rs : W64.t Array4.t
  proc __reduce4 (z:W64.t Array8.t) : ((W64.t Array4.t) * to_check) = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var r:W64.t Array4.t;
    var r38:W64.t;
    var rax:W64.t;
    var h:W64.t;
    var l:W64.t;
    var cf:bool;
    var z8:W64.t;
    var i:int;
    var dc:W64.t;
    var r0:W64.t;
    var assume___reduce4:bool;
    var assert___reduce4:bool;
    var assume_proof___reduce4:bool;
    var assert_proof___reduce4:bool;
    assume___reduce4 <- true;
    assert___reduce4 <- true;
    assume_proof___reduce4 <- true;
    assert_proof___reduce4 <- assert___reduce4;
    r <- witness;
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
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! cf)));
    assert___reduce4 <- (assert___reduce4 /\ (! cf));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = 0));
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[2] l false);
    cf <- aux;
    r.[2] <- aux_0;
    r.[3] <- (MOV_64 (W64.of_int 0));
    rax <- z.[7];
    (aux, aux_0) <- (adc_64 r.[3] h cf);
    cf <- aux;
    r.[3] <- aux_0;
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! cf)));
    assert___reduce4 <- (assert___reduce4 /\ (! cf));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = 0));
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[3] l false);
    cf <- aux;
    r.[3] <- aux_0;
    z8 <- (MOV_64 (W64.of_int 0));
    (cf, z8) <- (adc_64 z8 h cf);
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! cf)));
    assert___reduce4 <- (assert___reduce4 /\ (! cf));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = 0));
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
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! cf)));
    assert___reduce4 <- (assert___reduce4 /\ (! cf));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = 0));
    (dc, z8) <- (mulu_64 z8 (W64.of_int 38));
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (dc = (W64.of_int 0))));
    assert___reduce4 <- (assert___reduce4 /\ (dc = (W64.of_int 0)));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (dc = (W64.of_int 0))));
    assume___reduce4 <- (assume___reduce4 /\ (dc = (W64.of_int 0)));
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
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! cf)));
    assert___reduce4 <- (assert___reduce4 /\ (! cf));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = 0));
    (dc, r0) <- (mulu_64 r0 (W64.of_int 38));
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (dc = (W64.of_int 0))));
    assert___reduce4 <- (assert___reduce4 /\ (dc = (W64.of_int 0)));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (dc = (W64.of_int 0))));
    assume___reduce4 <- (assume___reduce4 /\ (dc = (W64.of_int 0)));
    (aux, aux_0) <- (adc_64 r.[0] r0 false);
    cf <- aux;
    r.[0] <- aux_0;
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! cf)));
    assert___reduce4 <- (assert___reduce4 /\ (! cf));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = 0));
    return (r,
           (assume___reduce4, assert___reduce4, assume_proof___reduce4,
           assert_proof___reduce4));
  }
  proc __sqr4_rs (xa:W64.t Array4.t) : ((W64.t Array4.t) * to_check) = {
    var aux:bool;
    var aux_0:W64.t;
    var r:W64.t Array4.t;
    var z:W64.t Array8.t;
    var zero:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var cf:bool;
    var t:W64.t Array5.t;
    var assume___sqr4_rs:bool;
    var assert___sqr4_rs:bool;
    var assume_proof___sqr4_rs:bool;
    var assert_proof___sqr4_rs:bool;
    assume___sqr4_rs <- true;
    assert___sqr4_rs <- true;
    assume_proof___sqr4_rs <- true;
    assert_proof___sqr4_rs <- assert___sqr4_rs;
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
    assert_proof___sqr4_rs <-
    (assert_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => (! cf)));
    assert___sqr4_rs <- (assert___sqr4_rs /\ (! cf));
    assume_proof___sqr4_rs <-
    (assume_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => ((b2i cf) = 0)));
    assume___sqr4_rs <- (assume___sqr4_rs /\ ((b2i cf) = 0));
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
    assert_proof___sqr4_rs <-
    (assert_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => (! cf)));
    assert___sqr4_rs <- (assert___sqr4_rs /\ (! cf));
    assume_proof___sqr4_rs <-
    (assume_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => ((b2i cf) = 0)));
    assume___sqr4_rs <- (assume___sqr4_rs /\ ((b2i cf) = 0));
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
    assert_proof___sqr4_rs <-
    (assert_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => (! cf)));
    assert___sqr4_rs <- (assert___sqr4_rs /\ (! cf));
    assume_proof___sqr4_rs <-
    (assume_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => ((b2i cf) = 0)));
    assume___sqr4_rs <- (assume___sqr4_rs /\ ((b2i cf) = 0));
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
    assert_proof___sqr4_rs <-
    (assert_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => (! cf)));
    assert___sqr4_rs <- (assert___sqr4_rs /\ (! cf));
    assume_proof___sqr4_rs <-
    (assume_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => ((b2i cf) = 0)));
    assume___sqr4_rs <- (assume___sqr4_rs /\ ((b2i cf) = 0));
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
    assert_proof___sqr4_rs <-
    (assert_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => (! cf)));
    assert___sqr4_rs <- (assert___sqr4_rs /\ (! cf));
    assume_proof___sqr4_rs <-
    (assume_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => ((b2i cf) = 0)));
    assume___sqr4_rs <- (assume___sqr4_rs /\ ((b2i cf) = 0));
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[3]);
    (aux, aux_0) <- (adc_64 z.[6] rax false);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] rdx cf);
    cf <- aux;
    z.[7] <- aux_0;
    assert_proof___sqr4_rs <-
    (assert_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => (! cf)));
    assert___sqr4_rs <- (assert___sqr4_rs /\ (! cf));
    assume_proof___sqr4_rs <-
    (assume_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) => ((b2i cf) = 0)));
    assume___sqr4_rs <- (assume___sqr4_rs /\ ((b2i cf) = 0));
    (tmp__data___reduce4, tmp__check) <@ __reduce4 (z);
    tmp____reduce4 <- tmp__data___reduce4;
    (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs,
    assert_proof___sqr4_rs) <-
    (upd_call
    (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs,
    assert_proof___sqr4_rs) tmp__check);
    assert_proof___sqr4_rs <-
    (assert_proof___sqr4_rs /\
    ((assert___sqr4_rs /\ assume___sqr4_rs) =>
    (eqmod
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
    (iota_ 0 4)))
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i z.[ii]))) (iota_ 0 8)))
    (single ((pow 2 255) - 19)))));
    assert___sqr4_rs <-
    (assert___sqr4_rs /\
    (eqmod
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
    (iota_ 0 4)))
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i z.[ii]))) (iota_ 0 8)))
    (single ((pow 2 255) - 19))));
    r <- tmp____reduce4;
    return (r,
           (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs,
           assert_proof___sqr4_rs));
  }
}.

(* All assume are valid. *)

lemma __reduce4_assume  : hoare [M.__reduce4 : true ==> (assume_proof_ res)].
proof.
    proc. 
     seq 21 : (assume_proof__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />.
     seq 13 : (assume_proof__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />.
     seq 16 : (assume_proof__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />.
     seq 12 : (assume_proof__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. auto => />.
     seq 7 : (assume_proof__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. auto => />.
     auto => />.
qed.

lemma __sqr4_rs_assume  : hoare [M.__sqr4_rs : true ==> (assume_proof_ res)].
proof.
    proc. wp.
    call __reduce4_assume.
    seq 32: ( assume_proof__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />.
    seq 15: ( assume_proof__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />.
    seq 21: ( assume_proof__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />.
    seq 25: ( assume_proof__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />.
    seq 38: ( assume_proof__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />.
    seq 15: ( assume_proof__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />. auto => />.
qed.

(* Soundness of assert/assume. *)

lemma __reduce4_assert_assume_sound  :
      hoare [M.__reduce4 : true ==> (soundness_ res)].
proof.
    proc.
    seq 20: ( soundness__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />.
    seq 18: ( soundness__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. smt().
    seq 12: ( soundness__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. smt(). 
    seq 3: ( soundness__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. auto => />.
    seq 13: ( soundness__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. smt().
    seq 3: ( soundness__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. auto => />.
    auto => />. smt().
qed.

lemma __sqr4_rs_assert_assume_sound  :
      hoare [M.__sqr4_rs : true ==> (soundness_ res)].
proof.
    proc. wp.
    call __reduce4_assert_assume_sound.
    seq 32: ( soundness__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />.
    seq 15: ( soundness__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />. smt().
    seq 21: ( soundness__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />. smt().
    seq 25: ( soundness__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />. smt().
    seq 37: ( soundness__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />. smt().
    seq 16: ( soundness__ (assume___sqr4_rs, assert___sqr4_rs, assume_proof___sqr4_rs, assert_proof___sqr4_rs)). auto => />. smt().
    wp. skip. auto => />. smt(). 
qed.
(* Lemmas proved by cryptoline. *)

axiom __reduce4_assert _z :
      hoare [M.__reduce4 :
      ((_z = z) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
      (single ((pow 2 255) - 19))))].

axiom __sqr4_rs_assert _xa :
      hoare [M.__sqr4_rs :
      ((_xa = xa) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].

(* Final specification for the functions. *)

lemma __reduce4_spec  :
      forall _z,
      hoare [M.__reduce4 :
      ((_z = z) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
      (single ((pow 2 255) - 19)))].
proof.
move => _z.
have h  :
     hoare [M.__reduce4 :
     ((_z = z) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
     (single ((pow 2 255) - 19))))].
by conseq __reduce4_assume (__reduce4_assert _z).
conseq h __reduce4_assert_assume_sound => // ; smt ().
qed .

lemma __sqr4_rs_spec  :
      forall _xa,
      hoare [M.__sqr4_rs :
      ((_xa = xa) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
move => _xa.
have h  :
     hoare [M.__sqr4_rs :
     ((_xa = xa) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))].
by conseq __sqr4_rs_assume (__sqr4_rs_assert _xa).
conseq h __sqr4_rs_assert_assume_sound => // ; smt ().
qed .


lemma sqr4_equiv_contract (xa h: Rep4) :
      inzpRep4 h = inzp (valRep4 xa * valRep4 xa) <=>       
           (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i xa.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i xa.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))).
proof.      
      rewrite -!limbs_are_same.
      rewrite !inzpRep4E !/inzp. smt(@Zp_25519).      
qed.




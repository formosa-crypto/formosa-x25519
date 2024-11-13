require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Jcheck.

require import Array4 Array8.

require import WArray32 WArray64.

require import Jcheck Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.

module M = {
  var tmp__check : to_check
  var tmp__data___reduce4 : (W64.t Array4.t)
  var tmp____reduce4 : W64.t Array4.t
  var tmp__data___sqr4_rr : (W64.t Array4.t)
  var tmp____sqr4_rr : W64.t Array4.t
  proc __reduce4 (x:W64.t Array4.t, r:W64.t Array4.t, _38:W64.t, z:W64.t,
                  cf:bool, of_0:bool) : ((W64.t Array4.t) * to_check) = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var h:W64.t Array4.t;
    var h0:W64.t Array4.t;
    var hi:W64.t;
    var lo:W64.t;
    var carryo:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var assume___reduce4:bool;
    var assert___reduce4:bool;
    var assume_proof___reduce4:bool;
    var assert_proof___reduce4:bool;
    assume___reduce4 <- true;
    assert___reduce4 <- true;
    assume_proof___reduce4 <- true;
    assert_proof___reduce4 <- assert___reduce4;
    h <- witness;
    h0 <- witness;
    z <- (W64.of_int 0);
    _38 <- (W64.of_int 38);
    h <- (copy_64 x);
    h0 <- (copy_64 r);
    (hi, lo) <- (MULX_64 _38 h0.[0]);
    (aux, aux_1) <- (ADOX_64 h.[0] lo of_0);
    of_0 <- aux;
    h.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[1] hi cf);
    cf <- aux;
    h.[1] <- aux_1;
    (hi, lo) <- (MULX_64 _38 h0.[1]);
    (aux, aux_1) <- (ADOX_64 h.[1] lo of_0);
    of_0 <- aux;
    h.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[2] hi cf);
    cf <- aux;
    h.[2] <- aux_1;
    (hi, lo) <- (MULX_64 _38 h0.[2]);
    (aux, aux_1) <- (ADOX_64 h.[2] lo of_0);
    of_0 <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[3] hi cf);
    cf <- aux;
    h.[3] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 _38 h0.[3]);
    h0.[0] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h0.[0] z cf);
    cf <- aux;
    h0.[0] <- aux_1;
    (aux, aux_1) <- (ADOX_64 h0.[0] z of_0);
    of_0 <- aux;
    h0.[0] <- aux_1;
    ( _0,  _1,  _2,  _3,  _4, lo) <- (IMULri_64 h0.[0] (W64.of_int 38));
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! cf)));
    assert___reduce4 <- (assert___reduce4 /\ (! cf));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = 0));
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! of_0)));
    assert___reduce4 <- (assert___reduce4 /\ (! of_0));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i of_0) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i of_0) = 0));
    (aux, aux_1) <- (adc_64 h.[0] lo false);
    cf <- aux;
    h.[0] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[1] z cf);
    cf <- aux;
    h.[1] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[2] z cf);
    cf <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[3] z cf);
    cf <- aux;
    h.[3] <- aux_1;
    carryo <- cf;
    (cf, z) <- (sbb_64 z z cf);
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (cf = carryo)));
    assert___reduce4 <- (assert___reduce4 /\ (cf = carryo));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = (b2i carryo))));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = (b2i carryo)));
    z <- (z `&` (W64.of_int 38));
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) =>
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38))))));
    assert___reduce4 <-
    (assert___reduce4 /\
    (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((u64i z) = ((b2i cf) * 38))));
    assume___reduce4 <- (assume___reduce4 /\ ((u64i z) = ((b2i cf) * 38)));
    (aux, aux_1) <- (adc_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_1;
    assert_proof___reduce4 <-
    (assert_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => (! cf)));
    assert___reduce4 <- (assert___reduce4 /\ (! cf));
    assume_proof___reduce4 <-
    (assume_proof___reduce4 /\
    ((assert___reduce4 /\ assume___reduce4) => ((b2i cf) = 0)));
    assume___reduce4 <- (assume___reduce4 /\ ((b2i cf) = 0));
    return (h,
           (assume___reduce4, assert___reduce4, assume_proof___reduce4,
           assert_proof___reduce4));
  }
  proc __sqr4_rr (f:W64.t Array4.t) : ((W64.t Array4.t) * to_check) = {
    var aux_1:bool;
    var aux_0:W64.t;
    var aux:W64.t;
    var h:W64.t Array4.t;
    var of_0:bool;
    var cf:bool;
    var z:W64.t;
    var fx:W64.t;
    var t:W64.t Array8.t;
    var r:W64.t Array4.t;
    var _38:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var assume___sqr4_rr:bool;
    var assert___sqr4_rr:bool;
    var assume_proof___sqr4_rr:bool;
    var assert_proof___sqr4_rr:bool;
    assume___sqr4_rr <- true;
    assert___sqr4_rr <- true;
    assume_proof___sqr4_rr <- true;
    assert_proof___sqr4_rr <- assert___sqr4_rr;
    h <- witness;
    r <- witness;
    t <- witness;
    (of_0, cf,  _0,  _1,  _2, z) <- (set0_64);
    fx <- f.[0];
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[1] <- aux_0;
    h.[0] <- aux;
    (aux_0, aux) <- (MULX_64 fx f.[1]);
    h.[2] <- aux_0;
    h.[1] <- aux;
    (aux_0, aux) <- (MULX_64 fx f.[2]);
    h.[3] <- aux_0;
    t.[2] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[2] t.[2] cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[0] <- aux_0;
    t.[3] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[3] t.[3] cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    fx <- f.[1];
    (aux_0, aux) <- (MULX_64 fx f.[2]);
    t.[4] <- aux_0;
    t.[3] <- aux;
    (aux_1, aux_0) <- (ADOX_64 h.[3] t.[3] of_0);
    of_0 <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[0] t.[4] cf);
    cf <- aux_1;
    r.[0] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[1] <- aux_0;
    t.[4] <- aux;
    (aux_1, aux_0) <- (ADOX_64 r.[0] t.[4] of_0);
    of_0 <- aux_1;
    r.[0] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[3] <- aux_0;
    t.[2] <- aux;
    fx <- f.[2];
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[2] <- aux_0;
    t.[5] <- aux;
    (aux_1, aux_0) <- (ADCX_64 r.[1] t.[5] cf);
    cf <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[1] z of_0);
    of_0 <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[2] z cf);
    cf <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[2] z of_0);
    of_0 <- aux_1;
    r.[2] <- aux_0;
    assert_proof___sqr4_rr <-
    (assert_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) => (! cf)));
    assert___sqr4_rr <- (assert___sqr4_rr /\ (! cf));
    assume_proof___sqr4_rr <-
    (assume_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) => ((b2i cf) = 0)));
    assume___sqr4_rr <- (assume___sqr4_rr /\ ((b2i cf) = 0));
    assert_proof___sqr4_rr <-
    (assert_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) => (! of_0)));
    assert___sqr4_rr <- (assert___sqr4_rr /\ (! of_0));
    assume_proof___sqr4_rr <-
    (assume_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) => ((b2i of_0) = 0)));
    assume___sqr4_rr <- (assume___sqr4_rr /\ ((b2i of_0) = 0));
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[5] <- aux_0;
    t.[4] <- aux;
    fx <- f.[3];
    (aux_0, aux) <- (MULX_64 fx fx);
    r.[3] <- aux_0;
    t.[6] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[1] h.[1] cf);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[1] t.[1] of_0);
    of_0 <- aux_1;
    h.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 h.[2] h.[2] cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[2] t.[2] of_0);
    of_0 <- aux_1;
    h.[2] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 h.[3] h.[3] cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[3] t.[3] of_0);
    of_0 <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[0] r.[0] cf);
    cf <- aux_1;
    r.[0] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[0] t.[4] of_0);
    of_0 <- aux_1;
    r.[0] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[1] r.[1] cf);
    cf <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[1] t.[5] of_0);
    of_0 <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[2] r.[2] cf);
    cf <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[2] t.[6] of_0);
    of_0 <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[3] z cf);
    cf <- aux_1;
    r.[3] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[3] z of_0);
    of_0 <- aux_1;
    r.[3] <- aux_0;
    assert_proof___sqr4_rr <-
    (assert_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) => (! cf)));
    assert___sqr4_rr <- (assert___sqr4_rr /\ (! cf));
    assume_proof___sqr4_rr <-
    (assume_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) => ((b2i cf) = 0)));
    assume___sqr4_rr <- (assume___sqr4_rr /\ ((b2i cf) = 0));
    assert_proof___sqr4_rr <-
    (assert_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) => (! of_0)));
    assert___sqr4_rr <- (assert___sqr4_rr /\ (! of_0));
    assume_proof___sqr4_rr <-
    (assume_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) => ((b2i of_0) = 0)));
    assume___sqr4_rr <- (assume___sqr4_rr /\ ((b2i of_0) = 0));
    _38 <- (W64.of_int 38);
    (tmp__data___reduce4, tmp__check) <@ __reduce4 (h, r, _38, z, cf, of_0);
    tmp____reduce4 <- tmp__data___reduce4;
    (assume___sqr4_rr, assert___sqr4_rr, assume_proof___sqr4_rr,
    assert_proof___sqr4_rr) <-
    (upd_call
    (assume___sqr4_rr, assert___sqr4_rr, assume_proof___sqr4_rr,
    assert_proof___sqr4_rr) tmp__check);
    assert_proof___sqr4_rr <-
    (assert_proof___sqr4_rr /\
    ((assert___sqr4_rr /\ assume___sqr4_rr) =>
    (eqmod
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
    (iota_ 0 4)))
    ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4))) +
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i r.[ii]))) (iota_ 0 4))))
    (single ((pow 2 255) - 19)))));
    assert___sqr4_rr <-
    (assert___sqr4_rr /\
    (eqmod
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
    (iota_ 0 4)))
    ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4))) +
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i r.[ii]))) (iota_ 0 4))))
    (single ((pow 2 255) - 19))));
    h <- tmp____reduce4;
    return (h,
           (assume___sqr4_rr, assert___sqr4_rr, assume_proof___sqr4_rr,
           assert_proof___sqr4_rr));
  }
}.

(* All assume are valid. *)

lemma __reduce4_assume  : hoare [M.__reduce4 : true ==> (assume_proof_ res)].
proof.
    proc. 
    seq 52 : (assume_proof__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />.
    seq 23 : (assume_proof__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />.    
    move => &hr. smt(@Zp_25519 @W64 @JUtils).
    auto => />.
qed.

lemma __sqr4_rr_assume  : hoare [M.__sqr4_rr : true ==> (assume_proof_ res)].
proof.
    proc.
    wp. call __reduce4_assume. 
    seq 70 : (assume_proof__ (assume___sqr4_rr, assert___sqr4_rr, assume_proof___sqr4_rr, assert_proof___sqr4_rr)). auto => />. 
    seq 58 : (assume_proof__ (assume___sqr4_rr, assert___sqr4_rr, assume_proof___sqr4_rr, assert_proof___sqr4_rr)). auto => />. auto => />.
qed.

(* Soundness of assert/assume. *)

lemma __reduce4_assert_assume_sound  :
      hoare [M.__reduce4 : true ==> (soundness_ res)].
proof.
    proc.
    seq 52 : (soundness__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. smt().
    seq 23 : (soundness__ (assume___reduce4, assert___reduce4, assume_proof___reduce4, assert_proof___reduce4)). auto => />. smt().
    auto => />. smt().
qed.

lemma __sqr4_rr_assert_assume_sound  :
      hoare [M.__sqr4_rr : true ==> (soundness_ res)].
proof.
    proc.
    wp. call __reduce4_assert_assume_sound.
     seq 70 : (soundness__ (assume___sqr4_rr, assert___sqr4_rr, assume_proof___sqr4_rr, assert_proof___sqr4_rr)). auto => />. smt().
    seq 58 : (soundness__ (assume___sqr4_rr, assert___sqr4_rr, assume_proof___sqr4_rr, assert_proof___sqr4_rr)). auto => />. smt().
    auto => />. smt().
qed.

(* Lemmas proved by cryptoline. *)

axiom __reduce4_assert _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      (((_of = of_0) /\
       ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) /\
      true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii]))) (iota_ 0 4)
      ))) (single ((pow 2 255) - 19))))].

axiom __sqr4_rr_assert _f :
      hoare [M.__sqr4_rr :
      ((_f = f) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].

(* Final specification for the functions. *)

lemma __reduce4_spec  :
      forall _x _r __38 _z _cf _of,
      hoare [M.__reduce4 :
      (((_of = of_0) /\
       ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) /\
      true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii]))) (iota_ 0 4)
      ))) (single ((pow 2 255) - 19)))].
proof.
move => _x _r __38 _z _cf _of.
have h  :
     hoare [M.__reduce4 :
     (((_of = of_0) /\
      ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) /\
     true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii]))) (iota_ 0 4))
     )) (single ((pow 2 255) - 19))))].
by conseq __reduce4_assume (__reduce4_assert _x _r __38 _z _cf _of).
conseq h __reduce4_assert_assume_sound => // ; smt ().
qed .

lemma __sqr4_rr_spec  :
      forall _f,
      hoare [M.__sqr4_rr :
      ((_f = f) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
move => _f.
have h  :
     hoare [M.__sqr4_rr :
     ((_f = f) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))].
by conseq __sqr4_rr_assume (__sqr4_rr_assert _f).
conseq h __sqr4_rr_assert_assume_sound => // ; smt ().
qed .

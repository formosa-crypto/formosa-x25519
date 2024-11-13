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
  var tmp__data___mul4_rss : (W64.t Array4.t)
  var tmp____mul4_rss : W64.t Array4.t
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
  proc __mul4_rss (xa:W64.t Array4.t, ya:W64.t Array4.t) : ((W64.t Array4.t) *
                                                           to_check) = {
    var aux_0:bool;
    var aux:int;
    var aux_1:W64.t;
    var r:W64.t Array4.t;
    var i:int;
    var z:W64.t Array8.t;
    var x:W64.t Array4.t;
    var j:int;
    var y:W64.t Array4.t;
    var h:W64.t;
    var l:W64.t;
    var cf:bool;
    var hprev:W64.t;
    var assume___mul4_rss:bool;
    var assert___mul4_rss:bool;
    var assume_proof___mul4_rss:bool;
    var assert_proof___mul4_rss:bool;
    assume___mul4_rss <- true;
    assert___mul4_rss <- true;
    assume_proof___mul4_rss <- true;
    assert_proof___mul4_rss <- assert___mul4_rss;
    r <- witness;
    x <- witness;
    y <- witness;
    z <- witness;
    i <- 2;
    while ((i < 8)) {
      z.[i] <- (MOV_64 (W64.of_int 0));
      i <- (i + 1);
    }
    x.[0] <- xa.[0];
    j <- 0;
    while ((j < 4)) {
      y.[j] <- ya.[j];
      (h, l) <- (mulu_64 y.[j] x.[0]);
      if ((j = 0)) {
        z.[0] <- l;
        z.[1] <- h;
      } else {
        (aux_0, aux_1) <- (adc_64 z.[j] l false);
        cf <- aux_0;
        z.[j] <- aux_1;
        (aux_0, aux_1) <- (adc_64 z.[(j + 1)] h cf);
        cf <- aux_0;
        z.[(j + 1)] <- aux_1;
        assert_proof___mul4_rss <-
        (assert_proof___mul4_rss /\
        ((assert___mul4_rss /\ assume___mul4_rss) => (! cf)));
        assert___mul4_rss <- (assert___mul4_rss /\ (! cf));
        assume_proof___mul4_rss <-
        (assume_proof___mul4_rss /\
        ((assert___mul4_rss /\ assume___mul4_rss) => ((b2i cf) = 0)));
        assume___mul4_rss <- (assume___mul4_rss /\ ((b2i cf) = 0));
      }
      j <- (j + 1);
    }
    i <- 1;
    while ((i < 4)) {
      x.[i] <- xa.[i];
      j <- 0;
      while ((j < 4)) {
        y.[j] <- ya.[j];
        (h, l) <- (mulu_64 y.[j] x.[i]);
        (aux_0, aux_1) <- (adc_64 z.[(i + j)] l false);
        cf <- aux_0;
        z.[(i + j)] <- aux_1;
        if ((j = 0)) {
          hprev <- (MOV_64 (W64.of_int 0));
          (cf, hprev) <- (adc_64 hprev h cf);
          assert_proof___mul4_rss <-
          (assert_proof___mul4_rss /\
          ((assert___mul4_rss /\ assume___mul4_rss) => (! cf)));
          assert___mul4_rss <- (assert___mul4_rss /\ (! cf));
          assume_proof___mul4_rss <-
          (assume_proof___mul4_rss /\
          ((assert___mul4_rss /\ assume___mul4_rss) => ((b2i cf) = 0)));
          assume___mul4_rss <- (assume___mul4_rss /\ ((b2i cf) = 0));
        } else {
          (cf, h) <- (adc_64 h (W64.of_int 0) cf);
          assert_proof___mul4_rss <-
          (assert_proof___mul4_rss /\
          ((assert___mul4_rss /\ assume___mul4_rss) => (! cf)));
          assert___mul4_rss <- (assert___mul4_rss /\ (! cf));
          assume_proof___mul4_rss <-
          (assume_proof___mul4_rss /\
          ((assert___mul4_rss /\ assume___mul4_rss) => ((b2i cf) = 0)));
          assume___mul4_rss <- (assume___mul4_rss /\ ((b2i cf) = 0));
          (aux_0, aux_1) <- (adc_64 z.[(i + j)] hprev false);
          cf <- aux_0;
          z.[(i + j)] <- aux_1;
          if (((1 <= j) /\ (j < (4 - 1)))) {
            hprev <- (MOV_64 (W64.of_int 0));
            (cf, hprev) <- (adc_64 hprev h cf);
            assert_proof___mul4_rss <-
            (assert_proof___mul4_rss /\
            ((assert___mul4_rss /\ assume___mul4_rss) => (! cf)));
            assert___mul4_rss <- (assert___mul4_rss /\ (! cf));
            assume_proof___mul4_rss <-
            (assume_proof___mul4_rss /\
            ((assert___mul4_rss /\ assume___mul4_rss) => ((b2i cf) = 0)));
            assume___mul4_rss <- (assume___mul4_rss /\ ((b2i cf) = 0));
          } else {
            (aux_0, aux_1) <- (adc_64 z.[((i + j) + 1)] h cf);
            cf <- aux_0;
            z.[((i + j) + 1)] <- aux_1;
            assert_proof___mul4_rss <-
            (assert_proof___mul4_rss /\
            ((assert___mul4_rss /\ assume___mul4_rss) => (! cf)));
            assert___mul4_rss <- (assert___mul4_rss /\ (! cf));
            assume_proof___mul4_rss <-
            (assume_proof___mul4_rss /\
            ((assert___mul4_rss /\ assume___mul4_rss) => ((b2i cf) = 0)));
            assume___mul4_rss <- (assume___mul4_rss /\ ((b2i cf) = 0));
          }
        }
        j <- (j + 1);
      }
      i <- (i + 1);
    }
    (tmp__data___reduce4, tmp__check) <@ __reduce4 (z);
    tmp____reduce4 <- tmp__data___reduce4;
    (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
    assert_proof___mul4_rss) <-
    (upd_call
    (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
    assert_proof___mul4_rss) tmp__check);
    assert_proof___mul4_rss <-
    (assert_proof___mul4_rss /\
    ((assert___mul4_rss /\ assume___mul4_rss) =>
    (eqmod
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
    (iota_ 0 4)))
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i z.[ii]))) (iota_ 0 8)))
    (single ((pow 2 255) - 19)))));
    assert___mul4_rss <-
    (assert___mul4_rss /\
    (eqmod
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
    (iota_ 0 4)))
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i z.[ii]))) (iota_ 0 8)))
    (single ((pow 2 255) - 19))));
    r <- tmp____reduce4;
    return (r,
           (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
           assert_proof___mul4_rss));
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
lemma __mul4_rss_assume  :
      hoare [M.__mul4_rss : true ==> (assume_proof_ res)].
proof.
    proc. wp. call __reduce4_assume.
    seq 8 : (assume_proof__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). auto => />.
    unroll for ^while. auto => />. auto => />. auto => />. 
    seq 14 : (assume_proof__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). auto => />.
    seq 2 : (assume_proof__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). 
    unroll for ^while. auto => />.
    seq 2 : (assume_proof__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). 
    unroll for ^while. auto => />. 
    seq 5 : (assume_proof__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). 
    unroll for ^while. auto => />.
    seq 5 : (assume_proof__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). 
    unroll for ^while. 
    rcondt ^if. auto => />. rcondf ^if. auto => />. rcondt ^if. auto => />.
    rcondf ^if. auto => />. rcondt ^if. auto => />. rcondf ^if. auto => />.
    rcondf ^if. auto => />. auto => />. 
    unroll for ^while. 
    rcondt ^if. auto => />. rcondf ^if. auto => />. rcondt ^if. auto => />.
    rcondf ^if. auto => />. rcondt ^if. auto => />. rcondf ^if. auto => />.
    rcondf ^if. auto => />. auto => />. 
    auto => />. 
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

lemma __mul4_rss_assert_assume_sound  :
      hoare [M.__mul4_rss : true ==> (soundness_ res)].
proof.
    proc. wp. call __reduce4_assert_assume_sound.        
    seq 8 : (soundness__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). auto => />.
    unroll for ^while. auto => />. auto => />. auto => />. 
    seq 14 : (soundness__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). auto => />.
    seq 2 : (soundness__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). 
    unroll for ^while. auto => />. smt().
    seq 2 : (soundness__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). 
    unroll for ^while. auto => />. 
    seq 5 : (soundness__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). 
    unroll for ^while. auto => />. smt().
    seq 5 : (soundness__ (assume___mul4_rss, assert___mul4_rss, assume_proof___mul4_rss,
      assert_proof___mul4_rss)). 
    unroll for ^while. 
    rcondt ^if. auto => />. rcondf ^if. auto => />. rcondt ^if. auto => />.
    rcondf ^if. auto => />. rcondt ^if. auto => />. rcondf ^if. auto => />.
    rcondf ^if. auto => />. wp. skip. auto => />. smt().
    unroll for ^while. 
    rcondt ^if. auto => />. rcondf ^if. auto => />. rcondt ^if. auto => />.
    rcondf ^if. auto => />. rcondt ^if. auto => />. rcondf ^if. auto => />.
    rcondf ^if. auto => />. wp. skip. auto => />. smt(). 
    auto => />. smt().
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

axiom __mul4_rss_assert _xa _ya :
      hoare [M.__mul4_rss :
      (((_ya = ya) /\ (_xa = xa)) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ya.[ii]))) (iota_ 0 4))))
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
qed.

lemma __mul4_rss_spec  :
      forall _xa _ya,
      hoare [M.__mul4_rss :
      (((_ya = ya) /\ (_xa = xa)) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ya.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
move => _xa _ya.
have h  :
     hoare [M.__mul4_rss :
     (((_ya = ya) /\ (_xa = xa)) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ya.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))].
by conseq __mul4_rss_assume (__mul4_rss_assert _xa _ya).
conseq h __mul4_rss_assert_assume_sound => // ; smt ().
qed .


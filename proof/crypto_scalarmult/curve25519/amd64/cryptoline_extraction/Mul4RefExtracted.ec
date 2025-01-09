require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck.

require import Array4 Array8.

require import WArray32 WArray64.

require import Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.


module M = {
  var tmp__trace : trace
  var tmp__data___reduce4 : (W64.t Array4.t)
  var tmp____reduce4 : W64.t Array4.t
  var tmp__data___mul4_rss : (W64.t Array4.t)
  var tmp____mul4_rss : W64.t Array4.t
  proc __reduce4 (z:W64.t Array8.t) : ((W64.t Array4.t) * trace) = {
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
    var old_z:W64.t Array8.t;
    var trace___reduce4:trace;
    old_z <- z;
    trace___reduce4 <- [];
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
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[2] l false);
    cf <- aux;
    r.[2] <- aux_0;
    r.[3] <- (MOV_64 (W64.of_int 0));
    rax <- z.[7];
    (aux, aux_0) <- (adc_64 r.[3] h cf);
    cf <- aux;
    r.[3] <- aux_0;
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[3] l false);
    cf <- aux;
    r.[3] <- aux_0;
    z8 <- (MOV_64 (W64.of_int 0));
    (cf, z8) <- (adc_64 z8 h cf);
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
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
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (dc, z8) <- (mulu_64 z8 (W64.of_int 38));
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assert, (dc = (W64.of_int 0)))]);
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assume, (dc = (W64.of_int 0)))]);
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
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    (dc, r0) <- (mulu_64 r0 (W64.of_int 38));
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assert, (dc = (W64.of_int 0)))]);
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assume, (dc = (W64.of_int 0)))]);
    (aux, aux_0) <- (adc_64 r.[0] r0 false);
    cf <- aux;
    r.[0] <- aux_0;
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    trace___reduce4 <-
    (trace___reduce4 ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i r.[ii]))) (iota_ 0 4)))
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_z.[ii]))) (iota_ 0 8)))
     (single ((pow 2 255) - 19))))]);
    return (r, trace___reduce4);
  }
  proc __mul4_rss (xa:W64.t Array4.t, ya:W64.t Array4.t) : ((W64.t Array4.t) *
                                                           trace) = {
    var aux_0:bool;
    var aux:int;
    var aux_1:W64.t;
    var r:W64.t Array4.t;
    var i:int;
    var z:W64.t Array8.t;
    var hprev:W64.t;
    var x:W64.t Array4.t;
    var j:int;
    var y:W64.t Array4.t;
    var h:W64.t;
    var l:W64.t;
    var cf:bool;
    var old_ya:W64.t Array4.t;
    var old_xa:W64.t Array4.t;
    var trace___mul4_rss:trace;
    old_xa <- xa;
    old_ya <- ya;
    trace___mul4_rss <- [];
    r <- witness;
    x <- witness;
    y <- witness;
    z <- witness;
    i <- 0;
    while ((i < 8)) {
      z.[i] <- (MOV_64 (W64.of_int 0));
      i <- (i + 1);
    }
    hprev <- (MOV_64 (W64.of_int 0));
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
        trace___mul4_rss <- (trace___mul4_rss ++ [(Assert, (! cf))]);
        trace___mul4_rss <- (trace___mul4_rss ++ [(Assume, ((b2i cf) = 0))]);
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
          trace___mul4_rss <- (trace___mul4_rss ++ [(Assert, (! cf))]);
          trace___mul4_rss <-
          (trace___mul4_rss ++ [(Assume, ((b2i cf) = 0))]);
        } else {
          (cf, h) <- (adc_64 h (W64.of_int 0) cf);
          trace___mul4_rss <- (trace___mul4_rss ++ [(Assert, (! cf))]);
          trace___mul4_rss <-
          (trace___mul4_rss ++ [(Assume, ((b2i cf) = 0))]);
          (aux_0, aux_1) <- (adc_64 z.[(i + j)] hprev false);
          cf <- aux_0;
          z.[(i + j)] <- aux_1;
          if (((1 <= j) /\ (j < (4 - 1)))) {
            hprev <- (MOV_64 (W64.of_int 0));
            (cf, hprev) <- (adc_64 hprev h cf);
            trace___mul4_rss <- (trace___mul4_rss ++ [(Assert, (! cf))]);
            trace___mul4_rss <-
            (trace___mul4_rss ++ [(Assume, ((b2i cf) = 0))]);
          } else {
            (aux_0, aux_1) <- (adc_64 z.[((i + j) + 1)] h cf);
            cf <- aux_0;
            z.[((i + j) + 1)] <- aux_1;
            trace___mul4_rss <- (trace___mul4_rss ++ [(Assert, (! cf))]);
            trace___mul4_rss <-
            (trace___mul4_rss ++ [(Assume, ((b2i cf) = 0))]);
          }
        }
        j <- (j + 1);
      }
      i <- (i + 1);
    }
    (tmp__data___reduce4, tmp__trace) <@ __reduce4 (z);
    tmp____reduce4 <- tmp__data___reduce4;
    trace___mul4_rss <- (trace___mul4_rss ++ tmp__trace);
    trace___mul4_rss <-
    (trace___mul4_rss ++
    [(Assume,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
     (iota_ 0 4)))
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i z.[ii]))) (iota_ 0 8)))
     (single ((pow 2 255) - 19))))]);
    r <- tmp____reduce4;
    trace___mul4_rss <-
    (trace___mul4_rss ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i r.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_xa.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_ya.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))]);
    return (r, trace___mul4_rss);
  }
}.
(* The post is in the trace. *)

lemma __reduce4_valid_post _z :
      hoare [M.__reduce4 :
      (_z = z) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
      (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> (_z = old_z)).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 1 : ((_z = old_z)).
by auto .
by conseq  />.
qed .

lemma __mul4_rss_valid_post _xa _ya :
      hoare [M.__mul4_rss :
      ((_ya = ya) /\ (_xa = xa)) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ya.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> ((_ya = old_ya) /\ (_xa = old_xa))).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 2 : (((_ya = old_ya) /\ (_xa = old_xa))).
by auto .
by conseq  />.
qed .

(* The post is in the trace and all assumes are valid. *)

lemma __reduce4_assume_ _z :
      hoare [M.__reduce4 :
      (_z = z) ==> (true => (validk Assume (trace res)))].
proof.
    proc. do 2! unroll for ^while. 
    auto => />.
qed.

lemma __reduce4_assume _z :
      hoare [M.__reduce4 :
      (_z = z) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
       (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__reduce4_assume_ _z) (__reduce4_valid_post _z) => />.
qed .

lemma __mul4_rss_assume_ _xa _ya :
      hoare [M.__mul4_rss :
      ((_ya = ya) /\ (_xa = xa)) ==> (true => (validk Assume (trace res)))].
proof.
    proc. wp. 
    seq 3: (#pre /\ validk Assume (trace___mul4_rss)). auto => />.  
    seq 8: (#pre). unroll for ^while.  auto => />.  
    seq 2: (#pre). unroll for ^while.   
    rcondt ^if. auto. rcondf ^if. auto. rcondf ^if. auto. rcondf ^if. auto. auto => />.
    move => &hr H. rewrite !validk_cat //=; 1..3:smt(Jcheck.valid_cat). 
    seq 2: (#pre). unroll for ^while.   
    seq 3: (#pre). unroll for ^while.   
    rcondt ^if. auto. rcondf ^if. auto. rcondt ^if. auto. rcondf ^if. auto. rcondt ^if. auto. 
    rcondf ^if. auto. rcondf ^if. auto. auto => />.  
    move => &hr H. rewrite !validk_cat //=; 1..7:smt(Jcheck.valid_cat).
    seq 3: (#pre). unroll for ^while.   
    rcondt ^if. auto. rcondf ^if. auto. rcondt ^if. auto. rcondf ^if. auto. rcondt ^if. auto. 
    rcondf ^if. auto. rcondf ^if. auto. auto => />.
    move => &hr H. rewrite !validk_cat //=; 1..7:smt(Jcheck.valid_cat).
    seq 3: (#pre). unroll for ^while.   
    rcondt ^if. auto. rcondf ^if. auto. rcondt ^if. auto. rcondf ^if. auto. rcondt ^if. auto. 
    rcondf ^if. auto. rcondf ^if. auto. auto => />.
    move => &hr H. rewrite !validk_cat //=; 1..7:smt(Jcheck.valid_cat).
    auto. inline M.__reduce4. 
    do 2! unroll for ^while. 
    auto => />.
    move => &hr H. rewrite !/trace //= !validk_cat //=. move => H0 H1.
    rewrite !H1 !b2i0 => />. rewrite !valid_cat //=. smt(forall_validk_valid).
qed.


lemma __mul4_rss_assume _xa _ya :
      hoare [M.__mul4_rss :
      ((_ya = ya) /\ (_xa = xa)) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ya.[ii]))) (iota_ 0 4))))
       (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__mul4_rss_assume_ _xa _ya) (__mul4_rss_valid_post _xa _ya) => />.
qed .

(* All assert are valid. *)

lemma __reduce4_assert _z :
      hoare [M.__reduce4 :
      ((_z = z) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

lemma __mul4_rss_assert _xa _ya :
      hoare [M.__mul4_rss :
      (((_ya = ya) /\ (_xa = xa)) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __reduce4_spec _z :
      hoare [M.__reduce4 :
      ((_z = z) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _z.[ii]))) (iota_ 0 8)))
      (single ((pow 2 255) - 19)))].
proof.
conseq (__reduce4_assume _z) (__reduce4_assert _z) => />.
smt (all_validk_valid).
qed .

lemma __mul4_rss_spec _xa _ya :
      hoare [M.__mul4_rss :
      (((_ya = ya) /\ (_xa = xa)) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _xa.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _ya.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
conseq (__mul4_rss_assume _xa _ya) (__mul4_rss_assert _xa _ya) => />.
smt (all_validk_valid).
qed .


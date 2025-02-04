require import Bool List Int IntDiv.
from Jasmin require import JModel.

require import Curve25519_Spec Zp_25519 Curve25519_Operations Zp_25519.

import Zp Ring.IntID.

module CurveProcedures = {

  (* h = f + g *)
  proc add(f g : zp) : zp =
  {
    var h: zp;
    h <- f + g;
    return h;
  }

  (* h = f - g *)
  proc sub(f g : zp) : zp =
  {
    var h: zp;
    h <- f - g;
    return h;
  }

  (* h = f * a24 *)
  proc mul_a24 (f : zp, a24 : int) : zp =
  {
    var h: zp;
    h <- f * (inzp a24);
    return h;
  }

  (* h = f * g *)
  proc mul (f g : zp) : zp =
  {
    var h : zp;
    h <- f * g;
    return h;
  }

  (* h = f * f *)
  proc sqr (f : zp) : zp =
  {
    var h : zp;
    (*h <- f * f;*)
    h <- ZModpRing.exp f 2;
    return h;
  }

  (* iterated sqr *)
  proc it_sqr (f : zp, i : int) : zp =
  {
    var h, g: zp;
    var ii, counter: int;

    counter <- 1;
    g <- f;
    ii <- i;
    h <@ sqr(f);

    ii <- ii - 1;
    while (0 < ii) {
      h <@ sqr(h);
      counter <- counter + 1;
      ii <- ii - 1;
    }
  return h;
}

proc it_sqr_aux (a : zp, l : int) : zp = {
  var f, h: zp;
  var ii: int;
  ii <- l;
  h <@ sqr(a);
  f <@ sqr(h);
  ii <- ii - 1;
  while (0 < ii) {
   h <@ sqr(f);
   f <@ sqr(h);
   ii <- ii - 1;
}
    return f;
  }

  (* f ** 2**255-19-2 *)
  proc invert (fs : zp) : zp =
  {
    var t1s : zp;
    var t0s : zp;
    var t2s : zp;
    var t3s : zp;

    t0s <- witness;
    t1s <- witness;
    t2s <- witness;
    t3s <- witness;

    t0s <@ sqr (fs);
    t1s <@ sqr (t0s);
    t1s <@ sqr (t1s);
    t1s <@ mul (fs, t1s);
    t0s <@ mul (t0s, t1s);
    t2s <@ sqr (t0s);
    t1s <@ mul (t1s, t2s);
    t2s <@ sqr (t1s);
    t2s <@ it_sqr (t2s,4);
    t1s <@ mul (t1s, t2s);
    t2s <@ it_sqr (t1s,10);
    t2s <@ mul (t1s, t2s);
    t3s <@ it_sqr (t2s,20);
    t2s <@ mul(t2s, t3s);
    t2s <@ it_sqr (t2s,10);
    t1s <@ mul (t1s, t2s);
    t2s <@ it_sqr (t1s,50);
    t2s <@ mul (t1s, t2s);
    t3s <@ it_sqr (t2s,100);
    t2s <@ mul (t2s, t3s);
    t2s <@ it_sqr (t2s,50);
    t1s <@ mul (t1s, t2s);
    t1s <@ it_sqr (t1s,4);
    t1s <@ sqr (t1s);
    t1s <@ mul (t0s, t1s);
    return t1s;
  }

proc invert_helper (fs : zp) : zp =
{
    var t1s : zp;
    var t0s : zp;
    var t2s : zp;
    var t3s : zp;
    t0s <- witness;
    t1s <- witness;
    t2s <- witness;
    t3s <- witness;
    t0s <@ sqr (fs);
    t1s <@ sqr (t0s);
    t1s <@ sqr (t1s);
    t1s <@ mul (t1s, fs);
    t0s <@ mul (t0s, t1s);
    t2s <@ sqr (t0s);
    t1s <@ mul (t1s, t2s);
    t2s <@ sqr (t1s);
    t2s <@ it_sqr (t2s, 4);
    t1s <@ mul (t1s, t2s);
    t2s <@ it_sqr (t1s, 10);
    t2s <@ mul (t2s, t1s);
    t3s <@ it_sqr (t2s, 20);
    t2s <@ mul(t2s, t3s);
    t2s <@ it_sqr (t2s, 10);
    t1s <@ mul (t1s, t2s);
    t2s <@ it_sqr (t1s, 50);
    t2s <@ mul (t2s, t1s);
    t3s <@ it_sqr (t2s, 100);
    t2s <@ mul (t2s, t3s);
    t2s <@ it_sqr (t2s, 50);
    t1s <@ mul (t1s, t2s);
    t1s <@ it_sqr (t1s, 4);
    t1s <@ sqr (t1s);
    t1s <@ mul (t1s, t0s);
    return t1s;
}

  proc cswap (x2 z2 x3 z3 : zp, toswap : bool) : zp * zp * zp * zp =
  {
    if(toswap){
     (x2,z2,x3,z3) <- (x3,z3,x2,z2);
    }else{
     (x2,z2,x3,z3) <- (x2,z2,x3,z3);}
    return (x2,z2,x3,z3);
  }

  proc ith_bit (k' : W256.t, ctr : int) : bool =
  {
    return k'.[ctr];
  }

  proc decode_scalar (k' : W256.t) : W256.t =
  {
    k'.[0] <- false;
    k'.[1] <- false;
    k'.[2] <- false;
    k'.[255] <- false;
    k'.[254] <- true;
    return k';
  }

  proc decode_u_coordinate (u' : W256.t) : zp =
  {
    (* last bit of u is cleared but that can be introduced at the same time as arrays *)
    u'.[255] <- false;
    return inzp ( to_uint u' );
  }

  proc init_points (init : zp) : zp * zp * zp * zp =
  {
    var x2 : zp;
    var z2 : zp;
    var x3 : zp;
    var z3 : zp;

    x2 <- witness;
    x3 <- witness;
    z2 <- witness;
    z3 <- witness;

    x2 <- Zp.one;
    z2 <- Zp.zero;
    x3 <- init;
    z3 <- Zp.one;

    return (x2, z2, x3, z3);
  }

proc decode_u_coordinate_base () : zp =
  {
      var u' : zp;
      u' <@ decode_u_coordinate (W256.of_int 9);
      return u';
 }

  proc add_and_double (init x2 z2 x3 z3 : zp) : zp * zp * zp * zp =
  {
    var t0 : zp;
    var t1 : zp;
    var t2 : zp;
    t0 <- witness;
    t1 <- witness;
    t2 <- witness;
    t0 <@ sub (x2, z2);
    x2 <@ add (z2, x2);
    t1 <@ sub (x3, z3);
    z2 <@ add (x3, z3);
    z3 <@ mul (x2, t1);
    z2 <@ mul (z2, t0);
    t2 <@ sqr (x2);
    t1 <@ sqr (t0);
    x3 <@ add (z3, z2);
    z2 <@ sub (z3, z2);
    x2 <@ mul (t2, t1);
    t0 <@ sub (t2, t1);
    z2 <@ sqr (z2);
    z3 <@ mul_a24 (t0, 121665);
    x3 <@ sqr (x3);
    t2 <@ add (t2, z3);
    z3 <@ mul (init, z2);
    z2 <@ mul (t0, t2);
    return (x2, z2, x3, z3);
  }

  proc montgomery_ladder_step (k' : W256.t, init' x2 z2 x3 z3 : zp,  swapped : bool,  ctr' : int) : zp * zp * zp * zp * bool =
  {
    var bit : bool;
    var toswap : bool;
    bit <@ ith_bit (k', ctr');
    toswap <- swapped;
    toswap <- (toswap ^^ bit);
    (x2, z2, x3, z3) <@ cswap (x2, z2, x3, z3, toswap);
    swapped <- bit;
    (x2, z2, x3, z3) <@ add_and_double (init', x2, z2, x3, z3);
    return (x2, z2, x3, z3, swapped);
  }

   proc montgomery_ladder (init' : zp, k' : W256.t) : zp * zp * zp * zp =
  {
    var x2 : zp;
    var z2 : zp;
    var x3 : zp;
    var z3 : zp;
    var ctr : int;
    var c : int;
    var swapped : bool;


    x2 <- witness;
    x3 <- witness;
    z2 <- witness;
    z3 <- witness;
    (x2, z2, x3, z3) <@ init_points (init');
    ctr <- 255;
    swapped <- false;

    while (0 < ctr)
    {
     ctr <- ctr - 1;
     (x2, z2, x3, z3, swapped) <@ montgomery_ladder_step (k', init', x2, z2, x3, z3, swapped, ctr);

    }
    return (x2, z2, x3, z3);
  }

  proc encode_point (x2 z2 : zp) : W256.t =
  {
    var r : zp;
    r <- witness;
    z2 <@ invert (z2);
    r <@  mul (x2, z2);
    (* no need to 'freeze' or 'tobytes' r in this spec *)
    return (W256.of_int (asint r));
  }
proc scalarmult_internal(u'': zp,  k': W256.t ) : W256.t =   {
  var x2 : zp;
  var z2 : zp;
  var x3 : zp;
  var z3 : zp;
  var r : W256.t;
  r <- witness;
  x2 <- witness;
  x3 <- witness;
  z2 <- witness;
  z3 <- witness;
  (x2, z2, x3, z3) <@ montgomery_ladder(u'', k');
  r <@ encode_point(x2, z2);
  return r;
}

  proc scalarmult (k' u' : W256.t) : W256.t =
  {
    var u'' : zp;
    var r : W256.t;
    r <- witness;

    k'  <@ decode_scalar (k');
    u'' <@ decode_u_coordinate (u');
    r   <@ scalarmult_internal(u'', k');
    return r;
  }

proc scalarmult_base(k': W256.t) : W256.t =  {
  var u'' : zp;
  var x2 : zp;
  var z2 : zp;
  var x3 : zp;
  var z3 : zp;
  var r : W256.t;
  r <- witness;
  x2 <- witness;
  x3 <- witness;
  z2 <- witness;
  z3 <- witness;
  k'  <@ decode_scalar (k');
u'' <@ decode_u_coordinate_base ();
  r   <@ scalarmult_internal(u'', k');

  return r; }
}.

(** step 1 : decode_scalar_25519 **)
lemma eq_proc_op_decode_scalar k:
  hoare [ CurveProcedures.decode_scalar: k' = k
          ==> res = spec_decode_scalar_25519 k].
proof.
  proc; wp; rewrite /spec_decode_scalar_25519 /=; skip.
  move => &hr hk; rewrite hk //.
qed.

(** step 2 : decode_u_coordinate **)
lemma eq_proc_op_decode_u_coordinate u:
  hoare [ CurveProcedures.decode_u_coordinate : u' = u
          ==> res = Zp.inzp (to_uint (spec_decode_u_coordinate u))].
proof.
  proc; wp. rewrite /spec_decode_u_coordinate /=; skip.
  move => &mu hu; rewrite hu //.
qed.

lemma eq_proc_op_decode_u_coordinate_base:
  hoare[ CurveProcedures.decode_u_coordinate_base:
      true
      ==>
      res = Zp.inzp (to_uint (spec_decode_u_coordinate( W256.of_int 9)))
  ].
proof.
  proc *; inline 1; wp.
  ecall (eq_proc_op_decode_u_coordinate (W256.of_int 9)).
  auto => />.
 qed.

(** step 3 : ith_bit **)
lemma eq_proc_op_ith_bit (k : W256.t) i:
  hoare [CurveProcedures.ith_bit : k' = k /\ ctr = i ==> res = spec_ith_bit k i].
proof.
  proc. rewrite /spec_ith_bit. skip => />.
qed.

(** step 4 : cswap **)
lemma eq_proc_op_cswap (t : (zp * zp) * (zp * zp) )  b:
  hoare [CurveProcedures.cswap : x2 = (t.`1).`1 /\
                       z2 = (t.`1).`2 /\
                       x3 = (t.`2).`1 /\
                       z3 = (t.`2).`2 /\
                       toswap = b
         ==> ((res.`1, res.`2),(res.`3, res.`4)) = cswap t b].
proof.
  by proc; wp; skip; simplify => /#.
qed.

(** step 5 : add_and_double **)
lemma eq_proc_op_add_and_double (qx : zp) (nqs : (zp * zp) * (zp * zp)):
  hoare [CurveProcedures.add_and_double : init = qx /\
                                x2 = nqs.`1.`1 /\
                                z2 = nqs.`1.`2 /\
                                x3 = nqs.`2.`1 /\
                                z3 = nqs.`2.`2
         ==> ((res.`1, res.`2),(res.`3, res.`4)) = op_add_and_double qx nqs].
proof.
  proc; inline *; wp; skip.
  rewrite /op_add_and_double /=. rewrite !ZModpRing.expr2. smt().
qed.

(** step 6 : montgomery_ladder_step **)
lemma eq_proc_op_montgomery_ladder_step (k : W256.t)
                                   (init : zp)
                                   (nqs : (zp * zp) * (zp * zp) * bool)
                                   (ctr : int) :
  hoare [CurveProcedures.montgomery_ladder_step : k' = k /\
                                        init' = init /\
                                        x2 = nqs.`1.`1 /\
                                        z2 = nqs.`1.`2 /\
                                        x3 = nqs.`2.`1 /\
                                        z3 = nqs.`2.`2 /\
                                        swapped = nqs.`3 /\
                                        ctr' = ctr
         ==> ((res.`1, res.`2),(res.`3, res.`4),res.`5) =
             op_montgomery_ladder3_step k init nqs ctr].
proof.
  proc => /=.
  ecall (eq_proc_op_add_and_double init (cswap (select_double_from_triple nqs) (nqs.`3 ^^ (spec_ith_bit k ctr)))).
  wp.
  ecall (eq_proc_op_cswap (select_double_from_triple nqs) (nqs.`3 ^^ (spec_ith_bit k ctr))).
  wp.
  ecall (eq_proc_op_ith_bit k ctr). auto.
  rewrite /op_montgomery_ladder3_step => /#.
qed.

(** step 7 : montgomery_ladder **)
lemma unroll_ml3s  k init nqs (ctr : int) : (** unroll montgomery ladder 3 step **)
  0 <= ctr =>
    foldl (op_montgomery_ladder3_step k init)
          nqs
          (rev (iota_ 0 (ctr+1)))
    =
    foldl (op_montgomery_ladder3_step k init)
          (op_montgomery_ladder3_step k init nqs ctr)
          (rev (iota_ 0 (ctr))).
proof.
move => ctrge0.
rewrite 2!foldl_rev iotaSr //= -cats1 foldr_cat => /#.
qed.

lemma eq_proc_op_montgomery_ladder (init : zp)
                              (k : W256.t) :
  hoare [CurveProcedures.montgomery_ladder : init' = init /\
                                   k.[0] = false /\
                                   k' = k
         ==> ((res.`1, res.`2),(res.`3,res.`4)) =
             select_double_from_triple (op_montgomery_ladder3 init k)].
proof.
proc.
  inline CurveProcedures.init_points. sp. simplify.
  rewrite /op_montgomery_ladder3.
  while (foldl (op_montgomery_ladder3_step k' init')
               ((Zp.one, Zp.zero), (init, Zp.one), false)
               (rev (iota_ 0 255))
         =
         foldl (op_montgomery_ladder3_step k' init')
               ((x2,z2), (x3,z3), swapped)
               (rev (iota_ 0 (ctr)))
         ).
  wp. sp.
  ecall (eq_proc_op_montgomery_ladder_step k' init' ((x2,z2),(x3,z3),swapped) ctr).
  skip. simplify.
  move => &hr [?] ? ? ?. smt(unroll_ml3s).
  skip. move => &hr [?] [?] [?] [?] [?] [?] [?] [?] [?] [?] [?] [?] [?] ?. subst.
  split; first by done.
  move => H H0 H1 H2 H3 H4 H5 H6.
  have _ : rev (iota_ 0 (H)) = []; smt(iota0).
qed.

(** step 8 : iterated square **)


lemma eq_proc_op_it_sqr (e : int) (z : zp) :
  hoare[CurveProcedures.it_sqr :
         i = e && 1 <= i && f =  z
         ==>
        res = op_it_sqr1 e z].
proof.
  proc. inline CurveProcedures.sqr. sp. wp.  simplify.
  while (0 <= i && 0 <= ii && op_it_sqr1 e z = op_it_sqr1 ii h).
  wp; skip.
  move => &hr [[H [H0 H1 H2 H3]]]. split.
  apply H. move => H4. split. rewrite /H3.
  smt(). move => H5. rewrite /H3.
  smt(op_it_sqr1_m2_exp1). skip.
  move => &hr [H [H0 [H1 [H2 [H3]]]]] H4. split. split. smt(). move => H5. split. smt(). move => H6.
  smt(op_it_sqr1_m2_exp1). move => H5 H6 H7 [H8 [H9 H10]]. smt(op_it_sqr1_0).
qed.

lemma eq_proc_op_it_sqr_x2 (e : int) (z : zp) :
  hoare[CurveProcedures.it_sqr :
    i%/2 = e && 2 <= i && i %% 2 = 0 && f = z
    ==>
    res = op_it_sqr1_x2 e z].
proof.
  proc. inline CurveProcedures.sqr. sp. wp. simplify.
  while (0 <= i && 0 <= ii && 2*e = i && op_it_sqr1_x2 e z = op_it_sqr1 i f && op_it_sqr1 (2*e) z = op_it_sqr1 ii h).
  wp; skip.
  move => &hr [[H]] [H0] [H1] [H2] H3 H4 H5.
  split. assumption. move => H6.
  split. smt(). move => H7.
  split. assumption. move => H8.
  split. assumption. move => H9.
  rewrite H3 /H5 => />. smt(op_it_sqr1_m2_exp1). skip.
move => &hr [H] [H0] [H1] [H2] [H3] [H4] [H5] [H6] [H7] H8.
  do! split.
  + smt(). move => H9.
  split. smt(). move => H10.
  split. smt(). move => H11.
  split. rewrite eq_op_it_sqr1_x2. smt().
  rewrite eq_op_it_sqr1. smt().
  rewrite /op_it_sqr_x2 /op_it_sqr H8 -H11. congr.
  rewrite exprM => />. move => H12.
  rewrite !eq_op_it_sqr1; first smt(). smt().
  rewrite !/op_it_sqr. rewrite H3 H2 H1 -H8 H11. rewrite -ZModpRing.exprM => />.
  congr. rewrite H4.
  have ->: 2 * 2 ^ (i{hr} - 1) = 2^1 * 2 ^ (i{hr} - 1). rewrite expr1 //.
  rewrite -exprD_nneg //. smt().
  move => h II H9 [H10] [H11] [H12] [H13] H14. rewrite H13 -H12 H8 H14.
  smt(op_it_sqr1_0).
 qed.

(** step 9 : invert **)
lemma eq_proc_op_invert (z : zp) :
  hoare[CurveProcedures.invert : fs = z ==> res = op_invert2 z].
proof.
  proc.
  inline CurveProcedures.sqr CurveProcedures.mul.  wp.
  ecall (eq_proc_op_it_sqr 4   t1s). wp.
  ecall (eq_proc_op_it_sqr 50  t2s). wp.
  ecall (eq_proc_op_it_sqr 100 t2s). wp.
  ecall (eq_proc_op_it_sqr 50  t1s). wp.
  ecall (eq_proc_op_it_sqr 10  t2s). wp.
  ecall (eq_proc_op_it_sqr 20  t2s). wp.
  ecall (eq_proc_op_it_sqr 10  t1s). wp.
  ecall (eq_proc_op_it_sqr 4   t2s). wp.
  skip. simplify.
  move => &hr H.
  move=> ? ->. move=> ? ->.
  move=> ? ->. move=> ? ->.
  move=> ? ->. move=> ? ->.
  move=> ? ->. move=> ? ->.
  rewrite op_invert2E /sqr /= H /#.
qed.

equiv eq_sqr:
    CurveProcedures.it_sqr ~ CurveProcedures.it_sqr:
    f{1} = f{2} /\ i{1} = i{2} ==> ={res}.
proof.
    sim.
qed.

equiv eq_proc_proc_invert:
  CurveProcedures.invert_helper ~ CurveProcedures.invert:
  fs{1} = fs{2} ==> res{1} = res{2}.
proof.
  proc => //=; inline CurveProcedures.sqr CurveProcedures.mul; wp.
  call eq_sqr; wp. call eq_sqr; wp. call eq_sqr; wp.
  call eq_sqr; wp. call eq_sqr; wp. call eq_sqr; wp.
  call eq_sqr; wp. call eq_sqr; wp.
  skip => />. move => &2. do split.
  smt(). smt().
qed.


(** step 10 : encode point **)
lemma eq_proc_op_encode_point (q : zp * zp) :
  hoare[CurveProcedures.encode_point : x2 =  q.`1 /\ z2 = q.`2 ==> res = op_encode_point q].
proof.
  proc. inline CurveProcedures.mul. wp. sp.
  ecall (eq_proc_op_invert z2).
  skip. simplify.
  move => &hr [H] [H0] H1 H2 H3.
  rewrite op_encode_pointE.
  auto => />. congr; congr; congr. rewrite -H1. apply H3.
qed.

(** step 11 : scalarmult **)
lemma eq_proc_op_scalarmult_internal (u: zp, k: W256.t) :
  hoare[CurveProcedures.scalarmult_internal : k.[0] = false  /\ k' = k /\ u'' = u ==> res = op_scalarmult_internal u k].
proof.
  proc; sp.
  ecall (eq_proc_op_encode_point (x2, z2)). simplify.
  ecall (eq_proc_op_montgomery_ladder u'' k'). simplify. skip.
  move => &1 [H0] [H1] [H2] [H3] [H4] [H5] [H6] H7. split.
  rewrite H6 => />. rewrite /select_double_from_triple /op_montgomery_ladder3 => />.
  move => [#] H8 H9 H10 H11. smt().
qed.

lemma eq_proc_op_scalarmult (k u : W256.t) :
  hoare[CurveProcedures.scalarmult : k' = k /\ u' = u ==> res = spec_scalarmult k u].
proof.
  rewrite -eq_op_scalarmult.
  proc.
  pose dk := spec_decode_scalar_25519 k.
  have kb0f  : (dk).[0] = false. (* k bit 0 false *)
    rewrite /dk /spec_decode_scalar_25519 //.
  ecall (eq_proc_op_scalarmult_internal u'' k').
  ecall (eq_proc_op_decode_u_coordinate u').
  ecall (eq_proc_op_decode_scalar k').
  simplify. sp. skip.
  move => &hr [H] [H0] H1 H2 H3 H4 H5. split. rewrite H3 H0. apply kb0f.
  move=> H6 H7 ->. rewrite !op_encode_pointE. auto => />. congr. congr. congr. congr. congr.
  rewrite H5 H3 H1 H0 => />.
rewrite H5 H1 H3 H0 => />.
 qed.

lemma eq_proc_op_scalarmult_base (k : W256.t) :
  hoare[CurveProcedures.scalarmult_base : k' = k ==> res = spec_scalarmult_base k].
proof.
  rewrite -eq_op_scalarmult_base.
  proc.
  pose dk := spec_decode_scalar_25519 k.
  have kb0f  : (dk).[0] = false. (* k bit 0 false *)
      rewrite /dk /spec_decode_scalar_25519 //.
  ecall (eq_proc_op_scalarmult_internal u'' k').
  ecall (eq_proc_op_decode_u_coordinate_base).
  ecall (eq_proc_op_decode_scalar k').   simplify. sp. skip.
  move => &hr [H] [H0] [H1] [H2] [H3] H4 H5 H6 H7 H8. split. rewrite H6 H4. apply kb0f.
  move=> H9 H10 ->. rewrite /op_scalarmult_base  /op_scalarmult. auto => />.
  rewrite !op_encode_pointE. progress. congr; congr; congr; congr. congr. congr.
  rewrite H6 H4 => />. congr. congr. congr. rewrite H6 H4 => />.
 qed.

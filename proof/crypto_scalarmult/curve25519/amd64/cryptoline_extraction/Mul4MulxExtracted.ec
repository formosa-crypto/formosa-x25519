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
  var tmp__data___reduce4 : (W64.t Array4.t)
  var tmp____reduce4 : W64.t Array4.t
  var tmp__data___mul4_c0 : (W64.t Array4.t * W64.t Array4.t * bool * bool)
  var tmp____mul4_c0 : W64.t Array4.t
  var tmp____mul4_c0_0 : W64.t Array4.t
  var tmp____mul4_c0_1 : bool
  var tmp____mul4_c0_2 : bool
  var tmp__data___mul4_c1 : (W64.t Array4.t * W64.t Array4.t * bool * bool)
  var tmp____mul4_c1 : W64.t Array4.t
  var tmp____mul4_c1_0 : W64.t Array4.t
  var tmp____mul4_c1_1 : bool
  var tmp____mul4_c1_2 : bool
  var tmp__data___mul4_c2 : (W64.t Array4.t * W64.t Array4.t * bool * bool)
  var tmp____mul4_c2 : W64.t Array4.t
  var tmp____mul4_c2_0 : W64.t Array4.t
  var tmp____mul4_c2_1 : bool
  var tmp____mul4_c2_2 : bool
  var tmp__data___mul4_c3 : (W64.t Array4.t * W64.t Array4.t * bool * bool)
  var tmp____mul4_c3 : W64.t Array4.t
  var tmp____mul4_c3_0 : W64.t Array4.t
  var tmp____mul4_c3_1 : bool
  var tmp____mul4_c3_2 : bool
  var tmp__data___mul4_rsr : (W64.t Array4.t)
  var tmp____mul4_rsr : W64.t Array4.t
  proc __reduce4 (x:W64.t Array4.t, r:W64.t Array4.t, _38:W64.t, z:W64.t,
                  cf:bool, of_0:bool) : ((W64.t Array4.t) * trace) = {
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
    var old_of:bool;
    var old_cf:bool;
    var old_z:W64.t;
    var old__38:W64.t;
    var old_r:W64.t Array4.t;
    var old_x:W64.t Array4.t;
    var trace___reduce4:trace;
    old_x <- x;
    old_r <- r;
    old__38 <- _38;
    old_z <- z;
    old_cf <- cf;
    old_of <- of_0;
    trace___reduce4 <- [];
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
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! of_0))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i of_0) = 0))]);
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
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (cf = carryo))]);
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assume, ((b2i cf) = (b2i carryo)))]);
    z <- (z `&` (W64.of_int 38));
    trace___reduce4 <-
    (trace___reduce4 ++
    [(Assert,
     (((! cf) /\ (z = (W64.of_int 0))) \/ (cf /\ (z = (W64.of_int 38)))))]);
    trace___reduce4 <-
    (trace___reduce4 ++ [(Assume, ((u64i z) = ((b2i cf) * 38)))]);
    (aux, aux_1) <- (adc_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_1;
    trace___reduce4 <- (trace___reduce4 ++ [(Assert, (! cf))]);
    trace___reduce4 <- (trace___reduce4 ++ [(Assume, ((b2i cf) = 0))]);
    trace___reduce4 <-
    (trace___reduce4 ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_x.[ii]))) (iota_ 0 4))) +
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i old_r.[ii])))
     (iota_ 0 4)))) (single ((pow 2 255) - 19))))]);
    return (h, trace___reduce4);
  }
  proc __mul4_c0 (f0:W64.t, g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : 
  ((W64.t Array4.t * W64.t Array4.t * bool * bool) * trace) = {
    var aux_1:bool;
    var aux_0:W64.t;
    var aux:W64.t;
    var h:W64.t Array4.t;
    var r:W64.t Array4.t;
    var lo:W64.t;
    var old_of:bool;
    var old_cf:bool;
    var old_z:W64.t;
    var old_g:W64.t Array4.t;
    var old_f0:W64.t;
    var trace___mul4_c0:trace;
    old_f0 <- f0;
    old_g <- g;
    old_z <- z;
    old_cf <- cf;
    old_of <- of_0;
    trace___mul4_c0 <- [];
    h <- witness;
    r <- witness;
    (aux_0, aux) <- (MULX_64 f0 g.[0]);
    h.[1] <- aux_0;
    h.[0] <- aux;
    (aux_0, aux) <- (MULX_64 f0 g.[1]);
    h.[2] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[1] lo cf);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_0, aux) <- (MULX_64 f0 g.[2]);
    h.[3] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[2] lo cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_0, aux) <- (MULX_64 f0 g.[3]);
    r.[0] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[3] lo cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[0] z cf);
    cf <- aux_1;
    r.[0] <- aux_0;
    trace___mul4_c0 <- (trace___mul4_c0 ++ [(Assert, (! cf))]);
    trace___mul4_c0 <- (trace___mul4_c0 ++ [(Assume, ((b2i cf) = 0))]);
    return ((h, r, cf, of_0), trace___mul4_c0);
  }
  proc __mul4_c1 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : ((W64.t Array4.t *
                                                                    W64.t Array4.t *
                                                                    bool *
                                                                    bool) *
                                                                   trace) = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var old_of:bool;
    var old_cf:bool;
    var old_z:W64.t;
    var old_g:W64.t Array4.t;
    var old_f:W64.t;
    var old_r:W64.t Array4.t;
    var old_h:W64.t Array4.t;
    var trace___mul4_c1:trace;
    old_h <- h;
    old_r <- r;
    old_f <- f;
    old_g <- g;
    old_z <- z;
    old_cf <- cf;
    old_of <- of_0;
    trace___mul4_c1 <- [];
    (hi, lo) <- (MULX_64 f g.[0]);
    (aux, aux_1) <- (ADOX_64 h.[1] lo of_0);
    of_0 <- aux;
    h.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[2] hi cf);
    cf <- aux;
    h.[2] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[1]);
    (aux, aux_1) <- (ADOX_64 h.[2] lo of_0);
    of_0 <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[3] hi cf);
    cf <- aux;
    h.[3] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[2]);
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[0] hi cf);
    cf <- aux;
    r.[0] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 f g.[3]);
    r.[1] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 r.[0] lo of_0);
    of_0 <- aux;
    r.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[1] z cf);
    cf <- aux;
    r.[1] <- aux_1;
    (aux, aux_1) <- (ADOX_64 r.[1] z of_0);
    of_0 <- aux;
    r.[1] <- aux_1;
    trace___mul4_c1 <- (trace___mul4_c1 ++ [(Assert, (! cf))]);
    trace___mul4_c1 <- (trace___mul4_c1 ++ [(Assume, ((b2i cf) = 0))]);
    trace___mul4_c1 <- (trace___mul4_c1 ++ [(Assert, (! of_0))]);
    trace___mul4_c1 <- (trace___mul4_c1 ++ [(Assume, ((b2i of_0) = 0))]);
    return ((h, r, cf, of_0), trace___mul4_c1);
  }
  proc __mul4_c2 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : ((W64.t Array4.t *
                                                                    W64.t Array4.t *
                                                                    bool *
                                                                    bool) *
                                                                   trace) = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var old_of:bool;
    var old_cf:bool;
    var old_z:W64.t;
    var old_g:W64.t Array4.t;
    var old_f:W64.t;
    var old_r:W64.t Array4.t;
    var old_h:W64.t Array4.t;
    var trace___mul4_c2:trace;
    old_h <- h;
    old_r <- r;
    old_f <- f;
    old_g <- g;
    old_z <- z;
    old_cf <- cf;
    old_of <- of_0;
    trace___mul4_c2 <- [];
    (hi, lo) <- (MULX_64 f g.[0]);
    (aux, aux_1) <- (ADOX_64 h.[2] lo of_0);
    of_0 <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[3] hi cf);
    cf <- aux;
    h.[3] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[1]);
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[0] hi cf);
    cf <- aux;
    r.[0] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[2]);
    (aux, aux_1) <- (ADOX_64 r.[0] lo of_0);
    of_0 <- aux;
    r.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[1] hi cf);
    cf <- aux;
    r.[1] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 f g.[3]);
    r.[2] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 r.[1] lo of_0);
    of_0 <- aux;
    r.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[2] z cf);
    cf <- aux;
    r.[2] <- aux_1;
    (aux, aux_1) <- (ADOX_64 r.[2] z of_0);
    of_0 <- aux;
    r.[2] <- aux_1;
    trace___mul4_c2 <- (trace___mul4_c2 ++ [(Assert, (! cf))]);
    trace___mul4_c2 <- (trace___mul4_c2 ++ [(Assume, ((b2i cf) = 0))]);
    trace___mul4_c2 <- (trace___mul4_c2 ++ [(Assert, (! of_0))]);
    trace___mul4_c2 <- (trace___mul4_c2 ++ [(Assume, ((b2i of_0) = 0))]);
    return ((h, r, cf, of_0), trace___mul4_c2);
  }
  proc __mul4_c3 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : ((W64.t Array4.t *
                                                                    W64.t Array4.t *
                                                                    bool *
                                                                    bool) *
                                                                   trace) = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var old_of:bool;
    var old_cf:bool;
    var old_z:W64.t;
    var old_g:W64.t Array4.t;
    var old_f:W64.t;
    var old_r:W64.t Array4.t;
    var old_h:W64.t Array4.t;
    var trace___mul4_c3:trace;
    old_h <- h;
    old_r <- r;
    old_f <- f;
    old_g <- g;
    old_z <- z;
    old_cf <- cf;
    old_of <- of_0;
    trace___mul4_c3 <- [];
    (hi, lo) <- (MULX_64 f g.[0]);
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[0] hi cf);
    cf <- aux;
    r.[0] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[1]);
    (aux, aux_1) <- (ADOX_64 r.[0] lo of_0);
    of_0 <- aux;
    r.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[1] hi cf);
    cf <- aux;
    r.[1] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[2]);
    (aux, aux_1) <- (ADOX_64 r.[1] lo of_0);
    of_0 <- aux;
    r.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[2] hi cf);
    cf <- aux;
    r.[2] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 f g.[3]);
    r.[3] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 r.[2] lo of_0);
    of_0 <- aux;
    r.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[3] z cf);
    cf <- aux;
    r.[3] <- aux_1;
    (aux, aux_1) <- (ADOX_64 r.[3] z of_0);
    of_0 <- aux;
    r.[3] <- aux_1;
    trace___mul4_c3 <- (trace___mul4_c3 ++ [(Assert, (! cf))]);
    trace___mul4_c3 <- (trace___mul4_c3 ++ [(Assume, ((b2i cf) = 0))]);
    trace___mul4_c3 <- (trace___mul4_c3 ++ [(Assert, (! of_0))]);
    trace___mul4_c3 <- (trace___mul4_c3 ++ [(Assume, ((b2i of_0) = 0))]);
    return ((h, r, cf, of_0), trace___mul4_c3);
  }
  proc __mul4_rsr (fs:W64.t Array4.t, g:W64.t Array4.t) : ((W64.t Array4.t) *
                                                          trace) = {
    var h:W64.t Array4.t;
    var of_0:bool;
    var cf:bool;
    var z:W64.t;
    var g0:W64.t Array4.t;
    var f:W64.t;
    var r:W64.t Array4.t;
    var _38:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var old_g:W64.t Array4.t;
    var old_fs:W64.t Array4.t;
    var trace___mul4_rsr:trace;
    old_fs <- fs;
    old_g <- g;
    trace___mul4_rsr <- [];
    g0 <- witness;
    h <- witness;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, z) <- (set0_64);
    g0 <- (copy_64 g);
    f <- fs.[0];
    (tmp__data___mul4_c0, tmp__trace) <@ __mul4_c0 (f, g0, z, cf, of_0);
    (tmp____mul4_c0, tmp____mul4_c0_0, tmp____mul4_c0_1, tmp____mul4_c0_2) <-
    tmp__data___mul4_c0;
    trace___mul4_rsr <- (trace___mul4_rsr ++ tmp__trace);
    h <- tmp____mul4_c0;
    r <- tmp____mul4_c0_0;
    cf <- tmp____mul4_c0_1;
    of_0 <- tmp____mul4_c0_2;
    f <- fs.[1];
    (tmp__data___mul4_c1, tmp__trace) <@ __mul4_c1 (h, r, f, g0, z, cf,
    of_0);
    (tmp____mul4_c1, tmp____mul4_c1_0, tmp____mul4_c1_1, tmp____mul4_c1_2) <-
    tmp__data___mul4_c1;
    trace___mul4_rsr <- (trace___mul4_rsr ++ tmp__trace);
    h <- tmp____mul4_c1;
    r <- tmp____mul4_c1_0;
    cf <- tmp____mul4_c1_1;
    of_0 <- tmp____mul4_c1_2;
    f <- fs.[2];
    (tmp__data___mul4_c2, tmp__trace) <@ __mul4_c2 (h, r, f, g0, z, cf,
    of_0);
    (tmp____mul4_c2, tmp____mul4_c2_0, tmp____mul4_c2_1, tmp____mul4_c2_2) <-
    tmp__data___mul4_c2;
    trace___mul4_rsr <- (trace___mul4_rsr ++ tmp__trace);
    h <- tmp____mul4_c2;
    r <- tmp____mul4_c2_0;
    cf <- tmp____mul4_c2_1;
    of_0 <- tmp____mul4_c2_2;
    f <- fs.[3];
    (tmp__data___mul4_c3, tmp__trace) <@ __mul4_c3 (h, r, f, g0, z, cf,
    of_0);
    (tmp____mul4_c3, tmp____mul4_c3_0, tmp____mul4_c3_1, tmp____mul4_c3_2) <-
    tmp__data___mul4_c3;
    trace___mul4_rsr <- (trace___mul4_rsr ++ tmp__trace);
    h <- tmp____mul4_c3;
    r <- tmp____mul4_c3_0;
    cf <- tmp____mul4_c3_1;
    of_0 <- tmp____mul4_c3_2;
    _38 <- (W64.of_int 38);
    (tmp__data___reduce4, tmp__trace) <@ __reduce4 (h, r, _38, z, cf, of_0);
    tmp____reduce4 <- tmp__data___reduce4;
    trace___mul4_rsr <- (trace___mul4_rsr ++ tmp__trace);
    trace___mul4_rsr <-
    (trace___mul4_rsr ++
    [(Assume,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
     (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4))) +
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i r.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))]);
    h <- tmp____reduce4;
    trace___mul4_rsr <-
    (trace___mul4_rsr ++
    [(Assert,
     (eqmod
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_fs.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc:int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i old_g.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))]);
    return (h, trace___mul4_rsr);
  }
}.

(* The post is in the trace. *)

lemma __reduce4_valid_post _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      ((_of = of_0) /\
      ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii]))) (iota_ 0 4)
      ))) (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=. auto => />.
qed .

lemma __mul4_c0_valid_post _f0 _g _z _cf _of :
      hoare [M.__mul4_c0 :
      ((_of = of_0) /\ ((_cf = cf) /\ ((_z = z) /\ ((_g = g) /\ (_f0 = f0))))) ==>
      ((valid (trace res)) => true)].
proof.
proc .
wp -1 => /=. auto => />.
qed.

lemma __mul4_c1_valid_post _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c1 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      ((valid (trace res)) => true)].
proof.
proc .
wp -1 => /=. auto => />.
qed.

lemma __mul4_c2_valid_post _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c2 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      ((valid (trace res)) => true)].
proof.
proc .
wp -1 => /=. auto => />.
qed.

lemma __mul4_c3_valid_post _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c3 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      ((valid (trace res)) => true)].
proof.
proc .
wp -1 => /=. auto => />.
qed .

lemma __mul4_rsr_valid_post _fs _g :
      hoare [M.__mul4_rsr :
      ((_g = g) /\ (_fs = fs)) ==>
      ((valid (trace res)) =>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))))].
proof.
proc .
wp -1 => /=.
conseq (:  _ ==> ((_g = old_g) /\ (_fs = old_fs))).
move => ? _ /> 2?.
rewrite /trace /= valid_cat /valid //=.
seq 2 : (((_g = old_g) /\ (_fs = old_fs))).
by auto .
by conseq  />.
qed .

(* The post is in the trace and all assumes are valid. *)

lemma __reduce4_assume_ _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      ((_of = of_0) /\
      ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) ==>
      (true => (validk Assume (trace res)))].
proof.
    proc. auto => />. move => H H0 H1. 
    smt(@JUtils @Zp_25519 @Jcheck @W64).
qed.

lemma __reduce4_assume _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      ((_of = of_0) /\
      ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii])))
       (iota_ 0 4)))) (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__reduce4_assume_ _x _r __38 _z _cf _of) (__reduce4_valid_post 
                                                  _x _r __38 _z _cf _of) 
       => />.
qed .

lemma __mul4_c0_assume_ _f0 _g _z _cf _of :
      hoare [M.__mul4_c0 :
      ((_of = of_0) /\ ((_cf = cf) /\ ((_z = z) /\ ((_g = g) /\ (_f0 = f0))))) ==>
      (true => (validk Assume (trace res)))].
proof.
    proc. auto => />.
qed.

lemma __mul4_c0_assume _f0 _g _z _cf _of :
      hoare [M.__mul4_c0 :
      ((_of = of_0) /\ ((_cf = cf) /\ ((_z = z) /\ ((_g = g) /\ (_f0 = f0))))) ==>
      (((valid (trace res)) => true) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__mul4_c0_assume_ _f0 _g _z _cf _of) (__mul4_c0_valid_post _f0 
                                              _g _z _cf _of) => />.
qed .

lemma __mul4_c1_assume_ _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c1 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      (true => (validk Assume (trace res)))].
proof.
    proc. auto => />.
qed.

lemma __mul4_c1_assume _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c1 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      (((valid (trace res)) => true) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__mul4_c1_assume_ _h _r _f _g _z _cf _of) (__mul4_c1_valid_post 
                                                   _h _r _f _g _z _cf 
                                                   _of) => />.
qed .

lemma __mul4_c2_assume_ _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c2 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      (true => (validk Assume (trace res)))].
proof.
    proc. auto => />.
qed.

lemma __mul4_c2_assume _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c2 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      (((valid (trace res)) => true) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__mul4_c2_assume_ _h _r _f _g _z _cf _of) (__mul4_c2_valid_post 
                                                   _h _r _f _g _z _cf 
                                                   _of) => />.
qed .

lemma __mul4_c3_assume_ _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c3 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      (true => (validk Assume (trace res)))].
proof.
    proc. auto => />.
qed.

lemma __mul4_c3_assume _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c3 :
      ((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) ==>
      (((valid (trace res)) => true) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__mul4_c3_assume_ _h _r _f _g _z _cf _of) (__mul4_c3_valid_post 
                                                   _h _r _f _g _z _cf 
                                                   _of) => />.
qed .

lemma __mul4_rsr_assume_ _fs _g :
      hoare [M.__mul4_rsr :
      ((_g = g) /\ (_fs = fs)) ==> (true => (validk Assume (trace res)))].
proof.
    proc. auto => />.
    ecall (__reduce4_assume h r _38 z cf of_0). auto => />.
    smt (valid_cat all_cat).
    ecall (__mul4_c3_assume h r f g0 z cf of_0). auto => />.
    ecall (__mul4_c2_assume h r f g0 z cf of_0). auto => />.
    ecall (__mul4_c1_assume h r f g0 z cf of_0). auto => />.
    ecall (__mul4_c0_assume f g0 z cf of_0). auto => />.
    move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    rewrite !/trace //= !validk_cat //=. 
    rewrite !valid_cat //=. smt(forall_validk_valid).
qed.

lemma __mul4_rsr_assume _fs _g :
      hoare [M.__mul4_rsr :
      ((_g = g) /\ (_fs = fs)) ==>
      (((valid (trace res)) =>
       (eqmod
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4))
       )
       ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
        (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
       (foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
       (single ((pow 2 255) - 19)))) /\
      (true => (validk Assume (trace res))))].
proof.
conseq (__mul4_rsr_assume_ _fs _g) (__mul4_rsr_valid_post _fs _g) => />.
qed .

(* All assert are valid. *)

lemma __reduce4_assert _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      (((_of = of_0) /\
       ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) /\
      true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

lemma __mul4_c0_assert _f0 _g _z _cf _of :
      hoare [M.__mul4_c0 :
      (((_of = of_0) /\ ((_cf = cf) /\ ((_z = z) /\ ((_g = g) /\ (_f0 = f0))))) /\
      true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

lemma __mul4_c1_assert _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c1 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

lemma __mul4_c2_assert _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c2 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

lemma __mul4_c3_assert _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c3 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

lemma __mul4_rsr_assert _fs _g :
      hoare [M.__mul4_rsr :
      (((_g = g) /\ (_fs = fs)) /\ true) ==> (validk Assert (trace res))].
proof.
admitted (* Proven by Cryptoline *).

(* Final specification for the functions. *)

lemma __reduce4_spec _x _r __38 _z _cf _of :
      hoare [M.__reduce4 :
      (((_of = of_0) /\
       ((_cf = cf) /\ ((_z = z) /\ ((__38 = _38) /\ ((_r = r) /\ (_x = x)))))) /\
      true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _x.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i _r.[ii]))) (iota_ 0 4)
      ))) (single ((pow 2 255) - 19)))].
proof.
conseq (__reduce4_assume _x _r __38 _z _cf _of) (__reduce4_assert _x 
                                                 _r __38 _z _cf _of) 
       => />.
smt (all_validk_valid).
qed .

lemma __mul4_c0_spec _f0 _g _z _cf _of :
      hoare [M.__mul4_c0 :
      (((_of = of_0) /\ ((_cf = cf) /\ ((_z = z) /\ ((_g = g) /\ (_f0 = f0))))) /\
      true) ==> true].
proof.
conseq (__mul4_c0_assume _f0 _g _z _cf _of) (__mul4_c0_assert _f0 _g 
                                             _z _cf _of) => />.
qed .

lemma __mul4_c1_spec _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c1 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> true].
proof.
conseq (__mul4_c1_assume _h _r _f _g _z _cf _of) (__mul4_c1_assert _h 
                                                  _r _f _g _z _cf _of) 
       => />.
qed .

lemma __mul4_c2_spec _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c2 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> true].
proof.
conseq (__mul4_c2_assume _h _r _f _g _z _cf _of) (__mul4_c2_assert _h 
                                                  _r _f _g _z _cf _of) 
       => />.
qed .

lemma __mul4_c3_spec _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c3 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> true].
proof.
conseq (__mul4_c3_assume _h _r _f _g _z _cf _of) (__mul4_c3_assert _h 
                                                  _r _f _g _z _cf _of) 
       => />.
qed .

lemma __mul4_rsr_spec _fs _g :
      hoare [M.__mul4_rsr :
      (((_g = g) /\ (_fs = fs)) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc:int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
conseq (__mul4_rsr_assume _fs _g) (__mul4_rsr_assert _fs _g) => />.
smt (all_validk_valid).
qed .

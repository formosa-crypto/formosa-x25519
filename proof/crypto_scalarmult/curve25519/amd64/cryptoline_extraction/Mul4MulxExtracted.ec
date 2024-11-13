require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Jcheck.

require import Array4.

require import WArray32.


require import Jcheck Zp_limbs Zp_25519 CommonCryptoline.
import Zp_25519 Zp Zp_limbs EClib.


module M = {
  var tmp__check : to_check
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
  proc __mul4_c0 (f0:W64.t, g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : 
  ((W64.t Array4.t * W64.t Array4.t * bool * bool) * to_check) = {
    var aux_1:bool;
    var aux_0:W64.t;
    var aux:W64.t;
    var h:W64.t Array4.t;
    var r:W64.t Array4.t;
    var lo:W64.t;
    var assume___mul4_c0:bool;
    var assert___mul4_c0:bool;
    var assume_proof___mul4_c0:bool;
    var assert_proof___mul4_c0:bool;
    assume___mul4_c0 <- true;
    assert___mul4_c0 <- true;
    assume_proof___mul4_c0 <- true;
    assert_proof___mul4_c0 <- assert___mul4_c0;
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
    assert_proof___mul4_c0 <-
    (assert_proof___mul4_c0 /\
    ((assert___mul4_c0 /\ assume___mul4_c0) => (! cf)));
    assert___mul4_c0 <- (assert___mul4_c0 /\ (! cf));
    assume_proof___mul4_c0 <-
    (assume_proof___mul4_c0 /\
    ((assert___mul4_c0 /\ assume___mul4_c0) => ((b2i cf) = 0)));
    assume___mul4_c0 <- (assume___mul4_c0 /\ ((b2i cf) = 0));
    return ((h, r, cf, of_0),
           (assume___mul4_c0, assert___mul4_c0, assume_proof___mul4_c0,
           assert_proof___mul4_c0));
  }
  proc __mul4_c1 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : ((W64.t Array4.t *
                                                                    W64.t Array4.t *
                                                                    bool *
                                                                    bool) *
                                                                   to_check) = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var assume___mul4_c1:bool;
    var assert___mul4_c1:bool;
    var assume_proof___mul4_c1:bool;
    var assert_proof___mul4_c1:bool;
    assume___mul4_c1 <- true;
    assert___mul4_c1 <- true;
    assume_proof___mul4_c1 <- true;
    assert_proof___mul4_c1 <- assert___mul4_c1;
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
    assert_proof___mul4_c1 <-
    (assert_proof___mul4_c1 /\
    ((assert___mul4_c1 /\ assume___mul4_c1) => (! cf)));
    assert___mul4_c1 <- (assert___mul4_c1 /\ (! cf));
    assume_proof___mul4_c1 <-
    (assume_proof___mul4_c1 /\
    ((assert___mul4_c1 /\ assume___mul4_c1) => ((b2i cf) = 0)));
    assume___mul4_c1 <- (assume___mul4_c1 /\ ((b2i cf) = 0));
    assert_proof___mul4_c1 <-
    (assert_proof___mul4_c1 /\
    ((assert___mul4_c1 /\ assume___mul4_c1) => (! of_0)));
    assert___mul4_c1 <- (assert___mul4_c1 /\ (! of_0));
    assume_proof___mul4_c1 <-
    (assume_proof___mul4_c1 /\
    ((assert___mul4_c1 /\ assume___mul4_c1) => ((b2i of_0) = 0)));
    assume___mul4_c1 <- (assume___mul4_c1 /\ ((b2i of_0) = 0));
    return ((h, r, cf, of_0),
           (assume___mul4_c1, assert___mul4_c1, assume_proof___mul4_c1,
           assert_proof___mul4_c1));
  }
  proc __mul4_c2 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : ((W64.t Array4.t *
                                                                    W64.t Array4.t *
                                                                    bool *
                                                                    bool) *
                                                                   to_check) = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var assume___mul4_c2:bool;
    var assert___mul4_c2:bool;
    var assume_proof___mul4_c2:bool;
    var assert_proof___mul4_c2:bool;
    assume___mul4_c2 <- true;
    assert___mul4_c2 <- true;
    assume_proof___mul4_c2 <- true;
    assert_proof___mul4_c2 <- assert___mul4_c2;
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
    assert_proof___mul4_c2 <-
    (assert_proof___mul4_c2 /\
    ((assert___mul4_c2 /\ assume___mul4_c2) => (! cf)));
    assert___mul4_c2 <- (assert___mul4_c2 /\ (! cf));
    assume_proof___mul4_c2 <-
    (assume_proof___mul4_c2 /\
    ((assert___mul4_c2 /\ assume___mul4_c2) => ((b2i cf) = 0)));
    assume___mul4_c2 <- (assume___mul4_c2 /\ ((b2i cf) = 0));
    assert_proof___mul4_c2 <-
    (assert_proof___mul4_c2 /\
    ((assert___mul4_c2 /\ assume___mul4_c2) => (! of_0)));
    assert___mul4_c2 <- (assert___mul4_c2 /\ (! of_0));
    assume_proof___mul4_c2 <-
    (assume_proof___mul4_c2 /\
    ((assert___mul4_c2 /\ assume___mul4_c2) => ((b2i of_0) = 0)));
    assume___mul4_c2 <- (assume___mul4_c2 /\ ((b2i of_0) = 0));
    return ((h, r, cf, of_0),
           (assume___mul4_c2, assert___mul4_c2, assume_proof___mul4_c2,
           assert_proof___mul4_c2));
  }
  proc __mul4_c3 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : ((W64.t Array4.t *
                                                                    W64.t Array4.t *
                                                                    bool *
                                                                    bool) *
                                                                   to_check) = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var assume___mul4_c3:bool;
    var assert___mul4_c3:bool;
    var assume_proof___mul4_c3:bool;
    var assert_proof___mul4_c3:bool;
    assume___mul4_c3 <- true;
    assert___mul4_c3 <- true;
    assume_proof___mul4_c3 <- true;
    assert_proof___mul4_c3 <- assert___mul4_c3;
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
    assert_proof___mul4_c3 <-
    (assert_proof___mul4_c3 /\
    ((assert___mul4_c3 /\ assume___mul4_c3) => (! cf)));
    assert___mul4_c3 <- (assert___mul4_c3 /\ (! cf));
    assume_proof___mul4_c3 <-
    (assume_proof___mul4_c3 /\
    ((assert___mul4_c3 /\ assume___mul4_c3) => ((b2i cf) = 0)));
    assume___mul4_c3 <- (assume___mul4_c3 /\ ((b2i cf) = 0));
    assert_proof___mul4_c3 <-
    (assert_proof___mul4_c3 /\
    ((assert___mul4_c3 /\ assume___mul4_c3) => (! of_0)));
    assert___mul4_c3 <- (assert___mul4_c3 /\ (! of_0));
    assume_proof___mul4_c3 <-
    (assume_proof___mul4_c3 /\
    ((assert___mul4_c3 /\ assume___mul4_c3) => ((b2i of_0) = 0)));
    assume___mul4_c3 <- (assume___mul4_c3 /\ ((b2i of_0) = 0));
    return ((h, r, cf, of_0),
           (assume___mul4_c3, assert___mul4_c3, assume_proof___mul4_c3,
           assert_proof___mul4_c3));
  }
  proc __mul4_rsr (fs:W64.t Array4.t, g:W64.t Array4.t) : ((W64.t Array4.t) *
                                                          to_check) = {
    var h:W64.t Array4.t;
    var of_0:bool;
    var cf:bool;
    var z:W64.t;
    var f:W64.t;
    var r:W64.t Array4.t;
    var _38:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var assume___mul4_rsr:bool;
    var assert___mul4_rsr:bool;
    var assume_proof___mul4_rsr:bool;
    var assert_proof___mul4_rsr:bool;
    assume___mul4_rsr <- true;
    assert___mul4_rsr <- true;
    assume_proof___mul4_rsr <- true;
    assert_proof___mul4_rsr <- assert___mul4_rsr;
    h <- witness;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, z) <- (set0_64);
    f <- fs.[0];
    (tmp__data___mul4_c0, tmp__check) <@ __mul4_c0 (f, g, z, cf, of_0);
    (tmp____mul4_c0, tmp____mul4_c0_0, tmp____mul4_c0_1, tmp____mul4_c0_2) <-
    tmp__data___mul4_c0;
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) <-
    (upd_call
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) tmp__check);
    h <- tmp____mul4_c0;
    r <- tmp____mul4_c0_0;
    cf <- tmp____mul4_c0_1;
    of_0 <- tmp____mul4_c0_2;
    f <- fs.[1];
    (tmp__data___mul4_c1, tmp__check) <@ __mul4_c1 (h, r, f, g, z, cf, of_0);
    (tmp____mul4_c1, tmp____mul4_c1_0, tmp____mul4_c1_1, tmp____mul4_c1_2) <-
    tmp__data___mul4_c1;
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) <-
    (upd_call
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) tmp__check);
    h <- tmp____mul4_c1;
    r <- tmp____mul4_c1_0;
    cf <- tmp____mul4_c1_1;
    of_0 <- tmp____mul4_c1_2;
    f <- fs.[2];
    (tmp__data___mul4_c2, tmp__check) <@ __mul4_c2 (h, r, f, g, z, cf, of_0);
    (tmp____mul4_c2, tmp____mul4_c2_0, tmp____mul4_c2_1, tmp____mul4_c2_2) <-
    tmp__data___mul4_c2;
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) <-
    (upd_call
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) tmp__check);
    h <- tmp____mul4_c2;
    r <- tmp____mul4_c2_0;
    cf <- tmp____mul4_c2_1;
    of_0 <- tmp____mul4_c2_2;
    f <- fs.[3];
    (tmp__data___mul4_c3, tmp__check) <@ __mul4_c3 (h, r, f, g, z, cf, of_0);
    (tmp____mul4_c3, tmp____mul4_c3_0, tmp____mul4_c3_1, tmp____mul4_c3_2) <-
    tmp__data___mul4_c3;
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) <-
    (upd_call
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) tmp__check);
    h <- tmp____mul4_c3;
    r <- tmp____mul4_c3_0;
    cf <- tmp____mul4_c3_1;
    of_0 <- tmp____mul4_c3_2;
    _38 <- (W64.of_int 38);
    (tmp__data___reduce4, tmp__check) <@ __reduce4 (h, r, _38, z, cf, of_0);
    tmp____reduce4 <- tmp__data___reduce4;
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) <-
    (upd_call
    (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
    assert_proof___mul4_rsr) tmp__check);
    assert_proof___mul4_rsr <-
    (assert_proof___mul4_rsr /\
    ((assert___mul4_rsr /\ assume___mul4_rsr) =>
    (eqmod
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * ii)) * (u64i tmp____reduce4.[ii])))
    (iota_ 0 4)))
    ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4))) +
    (foldr (fun x => (fun (acc: int) => (x + acc))) 0
    (map (fun ii => ((pow 2 (64 * (ii + 4))) * (u64i r.[ii]))) (iota_ 0 4))))
    (single ((pow 2 255) - 19)))));
    assert___mul4_rsr <-
    (assert___mul4_rsr /\
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
           (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr,
           assert_proof___mul4_rsr));
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

lemma __mul4_c0_assume  : hoare [M.__mul4_c0 : true ==> (assume_proof_ res)].
proof.
    proc. 
    seq 5 : (assume_proof__ (assume___mul4_c0, assert___mul4_c0, assume_proof___mul4_c0, assert_proof___mul4_c0)). auto => />.
    auto => />. 
qed.


lemma __mul4_c1_assume  : hoare [M.__mul4_c1 : true ==> (assume_proof_ res)].
proof.
    proc. 
    seq 5 : (assume_proof__ (assume___mul4_c1, assert___mul4_c1, assume_proof___mul4_c1, assert_proof___mul4_c1)). auto => />.
    auto => />. 
qed.

lemma __mul4_c2_assume  : hoare [M.__mul4_c2 : true ==> (assume_proof_ res)].
proof.
    proc. 
    seq 5 : (assume_proof__ (assume___mul4_c2, assert___mul4_c2, assume_proof___mul4_c2, assert_proof___mul4_c2)). auto => />.
    auto => />. 
qed.

lemma __mul4_c3_assume  : hoare [M.__mul4_c3 : true ==> (assume_proof_ res)].
proof.
    proc. 
    seq 5 : (assume_proof__ (assume___mul4_c3, assert___mul4_c3, assume_proof___mul4_c3, assert_proof___mul4_c3)). auto => />.
    auto => />. 
qed.

lemma __mul4_rsr_assume  :
      hoare [M.__mul4_rsr : true ==> (assume_proof_ res)].
proof.
    proc.  
    seq 8 : (assume_proof__ (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr, assert_proof___mul4_rsr)). auto => />.
    wp; call __reduce4_assume.
    wp; call __mul4_c3_assume.
    wp; call __mul4_c2_assume.
    wp; call __mul4_c1_assume.
    wp; call __mul4_c0_assume.
    auto => />.
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

lemma __mul4_c0_assert_assume_sound  :
      hoare [M.__mul4_c0 : true ==> (soundness_ res)].
proof.
 proc. 
 seq 5 : (soundness__ (assume___mul4_c0, assert___mul4_c0, assume_proof___mul4_c0, assert_proof___mul4_c0)). auto => />. auto => />. 
  smt().
qed.


lemma __mul4_c1_assert_assume_sound  :
      hoare [M.__mul4_c1 : true ==> (soundness_ res)].
proof.
 proc. 
 seq 5 : (soundness__ (assume___mul4_c1, assert___mul4_c1, assume_proof___mul4_c1, assert_proof___mul4_c1)). auto => />. auto => />. 
  smt().
qed.

lemma __mul4_c2_assert_assume_sound  :
      hoare [M.__mul4_c2 : true ==> (soundness_ res)].
proof.
 proc. 
 seq 5 : (soundness__ (assume___mul4_c2, assert___mul4_c2, assume_proof___mul4_c2, assert_proof___mul4_c2)). auto => />. auto => />. 
  smt().
qed.

lemma __mul4_c3_assert_assume_sound  :
      hoare [M.__mul4_c3 : true ==> (soundness_ res)].
proof.
 proc. 
 seq 5 : (soundness__ (assume___mul4_c3, assert___mul4_c3, assume_proof___mul4_c3, assert_proof___mul4_c3)). auto => />. auto => />. 
  smt().
qed.

lemma __mul4_rsr_assert_assume_sound  :
      hoare [M.__mul4_rsr : true ==> (soundness_ res)].
proof.
    proc.  
    seq 8 : (soundness__ (assume___mul4_rsr, assert___mul4_rsr, assume_proof___mul4_rsr, assert_proof___mul4_rsr)). auto => />.
    wp; call __reduce4_assert_assume_sound.
    wp; call __mul4_c3_assert_assume_sound.
    wp; call __mul4_c2_assert_assume_sound.
    wp; call __mul4_c1_assert_assume_sound.
    wp; call __mul4_c0_assert_assume_sound.
    auto => />. smt().
qed.

(* Lemmas proved by cryptoline. *)

(* of is a reserved keyword, rename to of_0 *)
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

axiom __mul4_c0_assert _f0 _g _z _cf _of :
      hoare [M.__mul4_c0 :
      (((_of = of_0) /\ ((_cf = cf) /\ ((_z = z) /\ ((_g = g) /\ (_f0 = f0))))) /\
      true) ==> (_assert_spec res true)].

axiom __mul4_c1_assert _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c1 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> (_assert_spec res true)].

axiom __mul4_c2_assert _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c2 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> (_assert_spec res true)].

axiom __mul4_c3_assert _h _r _f _g _z _cf _of :
      hoare [M.__mul4_c3 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> (_assert_spec res true)].

axiom __mul4_rsr_assert _fs _g :
      hoare [M.__mul4_rsr :
      (((_g = g) /\ (_fs = fs)) /\ true) ==>
      (_assert_spec res
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
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

lemma __mul4_c0_spec  :
      forall _f0 _g _z _cf _of,
      hoare [M.__mul4_c0 :
      (((_of = of_0) /\ ((_cf = cf) /\ ((_z = z) /\ ((_g = g) /\ (_f0 = f0))))) /\
      true) ==> true].
proof.
move => _f0 _g _z _cf _of.
have h  :
     hoare [M.__mul4_c0 :
     (((_of = of_0) /\ ((_cf = cf) /\ ((_z = z) /\ ((_g = g) /\ (_f0 = f0))))) /\
     true) ==> (_spec_soundness res true)].
by conseq __mul4_c0_assume (__mul4_c0_assert _f0 _g _z _cf _of).
conseq h __mul4_c0_assert_assume_sound => // ; smt ().
qed .

lemma __mul4_c1_spec  :
      forall _h _r _f _g _z _cf _of,
      hoare [M.__mul4_c1 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> true].
proof.
move => _h _r _f _g _z _cf _of.
have h  :
     hoare [M.__mul4_c1 :
     (((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
     true) ==> (_spec_soundness res true)].
by conseq __mul4_c1_assume (__mul4_c1_assert _h _r _f _g _z _cf _of).
conseq h __mul4_c1_assert_assume_sound => // ; smt ().
qed .

lemma __mul4_c2_spec  :
      forall _h _r _f _g _z _cf _of,
      hoare [M.__mul4_c2 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> true].
proof.
move => _h _r _f _g _z _cf _of.
have h  :
     hoare [M.__mul4_c2 :
     (((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
     true) ==> (_spec_soundness res true)].
by conseq __mul4_c2_assume (__mul4_c2_assert _h _r _f _g _z _cf _of).
conseq h __mul4_c2_assert_assume_sound => // ; smt ().
qed .

lemma __mul4_c3_spec  :
      forall _h _r _f _g _z _cf _of,
      hoare [M.__mul4_c3 :
      (((_of = of_0) /\
       ((_cf = cf) /\
       ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
      true) ==> true].
proof.
move => _h _r _f _g _z _cf _of.
have h  :
     hoare [M.__mul4_c3 :
     (((_of = of_0) /\
      ((_cf = cf) /\
      ((_z = z) /\ ((_g = g) /\ ((_f = f) /\ ((_r = r) /\ (_h = h))))))) /\
     true) ==> (_spec_soundness res true)].
by conseq __mul4_c3_assume (__mul4_c3_assert _h _r _f _g _z _cf _of).
conseq h __mul4_c3_assert_assume_sound => // ; smt ().
qed .

lemma __mul4_rsr_spec  :
      forall _fs _g,
      hoare [M.__mul4_rsr :
      (((_g = g) /\ (_fs = fs)) /\ true) ==>
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19)))].
proof.
move => _fs _g.
have h  :
     hoare [M.__mul4_rsr :
     (((_g = g) /\ (_fs = fs)) /\ true) ==>
     (_spec_soundness res
     (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i res.`1.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _fs.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))))].
by conseq __mul4_rsr_assume (__mul4_rsr_assert _fs _g).
conseq h __mul4_rsr_assert_assume_sound => // ; smt ().
qed .

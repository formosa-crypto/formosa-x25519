require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4 Array5 Array32.
require import WArray32 WArray40.



module M = {
  proc __ith_bit (k:W8.t Array32.t, ctr:W64.t) : W64.t = {
    
    var bit:W64.t;
    var p:W64.t;
    
    p <- ctr;
    p <- (p `>>` (W8.of_int 3));
    bit <- (zeroextu64 k.[(W64.to_uint p)]);
    p <- ctr;
    p <- (p `&` (W64.of_int 7));
    bit <- (bit `>>` (truncateu8 (p `&` (W64.of_int 63))));
    bit <- (bit `&` (W64.of_int 1));
    return (bit);
  }
  
  proc __decode_scalar (k:W64.t Array4.t) : W8.t Array32.t = {
    var aux: int;
    
    var ks:W8.t Array32.t;
    var i:int;
    ks <- witness;
    i <- 0;
    while (i < 4) {
      ks <-
      Array32.init
      (WArray32.get8 (WArray32.set64 (WArray32.init8 (fun i_0 => (ks).[i_0])) i (
      k.[i])));
      i <- i + 1;
    }
    ks.[0] <- (ks.[0] `&` (W8.of_int 248));
    ks.[31] <- (ks.[31] `&` (W8.of_int 127));
    ks.[31] <- (ks.[31] `|` (W8.of_int 64));
    return (ks);
  }
  
  proc __decode_u_coordinate5 (t:W64.t Array4.t) : W64.t Array5.t = {
    
    var u:W64.t Array5.t;
    var mask:W64.t;
    u <- witness;
    mask <- (W64.of_int 2251799813685247);
    u.[0] <- t.[0];
    u.[0] <- (u.[0] `&` mask);
    u.[1] <- t.[1];
    u.[1] <- (u.[1] `<<` (W8.of_int 13));
    t.[0] <- (t.[0] `>>` (W8.of_int 51));
    u.[1] <- (u.[1] `|` t.[0]);
    u.[1] <- (u.[1] `&` mask);
    u.[2] <- t.[2];
    u.[2] <- (u.[2] `<<` (W8.of_int 26));
    t.[1] <- (t.[1] `>>` (W8.of_int 38));
    u.[2] <- (u.[2] `|` t.[1]);
    u.[2] <- (u.[2] `&` mask);
    u.[3] <- t.[3];
    u.[3] <- (u.[3] `<<` (W8.of_int 39));
    t.[2] <- (t.[2] `>>` (W8.of_int 25));
    u.[3] <- (u.[3] `|` t.[2]);
    u.[3] <- (u.[3] `&` mask);
    u.[4] <- t.[3];
    u.[4] <- (u.[4] `>>` (W8.of_int 12));
    u.[4] <- (u.[4] `&` mask);
    return (u);
  }
  
  proc __decode_u_coordinate_base5 () : W64.t Array5.t = {
    
    var u:W64.t Array5.t;
    u <- witness;
    u.[0] <- (W64.of_int 9);
    u.[1] <- (W64.of_int 0);
    u.[2] <- (W64.of_int 0);
    u.[3] <- (W64.of_int 0);
    u.[4] <- (W64.of_int 0);
    return (u);
  }
  
  proc __init_points5 (initr:W64.t Array5.t) : W64.t Array5.t *
                                               W64.t Array5.t *
                                               W64.t Array5.t *
                                               W64.t Array5.t = {
    var aux: int;
    
    var x2:W64.t Array5.t;
    var z2r:W64.t Array5.t;
    var x3:W64.t Array5.t;
    var z3:W64.t Array5.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var z:W64.t;
    var i:int;
    var  _0:bool;
    x2 <- witness;
    x3 <- witness;
    z2r <- witness;
    z3 <- witness;
    (_of_, _cf_, _sf_,  _0, _zf_, z) <- set0_64 ;
    x2.[0] <- (W64.of_int 1);
    z2r.[0] <- (W64.of_int 0);
    x3 <- copy_64 initr;
    z3.[0] <- (W64.of_int 1);
    i <- 1;
    while (i < 5) {
      x2.[i] <- z;
      z2r.[i] <- z;
      z3.[i] <- z;
      i <- i + 1;
    }
    return (x2, z2r, x3, z3);
  }
  
  proc __add5_rrs (f:W64.t Array5.t, g:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    
    var h:W64.t Array5.t;
    var i:int;
    h <- witness;
    h <- copy_64 f;
    h.[0] <- (h.[0] + g.[0]);
    i <- 1;
    while (i < 5) {
      h.[i] <- (h.[i] + g.[i]);
      i <- i + 1;
    }
    return (h);
  }
  
  proc __add5_sss (fs:W64.t Array5.t, gs:W64.t Array5.t) : W64.t Array5.t = {
    
    var hs:W64.t Array5.t;
    var f:W64.t Array5.t;
    var h:W64.t Array5.t;
    f <- witness;
    h <- witness;
    hs <- witness;
    f <- copy_64 fs;
    h <@ __add5_rrs (f, gs);
    hs <- copy_64 h;
    return (hs);
  }
  
  proc __add5_ssr (fs:W64.t Array5.t, g:W64.t Array5.t) : W64.t Array5.t = {
    
    var hs:W64.t Array5.t;
    var h:W64.t Array5.t;
    h <- witness;
    hs <- witness;
    h <@ __add5_rrs (g, fs);
    hs <- copy_64 h;
    return (hs);
  }
  
  proc __sub5_rrs (f:W64.t Array5.t, gs:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    
    var h:W64.t Array5.t;
    var _2p0:W64.t;
    var _2p1234:W64.t;
    var i:int;
    h <- witness;
    _2p0 <- (W64.of_int 4503599627370458);
    _2p1234 <- (W64.of_int 4503599627370494);
    h <- copy_64 f;
    h.[0] <- (h.[0] + _2p0);
    i <- 1;
    while (i < 5) {
      h.[i] <- (h.[i] + _2p1234);
      i <- i + 1;
    }
    i <- 0;
    while (i < 5) {
      h.[i] <- (h.[i] - gs.[i]);
      i <- i + 1;
    }
    return (h);
  }
  
  proc __sub5_sss (fs:W64.t Array5.t, gs:W64.t Array5.t) : W64.t Array5.t = {
    
    var hs:W64.t Array5.t;
    var f:W64.t Array5.t;
    var h:W64.t Array5.t;
    f <- witness;
    h <- witness;
    hs <- witness;
    f <- copy_64 fs;
    h <@ __sub5_rrs (f, gs);
    hs <- copy_64 h;
    return (hs);
  }
  
  proc __sub5_rsr (fs:W64.t Array5.t, g:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    
    var h:W64.t Array5.t;
    var _2p0:W64.t;
    var _2p1234:W64.t;
    var i:int;
    h <- witness;
    _2p0 <- (W64.of_int 4503599627370458);
    _2p1234 <- (W64.of_int 4503599627370494);
    h <- copy_64 fs;
    h.[0] <- (h.[0] + _2p0);
    i <- 1;
    while (i < 5) {
      h.[i] <- (h.[i] + _2p1234);
      i <- i + 1;
    }
    i <- 0;
    while (i < 5) {
      h.[i] <- (h.[i] - g.[i]);
      i <- i + 1;
    }
    return (h);
  }
  
  proc __sub5_ssr (fs:W64.t Array5.t, g:W64.t Array5.t) : W64.t Array5.t = {
    
    var hs:W64.t Array5.t;
    var h:W64.t Array5.t;
    h <- witness;
    hs <- witness;
    h <@ __sub5_rsr (fs, g);
    hs <- copy_64 h;
    return (hs);
  }
  
  proc __cswap5 (x2:W64.t Array5.t, z2r:W64.t Array5.t, x3:W64.t Array5.t,
                 z3:W64.t Array5.t, toswap:W64.t) : W64.t Array5.t *
                                                    W64.t Array5.t *
                                                    W64.t Array5.t *
                                                    W64.t Array5.t = {
    var aux: int;
    
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var mask:W64.t;
    var t4:W64.t Array5.t;
    var i:int;
    var t:W64.t;
    var x3r:W64.t Array5.t;
    var x2r:W64.t Array5.t;
    var  _0:bool;
    t4 <- witness;
    x2r <- witness;
    x3r <- witness;
    (_of_, _cf_, _sf_,  _0, _zf_, mask) <- set0_64 ;
    mask <- (mask - toswap);
    t4 <- copy_64 z2r;
    i <- 0;
    while (i < 5) {
      t4.[i] <- (t4.[i] `^` z3.[i]);
      t4.[i] <- (t4.[i] `&` mask);
      i <- i + 1;
    }
    i <- 0;
    while (i < 5) {
      z2r.[i] <- (z2r.[i] `^` t4.[i]);
      t <- z3.[i];
      t <- (t `^` t4.[i]);
      z3.[i] <- t;
      i <- i + 1;
    }
    x3r <- copy_64 x3;
    i <- 0;
    while (i < 5) {
      x2r.[i] <- x2.[i];
      t <- x3r.[i];
      t <- (t `^` x2r.[i]);
      t <- (t `&` mask);
      x2r.[i] <- (x2r.[i] `^` t);
      x3r.[i] <- (x3r.[i] `^` t);
      x2.[i] <- x2r.[i];
      x3.[i] <- x3r.[i];
      i <- i + 1;
    }
    return (x2, z2r, x3, z3);
  }
  
  proc __tobytes5 (f:W64.t Array5.t) : W64.t Array4.t = {
    
    var h:W64.t Array4.t;
    var two51minus1:W64.t;
    var two51minus19:W64.t;
    var loop:W64.t;
    var t:W64.t;
    var eq:bool;
    h <- witness;
    two51minus1 <- (W64.of_int 2251799813685247);
    two51minus19 <- two51minus1;
    two51minus19 <- (two51minus19 - (W64.of_int 18));
    loop <- (W64.of_int 3);
    
    while (((W64.of_int 0) \ult loop)) {
      t <- f.[0];
      t <- (t `>>` (W8.of_int 51));
      f.[0] <- (f.[0] `&` two51minus1);
      f.[1] <- (f.[1] + t);
      t <- f.[1];
      t <- (t `>>` (W8.of_int 51));
      f.[1] <- (f.[1] `&` two51minus1);
      f.[2] <- (f.[2] + t);
      t <- f.[2];
      t <- (t `>>` (W8.of_int 51));
      f.[2] <- (f.[2] `&` two51minus1);
      f.[3] <- (f.[3] + t);
      t <- f.[3];
      t <- (t `>>` (W8.of_int 51));
      f.[3] <- (f.[3] `&` two51minus1);
      f.[4] <- (f.[4] + t);
      t <- f.[4];
      t <- (t `>>` (W8.of_int 51));
      f.[4] <- (f.[4] `&` two51minus1);
      t <- (t * (W64.of_int 19));
      f.[0] <- (f.[0] + t);
      loop <- (loop - (W64.of_int 1));
    }
    t <- (W64.of_int 1);
    t <- ((f.[0] \slt two51minus19) ? loop : t);
    eq <- (f.[1] = two51minus1);
    t <- ((! eq) ? loop : t);
    eq <- (f.[2] = two51minus1);
    t <- ((! eq) ? loop : t);
    eq <- (f.[3] = two51minus1);
    t <- ((! eq) ? loop : t);
    eq <- (f.[4] = two51minus1);
    t <- ((! eq) ? loop : t);
    t <- (- t);
    two51minus1 <- (two51minus1 `&` t);
    two51minus19 <- (two51minus19 `&` t);
    f.[0] <- (f.[0] - two51minus19);
    f.[1] <- (f.[1] - two51minus1);
    f.[2] <- (f.[2] - two51minus1);
    f.[3] <- (f.[3] - two51minus1);
    f.[4] <- (f.[4] - two51minus1);
    h.[0] <- f.[1];
    h.[0] <- (h.[0] `<<` (W8.of_int 51));
    h.[0] <- (h.[0] `|` f.[0]);
    h.[1] <- f.[2];
    h.[1] <- (h.[1] `<<` (W8.of_int 38));
    f.[1] <- (f.[1] `>>` (W8.of_int 13));
    h.[1] <- (h.[1] `|` f.[1]);
    h.[2] <- f.[3];
    h.[2] <- (h.[2] `<<` (W8.of_int 25));
    f.[2] <- (f.[2] `>>` (W8.of_int 26));
    h.[2] <- (h.[2] `|` f.[2]);
    h.[3] <- f.[4];
    h.[3] <- (h.[3] `<<` (W8.of_int 12));
    f.[3] <- (f.[3] `>>` (W8.of_int 39));
    h.[3] <- (h.[3] `|` f.[3]);
    return (h);
  }
  
  proc __mul5_rss (xa:W64.t Array5.t, ya:W64.t Array5.t) : W64.t Array5.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var r:W64.t Array5.t;
    var mulrax:W64.t;
    var mulx319_stack:W64.t;
    var mulrdx:W64.t;
    var mulr01:W64.t;
    var mulx419_stack:W64.t;
    var cf:bool;
    var mulr11:W64.t;
    var mulr21:W64.t;
    var mulr31:W64.t;
    var mulr41:W64.t;
    var mulredmask:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var mult:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    var  _20:bool;
    var  _21:bool;
    var  _22:bool;
    var  _23:bool;
    var  _24:bool;
    r <- witness;
    mulrax <- xa.[3];
    mulrax <- (mulrax * (W64.of_int 19));
    mulx319_stack <- mulrax;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    r.[0] <- mulrax;
    mulr01 <- mulrdx;
    mulrax <- xa.[4];
    mulrax <- (mulrax * (W64.of_int 19));
    mulx419_stack <- mulrax;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    (aux, aux_0) <- adc_64 r.[0] mulrax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _0, mulr01) <- adc_64 mulr01 mulrdx cf;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[0] mulrax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _1, mulr01) <- adc_64 mulr01 mulrdx cf;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    r.[1] <- mulrax;
    mulr11 <- mulrdx;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    r.[2] <- mulrax;
    mulr21 <- mulrdx;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    r.[3] <- mulrax;
    mulr31 <- mulrdx;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    r.[4] <- mulrax;
    mulr41 <- mulrdx;
    mulrax <- xa.[1];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[1] mulrax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _2, mulr11) <- adc_64 mulr11 mulrdx cf;
    mulrax <- xa.[1];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    (aux, aux_0) <- adc_64 r.[2] mulrax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _3, mulr21) <- adc_64 mulr21 mulrdx cf;
    mulrax <- xa.[1];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    (aux, aux_0) <- adc_64 r.[3] mulrax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _4, mulr31) <- adc_64 mulr31 mulrdx cf;
    mulrax <- xa.[1];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    (aux, aux_0) <- adc_64 r.[4] mulrax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _5, mulr41) <- adc_64 mulr41 mulrdx cf;
    mulrax <- xa.[1];
    mulrax <- (mulrax * (W64.of_int 19));
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    (aux, aux_0) <- adc_64 r.[0] mulrax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _6, mulr01) <- adc_64 mulr01 mulrdx cf;
    mulrax <- xa.[2];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[2] mulrax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _7, mulr21) <- adc_64 mulr21 mulrdx cf;
    mulrax <- xa.[2];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    (aux, aux_0) <- adc_64 r.[3] mulrax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _8, mulr31) <- adc_64 mulr31 mulrdx cf;
    mulrax <- xa.[2];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    (aux, aux_0) <- adc_64 r.[4] mulrax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _9, mulr41) <- adc_64 mulr41 mulrdx cf;
    mulrax <- xa.[2];
    mulrax <- (mulrax * (W64.of_int 19));
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    (aux, aux_0) <- adc_64 r.[0] mulrax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _10, mulr01) <- adc_64 mulr01 mulrdx cf;
    mulrax <- xa.[2];
    mulrax <- (mulrax * (W64.of_int 19));
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    (aux, aux_0) <- adc_64 r.[1] mulrax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _11, mulr11) <- adc_64 mulr11 mulrdx cf;
    mulrax <- xa.[3];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[3] mulrax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _12, mulr31) <- adc_64 mulr31 mulrdx cf;
    mulrax <- xa.[3];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    (aux, aux_0) <- adc_64 r.[4] mulrax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _13, mulr41) <- adc_64 mulr41 mulrdx cf;
    mulrax <- mulx319_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    (aux, aux_0) <- adc_64 r.[1] mulrax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _14, mulr11) <- adc_64 mulr11 mulrdx cf;
    mulrax <- mulx319_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    (aux, aux_0) <- adc_64 r.[2] mulrax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _15, mulr21) <- adc_64 mulr21 mulrdx cf;
    mulrax <- xa.[4];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[4] mulrax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _16, mulr41) <- adc_64 mulr41 mulrdx cf;
    mulrax <- mulx419_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    (aux, aux_0) <- adc_64 r.[1] mulrax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _17, mulr11) <- adc_64 mulr11 mulrdx cf;
    mulrax <- mulx419_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    (aux, aux_0) <- adc_64 r.[2] mulrax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _18, mulr21) <- adc_64 mulr21 mulrdx cf;
    mulrax <- mulx419_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    (aux, aux_0) <- adc_64 r.[3] mulrax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _19, mulr31) <- adc_64 mulr31 mulrdx cf;
    mulredmask <- (W64.of_int 2251799813685247);
    (_of_, _cf_, _sf_,  _20, _zf_, mulr01) <- SHLD_64 mulr01 r.[0]
    (W8.of_int 13);
    r.[0] <- (r.[0] `&` mulredmask);
    (_of_, _cf_, _sf_,  _21, _zf_, mulr11) <- SHLD_64 mulr11 r.[1]
    (W8.of_int 13);
    r.[1] <- (r.[1] `&` mulredmask);
    r.[1] <- (r.[1] + mulr01);
    (_of_, _cf_, _sf_,  _22, _zf_, mulr21) <- SHLD_64 mulr21 r.[2]
    (W8.of_int 13);
    r.[2] <- (r.[2] `&` mulredmask);
    r.[2] <- (r.[2] + mulr11);
    (_of_, _cf_, _sf_,  _23, _zf_, mulr31) <- SHLD_64 mulr31 r.[3]
    (W8.of_int 13);
    r.[3] <- (r.[3] `&` mulredmask);
    r.[3] <- (r.[3] + mulr21);
    (_of_, _cf_, _sf_,  _24, _zf_, mulr41) <- SHLD_64 mulr41 r.[4]
    (W8.of_int 13);
    r.[4] <- (r.[4] `&` mulredmask);
    r.[4] <- (r.[4] + mulr31);
    mulr41 <- (mulr41 * (W64.of_int 19));
    r.[0] <- (r.[0] + mulr41);
    mult <- r.[0];
    mult <- (mult `>>` (W8.of_int 51));
    mult <- (mult + r.[1]);
    r.[1] <- mult;
    mult <- (mult `>>` (W8.of_int 51));
    r.[0] <- (r.[0] `&` mulredmask);
    mult <- (mult + r.[2]);
    r.[2] <- mult;
    mult <- (mult `>>` (W8.of_int 51));
    r.[1] <- (r.[1] `&` mulredmask);
    mult <- (mult + r.[3]);
    r.[3] <- mult;
    mult <- (mult `>>` (W8.of_int 51));
    r.[2] <- (r.[2] `&` mulredmask);
    mult <- (mult + r.[4]);
    r.[4] <- mult;
    mult <- (mult `>>` (W8.of_int 51));
    r.[3] <- (r.[3] `&` mulredmask);
    mult <- (mult * (W64.of_int 19));
    r.[0] <- (r.[0] + mult);
    r.[4] <- (r.[4] `&` mulredmask);
    return (r);
  }
  
  proc __mul5_sss (xa:W64.t Array5.t, ya:W64.t Array5.t) : W64.t Array5.t = {
    
    var rs:W64.t Array5.t;
    var r:W64.t Array5.t;
    r <- witness;
    rs <- witness;
    r <@ __mul5_rss (xa, ya);
    rs <- copy_64 r;
    return (rs);
  }
  
  proc _mul5_pp (xa:W64.t Array5.t, ya:W64.t Array5.t) : W64.t Array5.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var mulrax:W64.t;
    var mulx319_stack:W64.t;
    var mulrdx:W64.t;
    var r:W64.t Array5.t;
    var mulr01:W64.t;
    var mulx419_stack:W64.t;
    var cf:bool;
    var mulr11:W64.t;
    var mulr21:W64.t;
    var mulr31:W64.t;
    var mulr41:W64.t;
    var mulredmask:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var mult:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    var  _20:bool;
    var  _21:bool;
    var  _22:bool;
    var  _23:bool;
    var  _24:bool;
    r <- witness;
    mulrax <- xa.[3];
    mulrax <- (mulrax * (W64.of_int 19));
    mulx319_stack <- mulrax;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    r.[0] <- mulrax;
    mulr01 <- mulrdx;
    mulrax <- xa.[4];
    mulrax <- (mulrax * (W64.of_int 19));
    mulx419_stack <- mulrax;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    (aux, aux_0) <- adc_64 r.[0] mulrax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _0, mulr01) <- adc_64 mulr01 mulrdx cf;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[0] mulrax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _1, mulr01) <- adc_64 mulr01 mulrdx cf;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    r.[1] <- mulrax;
    mulr11 <- mulrdx;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    r.[2] <- mulrax;
    mulr21 <- mulrdx;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    r.[3] <- mulrax;
    mulr31 <- mulrdx;
    mulrax <- xa.[0];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    r.[4] <- mulrax;
    mulr41 <- mulrdx;
    mulrax <- xa.[1];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[1] mulrax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _2, mulr11) <- adc_64 mulr11 mulrdx cf;
    mulrax <- xa.[1];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    (aux, aux_0) <- adc_64 r.[2] mulrax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _3, mulr21) <- adc_64 mulr21 mulrdx cf;
    mulrax <- xa.[1];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    (aux, aux_0) <- adc_64 r.[3] mulrax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _4, mulr31) <- adc_64 mulr31 mulrdx cf;
    mulrax <- xa.[1];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    (aux, aux_0) <- adc_64 r.[4] mulrax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _5, mulr41) <- adc_64 mulr41 mulrdx cf;
    mulrax <- xa.[1];
    mulrax <- (mulrax * (W64.of_int 19));
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    (aux, aux_0) <- adc_64 r.[0] mulrax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _6, mulr01) <- adc_64 mulr01 mulrdx cf;
    mulrax <- xa.[2];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[2] mulrax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _7, mulr21) <- adc_64 mulr21 mulrdx cf;
    mulrax <- xa.[2];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    (aux, aux_0) <- adc_64 r.[3] mulrax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _8, mulr31) <- adc_64 mulr31 mulrdx cf;
    mulrax <- xa.[2];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    (aux, aux_0) <- adc_64 r.[4] mulrax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _9, mulr41) <- adc_64 mulr41 mulrdx cf;
    mulrax <- xa.[2];
    mulrax <- (mulrax * (W64.of_int 19));
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    (aux, aux_0) <- adc_64 r.[0] mulrax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _10, mulr01) <- adc_64 mulr01 mulrdx cf;
    mulrax <- xa.[2];
    mulrax <- (mulrax * (W64.of_int 19));
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    (aux, aux_0) <- adc_64 r.[1] mulrax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _11, mulr11) <- adc_64 mulr11 mulrdx cf;
    mulrax <- xa.[3];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[3] mulrax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _12, mulr31) <- adc_64 mulr31 mulrdx cf;
    mulrax <- xa.[3];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[1];
    (aux, aux_0) <- adc_64 r.[4] mulrax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _13, mulr41) <- adc_64 mulr41 mulrdx cf;
    mulrax <- mulx319_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    (aux, aux_0) <- adc_64 r.[1] mulrax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _14, mulr11) <- adc_64 mulr11 mulrdx cf;
    mulrax <- mulx319_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    (aux, aux_0) <- adc_64 r.[2] mulrax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _15, mulr21) <- adc_64 mulr21 mulrdx cf;
    mulrax <- xa.[4];
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[0];
    (aux, aux_0) <- adc_64 r.[4] mulrax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _16, mulr41) <- adc_64 mulr41 mulrdx cf;
    mulrax <- mulx419_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[2];
    (aux, aux_0) <- adc_64 r.[1] mulrax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _17, mulr11) <- adc_64 mulr11 mulrdx cf;
    mulrax <- mulx419_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[3];
    (aux, aux_0) <- adc_64 r.[2] mulrax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _18, mulr21) <- adc_64 mulr21 mulrdx cf;
    mulrax <- mulx419_stack;
    (mulrdx, mulrax) <- mulu_64 mulrax ya.[4];
    (aux, aux_0) <- adc_64 r.[3] mulrax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _19, mulr31) <- adc_64 mulr31 mulrdx cf;
    mulredmask <- (W64.of_int 2251799813685247);
    (_of_, _cf_, _sf_,  _20, _zf_, mulr01) <- SHLD_64 mulr01 r.[0]
    (W8.of_int 13);
    r.[0] <- (r.[0] `&` mulredmask);
    (_of_, _cf_, _sf_,  _21, _zf_, mulr11) <- SHLD_64 mulr11 r.[1]
    (W8.of_int 13);
    r.[1] <- (r.[1] `&` mulredmask);
    r.[1] <- (r.[1] + mulr01);
    (_of_, _cf_, _sf_,  _22, _zf_, mulr21) <- SHLD_64 mulr21 r.[2]
    (W8.of_int 13);
    r.[2] <- (r.[2] `&` mulredmask);
    r.[2] <- (r.[2] + mulr11);
    (_of_, _cf_, _sf_,  _23, _zf_, mulr31) <- SHLD_64 mulr31 r.[3]
    (W8.of_int 13);
    r.[3] <- (r.[3] `&` mulredmask);
    r.[3] <- (r.[3] + mulr21);
    (_of_, _cf_, _sf_,  _24, _zf_, mulr41) <- SHLD_64 mulr41 r.[4]
    (W8.of_int 13);
    r.[4] <- (r.[4] `&` mulredmask);
    r.[4] <- (r.[4] + mulr31);
    mulr41 <- (mulr41 * (W64.of_int 19));
    r.[0] <- (r.[0] + mulr41);
    mult <- r.[0];
    mult <- (mult `>>` (W8.of_int 51));
    mult <- (mult + r.[1]);
    r.[1] <- mult;
    mult <- (mult `>>` (W8.of_int 51));
    r.[0] <- (r.[0] `&` mulredmask);
    mult <- (mult + r.[2]);
    r.[2] <- mult;
    mult <- (mult `>>` (W8.of_int 51));
    r.[1] <- (r.[1] `&` mulredmask);
    mult <- (mult + r.[3]);
    r.[3] <- mult;
    mult <- (mult `>>` (W8.of_int 51));
    r.[2] <- (r.[2] `&` mulredmask);
    mult <- (mult + r.[4]);
    r.[4] <- mult;
    mult <- (mult `>>` (W8.of_int 51));
    r.[3] <- (r.[3] `&` mulredmask);
    mult <- (mult * (W64.of_int 19));
    r.[0] <- (r.[0] + mult);
    r.[4] <- (r.[4] `&` mulredmask);
    i <- 0;
    while (i < 5) {
      xa.[i] <- r.[i];
      i <- i + 1;
    }
    return (xa);
  }
  
  proc _mul5_ss_ (xa:W64.t Array5.t, ya:W64.t Array5.t) : W64.t Array5.t = {
    
    var xp:W64.t Array5.t;
    var yp:W64.t Array5.t;
    xp <- witness;
    yp <- witness;
    xp <- xa;
    yp <- ya;
    xp <@ _mul5_pp (xp, yp);
    xa <- xp;
    return (xa);
  }
  
  proc __mul5_a24_add_rss (xa:W64.t Array5.t, ya:W64.t Array5.t, _a24:W64.t) : 
  W64.t Array5.t = {
    
    var r:W64.t Array5.t;
    var a24:W64.t;
    var mul121666rax:W64.t;
    var mul121666rdx:W64.t;
    r <- witness;
    a24 <- _a24;
    mul121666rax <- xa.[0];
    (mul121666rdx, mul121666rax) <- mulu_64 mul121666rax a24;
    mul121666rax <- (mul121666rax `>>` (W8.of_int 13));
    r.[0] <- mul121666rax;
    r.[1] <- mul121666rdx;
    mul121666rax <- xa.[1];
    (mul121666rdx, mul121666rax) <- mulu_64 mul121666rax a24;
    mul121666rax <- (mul121666rax `>>` (W8.of_int 13));
    r.[1] <- (r.[1] + mul121666rax);
    r.[2] <- mul121666rdx;
    mul121666rax <- xa.[2];
    (mul121666rdx, mul121666rax) <- mulu_64 mul121666rax a24;
    mul121666rax <- (mul121666rax `>>` (W8.of_int 13));
    r.[2] <- (r.[2] + mul121666rax);
    r.[3] <- mul121666rdx;
    mul121666rax <- xa.[3];
    (mul121666rdx, mul121666rax) <- mulu_64 mul121666rax a24;
    mul121666rax <- (mul121666rax `>>` (W8.of_int 13));
    r.[3] <- (r.[3] + mul121666rax);
    r.[4] <- mul121666rdx;
    mul121666rax <- xa.[4];
    (mul121666rdx, mul121666rax) <- mulu_64 mul121666rax a24;
    mul121666rax <- (mul121666rax `>>` (W8.of_int 13));
    r.[4] <- (r.[4] + mul121666rax);
    mul121666rdx <- (mul121666rdx * (W64.of_int 19));
    r.[0] <- (r.[0] + mul121666rdx);
    r.[0] <- (r.[0] + ya.[0]);
    r.[1] <- (r.[1] + ya.[1]);
    r.[2] <- (r.[2] + ya.[2]);
    r.[3] <- (r.[3] + ya.[3]);
    r.[4] <- (r.[4] + ya.[4]);
    return (r);
  }
  
  proc __mul5_a24_add_sss (xa:W64.t Array5.t, ya:W64.t Array5.t, a24:W64.t) : 
  W64.t Array5.t = {
    
    var rs:W64.t Array5.t;
    var r:W64.t Array5.t;
    r <- witness;
    rs <- witness;
    r <@ __mul5_a24_add_rss (xa, ya, a24);
    rs <- copy_64 r;
    return (rs);
  }
  
  proc __sqr5_rs (xa:W64.t Array5.t) : W64.t Array5.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var r:W64.t Array5.t;
    var squarerax:W64.t;
    var squarerdx:W64.t;
    var squarer01:W64.t;
    var squarer11:W64.t;
    var squarer21:W64.t;
    var squarer31:W64.t;
    var squarer41:W64.t;
    var cf:bool;
    var squareredmask:W64.t;
    var squaret:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    var  _20:bool;
    var  _21:bool;
    var  _22:bool;
    var  _23:bool;
    var  _24:bool;
    var  _25:bool;
    var  _26:bool;
    var  _27:bool;
    var  _28:bool;
    var  _29:bool;
    var  _30:bool;
    var  _31:bool;
    var  _32:bool;
    var  _33:bool;
    var  _34:bool;
    r <- witness;
    squarerax <- xa.[0];
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[0];
    r.[0] <- squarerax;
    squarer01 <- squarerdx;
    squarerax <- xa.[0];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[1];
    r.[1] <- squarerax;
    squarer11 <- squarerdx;
    squarerax <- xa.[0];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[2];
    r.[2] <- squarerax;
    squarer21 <- squarerdx;
    squarerax <- xa.[0];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[3];
    r.[3] <- squarerax;
    squarer31 <- squarerdx;
    squarerax <- xa.[0];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    r.[4] <- squarerax;
    squarer41 <- squarerdx;
    squarerax <- xa.[1];
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[1];
    (aux, aux_0) <- adc_64 r.[2] squarerax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _0, squarer21) <- adc_64 squarer21 squarerdx cf;
    squarerax <- xa.[1];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[2];
    (aux, aux_0) <- adc_64 r.[3] squarerax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _1, squarer31) <- adc_64 squarer31 squarerdx cf;
    squarerax <- xa.[1];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[3];
    (aux, aux_0) <- adc_64 r.[4] squarerax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _2, squarer41) <- adc_64 squarer41 squarerdx cf;
    squarerax <- xa.[1];
    squarerax <- (squarerax * (W64.of_int 38));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    (aux, aux_0) <- adc_64 r.[0] squarerax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _3, squarer01) <- adc_64 squarer01 squarerdx cf;
    squarerax <- xa.[2];
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[2];
    (aux, aux_0) <- adc_64 r.[4] squarerax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _4, squarer41) <- adc_64 squarer41 squarerdx cf;
    squarerax <- xa.[2];
    squarerax <- (squarerax * (W64.of_int 38));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[3];
    (aux, aux_0) <- adc_64 r.[0] squarerax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _5, squarer01) <- adc_64 squarer01 squarerdx cf;
    squarerax <- xa.[2];
    squarerax <- (squarerax * (W64.of_int 38));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    (aux, aux_0) <- adc_64 r.[1] squarerax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _6, squarer11) <- adc_64 squarer11 squarerdx cf;
    squarerax <- xa.[3];
    squarerax <- (squarerax * (W64.of_int 19));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[3];
    (aux, aux_0) <- adc_64 r.[1] squarerax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _7, squarer11) <- adc_64 squarer11 squarerdx cf;
    squarerax <- xa.[3];
    squarerax <- (squarerax * (W64.of_int 38));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    (aux, aux_0) <- adc_64 r.[2] squarerax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _8, squarer21) <- adc_64 squarer21 squarerdx cf;
    squarerax <- xa.[4];
    squarerax <- (squarerax * (W64.of_int 19));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    (aux, aux_0) <- adc_64 r.[3] squarerax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _9, squarer31) <- adc_64 squarer31 squarerdx cf;
    squareredmask <- (W64.of_int 2251799813685247);
    ( _10,  _11,  _12,  _13,  _14, squarer01) <- SHLD_64 squarer01 r.[0]
    (W8.of_int 13);
    r.[0] <- (r.[0] `&` squareredmask);
    ( _15,  _16,  _17,  _18,  _19, squarer11) <- SHLD_64 squarer11 r.[1]
    (W8.of_int 13);
    r.[1] <- (r.[1] `&` squareredmask);
    r.[1] <- (r.[1] + squarer01);
    ( _20,  _21,  _22,  _23,  _24, squarer21) <- SHLD_64 squarer21 r.[2]
    (W8.of_int 13);
    r.[2] <- (r.[2] `&` squareredmask);
    r.[2] <- (r.[2] + squarer11);
    ( _25,  _26,  _27,  _28,  _29, squarer31) <- SHLD_64 squarer31 r.[3]
    (W8.of_int 13);
    r.[3] <- (r.[3] `&` squareredmask);
    r.[3] <- (r.[3] + squarer21);
    ( _30,  _31,  _32,  _33,  _34, squarer41) <- SHLD_64 squarer41 r.[4]
    (W8.of_int 13);
    r.[4] <- (r.[4] `&` squareredmask);
    r.[4] <- (r.[4] + squarer31);
    squarer41 <- (squarer41 * (W64.of_int 19));
    r.[0] <- (r.[0] + squarer41);
    squaret <- r.[0];
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret + r.[1]);
    r.[0] <- (r.[0] `&` squareredmask);
    r.[1] <- squaret;
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret + r.[2]);
    r.[1] <- (r.[1] `&` squareredmask);
    r.[2] <- squaret;
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret + r.[3]);
    r.[2] <- (r.[2] `&` squareredmask);
    r.[3] <- squaret;
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret + r.[4]);
    r.[3] <- (r.[3] `&` squareredmask);
    r.[4] <- squaret;
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret * (W64.of_int 19));
    r.[0] <- (r.[0] + squaret);
    r.[4] <- (r.[4] `&` squareredmask);
    return (r);
  }
  
  proc __sqr5_ss (xa:W64.t Array5.t) : W64.t Array5.t = {
    
    var rs:W64.t Array5.t;
    var r:W64.t Array5.t;
    r <- witness;
    rs <- witness;
    r <@ __sqr5_rs (xa);
    rs <- copy_64 r;
    return (rs);
  }
  
  proc _sqr5_p (xa:W64.t Array5.t) : W64.t Array5.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var squarerax:W64.t;
    var squarerdx:W64.t;
    var r:W64.t Array5.t;
    var squarer01:W64.t;
    var squarer11:W64.t;
    var squarer21:W64.t;
    var squarer31:W64.t;
    var squarer41:W64.t;
    var cf:bool;
    var squareredmask:W64.t;
    var squaret:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    var  _20:bool;
    var  _21:bool;
    var  _22:bool;
    var  _23:bool;
    var  _24:bool;
    var  _25:bool;
    var  _26:bool;
    var  _27:bool;
    var  _28:bool;
    var  _29:bool;
    var  _30:bool;
    var  _31:bool;
    var  _32:bool;
    var  _33:bool;
    var  _34:bool;
    r <- witness;
    squarerax <- xa.[0];
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[0];
    r.[0] <- squarerax;
    squarer01 <- squarerdx;
    squarerax <- xa.[0];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[1];
    r.[1] <- squarerax;
    squarer11 <- squarerdx;
    squarerax <- xa.[0];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[2];
    r.[2] <- squarerax;
    squarer21 <- squarerdx;
    squarerax <- xa.[0];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[3];
    r.[3] <- squarerax;
    squarer31 <- squarerdx;
    squarerax <- xa.[0];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    r.[4] <- squarerax;
    squarer41 <- squarerdx;
    squarerax <- xa.[1];
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[1];
    (aux, aux_0) <- adc_64 r.[2] squarerax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _0, squarer21) <- adc_64 squarer21 squarerdx cf;
    squarerax <- xa.[1];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[2];
    (aux, aux_0) <- adc_64 r.[3] squarerax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _1, squarer31) <- adc_64 squarer31 squarerdx cf;
    squarerax <- xa.[1];
    squarerax <- (squarerax `<<` (W8.of_int 1));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[3];
    (aux, aux_0) <- adc_64 r.[4] squarerax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _2, squarer41) <- adc_64 squarer41 squarerdx cf;
    squarerax <- xa.[1];
    squarerax <- (squarerax * (W64.of_int 38));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    (aux, aux_0) <- adc_64 r.[0] squarerax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _3, squarer01) <- adc_64 squarer01 squarerdx cf;
    squarerax <- xa.[2];
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[2];
    (aux, aux_0) <- adc_64 r.[4] squarerax false;
    cf <- aux;
    r.[4] <- aux_0;
    ( _4, squarer41) <- adc_64 squarer41 squarerdx cf;
    squarerax <- xa.[2];
    squarerax <- (squarerax * (W64.of_int 38));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[3];
    (aux, aux_0) <- adc_64 r.[0] squarerax false;
    cf <- aux;
    r.[0] <- aux_0;
    ( _5, squarer01) <- adc_64 squarer01 squarerdx cf;
    squarerax <- xa.[2];
    squarerax <- (squarerax * (W64.of_int 38));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    (aux, aux_0) <- adc_64 r.[1] squarerax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _6, squarer11) <- adc_64 squarer11 squarerdx cf;
    squarerax <- xa.[3];
    squarerax <- (squarerax * (W64.of_int 19));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[3];
    (aux, aux_0) <- adc_64 r.[1] squarerax false;
    cf <- aux;
    r.[1] <- aux_0;
    ( _7, squarer11) <- adc_64 squarer11 squarerdx cf;
    squarerax <- xa.[3];
    squarerax <- (squarerax * (W64.of_int 38));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    (aux, aux_0) <- adc_64 r.[2] squarerax false;
    cf <- aux;
    r.[2] <- aux_0;
    ( _8, squarer21) <- adc_64 squarer21 squarerdx cf;
    squarerax <- xa.[4];
    squarerax <- (squarerax * (W64.of_int 19));
    (squarerdx, squarerax) <- mulu_64 squarerax xa.[4];
    (aux, aux_0) <- adc_64 r.[3] squarerax false;
    cf <- aux;
    r.[3] <- aux_0;
    ( _9, squarer31) <- adc_64 squarer31 squarerdx cf;
    squareredmask <- (W64.of_int 2251799813685247);
    ( _10,  _11,  _12,  _13,  _14, squarer01) <- SHLD_64 squarer01 r.[0]
    (W8.of_int 13);
    r.[0] <- (r.[0] `&` squareredmask);
    ( _15,  _16,  _17,  _18,  _19, squarer11) <- SHLD_64 squarer11 r.[1]
    (W8.of_int 13);
    r.[1] <- (r.[1] `&` squareredmask);
    r.[1] <- (r.[1] + squarer01);
    ( _20,  _21,  _22,  _23,  _24, squarer21) <- SHLD_64 squarer21 r.[2]
    (W8.of_int 13);
    r.[2] <- (r.[2] `&` squareredmask);
    r.[2] <- (r.[2] + squarer11);
    ( _25,  _26,  _27,  _28,  _29, squarer31) <- SHLD_64 squarer31 r.[3]
    (W8.of_int 13);
    r.[3] <- (r.[3] `&` squareredmask);
    r.[3] <- (r.[3] + squarer21);
    ( _30,  _31,  _32,  _33,  _34, squarer41) <- SHLD_64 squarer41 r.[4]
    (W8.of_int 13);
    r.[4] <- (r.[4] `&` squareredmask);
    r.[4] <- (r.[4] + squarer31);
    squarer41 <- (squarer41 * (W64.of_int 19));
    r.[0] <- (r.[0] + squarer41);
    squaret <- r.[0];
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret + r.[1]);
    r.[0] <- (r.[0] `&` squareredmask);
    r.[1] <- squaret;
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret + r.[2]);
    r.[1] <- (r.[1] `&` squareredmask);
    r.[2] <- squaret;
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret + r.[3]);
    r.[2] <- (r.[2] `&` squareredmask);
    r.[3] <- squaret;
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret + r.[4]);
    r.[3] <- (r.[3] `&` squareredmask);
    r.[4] <- squaret;
    squaret <- (squaret `>>` (W8.of_int 51));
    squaret <- (squaret * (W64.of_int 19));
    r.[0] <- (r.[0] + squaret);
    r.[4] <- (r.[4] `&` squareredmask);
    i <- 0;
    while (i < 5) {
      xa.[i] <- r.[i];
      i <- i + 1;
    }
    return (xa);
  }
  
  proc _sqr5_ss_ (xa:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    
    var ra:W64.t Array5.t;
    var j:int;
    var t:W64.t;
    var rp:W64.t Array5.t;
    ra <- witness;
    rp <- witness;
    j <- 0;
    while (j < 5) {
      t <- xa.[j];
      ra.[j] <- t;
      j <- j + 1;
    }
    rp <- ra;
    rp <@ _sqr5_p (rp);
    ra <- rp;
    return (ra);
  }
  
  proc _sqr5_s_ (x:W64.t Array5.t) : W64.t Array5.t = {
    
    var xp:W64.t Array5.t;
    xp <- witness;
    xp <- x;
    xp <@ _sqr5_p (xp);
    x <- xp;
    return (x);
  }
  
  proc _it_sqr5_p (x:W64.t Array5.t, i:W32.t) : W64.t Array5.t = {
    
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    
    x <@ _sqr5_p (x);
    ( _0,  _1,  _2, zf, i) <- DEC_32 i;
    while ((! zf)) {
      x <@ _sqr5_p (x);
      ( _0,  _1,  _2, zf, i) <- DEC_32 i;
    }
    return (x);
  }
  
  proc _it_sqr5_s_ (x:W64.t Array5.t, i:W32.t) : W64.t Array5.t = {
    
    var xp:W64.t Array5.t;
    xp <- witness;
    xp <- x;
    xp <@ _it_sqr5_p (xp, i);
    x <- xp;
    return (x);
  }
  
  proc _it_sqr5_ss_ (r:W64.t Array5.t, x:W64.t Array5.t, i:W32.t) : W64.t Array5.t = {
    var aux: int;
    
    var j:int;
    var t:W64.t;
    var rp:W64.t Array5.t;
    rp <- witness;
    j <- 0;
    while (j < 5) {
      t <- x.[j];
      r.[j] <- t;
      j <- j + 1;
    }
    rp <- r;
    rp <@ _it_sqr5_p (rp, i);
    r <- rp;
    return (r);
  }
  
  proc __invert5 (fs:W64.t Array5.t) : W64.t Array5.t = {
    
    var t1s:W64.t Array5.t;
    var t0s:W64.t Array5.t;
    var t2s:W64.t Array5.t;
    var i:W32.t;
    var t3s:W64.t Array5.t;
    t0s <- witness;
    t1s <- witness;
    t2s <- witness;
    t3s <- witness;
    t0s <@ _sqr5_ss_ (fs);
    t1s <@ _sqr5_ss_ (t0s);
    t1s <@ _sqr5_s_ (t1s);
    t1s <@ _mul5_ss_ (t1s, fs);
    t0s <@ _mul5_ss_ (t0s, t1s);
    t2s <@ _sqr5_ss_ (t0s);
    t1s <@ _mul5_ss_ (t1s, t2s);
    t2s <@ _sqr5_ss_ (t1s);
    i <- (W32.of_int 4);
    t2s <@ _it_sqr5_s_ (t2s, i);
    t1s <@ _mul5_ss_ (t1s, t2s);
    i <- (W32.of_int 10);
    t2s <@ _it_sqr5_ss_ (t2s, t1s, i);
    t2s <@ _mul5_ss_ (t2s, t1s);
    i <- (W32.of_int 20);
    t3s <@ _it_sqr5_ss_ (t3s, t2s, i);
    t2s <@ _mul5_ss_ (t2s, t3s);
    i <- (W32.of_int 10);
    t2s <@ _it_sqr5_s_ (t2s, i);
    t1s <@ _mul5_ss_ (t1s, t2s);
    i <- (W32.of_int 50);
    t2s <@ _it_sqr5_ss_ (t2s, t1s, i);
    t2s <@ _mul5_ss_ (t2s, t1s);
    i <- (W32.of_int 100);
    t3s <@ _it_sqr5_ss_ (t3s, t2s, i);
    t2s <@ _mul5_ss_ (t2s, t3s);
    i <- (W32.of_int 50);
    t2s <@ _it_sqr5_s_ (t2s, i);
    t1s <@ _mul5_ss_ (t1s, t2s);
    i <- (W32.of_int 4);
    t1s <@ _it_sqr5_s_ (t1s, i);
    t1s <@ _sqr5_s_ (t1s);
    t1s <@ _mul5_ss_ (t1s, t0s);
    return (t1s);
  }
  
  proc __add_and_double5 (init:W64.t Array5.t, x2:W64.t Array5.t,
                          z2r:W64.t Array5.t, x3:W64.t Array5.t,
                          z3:W64.t Array5.t) : W64.t Array5.t *
                                               W64.t Array5.t *
                                               W64.t Array5.t *
                                               W64.t Array5.t = {
    
    var t0:W64.t Array5.t;
    var t1:W64.t Array5.t;
    var z2:W64.t Array5.t;
    var t2:W64.t Array5.t;
    t0 <- witness;
    t1 <- witness;
    t2 <- witness;
    z2 <- witness;
    t0 <@ __sub5_ssr (x2, z2r);
    x2 <@ __add5_ssr (x2, z2r);
    t1 <@ __sub5_sss (x3, z3);
    z2 <@ __add5_sss (x3, z3);
    z3 <@ __mul5_sss (x2, t1);
    z2 <@ __mul5_sss (z2, t0);
    t2 <@ __sqr5_ss (x2);
    t1 <@ __sqr5_ss (t0);
    x3 <@ __add5_sss (z3, z2);
    z2 <@ __sub5_sss (z3, z2);
    x2 <@ __mul5_sss (t2, t1);
    t0 <@ __sub5_sss (t2, t1);
    z2 <@ __sqr5_ss (z2);
    t2 <@ __mul5_a24_add_sss (t0, t2, (W64.of_int 996679680));
    x3 <@ __sqr5_ss (x3);
    z3 <@ __mul5_sss (init, z2);
    z2r <@ __mul5_rss (t0, t2);
    return (x2, z2r, x3, z3);
  }
  
  proc __montgomery_ladder_step5 (k:W8.t Array32.t, init:W64.t Array5.t,
                                  x2:W64.t Array5.t, z2r:W64.t Array5.t,
                                  x3:W64.t Array5.t, z3:W64.t Array5.t,
                                  swapped:W64.t, ctr:W64.t) : W64.t Array5.t *
                                                              W64.t Array5.t *
                                                              W64.t Array5.t *
                                                              W64.t Array5.t *
                                                              W64.t = {
    
    var bit:W64.t;
    var toswap:W64.t;
    
    bit <@ __ith_bit (k, ctr);
    toswap <- swapped;
    toswap <- (toswap `^` bit);
    (x2, z2r, x3, z3) <@ __cswap5 (x2, z2r, x3, z3, toswap);
    swapped <- bit;
    (x2, z2r, x3, z3) <@ __add_and_double5 (init, x2, z2r, x3, z3);
    return (x2, z2r, x3, z3, swapped);
  }
  
  proc __montgomery_ladder5 (u:W64.t Array5.t, k:W8.t Array32.t) : W64.t Array5.t *
                                                                   W64.t Array5.t = {
    
    var x2:W64.t Array5.t;
    var z2r:W64.t Array5.t;
    var x3:W64.t Array5.t;
    var z3:W64.t Array5.t;
    var us:W64.t Array5.t;
    var ctr:W64.t;
    var swapped:W64.t;
    us <- witness;
    x2 <- witness;
    x3 <- witness;
    z2r <- witness;
    z3 <- witness;
    (x2, z2r, x3, z3) <@ __init_points5 (u);
    us <- copy_64 u;
    ctr <- (W64.of_int 255);
    swapped <- (W64.of_int 0);
    ctr <- (ctr - (W64.of_int 1));
    (* Erased call to spill *)
    (x2, z2r, x3, z3, swapped) <@ __montgomery_ladder_step5 (k, us, x2, z2r,
    x3, z3, swapped, ctr);
    (* Erased call to unspill *)
    while (((W64.of_int 0) \ult ctr)) {
      ctr <- (ctr - (W64.of_int 1));
      (* Erased call to spill *)
      (x2, z2r, x3, z3, swapped) <@ __montgomery_ladder_step5 (k, us, x2,
      z2r, x3, z3, swapped, ctr);
      (* Erased call to unspill *)
    }
    return (x2, z2r);
  }
  
  proc __encode_point5 (x2:W64.t Array5.t, z2r:W64.t Array5.t) : W64.t Array4.t = {
    
    var r2:W64.t Array4.t;
    var z2:W64.t Array5.t;
    var r1:W64.t Array5.t;
    r1 <- witness;
    r2 <- witness;
    z2 <- witness;
    z2 <- copy_64 z2r;
    z2 <@ __invert5 (z2);
    r1 <@ __mul5_rss (x2, z2);
    r2 <@ __tobytes5 (r1);
    return (r2);
  }
  
  proc __curve25519_internal_ref5 (k:W8.t Array32.t, u:W64.t Array5.t) : 
  W64.t Array4.t = {
    
    var r:W64.t Array4.t;
    var x2:W64.t Array5.t;
    var z2r:W64.t Array5.t;
    r <- witness;
    x2 <- witness;
    z2r <- witness;
    (x2, z2r) <@ __montgomery_ladder5 (u, k);
    r <@ __encode_point5 (x2, z2r);
    return (r);
  }
  
  proc __curve25519_ref5 (_k:W64.t Array4.t, _u:W64.t Array4.t) : W64.t Array4.t = {
    
    var r:W64.t Array4.t;
    var k:W8.t Array32.t;
    var u:W64.t Array5.t;
    k <- witness;
    r <- witness;
    u <- witness;
    k <@ __decode_scalar (_k);
    u <@ __decode_u_coordinate5 (_u);
    r <@ __curve25519_internal_ref5 (k, u);
    return (r);
  }
  
  proc __curve25519_ref5_base (_k:W64.t Array4.t) : W64.t Array4.t = {
    
    var r:W64.t Array4.t;
    var k:W8.t Array32.t;
    var u:W64.t Array5.t;
    k <- witness;
    r <- witness;
    u <- witness;
    k <@ __decode_scalar (_k);
    u <@ __decode_u_coordinate_base5 ();
    r <@ __curve25519_internal_ref5 (k, u);
    return (r);
  }
  
  proc jade_scalarmult_curve25519_amd64_ref5 (qp:W64.t Array4.t,
                                              np:W64.t Array4.t,
                                              pp:W64.t Array4.t) : W64.t Array4.t *
                                                                   W64.t = {
    
    var r:W64.t;
    var n:W64.t Array4.t;
    var p:W64.t Array4.t;
    var q:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
    n <- witness;
    p <- witness;
    q <- witness;
     _0 <- init_msf ;
    (* Erased call to spill *)
    n <- copy_64 np;
    p <- copy_64 pp;
    q <@ __curve25519_ref5 (n, p);
    (* Erased call to unspill *)
    qp <- copy_64 q;
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- set0_64 ;
    return (qp, r);
  }
  
  proc jade_scalarmult_curve25519_amd64_ref5_base (qp:W64.t Array4.t,
                                                   np:W64.t Array4.t) : 
  W64.t Array4.t * W64.t = {
    
    var r:W64.t;
    var n:W64.t Array4.t;
    var q:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
    n <- witness;
    q <- witness;
     _0 <- init_msf ;
    (* Erased call to spill *)
    n <- copy_64 np;
    q <@ __curve25519_ref5_base (n);
    (* Erased call to unspill *)
    qp <- copy_64 q;
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- set0_64 ;
    return (qp, r);
  }
}.


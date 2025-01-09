require import AllCore Int IntDiv CoreMap List Distr. (* useful to include Int import *)

from Jasmin require import JModel_x86 Jcheck.

import SLH64.

require import Zp_limbs Zp_25519.
import Zp_25519 Zp Zp_limbs EClib.

require import WArray32.

require import Array4.


abbrev u64i x = W64.to_uint x.
abbrev pow = Ring.IntID.exp.
abbrev single: int -> int = idfun.
abbrev quad (a b c d: W64.t) =  [a; b; c; d].
abbrev limbs_4u64 (r: W64.t list) = pack4 r.  
abbrev eqmod (a b c: int) = (a - b) %% c = 0.


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

lemma mul4_a24_equiv_contract (xa h: Rep4) :
      inzpRep4 h = inzp (valRep4 xa * 121665) <=>       
       (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i xa.[ii]))) (iota_ 0 4))) *
     121665) (single ((pow 2 255) - 19))).
proof.      
    do split.          
    rewrite -!limbs_are_same.             
    rewrite !inzpRep4E. move => H. rewrite /idfun -pE -!inzpK !inzpD inzpN !H -!inzpD //= !inzpK => />.
    smt(Zp_25519.two_pow255E).
    rewrite -!limbs_are_same.             
    rewrite !inzpRep4E. rewrite /idfun -pE -!inzpK !inzpD inzpN -!inzpD //= !inzpK => />.
    smt(Zp_25519.two_pow255E).       
qed.


lemma add4_equiv_contract (_f _g h: Rep4) :
      inzpRep4 h = inzpRep4 _f + inzpRep4 _g <=>       
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4))) +
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))).
proof.
      split.
      rewrite -!limbs_are_same.             
      rewrite !inzpRep4E. move => H. rewrite /idfun -pE -!inzpK !inzpD inzpN !H -!inzpD //= !inzpK => />.
      smt(Zp_25519.two_pow255E).
      rewrite -!limbs_are_same.             
      rewrite !inzpRep4E. rewrite /idfun -pE -!inzpK !inzpD inzpN -!inzpD //= !inzpK => />.
      smt(Zp_25519.two_pow255E).      
qed.

lemma mul4_equiv_contract (xa ya h: Rep4) :
      inzpRep4 h = inzp (valRep4 xa * valRep4 ya) <=>       
       (eqmod
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
     ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i xa.[ii]))) (iota_ 0 4))) *
     (foldr (fun x => (fun (acc: int) => (x + acc))) 0
     (map (fun ii => ((pow 2 (64 * ii)) * (u64i ya.[ii]))) (iota_ 0 4))))
     (single ((pow 2 255) - 19))).
proof.      
    do split.          
    rewrite -!limbs_are_same.             
    rewrite !inzpRep4E. move => H. rewrite /idfun -pE -!inzpK !inzpD inzpN !H -!inzpD //= !inzpK => />.
    smt(Zp_25519.two_pow255E).
    rewrite -!limbs_are_same.             
    rewrite !inzpRep4E. rewrite /idfun -pE -!inzpK !inzpD inzpN -!inzpD //= !inzpK => />.
    smt(Zp_25519.two_pow255E).          
qed.


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
    do split.          
    rewrite -!limbs_are_same.             
    rewrite !inzpRep4E. move => H. rewrite /idfun -pE -!inzpK !inzpD inzpN !H -!inzpD //= !inzpK => />.
    smt(Zp_25519.two_pow255E).
    rewrite -!limbs_are_same.             
    rewrite !inzpRep4E. rewrite /idfun -pE -!inzpK !inzpD inzpN -!inzpD //= !inzpK => />.
    smt(Zp_25519.two_pow255E).      
qed.


lemma sub4_equiv_contract (f g h: Rep4) :
      inzpRep4 h = inzpRep4 f - inzpRep4 g <=>       
      (eqmod
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
      ((foldr (fun x => (fun (acc: int) => (x + acc))) 0
       (map (fun ii => ((pow 2 (64 * ii)) * (u64i f.[ii]))) (iota_ 0 4))) -
      (foldr (fun x => (fun (acc: int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i g.[ii]))) (iota_ 0 4))))
      (single ((pow 2 255) - 19))).
proof.
    do split.          
    rewrite -!limbs_are_same.             
    rewrite !inzpRep4E. move => H. rewrite /idfun -pE -!inzpK !inzpD inzpN !H -!inzpD //= !inzpK => />.
    smt(Zp_25519.two_pow255E).
    rewrite -!limbs_are_same.             
    rewrite !inzpRep4E. rewrite /idfun -pE -!inzpK !inzpD inzpN -!inzpD //= !inzpK => />.
    smt(Zp_25519.two_pow255E).
qed.

lemma tobytes_equiv_contract (h _f: Rep4) :
      pack4 (to_list h) = (W256.of_int (asint (inzpRep4 _f))) <=>
      ((limbs_4u64 (quad h.[0] h.[1] h.[2] h.[3])) \ult
       (W256.of_int
       57896044618658097711785492504343953926634992332820282019728792003956564819949
       )) /\
      (((W256.of_int 0) \ule
       (limbs_4u64 (quad h.[0] h.[1] h.[2] h.[3]))) /\
      (eqmod
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i h.[ii]))) (iota_ 0 4)))
      (foldr (fun x => (fun (acc:int) => (x + acc))) 0
      (map (fun ii => ((pow 2 (64 * ii)) * (u64i _f.[ii]))) (iota_ 0 4)))
      (single ((pow 2 255) - 19)))).
proof.    
    auto => />.  
    rewrite -!limbs_are_same /idfun.    
    have E: to_uint (limbs_4u64 (quad _f.[0] _f.[1] _f.[2] _f.[3])) = valRep4 _f.
      + by rewrite valRep4ToPack /to_list /mkseq -iotaredE => />.
    have E0: to_uint (limbs_4u64 (quad h.[0] h.[1] h.[2] h.[3])) = valRep4 h.
      + by rewrite valRep4ToPack /to_list /mkseq -iotaredE => />.           
    have E1: 0 <= (asint (inzpRep4 _f)) && asint (inzpRep4 _f) < p. smt(ge0_asint gtp_asint).
    do split. move => H.    
    have E2: limbs_4u64 (quad h.[0] h.[1] h.[2] h.[3]) = (of_int (asint (inzpRep4 _f)))%W256.
      + move: H. by rewrite/to_list /mkseq -iotaredE => />.
    move: H. rewrite /to_list /mkseq -iotaredE //=. move => H.       
    have E3: W256.to_uint (limbs_4u64 (quad h.[0] h.[1] h.[2] h.[3])) = (asint (inzpRep4 _f)).
      + rewrite H of_uintK pmod_small //=. smt(ge0_asint gtp_asint pVal).      
    have E4: W256.to_uint (limbs_4u64 (quad h.[0] h.[1] h.[2] h.[3])) = valRep4 _f %% p.
        + by rewrite E3 inzpRep4E inzpK.
    do split.
    rewrite ultE E2 of_uintK pmod_small //=; 1,2:smt(ge0_asint gtp_asint pVal).
    rewrite uleE E2 of_uintK pmod_small //=; 1:smt(ge0_asint gtp_asint pVal).
    rewrite -E0 E2 of_uintK (pmod_small (asint (inzpRep4 _f)) (pow 2 256)) //=.
    + smt(ge0_asint gtp_asint pVal).
    move: E3. rewrite !inzpRep4E. move => E3. rewrite inzpK.
    smt(Zp_25519.two_pow255E).
    
    move => H H2.
    have E2: 0 <= valRep4 h && valRep4 h < p.
        + rewrite -E0. smt(Zp_25519.two_pow255E W256.to_uint_cmp W256.to_uint_small).
    move => H3.  
    have E3: W256.to_uint (limbs_4u64 (to_list h)) = (asint (inzpRep4 _f)).
    + rewrite /to_list /mkseq -iotaredE //= E0. rewrite inzpRep4E inzpK.
    smt(Zp_25519.two_pow255E W256.to_uint_cmp W256.to_uint_small).
    rewrite -E3.
    smt(Zp_25519.two_pow255E W256.to_uint_cmp W256.to_uint_small).
qed.

require import AllCore Int IntDiv CoreMap List Distr. (* useful to include Int import *)

from Jasmin require import JModel_x86.

import SLH64.

require import Jcheck  Zp_limbs Zp_25519.
import Zp_25519 Zp Zp_limbs EClib.

require import WArray32.

require import Array4.

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
      rewrite -!limbs_are_same.
      rewrite !inzpRep4E !/inzp. smt(@Zp_25519).      
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
      rewrite -!limbs_are_same.
      rewrite !inzpRep4E !/inzp. smt(@Zp_25519).      
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
      rewrite -!limbs_are_same.
      rewrite !inzpRep4E !/inzp. smt(@Zp_25519).      
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
      split.
      rewrite -!limbs_are_same.
      rewrite inzpRep4E /inzp. smt(@Zp_25519).
      rewrite -!limbs_are_same.
      rewrite inzpRep4E /inzp. smt(@Zp_25519).
qed.

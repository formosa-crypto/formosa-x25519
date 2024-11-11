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

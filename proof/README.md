# Curve25519 correctness proof
Correctness proof for the reference and optimised 4-limb implementation of Curve25519 scalar multiplication in Jasmin.

Easycrypt hash: git-hash: r2024.01-452-g1038c8b

Note, some lemmas are left with the tactic `admit`, which means that the lemmas are not proven, but assumed to be correct. 
All `admits` have been proved in Cryptoline and including them is future work.

## Overview
### Common files
The logic in the `common/` folder is that the following files provide various lemmas used throughout the correctness proofs.

#### Generic files
- **EClib.ec** includes lemmas relating to some simple mathematical lemmas that the other files will use. No dependencies.
- **Zp_25519** includes lemmas relating to the finite field of size 2^255 - 19, such as congruence over said finite field and reduction. No dependencies.
- **Zp_limbs** includes lemmas concerning the implementation of 4 limbs representations (called `valRep4` in these proofs). Depends on the above two files.

#### Curve25519 files
The logic behind these files is that a functional specification of X25519 are defined (`Curve25519_Specs.ec`). 
From these, various other related operations and lemmas are defined in another file (`Curve25519_Operations`).
From these two files, we can write an procedural specification of scalar multiplication in Easycrypt, which we show to be equivalent to the functional specification.
Finally, `Curve25519_PHoare` contains probabilistic hoare statements relating to the procedural specification.

From this, we now have a foundation to be able to prove the correctness of both the reference and optimised implementations of scalar multiplication in relation to the **procedural specification**.

Note that the dependency chain (where x <- y indicates that y depends on x) is:

```
Curve25519_Specs <- Curve25519_Operations <- Curve25519_Procedures <- Curve25519_PHoare
```

### Correctness proofs
The correctness proofs are similar for both implementations, so unless specified, all explanations apply to both implementations. 
Each lemma corresponds to a step in the X25519 implementation and are presented and proven in the same order. This order is:

0. Arithmetic, such as addition, subtraction, multiplication and squaring.
1. Decoding scalar value.
2. Decoding `u` coordinate.
3. Obtaining the `i`-th bit of a 4-limb representation of a 256-bit word.
4. Conditional swapping.
5. Add and doubling an elliptic curve point.
6. Montgomery ladder step.
7. Montgomery ladder (elliptic curve point multiplication).
8. Iterated square.
9. Inverting elliptic curve point.
10. Encoding of the resulting elliptic curve point (includes reduction to \mod p).
11. Scalar multiplication.

As mentioned, these correctness proofs prove that the Jasmin implementation is correct, with respect to the procedural specification.

### Note on admitted lemmas
The following list of lemmas are left as `admit`, but are proven in Cryptoline (not available on this repository, yet):

1. `h_add_rrs_ref4` (correctness proof for the implementation of 4-limb addition implementation).
2. `h_sub_rrs_ref4` (correctness proof for the implementation of 4-limb subtraction).
3. `h_mul_a24_ref4` and `h_mul_a24_mulx` (correctness proof for the implementation of 4-limb multiplication with a constant).
4. `h_mul_rss_ref4` and `h_mul_rsr_mulx` (correctness proof for the implementation of 4-limb multiplication).
5. `h_mul_pp_ref4` (correctness proof for the implementation of 4-limb multiplication).
6. `h_sqr_rs_ref4` and `h_sqr_rr_mulx` (correctness proof for the implementation of 4-limb squaring).
7. `h_sqr_p_ref4` (correctness proof for the implementation of 4-limb squaring with a constant).

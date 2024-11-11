require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JWord.

type to_check = bool * bool * bool * bool.
op assume__ (x : to_check) = x.`1.
op assert__ (x : to_check) = x.`2.
op assume_proof__ (x: to_check) = x.`3.
op assert_proof__ (x : to_check) = x.`4.

op assume_ ['a] (x : 'a * to_check) = assume__ x.`2.
op assert_ ['a] (x : 'a * to_check) = assert__ x.`2.
op assume_proof_ ['a] (x : 'a * to_check) = assume_proof__ x.`2.
op assert_proof_ ['a] (x : 'a * to_check) = assert_proof__ x.`2.

abbrev upd_call (before intern: to_check) =
   (assume__ before /\ assume__ intern,
    assert__ before /\ assert__ intern,
    assume_proof__ before /\ assume_proof__ intern,
    assert_proof__ before /\ assert_proof__ intern).

abbrev [-printing] soundness__ x =
  (assert_proof__ x /\ assume_proof__ x) =>
  (assert__ x /\ assume__ x).

abbrev [-printing] soundness_ ['a] (x : 'a * _) =
  soundness__ x.`2.

op _spec_soundness ['a] (x : 'a * _) (post : bool) =
   assert_proof_ x /\ assume_proof_ x
   /\
   ((assert_ x /\ assume_ x) => post).

abbrev [-printing] _assert_spec ['a] (r : 'a * _) (post : bool) =
  assert_proof_ r
  /\
  ((assert_ r /\ assume_ r) => post).

(* Extracted program *)

abbrev u64i x = W64.to_uint x.
abbrev pow = Ring.IntID.exp.
abbrev single: int -> int = idfun.
abbrev eqmod (a b c: int) = (a - b) %% c = 0.

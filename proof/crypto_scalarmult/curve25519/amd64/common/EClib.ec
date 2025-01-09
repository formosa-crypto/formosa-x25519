require import List Int IntDiv.

lemma foldl_in_eq_r (f1 : 'a1 -> 'b -> 'a1)
  (f2 : 'a2 -> 'b -> 'a2)
  (s  : 'b list)
  (a2 : 'a2)
  (r  : 'a2 -> 'a1) :
 (forall a2 b, b \in s => f1 (r a2) b = r (f2 a2 b)) =>
                  foldl f1 (r a2) s = r (foldl f2 a2 s).
 proof.
    move: s a2. elim. by move => a2.
    move => x l hrec a2 /= hin. rewrite hin.
    by left.
    rewrite hrec //; move => ? ? h; rewrite hin.
    by right.
    by trivial.
 qed.

lemma divzU a b q r:
 0 <= r < `|b|%Int => a = b * q + r => q = a%/b by smt().

lemma modz_minus x d:
 (d <= x < 2 * d)%Int => x %% d = x - d by smt().

lemma divz_div a b c:
 0 < b => 0 < c => a %/ b %/ c = a %/ (b * c).
proof.
move=> *. smt(IntDiv.divzMl).
qed.

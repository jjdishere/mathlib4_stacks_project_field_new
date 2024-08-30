import Mathlib

open Polynomial
/--Let `F` be a prime number. Let `F` be a field of characteristic `p`.
Let `t ∈ F` be an element which does not have a `p` th root in `F`.
Then the polynomial `x ^ p - t` is irreducible over $F$.[Stacks: Lemma 09HF, first part](https://stacks.math.columbia.edu/tag/09HF)-/
theorem expand_irreducible {F : Type*} [Fact (Nat.Prime p)][Field F] {hp : 0 < p }{t : F} (p : ℕ )(ht : ∀ a : F, a ^ n ≠ t ) [CharP F p] :
 Irreducible (X ^ p - C t) := by sorry

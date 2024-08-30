import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open Polynomial
variable {F : Type*} [Field F] (p : ℕ)(P : Polynomial F)(hp : 0 < p )


-- Here is the lemma 12.5

noncomputable def myfun : (P.comp (X ^ p)).rootSet (AlgebraicClosure F) → P.rootSet (AlgebraicClosure F) :=
  fun x => ⟨x ^ p, by
  obtain ⟨h1, h2⟩ := Polynomial.mem_rootSet.1 x.2
  rw [Polynomial.mem_rootSet]
  constructor
  · rw [← expand_eq_comp_X_pow] at h1
    exact (expand_ne_zero hp).1 h1
  · simp only [aeval_comp, aeval_X_pow, aeval_X] at h2
    exact h2 ⟩

/-- Let `F` be a field. Let `p > 0` be the characteristic of `F`. Let `P` be a polynomial over `F`.
Then the set of roots of `P` and `P(xᵖ)` in the algebraic closure of `F` have the same cardinality (not counting multiplicity).-/
theorem rootSet_card_eq (hp : 0 < p )[CharP F p] [Fact (Nat.Prime p)]:
 Fintype.card (P.rootSet (AlgebraicClosure F)) =  Fintype.card ((P.comp (X ^ p)).rootSet (AlgebraicClosure F)) := by
 symm ; apply Fintype.card_congr
 apply Equiv.ofBijective (myfun p P hp)
 constructor
 · intro x y hxy
   simp only [myfun, Subtype.mk.injEq] at hxy
   apply SetCoe.ext
   replace hxy : (x.1 - y.1) ^ p = 0 := by simp only [sub_pow_char, hxy, sub_self]
   exact sub_eq_zero.1 (pow_eq_zero hxy)
 · intro h
   obtain ⟨h1, h2⟩ := Polynomial.mem_rootSet.1 h.2
   obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq h.1 hp
   simp only [myfun, Subtype.exists]
   use a
   have : (a ∈ (P.comp (X ^ p)).rootSet (AlgebraicClosure F)) := by
       apply (mem_rootSet_of_ne ?hp).2
       · simpa only [aeval_comp, aeval_X_pow, aeval_X, ha]
       · rw [← expand_eq_comp_X_pow]
         exact (expand_ne_zero hp).2 h1
   use this
   simp_all only [ne_eq, Subtype.coe_eta]

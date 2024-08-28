import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Basic
variable {F : Type*} [Field F] (p : ℕ)(P : Polynomial F)
/-- Let $F$ be a field and let $\overline{F}$ be an algebraic closure of $F$.
Let $p > 0$ be the characteristic of $F$. Let $P$ be a polynomial
over $F$. Then the set of roots of $P$ and $P(x^p)$ in $\overline{F}$
have the same cardinality (not counting multiplicity).-/

theorem card_eq [CharP F p] :
 Fintype.card (P.rootSet (AlgebraicClosure F)) =  Fintype.card ((P.comp (X ^ p)).rootSet (AlgebraicClosure F)) := by
 apply Fintype.card_congr
 sorry

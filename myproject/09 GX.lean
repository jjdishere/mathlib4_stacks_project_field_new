import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Group.Units
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
open Ideal
variable {k : Type*} [Field k] (p q : Polynomial k)
-- Here is the definition 11.1 (09 GX)

/-- If `k` is any field, we say that two polynomails in `k[x]` are relatively prime
  if they generate the unit ideal in `k[x]` -/
def poly_is_relprime : Prop :=
  IsUnit (Ideal.span {p, q})

variable {k : Type*} [Field k] {p : Polynomial k}{q : Polynomial k}
theorem poly_relprime_iff_coprime : poly_is_relprime p q ↔ IsCoprime p q := by
  constructor
  · unfold poly_is_relprime
    intro h
    replace h : ∃ a b, a * p + b * q = 1 := by
      have : 1 ∈ Ideal.span {p, q} := by
        rw [isUnit_iff] at h
        exact (eq_top_iff_one (Ideal.span {p, q})).mp h
      rwa [← Ideal.mem_span_pair]
    exact h
  · unfold IsCoprime poly_is_relprime
    intro h
    rw [← Ideal.mem_span_pair] at h
    simpa only [isUnit_iff, eq_top_iff_one]

import Mathlib
variable {k : Type*} [Field k] (p q : Polynomial k)
/-- If k is any field, we say that two polynomails in k[x] are relatively prime if they generate the
  unit ideal in k[x] -/
def poly_is_relprime : Prop :=
  Ideal.span {p, q} = ⊤

variable {k : Type*} [Field k] {p : Polynomial k}{q : Polynomial k}
theorem poly_relprime_iff_coprime : poly_is_relprime p q ↔ IsCoprime p q := by
  constructor
  · unfold poly_is_relprime
    intro h
    replace h : ∃ a b, a * p + b * q = 1 := by
      have : 1 ∈  Ideal.span {p, q} := by
        exact (Ideal.eq_top_iff_one (Ideal.span {p, q})).mp h
      rwa [← Ideal.mem_span_pair]
    exact h
  · unfold IsCoprime poly_is_relprime
    intro h
    rw [← Ideal.mem_span_pair] at h
    exact (Ideal.eq_top_iff_one (Ideal.span {p, q})).mpr h

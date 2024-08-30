/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Cardinality
import Mathlib.Data.Complex.Module
import Mathlib.RingTheory.Algebraic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Complex number as a finite dimensional vector space over `ℝ`

This file contains the `FiniteDimensional ℝ ℂ` instance, as well as some results about the rank
(`finrank` and `Module.rank`).
-/

open FiniteDimensional

namespace Complex

instance : FiniteDimensional ℝ ℂ :=
  of_fintype_basis basisOneI

@[simp]
theorem finrank_real_complex : finrank ℝ ℂ = 2 := by
  rw [finrank_eq_card_basis basisOneI, Fintype.card_fin]

@[simp]
theorem rank_real_complex : Module.rank ℝ ℂ = 2 := by simp [← finrank_eq_rank, finrank_real_complex]

theorem rank_real_complex'.{u} : Cardinal.lift.{u} (Module.rank ℝ ℂ) = 2 := by
  rw [← finrank_eq_rank, finrank_real_complex, Cardinal.lift_natCast, Nat.cast_ofNat]

/-- `Fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
theorem finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2) :=
  ⟨finrank_real_complex⟩

end Complex

instance (priority := 100) FiniteDimensional.complexToReal (E : Type*) [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E] : FiniteDimensional ℝ E :=
  FiniteDimensional.trans ℝ ℂ E

theorem rank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module.rank ℝ E = 2 * Module.rank ℂ E :=
  Cardinal.lift_inj.{_,0}.1 <| by
    rw [← lift_rank_mul_lift_rank ℝ ℂ E, Complex.rank_real_complex']
    simp only [Cardinal.lift_id']

theorem finrank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    FiniteDimensional.finrank ℝ E = 2 * FiniteDimensional.finrank ℂ E := by
  rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]

section Rational

open Cardinal Module

@[simp]
lemma Real.rank_rat_real : Module.rank ℚ ℝ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℝ ?_).trans mk_real
  simpa [mk_real] using aleph0_lt_continuum

@[simp]
lemma Complex.rank_rat_complex : Module.rank ℚ ℂ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℂ ?_).trans mk_complex
  simpa using aleph0_lt_continuum

/-- `ℂ` and `ℝ` are isomorphic as vector spaces over `ℚ`, or equivalently,
as additive groups. -/
theorem Complex.nonempty_linearEquiv_real : Nonempty (ℂ ≃ₗ[ℚ] ℝ) :=
  LinearEquiv.nonempty_equiv_iff_rank_eq.mpr <| by simp

open Polynomial

/--
[Stacks: Lemma 09GD, first part](https://stacks.math.columbia.edu/tag/09GD)

The field $\mathbf{C}$ is algebraic over $\mathbf{R}$.
Namely, if $\alpha=a+i b$ in $\mathbf{C}$, then $\alpha^2-2 a \alpha+a^2+b^2=0$ is a polynomial
equation for $\alpha$ over $\mathbf{R}$.
-/

theorem Complex.IsAlgebraic_over_real : Algebra.IsAlgebraic ℝ ℂ where
  isAlgebraic := by
    have lemma1 (a : ℝ) : ((a : ℂ) ^ 2).re = a ^ 2 := by
      calc
        _ = (a ^ 2 : ℂ).re := by simp only
        _ = ((a ^ 2 : ℝ): ℂ).re := by rw [Complex.ofReal_pow]
    have lemma2 (a : ℝ) : ((a : ℂ) ^ 2).im = 0 := by
      calc
        _ = (a ^ 2 : ℂ).im := by simp only
        _ = ((a ^ 2 : ℝ): ℂ).im := by rw [Complex.ofReal_pow]
    have lemma3 (z : ℂ) : z ^ 2 - 2 * z.re * z + (z.re ^ 2 + z.im ^ 2) = 0 := by
      let a : ℝ := z.re
      let b : ℝ := z.im
      have : z = a + b * Complex.I := Eq.symm (Complex.re_add_im z)
      simp only [this, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one,sub_self, add_zero, Complex.add_im, Complex.mul_im,
        zero_add, pow_two (↑a + ↑b * Complex.I)]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
        Complex.mul_im, zero_add, Complex.re_ofNat, Complex.im_ofNat, sub_zero, zero_mul,
        Complex.zero_re, lemma1]
        ring_nf
      · simp only [Complex.add_im, Complex.sub_im,Complex.mul_im, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
        add_zero, zero_add, Complex.re_ofNat, Complex.im_ofNat, sub_zero, zero_mul, Complex.zero_im,
        lemma2]
        ring_nf
    intro z
    unfold IsAlgebraic
    let poly : ℝ[X] := X ^ 2 - (C (2 * z.re)) * X + (C (z.re ^ 2 + z.im ^ 2))
    use poly
    constructor
    · have : poly.degree = 2 := by
        unfold_let poly
        compute_degree
        norm_num
        exact Nat.le_of_ble_eq_true rfl
        exact Nat.le_of_ble_eq_true rfl
      apply @Polynomial.ne_zero_of_degree_gt _ _ poly 1 _
      rw [this]
      exact Nat.one_lt_ofNat
    · have : (aeval z) poly = z ^ 2 - 2 * z.re * z + (z.re ^ 2 + z.im ^ 2) := by
        unfold_let poly
        simp only [map_mul,map_ofNat, map_add,map_pow, map_sub, aeval_X,
         aeval_C, Complex.coe_algebraMap]
      rw [this]
      exact lemma3 z

end Rational

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Frequencies where a characteristic function equals one

A probability law has characteristic function equal to one at a frequency precisely when
its phase is almost surely an integer multiple of `2π`. This concerns equality to one,
not merely modulus one: the latter also allows translated lattices.

The inner-product-space statement identifies the frequencies fixed by convolution with a
probability measure. On the real line, its phase condition describes an unshifted lattice.

The argument uses Mathlib's `integral_eq_iff_of_ae_le` and
`Complex.exp_eq_one_iff`. See W. Feller, *An Introduction to Probability Theory and Its
Applications*, volume II, second edition (1971), Chapter XI, for the renewal-theoretic use
of the lattice obstruction.
-/

public section

open Complex
open scoped RealInnerProductSpace

namespace MeasureTheory

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- A characteristic function equals one exactly when its integrand is almost surely one.
Unlike an equality of moduli, this does not permit a nontrivial constant phase. -/
theorem charFun_eq_one_iff (t : E) :
    charFun μ t = 1 ↔ ∀ᵐ x ∂μ, exp (⟪x, t⟫ * I) = 1 := by
  have hi : Integrable (fun x : E => exp (⟪x, t⟫ * I)) μ :=
    ⟨by fun_prop, .of_bounded (C := 1) (ae_of_all _ fun x => by simp)⟩
  constructor
  · intro h
    have hre : (fun x : E => (exp (⟪x, t⟫ * I)).re) =ᵐ[μ] fun _ => 1 := by
      apply (integral_eq_iff_of_ae_le hi.re (integrable_const 1)
        (ae_of_all _ fun x => (re_le_norm _).trans (by simp))).mp
      simp only [integral_re hi, ← charFun_apply, h, RCLike.one_re, integral_const,
        probReal_univ, smul_eq_mul, mul_one]
    filter_upwards [hre] with x hx
    apply Complex.ext hx
    simpa using (abs_re_eq_norm.mp (by simp [hx] :
      |(exp (⟪x, t⟫ * I)).re| = ‖exp (⟪x, t⟫ * I)‖))
  · intro h
    exact integral_eq_const h

/-- The frequencies fixed by a probability law are those whose inner-product phases
are almost surely integer multiples of `2π`. -/
theorem charFun_eq_one_iff_ae_inner_mem_int_mul (t : E) :
    charFun μ t = 1 ↔ ∀ᵐ x ∂μ, ∃ n : ℤ, ⟪x, t⟫ = n * (2 * Real.pi) := by
  rw [charFun_eq_one_iff]
  apply Filter.eventually_congr
  filter_upwards [] with x
  rw [exp_eq_one_iff]
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa using congrArg Complex.im hn
  · simp only [hn, ofReal_mul, ofReal_intCast, ofReal_ofNat]
    ring

end MeasureTheory

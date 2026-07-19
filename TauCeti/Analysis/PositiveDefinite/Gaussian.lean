/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Bochner.CharFun.PositiveDefinite
public import TauCeti.Analysis.PositiveDefinite.Pullback
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The Gaussian is a positive-definite function

The Gaussian `a ↦ exp (-c‖a‖²)` on a finite-dimensional real inner-product space `V` is
continuous and positive definite for every `c ≥ 0`. This is the Gaussian acceptance example
requested in Part C of the `OneParameterSemigroups` roadmap in TauCetiRoadmap
("positive-definite functions and Bochner's theorem").

The positive-definiteness is not proved from scratch: Mathlib's
`ProbabilityTheory.charFun_stdGaussian` computes the characteristic function of the standard
Gaussian measure on `V` to be `t ↦ exp (-‖t‖²/2)`, and
`TauCeti.charFun_isPositiveDefinite_of_star_eq_neg` (the finite-measure Fourier-transform bridge)
already records that a characteristic function is positive definite for the negation involution
`a⋆ = -a`. Rescaling the argument by `√(2c)` and pulling back along that scaling
(`TauCeti.IsPositiveDefinite.comp_addMonoidHom`) turns `exp (-‖·‖²/2)` into `exp (-c‖·‖²)`. This
is the existence half of the Gaussian representing-measure statement; the full Bochner
representation is a later milestone.

## Main declarations

* `TauCeti.isPositiveDefinite_gaussian`: `a ↦ exp (-c‖a‖²)` is positive definite for `c ≥ 0`
  under the negation involution.
* `TauCeti.continuous_gaussian`: `a ↦ exp (-c‖a‖²)` is continuous.
* `TauCeti.continuous_gaussian_and_isPositiveDefinite`: the paired continuity and
  positive-definiteness statement.
* `TauCeti.isPositiveDefinite_exp_neg_normSq`, `TauCeti.continuous_exp_neg_normSq`: the `c = 1`
  acceptance example `a ↦ exp (-‖a‖²)`.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962) — Bochner's theorem and positive-definite
  functions.
* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open MeasureTheory ProbabilityTheory Complex
open scoped ComplexOrder

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Gaussian `a ↦ exp (-c‖a‖²)` is continuous on `V` for every real `c`. -/
theorem continuous_gaussian (c : ℝ) :
    Continuous fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  fun_prop

/-- The Gaussian `a ↦ exp (-c‖a‖²)` on a finite-dimensional real inner-product space is positive
definite for every `c ≥ 0`, under the negation involution `a⋆ = -a`.

It is the characteristic function of the standard Gaussian measure with the spatial variable
rescaled by `√(2c)`, so positive-definiteness comes from the finite-measure Fourier-transform
bridge `TauCeti.charFun_isPositiveDefinite_of_star_eq_neg` via pullback along that scaling. -/
theorem isPositiveDefinite_gaussian [StarAddMonoid V] (hstar : ∀ x : V, star x = -x)
    {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveDefinite fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  have hbridge : IsPositiveDefinite (charFun (stdGaussian V)) :=
    charFun_isPositiveDefinite_of_star_eq_neg hstar
  set φ : V →+ V := DistribSMul.toAddMonoidHom V (Real.sqrt (2 * c)) with hφ
  have hφstar : ∀ x : V, φ (star x) = star (φ x) := by
    intro x
    simp [hφ, hstar, smul_neg]
  have hpull := hbridge.comp_addMonoidHom φ hφstar
  have heq : (fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)))
      = fun x : V => charFun (stdGaussian V) (φ x) := by
    funext a
    have hsq : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (by positivity)
    have hn : ‖(Real.sqrt (2 * c)) • a‖ ^ 2 = 2 * c * ‖a‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hsq]
    simp only [hφ, DistribSMul.toAddMonoidHom_apply, charFun_stdGaussian]
    rw [← Complex.ofReal_pow, hn]
    congr 1
    push_cast
    ring
  rw [heq]
  exact hpull

/-- The Gaussian `a ↦ exp (-c‖a‖²)` is both continuous and positive definite for `c ≥ 0`. -/
theorem continuous_gaussian_and_isPositiveDefinite [StarAddMonoid V]
    (hstar : ∀ x : V, star x = -x) {c : ℝ} (hc : 0 ≤ c) :
    (Continuous fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ))) ∧
      IsPositiveDefinite fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) :=
  ⟨continuous_gaussian c, isPositiveDefinite_gaussian hstar hc⟩

/-- The Gaussian acceptance example: `a ↦ exp (-‖a‖²)` is positive definite. -/
theorem isPositiveDefinite_exp_neg_normSq [StarAddMonoid V] (hstar : ∀ x : V, star x = -x) :
    IsPositiveDefinite fun a : V => Complex.exp (-(‖a‖ ^ 2 : ℝ)) := by
  have h := isPositiveDefinite_gaussian hstar (c := 1) zero_le_one
  simpa using h

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Gaussian acceptance example `a ↦ exp (-‖a‖²)` is continuous. -/
theorem continuous_exp_neg_normSq :
    Continuous fun a : V => Complex.exp (-(‖a‖ ^ 2 : ℝ)) := by
  simpa using continuous_gaussian (V := V) 1

end TauCeti

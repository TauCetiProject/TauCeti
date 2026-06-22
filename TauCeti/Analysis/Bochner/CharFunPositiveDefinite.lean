/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.Bochner.CharFunPosDef
import TauCeti.Analysis.PositiveDefinite.Basic
import TauCeti.Analysis.PositiveDefinite.Kernel
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Characteristic functions as positive-definite functions

This file connects the quadratic-form positivity calculation for characteristic functions to
Tau Ceti's generic positive-definite-function predicate. If the involution on an additive group is
negation, then Mathlib's characteristic function `MeasureTheory.charFun μ` of a finite measure is
`TauCeti.IsPositiveDefinite`.

Together with Mathlib's continuity theorem for characteristic functions, this gives the "finite
measure's Fourier transform is continuous positive-definite" bridge lemma requested in Part C of
the `OneParameterSemigroups` roadmap, before the harder converse direction of Bochner's theorem.

## Main declarations

* `TauCeti.charFun_isPositiveDefiniteKernel`: the translation-invariant kernel
  `K(a, b) = charFun μ (a - b)` is positive definite.
* `TauCeti.charFun_star_kernel_isPositiveDefiniteKernel_of_star_eq_neg`: with an explicit
  `star = -` involution, the kernel `K(a, b) = charFun μ (a + star b)` is positive definite.
* `TauCeti.charFun_isPositiveDefinite_of_star_eq_neg`: `charFun μ` is positive definite for any
  explicit `star = -` involution.
* `TauCeti.continuous_charFun_and_isPositiveDefinite_of_star_eq_neg`: the paired continuity and
  positive-definiteness package.
-/

open MeasureTheory

namespace TauCeti

open scoped ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- The translation-invariant characteristic-function kernel
`(a, b) ↦ charFun μ (a - b)` is positive definite. This repackages the existing Gram-matrix
statement `charFun_posSemidef` as a `TauCeti.IsPositiveDefiniteKernel`. -/
theorem charFun_isPositiveDefiniteKernel :
    IsPositiveDefiniteKernel (fun a b : E => MeasureTheory.charFun μ (a - b)) := by
  rw [isPositiveDefiniteKernel_def]
  simpa using charFun_posSemidef (μ := μ) (fun x : E => x)

/-- With an explicit `star = -` involution, the kernel associated to `charFun μ` by the generic
positive-definite-function construction, `(a, b) ↦ charFun μ (a + star b)`, is positive
definite. -/
theorem charFun_star_kernel_isPositiveDefiniteKernel_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    IsPositiveDefiniteKernel (fun a b : E => MeasureTheory.charFun μ (a + star b)) := by
  rw [isPositiveDefiniteKernel_def]
  simpa [hstar, sub_eq_add_neg] using charFun_posSemidef (μ := μ) (fun x : E => x)

/-- The characteristic function of a finite measure is positive definite for any additive-group
involution that is explicitly negation. This is the generic-predicate form of
`charFun_fintype_sum_mul_conj_nonneg`, using
`F (vᵢ + star vⱼ) = charFun μ (vᵢ - vⱼ)`. -/
theorem charFun_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    IsPositiveDefinite (MeasureTheory.charFun μ) := by
  intro n c v
  have h := charFun_fintype_sum_mul_conj_nonneg (μ := μ) c v
  refine le_of_le_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [hstar, sub_eq_add_neg]

/-- The characteristic function of a finite measure on a second-countable real inner product space
is continuous and positive definite, provided the chosen involution is negation. This is the
forward bridge toward Bochner's theorem in the language of `TauCeti.IsPositiveDefinite`. -/
theorem continuous_charFun_and_isPositiveDefinite_of_star_eq_neg
    [BorelSpace E] [SecondCountableTopology E] [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    Continuous (MeasureTheory.charFun μ) ∧ IsPositiveDefinite (MeasureTheory.charFun μ) :=
  ⟨MeasureTheory.continuous_charFun, charFun_isPositiveDefinite_of_star_eq_neg hstar⟩

/-- The continuous positive-definite characteristic function, together with its associated
positive-definite kernel. This is a convenient bundled form for downstream Bochner arguments that
need both the one-variable predicate and the two-variable Gram-kernel predicate. -/
theorem continuous_charFun_and_isPositiveDefinite_and_kernel_of_star_eq_neg
    [BorelSpace E] [SecondCountableTopology E] [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    Continuous (MeasureTheory.charFun μ) ∧ IsPositiveDefinite (MeasureTheory.charFun μ) ∧
      IsPositiveDefiniteKernel (fun a b : E => MeasureTheory.charFun μ (a + star b)) :=
  ⟨MeasureTheory.continuous_charFun, charFun_isPositiveDefinite_of_star_eq_neg hstar,
    charFun_star_kernel_isPositiveDefiniteKernel_of_star_eq_neg hstar⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.WeakMixing
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Checks for weak mixing of actions of `ℝ`

Checks for `MeasureTheory.Measure.IsWeaklyMixing` and its zero-one law.

* For a set `A` invariant under every translate, the integrand of the definition for the pair
  `(A, A)` is the constant `|μ(A) - μ(A)²|`, which is `1/4` when `μ(A) = 1/2`; for the pair
  `(A, Aᶜ)` it is the constant `μ(A) μ(Aᶜ)`.
* The trivial action of `ℝ` on a two-point space with the uniform probability measure is not
  weakly mixing: a point is an invariant set of measure `1/2`, and for `A = B` a point the
  integrand is `|1/2 - 1/4| = 1/4`.
-/

public section

noncomputable section

open MeasureTheory Measure Set
open scoped ENNReal

namespace TauCeti.Examples.WeakMixing

section Invariant

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] {μ : Measure X} {A : Set X}

/-- For a set invariant under every translate, the integrand of weak mixing for the pair
`(A, A)` is the constant `|μ(A) - μ(A)²|`. -/
theorem integrand_self_of_invariant (hA : ∀ t : ℝ, (fun x => t +ᵥ x) ⁻¹' A = A) (t : ℝ) :
    |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ A) - μ.real A * μ.real A| =
      |μ.real A - μ.real A * μ.real A| := by
  rw [hA t, inter_self]

/-- An invariant set of measure `1/2` gives the constant integrand `1/4`. -/
example (hA : ∀ t : ℝ, (fun x => t +ᵥ x) ⁻¹' A = A) (hμA : μ.real A = 1 / 2) (t : ℝ) :
    |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ A) - μ.real A * μ.real A| = 1 / 4 := by
  rw [integrand_self_of_invariant hA, hμA]
  norm_num

/-- For a set invariant under every translate, the integrand of weak mixing for the pair
`(A, Aᶜ)` is the constant `μ(A) μ(Aᶜ)`. -/
theorem integrand_compl_of_invariant (hA : ∀ t : ℝ, (fun x => t +ᵥ x) ⁻¹' A = A) (t : ℝ) :
    |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ Aᶜ) - μ.real A * μ.real Aᶜ| = μ.real A * μ.real Aᶜ := by
  rw [hA t, inter_compl_self, measureReal_empty, zero_sub, abs_neg,
    abs_of_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)]

end Invariant

/-- A two-point space, carrying the trivial action of `ℝ`. -/
def TwoPoint : Type := Bool

/-- The two-point space carries the discrete σ-algebra. -/
instance instMeasurableSpaceTwoPoint : MeasurableSpace TwoPoint := ⊤

instance instMeasurableSingletonClassTwoPoint : MeasurableSingletonClass TwoPoint :=
  ⟨fun _ => trivial⟩

/-- The trivial action of `ℝ` on the two-point space. -/
instance instAddActionTwoPoint : AddAction ℝ TwoPoint where
  vadd _ x := x
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

/-- The two points of `TwoPoint`. -/
def TwoPoint.pt (b : Bool) : TwoPoint := b

/-- The uniform probability measure on the two-point space. -/
def uniform : Measure TwoPoint := (2 : ℝ≥0∞)⁻¹ • Measure.count

/-- The uniform measure on the two-point space is a probability measure. -/
instance isProbabilityMeasure_uniform : IsProbabilityMeasure uniform := by
  refine ⟨?_⟩
  rw [uniform, smul_apply, Measure.count_univ]
  change (2 : ℝ≥0∞)⁻¹ • ((ENat.card Bool : ℕ∞) : ℝ≥0∞) = 1
  simp [ENNReal.inv_mul_cancel]

/-- Each point has uniform measure `1/2`. -/
theorem uniform_real_singleton (b : Bool) : uniform.real {TwoPoint.pt b} = 1 / 2 := by
  simp [uniform, measureReal_def, ENNReal.toReal_inv]

/-- **The trivial action on two points is not weakly mixing.** For the uniform measure, a point is
an invariant set of measure `1/2`, so the zero-one law of weak mixing fails. -/
example : ¬uniform.IsWeaklyMixing := by
  intro h
  have := h.measureReal_eq_zero_or_one (s := {TwoPoint.pt true}) trivial fun t => by rfl
  rw [uniform_real_singleton] at this
  norm_num at this

/-- For the trivial action on two points with the uniform measure, the integrand of weak mixing
for `A = B` a point is the constant `|1/2 - 1/4| = 1/4`. -/
example (t : ℝ) :
    |uniform.real ((fun x : TwoPoint => t +ᵥ x) ⁻¹' {TwoPoint.pt true} ∩ {TwoPoint.pt true}) -
        uniform.real {TwoPoint.pt true} * uniform.real {TwoPoint.pt true}| = 1 / 4 := by
  rw [integrand_self_of_invariant (fun _ => rfl), uniform_real_singleton]
  norm_num

end TauCeti.Examples.WeakMixing

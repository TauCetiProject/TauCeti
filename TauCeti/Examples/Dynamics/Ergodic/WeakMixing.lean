/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.WeakMixing
public import Mathlib.Probability.UniformOn

/-!
# Checks for weak mixing of actions of `ℝ`

Checks for `MeasureTheory.Measure.IsWeaklyMixing` and its zero-one law.

* For a set `A` almost invariant under the translate by `t`, the integrand of the definition at
  time `t` for a pair `(A, B)` is `|μ(A ∩ B) - μ(A) μ(B)|`; for the pair `(A, A)` it is
  `|μ(A) - μ(A)²|`, which is `1/4` when `μ(A) = 1/2`; for the pair `(A, Aᶜ)` it is
  `μ(A) μ(Aᶜ)`.
* The trivial action of `ℝ` on a two-point space with the uniform probability measure is not
  weakly mixing: a point is an invariant set of measure `1/2`, and for `A = B` a point the
  integrand is `|1/2 - 1/4| = 1/4`.
-/

public section

noncomputable section

open MeasureTheory Measure Set ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Examples.WeakMixing

section Invariant

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] {μ : Measure X} {A : Set X}

/-- For a set almost invariant under the translate by `t`, the integrand of weak mixing for a
pair `(A, B)` at time `t` is `|μ(A ∩ B) - μ(A) μ(B)|`. -/
theorem integrand_of_invariant {t : ℝ} (hA : (fun x => t +ᵥ x) ⁻¹' A =ᵐ[μ] A) (B : Set X) :
    |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ B) - μ.real A * μ.real B| =
      |μ.real (A ∩ B) - μ.real A * μ.real B| := by
  rw [measureReal_congr (hA.inter (by rfl : B =ᵐ[μ] B))]

/-- For a set almost invariant under the translate by `t`, the integrand of weak mixing for the
pair `(A, A)` at time `t` is `|μ(A) - μ(A)²|`. -/
theorem integrand_self_of_invariant {t : ℝ} (hA : (fun x => t +ᵥ x) ⁻¹' A =ᵐ[μ] A) :
    |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ A) - μ.real A * μ.real A| =
      |μ.real A - μ.real A * μ.real A| := by
  rw [integrand_of_invariant hA, inter_self]

/-- An invariant set of measure `1/2` gives the constant integrand `1/4`. -/
example {t : ℝ} (hA : (fun x => t +ᵥ x) ⁻¹' A =ᵐ[μ] A) (hμA : μ.real A = 1 / 2) :
    |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ A) - μ.real A * μ.real A| = 1 / 4 := by
  rw [integrand_self_of_invariant hA, hμA]
  norm_num

/-- For a set almost invariant under the translate by `t`, the integrand of weak mixing for the
pair `(A, Aᶜ)` at time `t` is `μ(A) μ(Aᶜ)`. -/
theorem integrand_compl_of_invariant {t : ℝ} (hA : (fun x => t +ᵥ x) ⁻¹' A =ᵐ[μ] A) :
    |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ Aᶜ) - μ.real A * μ.real Aᶜ| = μ.real A * μ.real Aᶜ := by
  rw [integrand_of_invariant hA, inter_compl_self]
  simp [abs_of_nonneg, mul_nonneg, measureReal_nonneg]

end Invariant

/-- A two-point space, carrying the trivial action of `ℝ`. -/
def TwoPoint : Type := Bool

/-- The two-point space carries the discrete σ-algebra of `Bool`. -/
instance instMeasurableSpaceTwoPoint : MeasurableSpace TwoPoint :=
  inferInstanceAs (MeasurableSpace Bool)

instance instMeasurableSingletonClassTwoPoint : MeasurableSingletonClass TwoPoint :=
  inferInstanceAs (MeasurableSingletonClass Bool)

instance instFintypeTwoPoint : Fintype TwoPoint := inferInstanceAs (Fintype Bool)

instance instNonemptyTwoPoint : Nonempty TwoPoint := inferInstanceAs (Nonempty Bool)

/-- The two-point space has two points. -/
theorem TwoPoint.card_eq : Fintype.card TwoPoint = 2 := Fintype.card_bool

/-- The trivial action of `ℝ` on the two-point space. -/
instance instAddActionTwoPoint : AddAction ℝ TwoPoint where
  vadd _ x := x
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

/-- The action of `ℝ` on the two-point space is trivial. -/
theorem TwoPoint.vadd_eq (t : ℝ) (x : TwoPoint) : t +ᵥ x = x := rfl

/-- Every subset of the two-point space is invariant under every translate. -/
theorem TwoPoint.preimage_vadd (t : ℝ) (s : Set TwoPoint) : (fun x => t +ᵥ x) ⁻¹' s = s := by
  simp only [TwoPoint.vadd_eq, preimage_id']

/-- The two points of `TwoPoint`. -/
def TwoPoint.pt (b : Bool) : TwoPoint := b

/-- Each point has measure `1/2` for the uniform probability measure on the two-point space. -/
theorem TwoPoint.uniformOn_univ_real_singleton (x : TwoPoint) :
    (uniformOn (univ : Set TwoPoint)).real {x} = 1 / 2 := by
  simp [measureReal_def, uniformOn_univ, TwoPoint.card_eq, ENNReal.toReal_inv]

/-- **The trivial action on two points is not weakly mixing.** For the uniform probability
measure, a point is an invariant set of measure `1/2`, so the zero-one law of weak mixing fails. -/
example : ¬(uniformOn (univ : Set TwoPoint)).IsWeaklyMixing := by
  intro h
  have := h.measureReal_eq_zero_or_one (measurableSet_singleton (TwoPoint.pt true))
    fun t => by rw [TwoPoint.preimage_vadd]
  rw [TwoPoint.uniformOn_univ_real_singleton] at this
  norm_num at this

/-- For the trivial action on two points with the uniform probability measure, the integrand of
weak mixing for `A = B` a point is the constant `|1/2 - 1/4| = 1/4`. -/
example (t : ℝ) :
    |(uniformOn (univ : Set TwoPoint)).real
        ((fun x : TwoPoint => t +ᵥ x) ⁻¹' {TwoPoint.pt true} ∩ {TwoPoint.pt true}) -
      (uniformOn (univ : Set TwoPoint)).real {TwoPoint.pt true} *
        (uniformOn (univ : Set TwoPoint)).real {TwoPoint.pt true}| = 1 / 4 := by
  rw [integrand_self_of_invariant (by rw [TwoPoint.preimage_vadd]),
    TwoPoint.uniformOn_univ_real_singleton]
  norm_num

end TauCeti.Examples.WeakMixing

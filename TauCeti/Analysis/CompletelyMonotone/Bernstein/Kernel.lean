/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
public import TauCeti.Analysis.CompletelyMonotone.Laplace.Measurability
public import Mathlib.Probability.Kernel.Defs

/-!
# Measurable Bernstein measures and their kernel form

The Hausdorff--Bernstein--Widder theorem and its basic representing-measure API live in
`TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder`. This file shows that
the Bernstein measure depends **measurably** on a parameter: a family `a ↦ f a` of completely
monotone functions whose values at the natural numbers are measurable in `a` has Bernstein
measures forming a `ProbabilityTheory.Kernel`.

Measurability is not a selection statement. The representing measure is unique, so the family
`a ↦ bernsteinMeasure (f a)` is already determined; what has to be proved is that this
particular family is measurable, and that is
`TauCeti.measurable_of_measurable_laplaceTransform_natCast`, applied to the identity
`laplaceTransform (bernsteinMeasure (f a)) n = f a n`.

## Main declarations

* `TauCeti.measurable_bernsteinMeasure`: measurable dependence on a parameter.
* `TauCeti.bernsteinMeasureKernel`: the resulting kernel, with its finiteness criterion.
* `TauCeti.exists_isContinuousCompletelyMonotoneOnIoi_ae_eq`: a family that is completely
  monotone and bounded by `1` at `0` only almost everywhere agrees almost everywhere with one that
  is so everywhere, as the kernel requires.

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV; see also
R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012),
Theorem 1.4.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  (BCR semigroup--Bochner).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {F : α → ℝ → ℝ}

/-- **The Bernstein measure depends measurably on a parameter.** If every member of a family of
functions is continuous on `[0, ∞)` and completely monotone on `(0, ∞)`, and if the family is
measurable in the parameter at each natural number, then the family of Bernstein measures is
measurable for the Giry σ-algebra.

Only the values at natural numbers enter, because a finite measure on `ℝ≥0` is already determined
by its Laplace transform there. -/
theorem measurable_bernsteinMeasure (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) :
    Measurable fun a => bernsteinMeasure (F a) := by
  refine measurable_of_measurable_laplaceTransform_natCast fun n => ?_
  have hrw : (fun a => laplaceTransform (bernsteinMeasure (F a)) (n : ℝ))
      = fun a => F a (n : ℝ) := by
    funext a
    exact laplaceTransform_bernsteinMeasure (hcm a) (Nat.cast_nonneg n)
  rw [hrw]
  exact hmeas n

/-- **The Bernstein kernel of a measurable family.** The Bernstein representing measures of a
measurable family of completely monotone functions assemble into a kernel from the parameter
space to `ℝ≥0`. -/
noncomputable def bernsteinMeasureKernel (F : α → ℝ → ℝ)
    (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) : Kernel α ℝ≥0 :=
  ⟨fun a => bernsteinMeasure (F a), measurable_bernsteinMeasure hcm hmeas⟩

@[simp]
theorem bernsteinMeasureKernel_apply (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) (a : α) :
    bernsteinMeasureKernel F hcm hmeas a = bernsteinMeasure (F a) :=
  (rfl)

/-- Every fibre of the Bernstein kernel represents the corresponding member of the family. -/
theorem representsLaplace_bernsteinMeasureKernel
    (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) (a : α) :
    RepresentsLaplace (bernsteinMeasureKernel F hcm hmeas a) (F a) := by
  rw [bernsteinMeasureKernel_apply]
  exact representsLaplace_bernsteinMeasure (hcm a)

/-- The Bernstein kernel is finite as soon as the values of the family at `0` are bounded; those
values are exactly the fibre masses. -/
theorem isFiniteKernel_bernsteinMeasureKernel
    (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) {C : ℝ} (hC : ∀ a, F a 0 ≤ C) :
    IsFiniteKernel (bernsteinMeasureKernel F hcm hmeas) := by
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, fun a => ?_⟩
  rw [bernsteinMeasureKernel_apply, bernsteinMeasure_univ (hcm a)]
  exact ENNReal.ofReal_le_ofReal (hC a)

/-- A family of normalized functions gives a Markov kernel. -/
theorem isMarkovKernel_bernsteinMeasureKernel
    (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) (hone : ∀ a, F a 0 = 1) :
    IsMarkovKernel (bernsteinMeasureKernel F hcm hmeas) := by
  refine ⟨fun a => ?_⟩
  rw [bernsteinMeasureKernel_apply]
  exact isProbabilityMeasure_bernsteinMeasure (hcm a) (hone a)

/-- **Correcting a family on a null set.** Let `F` be a family of functions, indexed by a measure
space, whose evaluations at the natural numbers are measurable in the parameter, and which for
almost every parameter is continuous on `[0, ∞)`, completely monotone on `(0, ∞)` and bounded by
`1` at `0`. Then some family `g` agreeing with `F` almost everywhere has these properties at
*every* parameter and still has measurable evaluations at the natural numbers. These are the
hypotheses of `bernsteinMeasureKernel` and `isFiniteKernel_bernsteinMeasureKernel`.

The family `g` is `F` on a measurable set of full measure and `0` off it. -/
theorem exists_isContinuousCompletelyMonotoneOnIoi_ae_eq {ν : Measure α} (F : α → ℝ → ℝ)
    (hF : ∀ᵐ a ∂ν, IsContinuousCompletelyMonotoneOnIoi (F a) ∧ F a 0 ≤ 1)
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) :
    ∃ g : α → ℝ → ℝ, (∀ a, IsContinuousCompletelyMonotoneOnIoi (g a)) ∧
      (∀ n : ℕ, Measurable fun a => g a (n : ℝ)) ∧ (∀ a, g a 0 ≤ 1) ∧ ∀ᵐ a ∂ν, g a = F a := by
  classical
  obtain ⟨s, hs, hsm, hgood⟩ := hF.exists_measurable_mem
  refine ⟨fun a => if a ∈ s then F a else 0, fun a => ?_, fun n => ?_, fun a => ?_, ?_⟩
  · dsimp only
    split_ifs with ha
    exacts [(hgood a ha).1, representsLaplace_zero.isContinuousCompletelyMonotoneOnIoi]
  · simp only [apply_ite (fun h : ℝ → ℝ => h n), Pi.zero_apply]
    exact (hmeas n).ite hsm measurable_const
  · dsimp only
    split_ifs with ha
    exacts [(hgood a ha).2, zero_le_one]
  · filter_upwards [hs] with a ha
    exact ite_eq_left ha

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.ProductMeasure

/-!
# Translation and inversion invariance of infinite product measures

An arbitrary product `MeasureTheory.Measure.infinitePi μ` of probability measures on measurable
types `G i` inherits left-multiplication, right-multiplication, and inversion invariance from its
factors (along with their additive counterparts via `@[to_additive]`). These are the infinite
probability-product companions to Mathlib's `MeasureTheory.Measure.pi.isMulLeftInvariant`,
`isMulRightInvariant`, and `isInvInvariant` for finite products.

No group axioms or topological hypotheses are required: `Mul` with `MeasurableMul` (or `Inv` with
`MeasurableInv`) on each factor suffices, via `MeasureTheory.Measure.infinitePi_map_pi`.

## Main instances

* `MeasureTheory.Measure.infinitePi.isMulLeftInvariant` (`isAddLeftInvariant`)
* `MeasureTheory.Measure.infinitePi.isMulRightInvariant` (`isAddRightInvariant`)
* `MeasureTheory.Measure.infinitePi.isInvInvariant` (`isNegInvariant`)

## References

* P. R. Halmos, *Measure Theory*, Van Nostrand, 1950, §38 and §60.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer, 1979, §15.17.
-/

public section

namespace MeasureTheory.Measure

variable {ι : Type*} {G : ι → Type*} [∀ i, MeasurableSpace (G i)]
  (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- An infinite product of left-invariant probability measures is left-invariant. -/
@[to_additive /-- An infinite product of left-invariant probability measures is left-invariant. -/]
instance infinitePi.isMulLeftInvariant [∀ i, Mul (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, IsMulLeftInvariant (μ i)] : IsMulLeftInvariant (Measure.infinitePi μ) := by
  refine ⟨fun g ↦ ?_⟩
  change (Measure.infinitePi μ).map (fun x i ↦ g i * x i) = Measure.infinitePi μ
  rw [Measure.infinitePi_map_pi _ fun i ↦ measurable_const_mul (g i)]
  simp_rw [map_mul_left_eq_self]

/-- An infinite product of right-invariant probability measures is right-invariant. -/
@[to_additive /-- An infinite product of right-invariant probability measures is
right-invariant. -/]
instance infinitePi.isMulRightInvariant [∀ i, Mul (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, IsMulRightInvariant (μ i)] : IsMulRightInvariant (Measure.infinitePi μ) := by
  refine ⟨fun g ↦ ?_⟩
  change (Measure.infinitePi μ).map (fun x i ↦ x i * g i) = Measure.infinitePi μ
  rw [Measure.infinitePi_map_pi _ fun i ↦ measurable_mul_const (g i)]
  simp_rw [map_mul_right_eq_self]

/-- An infinite product of inversion-invariant probability measures is inversion-invariant. -/
@[to_additive /-- An infinite product of negation-invariant probability measures is
negation-invariant. -/]
instance infinitePi.isInvInvariant [∀ i, Inv (G i)] [∀ i, MeasurableInv (G i)]
    [∀ i, IsInvInvariant (μ i)] : IsInvInvariant (Measure.infinitePi μ) := by
  refine ⟨?_⟩
  change (Measure.infinitePi μ).map (fun x i ↦ (x i)⁻¹) = Measure.infinitePi μ
  rw [Measure.infinitePi_map_pi _ fun _ ↦ measurable_inv]
  simp_rw [← inv_def, inv_eq_self]

end MeasureTheory.Measure

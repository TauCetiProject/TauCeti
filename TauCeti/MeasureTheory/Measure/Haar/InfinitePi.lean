/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.ProductMeasure
import TauCeti.Probability.ProductMeasure

/-!
# Haar measure instances for infinite product probability measures

Given a family of probability measures `μ : ∀ i, Measure (G i)` on measurable spaces or topological
groups `G i`, Kolmogorov's infinite product `MeasureTheory.Measure.infinitePi μ` on `Π i, G i`
inherits left, right, and inversion invariance, positivity on nonempty open sets, and
`IsHaarMeasure`, generalizing `MeasureTheory.Measure.pi.isHaarMeasure` beyond `[Fintype ι]`.

## Main declarations

* `MeasureTheory.Measure.infinitePi.isMulLeftInvariant`,
  `MeasureTheory.Measure.infinitePi.isMulRightInvariant`,
  `MeasureTheory.Measure.infinitePi.isInvInvariant` (and additive counterparts): invariance of
  `Measure.infinitePi μ`.
* `MeasureTheory.Measure.infinitePi.isOpenPosMeasure`: positivity on nonempty open subsets of
  `Π i, G i`, with no measurability assumption on open subsets of the factors (via the
  unconditional cylinder formula `TauCeti.infinitePi_pi'`).
* `MeasureTheory.Measure.infinitePi.isHaarMeasure`,
  `MeasureTheory.Measure.infinitePi.isAddHaarMeasure`: Haar measure instances on `Π i, G i`.

## References

* P. R. Halmos, *Measure Theory*, Van Nostrand (1950), §38 and §60.
* A. Weil, *Basic Number Theory*, 3rd ed., Springer (1974), Chapter IV, §1.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {ι : Type*} {G : ι → Type*} [∀ i, MeasurableSpace (G i)]
variable (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- An infinite product of left-invariant probability measures is left-invariant. -/
@[to_additive /-- An infinite product of left-translation-invariant probability measures is
left-translation-invariant. -/]
instance infinitePi.isMulLeftInvariant [∀ i, Mul (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, IsMulLeftInvariant (μ i)] :
    IsMulLeftInvariant (infinitePi μ) where
  map_mul_left_eq_self g := by
    simp_rw [Pi.mul_def]
    rw [infinitePi_map_pi μ fun i ↦ measurable_const_mul (g i)]
    simp_rw [map_mul_left_eq_self]

/-- An infinite product of right-invariant probability measures is right-invariant. -/
@[to_additive /-- An infinite product of right-translation-invariant probability measures is
right-translation-invariant. -/]
instance infinitePi.isMulRightInvariant [∀ i, Mul (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, IsMulRightInvariant (μ i)] :
    IsMulRightInvariant (infinitePi μ) where
  map_mul_right_eq_self g := by
    simp_rw [Pi.mul_def]
    rw [infinitePi_map_pi μ fun i ↦ measurable_mul_const (g i)]
    simp_rw [map_mul_right_eq_self]

/-- An infinite product of inversion-invariant probability measures is inversion-invariant. -/
@[to_additive /-- An infinite product of negation-invariant probability measures is
negation-invariant. -/]
instance infinitePi.isInvInvariant [∀ i, Inv (G i)] [∀ i, MeasurableInv (G i)]
    [∀ i, IsInvInvariant (μ i)] :
    IsInvInvariant (infinitePi μ) where
  inv_eq_self := by
    rw [Measure.inv_def, funext Pi.inv_def, infinitePi_map_pi μ fun _ ↦ measurable_inv]
    simp_rw [map_inv_eq_self]

/-- An infinite product of probability measures that are positive on nonempty open sets is positive
on nonempty open sets of the product topology. -/
instance infinitePi.isOpenPosMeasure [∀ i, TopologicalSpace (G i)]
    [∀ i, IsOpenPosMeasure (μ i)] :
    IsOpenPosMeasure (infinitePi μ) where
  open_pos := by
    rintro U hU ⟨a, ha⟩
    obtain ⟨s, t, ht, hstU⟩ := isOpen_pi_iff.mp hU a ha
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hstU))
    rw [TauCeti.infinitePi_pi', CanonicallyOrderedAdd.prod_pos]
    exact fun i hi ↦ (ht i hi).1.measure_pos (μ i) ⟨a i, (ht i hi).2⟩

/-- An infinite product of probability Haar measures is a Haar measure on the product group. -/
@[to_additive /-- An infinite product of probability additive Haar measures is an additive Haar
measure on the product additive group. -/]
instance infinitePi.isHaarMeasure [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, MeasurableMul (G i)] [∀ i, IsHaarMeasure (μ i)] :
    IsHaarMeasure (infinitePi μ) where

end MeasureTheory.Measure

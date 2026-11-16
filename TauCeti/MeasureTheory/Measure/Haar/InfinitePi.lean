/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.ProductMeasure

/-!
# Invariance and Haar measure instances for infinite product measures

For an arbitrary family of probability measures `μ i` on measurable spaces `G i`, Mathlib's
`MeasureTheory.Measure.infinitePi μ` is the unique product probability measure on `∀ i, G i`.
This file supplies the group-invariance, open-positivity, and Haar measure instances parallel to
Mathlib's `MeasureTheory.Measure.pi.*` instances for finite products:

* `MeasureTheory.Measure.infinitePi.isMulLeftInvariant`,
  `MeasureTheory.Measure.infinitePi.isAddLeftInvariant`: left translation invariance on an arbitrary
  product of probability spaces with measurable multiplication (or addition).
* `MeasureTheory.Measure.infinitePi.isMulRightInvariant`,
  `MeasureTheory.Measure.infinitePi.isAddRightInvariant`: right translation invariance.
* `MeasureTheory.Measure.infinitePi.isInvInvariant`,
  `MeasureTheory.Measure.infinitePi.isNegInvariant`: inversion (or negation) invariance.
* `MeasureTheory.Measure.infinitePi.isOpenPosMeasure`: strict positivity on nonempty open sets in
  the product topology, using no countability hypothesis on the index type.
* `MeasureTheory.Measure.infinitePi.isHaarMeasure`,
  `MeasureTheory.Measure.infinitePi.isAddHaarMeasure`: an infinite product of left-invariant
  open-positive probability measures (in particular, Haar probability measures) is a Haar measure.

## References

* N. Bourbaki, *Integration*, Chapter VII.
* J. Tate, *Fourier analysis in number fields, and Hecke's zeta-functions*, in *Algebraic Number
  Theory* (Cassels–Fröhlich), §3.3.
-/

public section

namespace MeasureTheory.Measure

universe u v

variable {ι : Type u}

/-- An infinite product of left-invariant probability measures is left-invariant. -/
@[to_additive /-- An infinite product of left-invariant probability measures is left-invariant. -/]
instance infinitePi.isMulLeftInvariant {G : ι → Type v} [∀ i, Mul (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsMulLeftInvariant] :
    (Measure.infinitePi μ).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    have hmul : (fun x : ∀ i, G i ↦ g * x) = fun x i ↦ g i * x i := rfl
    rw [hmul, infinitePi_map_pi μ fun i ↦ measurable_const_mul (g i)]
    simp_rw [map_mul_left_eq_self]

/-- An infinite product of right-invariant probability measures is right-invariant. -/
@[to_additive
  /-- An infinite product of right-invariant probability measures is right-invariant. -/]
instance infinitePi.isMulRightInvariant {G : ι → Type v} [∀ i, Mul (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsMulRightInvariant] :
    (Measure.infinitePi μ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have hmul : (fun x : ∀ i, G i ↦ x * g) = fun x i ↦ x i * g i := rfl
    rw [hmul, infinitePi_map_pi μ fun i ↦ measurable_mul_const (g i)]
    simp_rw [map_mul_right_eq_self]

/-- An infinite product of inversion-invariant probability measures is inversion-invariant. -/
@[to_additive /-- An infinite product of negation-invariant probability measures is
negation-invariant. -/]
instance infinitePi.isInvInvariant {G : ι → Type v} [∀ i, Inv (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableInv (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsInvInvariant] :
    (Measure.infinitePi μ).IsInvInvariant where
  inv_eq_self := by
    have hinv : (Inv.inv : (∀ i, G i) → ∀ i, G i) = fun x i ↦ (x i)⁻¹ := rfl
    rw [inv_def, hinv, infinitePi_map_pi μ fun _ ↦ measurable_inv]
    simp_rw [← inv_def, inv_eq_self]

/-- An infinite product of open-positive probability measures is positive on every nonempty open set
in the product topology. -/
instance infinitePi.isOpenPosMeasure {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, OpensMeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsOpenPosMeasure] :
    (Measure.infinitePi μ).IsOpenPosMeasure where
  open_pos U hU := by
    rintro ⟨a, ha⟩
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hU a ha
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hIu))
    rw [infinitePi_pi μ fun i hi ↦ (hu i hi).1.measurableSet, CanonicallyOrderedAdd.prod_pos]
    exact fun i hi ↦ (hu i hi).1.measure_pos (μ i) ⟨a i, (hu i hi).2⟩

/-- An infinite product of left-invariant, open-positive probability measures (in particular, Haar
probability measures) is a Haar measure. -/
@[to_additive /-- An infinite product of left-invariant, open-positive probability measures (in
particular, additive Haar probability measures) is an additive Haar measure. -/]
instance infinitePi.isHaarMeasure {G : ι → Type v} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, OpensMeasurableSpace (G i)]
    [∀ i, MeasurableMul (G i)] (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsMulLeftInvariant] [∀ i, (μ i).IsOpenPosMeasure] :
    (Measure.infinitePi μ).IsHaarMeasure where

end MeasureTheory.Measure

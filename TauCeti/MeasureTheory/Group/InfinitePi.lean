/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Probability.ProductMeasure

/-!
# Translation invariance, open positivity, and Haar instances for `Measure.infinitePi`

Mathlib registers `IsMulLeftInvariant`, `IsMulRightInvariant`, `IsInvInvariant`, `IsOpenPosMeasure`,
and `IsHaarMeasure` for finite product measures `Measure.pi μ` in
`Mathlib.MeasureTheory.Constructions.Pi`, where the index type is finite. For an arbitrary index
type `ι` and a family of probability measures `μ i`, Kolmogorov's product measure
`Measure.infinitePi μ` on `∀ i, G i` (equipped with the product σ-algebra) enjoys the same
invariance and positivity properties without any countability assumption on `ι`:

* Coordinatewise maps commute with `Measure.infinitePi` (`Measure.infinitePi_map_pi`), so left
  translation, right translation, and inversion preserve `Measure.infinitePi μ` whenever they
  preserve every factor `μ i`.
* Every nonempty open subset of `∀ i, X i` contains a finite cylinder `(I : Set ι).pi u` with open
  nonempty factors `u i` (`i ∈ I`), whose `infinitePi` mass is the finite product
  `∏ i ∈ I, μ i (u i) > 0`.
* Because `Measure.infinitePi μ` is a probability measure, it is automatically finite on compact
  sets, so left invariance and positivity on nonempty open sets make it a Haar measure for the
  product σ-algebra (which coincides with the Borel σ-algebra when `ι` is countable and each factor
  is a second-countable Borel space).

## Main declarations

* `MeasureTheory.Measure.infinitePi.isOpenPosMeasure`: `Measure.infinitePi μ` charges every
  nonempty open set in the product topology.
* `MeasureTheory.Measure.infinitePi.isMulLeftInvariant`,
  `MeasureTheory.Measure.infinitePi.isMulRightInvariant`,
  `MeasureTheory.Measure.infinitePi.isInvInvariant` (and additive counterparts): translation and
  inversion invariance of `Measure.infinitePi μ`.
* `MeasureTheory.Measure.infinitePi.isHaarMeasure` (and `isAddHaarMeasure`): Haar measure instance
  on `Measure.infinitePi μ` for a family of probability Haar measures.

## References

* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979), §15.17.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Graduate Texts in
  Mathematics 186, Springer (1999), Chapter 5, §5.1.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {ι : Type*}

/-- An infinite product of probability measures, each positive on nonempty open sets, is positive on
nonempty open sets of the product space. -/
instance infinitePi.isOpenPosMeasure {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, OpensMeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsOpenPosMeasure (μ i)] :
    IsOpenPosMeasure (Measure.infinitePi μ) where
  open_pos U hU := by
    rintro ⟨a, ha⟩
    obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU a ha
    refine (lt_of_lt_of_le ?_ (measure_mono hIU)).ne'
    rw [infinitePi_pi μ fun i hi ↦ (hu i hi).1.measurableSet]
    exact CanonicallyOrderedAdd.prod_pos.mpr fun i hi ↦
      (hu i hi).1.measure_pos (μ i) ⟨a i, (hu i hi).2⟩

/-- An infinite product of left-invariant probability measures is left-invariant. -/
@[to_additive /-- An infinite product of left-addition-invariant probability measures is
left-addition-invariant. -/]
instance infinitePi.isMulLeftInvariant {G : ι → Type*} [∀ i, Mul (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul (G i)] (μ : ∀ i, Measure (G i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsMulLeftInvariant] :
    (Measure.infinitePi μ).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    have h := infinitePi_map_pi μ (f := fun i x ↦ g i * x) fun i ↦ measurable_const_mul (g i)
    simpa only [Pi.mul_def, map_mul_left_eq_self] using h

/-- An infinite product of right-invariant probability measures is right-invariant. -/
@[to_additive /-- An infinite product of right-addition-invariant probability measures is
right-addition-invariant. -/]
instance infinitePi.isMulRightInvariant {G : ι → Type*} [∀ i, Mul (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul (G i)] (μ : ∀ i, Measure (G i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsMulRightInvariant] :
    (Measure.infinitePi μ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have h := infinitePi_map_pi μ (f := fun i x ↦ x * g i) fun i ↦ measurable_mul_const (g i)
    simpa only [Pi.mul_def, map_mul_right_eq_self] using h

/-- An infinite product of inversion-invariant probability measures is inversion-invariant. -/
@[to_additive /-- An infinite product of negation-invariant probability measures is
negation-invariant. -/]
instance infinitePi.isInvInvariant {G : ι → Type*} [∀ i, Inv (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableInv (G i)] (μ : ∀ i, Measure (G i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsInvInvariant] :
    (Measure.infinitePi μ).IsInvInvariant where
  inv_eq_self := by
    rw [inv_def, funext Pi.inv_def]
    have h := infinitePi_map_pi μ (f := fun i ↦ (Inv.inv : G i → G i)) fun _ ↦ measurable_inv
    simpa only [map_inv_eq_self] using h

/-- An infinite product of probability Haar measures is a Haar measure (with respect to the product
σ-algebra). -/
@[to_additive /-- An infinite product of probability additive Haar measures is an additive Haar
measure (with respect to the product σ-algebra). -/]
instance infinitePi.isHaarMeasure {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, OpensMeasurableSpace (G i)]
    [∀ i, MeasurableMul (G i)] (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsHaarMeasure] : (Measure.infinitePi μ).IsHaarMeasure where

end MeasureTheory.Measure

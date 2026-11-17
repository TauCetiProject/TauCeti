/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.ProductMeasure

/-!
# Haar measures on infinite products

For an arbitrary family of probability measures `μ i` on spaces `X i`, Mathlib's
`MeasureTheory.Measure.infinitePi μ` constructs the product probability measure on `∀ i, X i`.
This file records the group-invariance and open-positivity instances inherited by `infinitePi μ`:

* If each `μ i` charges every nonempty open set (and open sets are measurable), then so does
  `Measure.infinitePi μ`, because every nonempty open set in the product topology contains a
  nonempty finite-cylinder box `s.pi V` of positive finite product mass.
* Left multiplication invariance, right multiplication invariance, and inversion invariance pass
  directly from the factor measures to `Measure.infinitePi μ` via
  `MeasureTheory.Measure.infinitePi_map_pi`, with no countability or topological assumptions.
* Combining these with finiteness (automatic from `IsProbabilityMeasure`), the infinite product
  of probability Haar measures is again a Haar measure.

All group instances carry `@[to_additive]` counterparts.

## Main instances

* `TauCeti.instIsOpenPosMeasureInfinitePi`: `Measure.infinitePi μ` is positive on nonempty open
  sets whenever each factor is.
* `TauCeti.instIsMulLeftInvariantInfinitePi` / `TauCeti.instIsAddLeftInvariantInfinitePi`:
  left-invariance of `Measure.infinitePi μ`.
* `TauCeti.instIsMulRightInvariantInfinitePi` / `TauCeti.instIsAddRightInvariantInfinitePi`:
  right-invariance of `Measure.infinitePi μ`.
* `TauCeti.instIsInvInvariantInfinitePi` / `TauCeti.instIsNegInvariantInfinitePi`:
  inversion/negation-invariance of `Measure.infinitePi μ`.
* `TauCeti.instIsHaarMeasureInfinitePi` / `TauCeti.instIsAddHaarMeasureInfinitePi`:
  `Measure.infinitePi μ` is a Haar measure whenever each `μ i` is a probability Haar measure.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section OpenPos

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, OpensMeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- An infinite product of probability measures that are positive on nonempty open sets is again
positive on nonempty open sets. -/
instance instIsOpenPosMeasureInfinitePi [∀ i, (μ i).IsOpenPosMeasure] :
    (Measure.infinitePi μ).IsOpenPosMeasure where
  open_pos U hU hne := by
    classical
    obtain ⟨x, hx⟩ := hne
    obtain ⟨s, V, hV, hsub⟩ := isOpen_pi_iff.mp hU x hx
    have hpos : ∏ i ∈ s, μ i (V i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi ↦
        ((hV i hi).1.measure_pos (μ i) ⟨x i, (hV i hi).2⟩).ne'
    have hmeas : ∀ i ∈ s, MeasurableSet (V i) := fun i hi ↦ (hV i hi).1.measurableSet
    have hle : ∏ i ∈ s, μ i (V i) ≤ Measure.infinitePi μ U := by
      rw [← Measure.infinitePi_pi μ hmeas]
      exact measure_mono hsub
    exact ne_zero_of_lt (pos_iff_ne_zero.mpr hpos |>.trans_le hle)

end OpenPos

section Invariant

variable {ι : Type*} {G : ι → Type*} [∀ i, MeasurableSpace (G i)]
  (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- An infinite product of left-invariant probability measures is left-invariant. -/
@[to_additive /-- An infinite product of left-translation-invariant probability measures is
left-translation-invariant. -/]
instance instIsMulLeftInvariantInfinitePi [∀ i, Mul (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, (μ i).IsMulLeftInvariant] :
    (Measure.infinitePi μ).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    have h := Measure.infinitePi_map_pi μ (f := fun i ↦ (g i * ·))
      fun i ↦ measurable_const_mul (g i)
    have hfun : (g * · : (∀ i, G i) → ∀ i, G i) = fun x i ↦ g i * x i := rfl
    simpa only [hfun, map_mul_left_eq_self] using h

/-- An infinite product of right-invariant probability measures is right-invariant. -/
@[to_additive /-- An infinite product of right-translation-invariant probability measures is
right-translation-invariant. -/]
instance instIsMulRightInvariantInfinitePi [∀ i, Mul (G i)] [∀ i, MeasurableMul (G i)]
    [∀ i, (μ i).IsMulRightInvariant] :
    (Measure.infinitePi μ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have h := Measure.infinitePi_map_pi μ (f := fun i ↦ (· * g i))
      fun i ↦ measurable_mul_const (g i)
    have hfun : (· * g : (∀ i, G i) → ∀ i, G i) = fun x i ↦ x i * g i := rfl
    simpa only [hfun, map_mul_right_eq_self] using h

/-- An infinite product of inversion-invariant probability measures is inversion-invariant. -/
@[to_additive /-- An infinite product of negation-invariant probability measures is
negation-invariant. -/]
instance instIsInvInvariantInfinitePi [∀ i, Inv (G i)] [∀ i, MeasurableInv (G i)]
    [∀ i, (μ i).IsInvInvariant] :
    (Measure.infinitePi μ).IsInvInvariant where
  inv_eq_self := by
    have h := Measure.infinitePi_map_pi μ (f := fun i ↦ (·⁻¹ : G i → G i))
      fun _ ↦ measurable_inv
    have hfun : (Inv.inv : (∀ i, G i) → ∀ i, G i) = fun x i ↦ (x i)⁻¹ := rfl
    simpa only [Measure.inv_def, hfun, Measure.map_inv_eq_self] using h

end Invariant

section Haar

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, OpensMeasurableSpace (G i)] [∀ i, MeasurableMul (G i)]
  (μ : ∀ i, Measure (G i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- An infinite product of probability Haar measures is a Haar measure. -/
@[to_additive /-- An infinite product of probability additive Haar measures is an additive Haar
measure. -/]
instance instIsHaarMeasureInfinitePi [∀ i, (μ i).IsHaarMeasure] :
    (Measure.infinitePi μ).IsHaarMeasure where

end Haar

end TauCeti

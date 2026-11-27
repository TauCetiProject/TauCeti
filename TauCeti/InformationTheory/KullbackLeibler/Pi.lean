/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ProductMeasure

import TauCeti.InformationTheory.KullbackLeibler.Basic
import TauCeti.InformationTheory.KullbackLeibler.ChainRule
import TauCeti.Probability.ProductMeasure

/-!
# Relative entropy of product measures

Relative entropy tensorizes over finite products of probability measures:
`klDiv (Measure.pi P) (Measure.pi Q) = ∑ i, klDiv (P i) (Q i)`. In particular the relative
entropy between the laws of `n` independent observations from `P` and from `Q` is
`n * klDiv P Q`, the form used in minimax lower bounds for samples of size `n`.

For factors indexed by `Fin n` the proof is by induction on `n`.
`MeasurableEquiv.piFinSuccAbove` splits off the first coordinate and carries `Measure.pi P` to a
binary product; measurable equivalences preserve relative entropy
(`MeasureTheory.Measure.klDiv_map_measurableEquiv`); and the binary case is
`TauCeti.klDiv_prod_prod`. A general finite index type is reduced to `Fin n` by
`MeasurableEquiv.piCongrLeft`.

For an infinite product `Measure.infinitePi` whose factors differ only on a finite set `S` of
coordinates, the product splits into the finite block over `S` and the block over its complement
(`TauCeti.measurePreserving_piEquivPiSubtypeProd_infinitePi`); the complement block is the same law
under both products, so it contributes nothing, and the finite block tensorizes.

## Main statements

* `TauCeti.klDiv_pi`: tensorization over a finite index type, for dependent products.
* `TauCeti.klDiv_infinitePi`: tensorization over an arbitrary index type, for factors that agree
  outside a finite set.
* `MeasureTheory.Measure.klDiv_pi_const`: `klDiv (P^n) (Q^n) = n * klDiv P Q`.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Section 2.4,
  property (iii) of the Kullback divergence, p. 85.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace TauCeti

/-- Tensorization of relative entropy over products indexed by `Fin n`; the general finite index
type is reduced to this case in `klDiv_pi`. -/
private theorem klDiv_pi_fin {n : ℕ} {X : Fin n → Type*} [∀ i, MeasurableSpace (X i)]
    (P Q : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] :
    klDiv (Measure.pi P) (Measure.pi Q) = ∑ i, klDiv (P i) (Q i) := by
  induction n with
  | zero => rw [Measure.pi_of_empty P, Measure.pi_of_empty Q]; simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove X 0
    rw [← Measure.klDiv_map_measurableEquiv _ _ e, (measurePreserving_piFinSuccAbove P 0).map_eq,
      (measurePreserving_piFinSuccAbove Q 0).map_eq, klDiv_prod_prod, Fin.sum_univ_succ]
    exact congrArg _ (ih _ _)

/-- **Tensorization** of relative entropy over finite products of probability measures. -/
theorem klDiv_pi {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (P Q : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] :
    klDiv (Measure.pi P) (Measure.pi Q) = ∑ i, klDiv (P i) (Q i) := by
  let f := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft P f).map_eq, ← (measurePreserving_piCongrLeft Q f).map_eq,
    Measure.klDiv_map_measurableEquiv, klDiv_pi_fin, Equiv.sum_comp f fun i ↦ klDiv (P i) (Q i)]

/-- **Tensorization** of relative entropy over an infinite product of probability measures whose
factors agree outside a finite set `S` of coordinates. -/
theorem klDiv_infinitePi {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (P Q : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] (S : Finset ι) (hPQ : ∀ i ∉ S, P i = Q i) :
    klDiv (Measure.infinitePi P) (Measure.infinitePi Q) = ∑ i ∈ S, klDiv (P i) (Q i) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd X (· ∈ S)
  have hmap (R : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (R i)] :=
    (measurePreserving_piEquivPiSubtypeProd_infinitePi R (· ∈ S)).map_eq
  have hcompl : (fun i : {i // i ∉ S} ↦ P i) = fun i : {i // i ∉ S} ↦ Q i :=
    funext fun i ↦ hPQ i i.property
  -- Split both products into the block over `S` and the block over its complement.
  rw [← Measure.klDiv_map_measurableEquiv _ _ e, hmap P, hmap Q, klDiv_prod_prod]
  -- The complement blocks are the same law, so they contribute nothing.
  rw [hcompl, klDiv_self, add_zero]
  -- The blocks over `S` are finite products, which tensorize.
  simp_rw [Measure.infinitePi_eq_pi, klDiv_pi]
  exact Finset.sum_coe_sort S fun i ↦ klDiv (P i) (Q i)

end TauCeti

namespace MeasureTheory.Measure

/-- Relative entropy between the laws of `n` independent observations from `P` and from `Q`:
`klDiv (P^n) (Q^n) = n * klDiv P Q`. -/
theorem klDiv_pi_const {X : Type*} [MeasurableSpace X] {n : ℕ} (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    klDiv (Measure.pi fun _ : Fin n ↦ P) (Measure.pi fun _ : Fin n ↦ Q) = n * klDiv P Q := by
  simp [TauCeti.klDiv_pi]

end MeasureTheory.Measure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.RankOne
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Restricted.UnitGaussValuation

/-!
# The unit Gauss point of a closed polydisc

Let `K` be an ultrametric normed field and `D = closedPolydisc n K` the closed unit polydisc of
dimension `n` over `K`, whose coordinate ring is the trivial-weight restricted power series ring
`K⟨T₁, …, Tₙ⟩`. The unit-radius Gauss valuation `TauCeti.Huber.unitGaussValuation n K` is
continuous and bounded by `1` on `K⟨T₁, …, Tₙ⟩°`, so it defines the *unit Gauss point*
`unitGaussPoint n K : closedPolydisc n K`.

A point `η` of `closedPolydisc n K` satisfies the predicate `IsUnitGaussPoint K n η` when it
compares restricted power series by their unit Gauss norms; this uniquely characterizes
`unitGaussPoint n K`. Its valuative relation has rank at most one and trivial support. In
dimension `0`, `closedPolydisc 0 K` is a subsingleton, so the unit Gauss point coincides with every
classical point; in positive dimension over a complete field, its trivial support implies that it
does not lie in `classicalPoints n K`.

## Main definitions

* `TauCeti.ValuationSpectrum.IsUnitGaussPoint`: predicate characterizing the valuation class of
  the unit Gauss point of `closedPolydisc n K` via `MvPowerSeries.gaussNorm`.
* `TauCeti.ValuationSpectrum.unitGaussPoint`: the unit Gauss point of `closedPolydisc n K`.

## Main results

* `TauCeti.ValuationSpectrum.isRankLeOne_unitGaussPoint`: the unit Gauss point has rank at most one.
* `TauCeti.ValuationSpectrum.isUnitGaussPoint_iff_eq_unitGaussPoint`: `IsUnitGaussPoint K n η`
  holds if and only if `η = unitGaussPoint n K`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_ne_classicalPoint` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_classicalPoints`: in positive dimension over a
  complete field, the unit Gauss point is not classical.
* `TauCeti.ValuationSpectrum.unitGaussPoint_zero_eq_classicalPoint` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_zero_mem_classicalPoints`: in dimension `0`, the unit
  Gauss point coincides with the unique classical point and lies in `classicalPoints 0 K`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50 and
  Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

section UnitGaussPoint

variable (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- A point `η` of the closed unit polydisc of dimension `n` over `K` is the unit Gauss point if it
compares restricted power series as their unit Gauss norms `‖∑ a_α T^α‖ = max ‖a_α‖` do. -/
def IsUnitGaussPoint (K : Type*) [NormedField K] [IsUltrametricDist K] (n : ℕ)
    (η : closedPolydisc n K) : Prop :=
  ∀ f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
    η.val.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) ≤
        MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (g : MvPowerSeries (Fin n) K)

/-- Unfolding lemma for `IsUnitGaussPoint`. -/
theorem isUnitGaussPoint_iff {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔
      ∀ f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
        η.val.toValuativeRel.vle f g ↔
          MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) ≤
            MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (g : MvPowerSeries (Fin n) K) :=
  Iff.rfl

/-- **The unit Gauss point of `closedPolydisc n K`**: the point of `Spa (K⟨T₁, …, Tₙ⟩, K⟨T⟩°)`
defined by `unitGaussValuation n K`. -/
noncomputable def unitGaussPoint : closedPolydisc n K :=
  ⟨ofValuation (unitGaussValuation n K), (mem_closedPolydisc_iff n K _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr <| by
        rw [unitGaussValuation_def]
        exact isContinuous_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)),
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact unitGaussValuation_le_one_of_mem_powerBoundedSubring hf⟩⟩

/-- The underlying point of `unitGaussPoint n K` in `Spv K⟨T₁, …, Tₙ⟩`. -/
theorem unitGaussPoint_val :
    (unitGaussPoint n K).val = ofValuation (unitGaussValuation n K) := (rfl)

/-- The unit Gauss point compares restricted power series by their unit Gauss valuations. -/
@[simp]
theorem unitGaussPoint_vle_iff
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).val.toValuativeRel.vle f g ↔
      unitGaussValuation n K f ≤ unitGaussValuation n K g := by
  rw [unitGaussPoint_val, vle_ofValuation]

/-- The unit Gauss point kills only the zero series. -/
theorem unitGaussPoint_vle_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    (unitGaussPoint n K).val.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [unitGaussPoint_vle_iff, map_zero, nonpos_iff_eq_zero, unitGaussValuation_eq_zero_iff]

/-- **The support of the unit Gauss point is trivial.** -/
@[simp]
theorem supp_unitGaussPoint : (unitGaussPoint n K).val.supp = ⊥ :=
  Ideal.ext fun _ ↦ by rw [mem_supp_iff, unitGaussPoint_vle_zero_iff, Ideal.mem_bot]

/-- **The unit Gauss point has rank at most one**: it compares series by the `ℝ≥0`-valued unit
Gauss valuation. -/
@[simp]
theorem isRankLeOne_unitGaussPoint :
    @ValuativeRel.IsRankLeOne _ _ (unitGaussPoint n K).val.toValuativeRel :=
  letI := (unitGaussPoint n K).val.toValuativeRel
  haveI : (unitGaussValuation n K).Compatible := ⟨unitGaussPoint_vle_iff n K⟩
  ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean (unitGaussValuation n K)

/-- `unitGaussPoint n K` satisfies `IsUnitGaussPoint K n`. -/
theorem isUnitGaussPoint_unitGaussPoint : IsUnitGaussPoint K n (unitGaussPoint n K) := by
  intro f g
  rw [unitGaussPoint_vle_iff, ← NNReal.coe_le_coe, coe_unitGaussValuation, coe_unitGaussValuation]

variable {n K} in
/-- Any point satisfying `IsUnitGaussPoint K n` equals `unitGaussPoint n K`. -/
theorem IsUnitGaussPoint.eq_unitGaussPoint {η : closedPolydisc n K}
    (hη : IsUnitGaussPoint K n η) : η = unitGaussPoint n K :=
  Subtype.ext <| ext' fun f g ↦
    (isUnitGaussPoint_iff.mp hη f g).trans (isUnitGaussPoint_unitGaussPoint n K f g).symm

/-- `IsUnitGaussPoint K n η` uniquely characterizes `unitGaussPoint n K`. -/
@[simp]
theorem isUnitGaussPoint_iff_eq_unitGaussPoint {n : ℕ} {K : Type*} [NormedField K]
    [IsUltrametricDist K] {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔ η = unitGaussPoint n K :=
  ⟨IsUnitGaussPoint.eq_unitGaussPoint, fun h ↦ h ▸ isUnitGaussPoint_unitGaussPoint n K⟩

/-- **In positive dimension over a complete field, the unit Gauss point is not classical.** -/
theorem unitGaussPoint_ne_classicalPoint {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [NeZero n] (x : spa (powerBoundedSubring K)) (a : Fin n → K)
    (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint n K ≠ classicalPoint x a ha :=
  ne_classicalPoint_of_supp_eq_bot _ (supp_unitGaussPoint n K) x a ha

/-- **In positive dimension over a complete field, the unit Gauss point is not in
`classicalPoints n K`.** -/
@[simp]
theorem unitGaussPoint_notMem_classicalPoints {n : ℕ} {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [NeZero n] :
    unitGaussPoint n K ∉ classicalPoints n K := by
  rw [mem_classicalPoints_iff]
  rintro ⟨a, ha, h⟩
  rw [normClassicalPoint_def] at h
  exact unitGaussPoint_ne_classicalPoint (normSpaPoint K) a ha h.symm

/-- **In dimension `0`, the unit Gauss point coincides with every classical point**, without any
residue-field assumption. -/
theorem unitGaussPoint_zero_eq_classicalPoint {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (x : spa (powerBoundedSubring K)) (a : Fin 0 → K)
    (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint 0 K = classicalPoint x a ha :=
  Subsingleton.elim _ _

/-- **In dimension `0`, the unit Gauss point lies in `classicalPoints 0 K`**, over every complete
ultrametric normed field. -/
@[simp]
theorem unitGaussPoint_zero_mem_classicalPoints {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] :
    unitGaussPoint 0 K ∈ classicalPoints 0 K := by
  rw [unitGaussPoint_zero_eq_classicalPoint (normSpaPoint K) Fin.elim0 fun i ↦ i.elim0]
  exact classicalPoint_mem_classicalPoints _ _ _

end UnitGaussPoint

end TauCeti.ValuationSpectrum

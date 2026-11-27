/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Restricted.Gauss.Valuation

/-!
# The unit Gauss point of a closed polydisc

Let `K` be an ultrametric normed field and `D = closedPolydisc n K` the closed unit polydisc
`Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` of dimension `n`. Applying the general unit-radius Gauss
valuation `TauCeti.Huber.weightedGaussValuation` to `NormedField.valuation` yields a continuous
valuation on `K⟨T₁, …, Tₙ⟩` bounded by `1` on `K⟨T₁, …, Tₙ⟩°`, whose real value is the unit Gauss
norm `‖∑ a_α T^α‖ = max_α ‖a_α‖`. Its equivalence class is the *unit Gauss point*
`unitGaussPoint n K : closedPolydisc n K`, which is uniquely characterized by the predicate
`IsUnitGaussPoint` comparing series by their unit Gauss norms. At `n = 0` it coincides with the
unique classical point; for `n ≥ 1` it has trivial support and is not classical (the `n = 1`
comparison with `gaussPoint zero_lt_one le_rfl` is in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Comparison`).

## Main definitions

* `TauCeti.ValuationSpectrum.unitGaussPoint`: the unit Gauss point of `closedPolydisc n K` for any
  ultrametric normed field `K`.
* `TauCeti.ValuationSpectrum.IsUnitGaussPoint`: the predicate characterizing the valuation class of
  the unit Gauss point via `MvPowerSeries.gaussNorm`.

## Main results

* `TauCeti.ValuationSpectrum.unitGaussPoint_vle_iff` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_vle_iff_norm`: comparison rules for `unitGaussPoint`
  in terms of `MvPowerSeries.gaussNorm` and the Gauss norm on `restrictedMvPowerSeriesGaussEquiv`.
* `TauCeti.ValuationSpectrum.supp_unitGaussPoint`: the support of `unitGaussPoint n K` is trivial.
* `TauCeti.ValuationSpectrum.isUnitGaussPoint_iff_eq_unitGaussPoint`: `unitGaussPoint n K` is the
  unique point satisfying `IsUnitGaussPoint`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_ne_classicalPoint`: in positive dimension over a
  complete field, `unitGaussPoint n K` is not classical.
* `TauCeti.ValuationSpectrum.unitGaussPoint_zero_eq_classicalPoint`: in dimension `0`,
  `unitGaussPoint 0 K` equals the unique classical point.

## References

* S. Howe and C. Klevdal, *Admissible pairs and p-adic Hodge structures II: the bi-analytic
  Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5, p. 60.
* B. Bhatt and D. Hansen, *The six functors for Zariski-constructible sheaves in rigid geometry*,
  arXiv:2101.09759v2, Example 2.1, p. 6.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

section Definition

/-- A point `η` of the closed unit polydisc of dimension `n` over `K` is the unit Gauss point if it
compares restricted power series as their unit Gauss norms `‖∑ a_α T^α‖ = max ‖a_α‖` do. -/
def IsUnitGaussPoint (K : Type*) [SeminormedCommRing K] [NonarchimedeanRing K] (n : ℕ)
    (η : closedPolydisc n K) : Prop :=
  ∀ f g : weightedRestrictedSubring
      (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
    η.val.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
        (f : MvPowerSeries (Fin n) K) ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
        (g : MvPowerSeries (Fin n) K)

/-- Unfolding rule for `IsUnitGaussPoint`. -/
theorem isUnitGaussPoint_def {K : Type*} [SeminormedCommRing K] [NonarchimedeanRing K] {n : ℕ}
    {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔
      ∀ f g : weightedRestrictedSubring
          (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
        η.val.toValuativeRel.vle f g ↔
          MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
            (f : MvPowerSeries (Fin n) K) ≤
          MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ))
            (g : MvPowerSeries (Fin n) K) :=
  Iff.rfl

end Definition

section UnitGaussPoint

open scoped NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The unit Gauss point of the closed polydisc `closedPolydisc n K`**: the point of
`Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` defined by the unit-radius Gauss valuation
`f ↦ max_ν ‖coeff ν f‖`. -/
noncomputable def unitGaussPoint (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    closedPolydisc n K :=
  ⟨ofValuation (weightedGaussValuation n (Valued.isContinuous_v (R := K))),
    (mem_closedPolydisc_iff n K _).mpr
      ⟨(isContinuous_ofValuation_iff _).mpr (isContinuous_weightedGaussValuation _),
        fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
          rw [map_one]
          exact weightedGaussValuation_le_one_of_mem_powerBoundedSubring n hf⟩⟩

/-- The underlying point of `unitGaussPoint n K` in `Spv K⟨T⟩` is the valuation spectrum point of
the unit-radius Gauss valuation. -/
theorem unitGaussPoint_val (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    (unitGaussPoint n K).val =
      ofValuation (weightedGaussValuation n (Valued.isContinuous_v (R := K))) :=
  (rfl)

/-- The unit Gauss point compares restricted power series by their unit Gauss norms. -/
@[simp]
theorem unitGaussPoint_vle_iff (n : ℕ)
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).val.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) ≤
        MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (g : MvPowerSeries (Fin n) K) := by
  rw [unitGaussPoint_val, vle_ofValuation, ← NNReal.coe_le_coe,
    coe_weightedGaussValuation_normedField, coe_weightedGaussValuation_normedField]

/-- The unit Gauss point compares restricted power series by the Gauss norms of their images under
`restrictedMvPowerSeriesGaussEquiv`. -/
theorem unitGaussPoint_vle_iff_norm (n : ℕ)
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).val.toValuativeRel.vle f g ↔
      ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
  rw [unitGaussPoint_vle_iff, MvPowerSeries.norm_eq_gaussNorm, MvPowerSeries.norm_eq_gaussNorm,
    coe_restrictedMvPowerSeriesGaussEquiv, coe_restrictedMvPowerSeriesGaussEquiv]

/-- The unit Gauss point sends a series to `0` if and only if the series is `0`. -/
theorem unitGaussPoint_vle_zero_iff (n : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).val.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [unitGaussPoint_vle_iff_norm, map_zero, norm_zero, norm_le_zero_iff,
    map_eq_zero_iff _ restrictedMvPowerSeriesGaussEquiv.injective]

/-- The support of the unit Gauss point is trivial. -/
@[simp]
theorem supp_unitGaussPoint (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    (unitGaussPoint n K).val.supp = ⊥ := by
  ext f
  rw [mem_supp_iff, unitGaussPoint_vle_zero_iff, Ideal.mem_bot]

/-- `unitGaussPoint n K` satisfies `IsUnitGaussPoint`. -/
theorem isUnitGaussPoint_unitGaussPoint (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    IsUnitGaussPoint K n (unitGaussPoint n K) :=
  fun f g ↦ unitGaussPoint_vle_iff n f g

/-- **Uniqueness of the unit Gauss point.** A point of `closedPolydisc n K` satisfies
`IsUnitGaussPoint` if and only if it equals `unitGaussPoint n K`. -/
@[simp]
theorem isUnitGaussPoint_iff_eq_unitGaussPoint {n : ℕ} {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔ η = unitGaussPoint n K := by
  refine ⟨fun h ↦ Subtype.ext (ext' fun f g ↦ ?_), fun h ↦ h ▸ isUnitGaussPoint_unitGaussPoint n K⟩
  rw [isUnitGaussPoint_def.mp h f g, unitGaussPoint_vle_iff]

/-- Over a complete ultrametric normed field, the unit Gauss point is not classical in positive
dimension. -/
theorem unitGaussPoint_ne_classicalPoint [CompleteSpace K] {n : ℕ} [NeZero n]
    (x : spa (powerBoundedSubring K)) (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint n K ≠ classicalPoint x a ha :=
  ne_classicalPoint_of_supp_eq_bot _ (supp_unitGaussPoint n K) x a ha

/-- **In dimension `0`, the unit Gauss point equals the unique classical point.** -/
theorem unitGaussPoint_zero_eq_classicalPoint [CompleteSpace K]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K = classicalPoint x Fin.elim0 (fun i ↦ i.elim0) :=
  eq_classicalPoint_zero x (unitGaussPoint 0 K)

end UnitGaussPoint

end TauCeti.ValuationSpectrum

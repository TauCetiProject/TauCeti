/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.FirstVariation.Measure
public import TauCeti.Analysis.Distribution.Mass.Restriction

/-!
# Restriction of the first variation to an open subset

Let `E` be a finite-dimensional real inner product space, `W' ⊆ W` open subsets and `V` a
`k`-varifold on `W`, finite on compact sets. The restriction `V ⌞ W'`
(`Euclidean.restrictOpens V h`) is a varifold on `W'`, and its first variation is the first
variation of `V` on the `C¹` vector fields with compact support in `W'`, extended by zero to `W`
(`Euclidean.firstVariation_restrictOpens`). Hence

* the total first variation of `V ⌞ W'` on `U` is that of `V` on `U ∩ W'`
  (`Euclidean.firstVariationMass_restrictOpens`);
* stationarity and locally bounded first variation pass to `V ⌞ W'`
  (`Euclidean.IsStationary.restrictOpens`,
  `Euclidean.HasLocallyBoundedFirstVariation.restrictOpens`);
* **restriction to open `W'` gives the restriction of `‖δV‖`**: `‖δ(V ⌞ W')‖` is the pullback of
  `‖δV‖` along the inclusion `W' → W` (`Euclidean.firstVariationMeasure_restrictOpens`), so the
  two measures agree on every Borel subset of `W'`
  (`Euclidean.firstVariationMeasure_restrictOpens_apply`).

This is Simon, *Lectures on Geometric Measure Theory*, 39.3, in Euclidean space.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §39.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Distribution TestFunction
open scoped Distributions ENNReal

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ} {W W' : Opens E}
  {V : Measure (W × grassmannian ℝ E k)}

/-- **The first variation of a restriction.** For `W' ⊆ W` and `V` finite on compact sets, the
first variation of `V ⌞ W'` at a `C¹` field `X` with compact support in `W'` is the first variation
of `V` at `X` extended by zero to `W`. -/
@[simp]
theorem firstVariation_restrictOpens [IsFiniteMeasureOnCompacts V] (h : W' ≤ W) :
    firstVariation (restrictOpens V h) =
      (firstVariation V).comp (monoCLM ℝ : 𝓓^{1}(W', E) →L[ℝ] 𝓓^{1}(W, E)) := by
  ext X
  have hX : ⇑(monoCLM ℝ X : 𝓓^{1}(W, E)) = X := coe_monoCLM_of_le le_rfl h X
  rw [ContinuousLinearMap.comp_apply, firstVariation_apply, firstVariation_apply, hX]
  have hS : ∫ p in Prod.fst ⁻¹' (Subtype.val ⁻¹' W'), tangentialDivergence X p.1 p.2 ∂V =
      ∫ p, tangentialDivergence X p.1 p.2 ∂V :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp =>
      tangentialDivergence_eq_zero_of_notMem_tsupport (fun hpX => hp (X.tsupport_subset hpX)) _
  rw [← hS, ← map_restrictOpens h, (measurableEmbedding_inclusion_prodMap h).integral_map]
  simp only [Prod.map_fst, Prod.map_snd, id_eq]

/-- **Total first variation of a restriction.** For every set `U`, the total first variation of
`V ⌞ W'` on `U` is the total first variation of `V` on `U ∩ W'`. -/
@[simp]
theorem firstVariationMass_restrictOpens [IsFiniteMeasureOnCompacts V] (h : W' ≤ W)
    (U : Set E) :
    firstVariationMass (restrictOpens V h) U = firstVariationMass V (U ∩ W') := by
  rw [firstVariationMass_eq_localMass, firstVariationMass_eq_localMass,
    firstVariation_restrictOpens h, ContinuousLinearMap.coe_comp]
  exact localMass_comp_monoCLM _ h U

/-- Stationarity passes to restrictions to open subsets. -/
theorem IsStationary.restrictOpens [IsFiniteMeasureOnCompacts V] (hV : IsStationary V)
    (h : W' ≤ W) : IsStationary (restrictOpens V h) := by
  rw [isStationary_iff] at hV ⊢
  intro X
  rw [firstVariation_restrictOpens h, ContinuousLinearMap.comp_apply]
  exact hV _

/-- Locally bounded first variation passes to restrictions to open subsets. -/
theorem HasLocallyBoundedFirstVariation.restrictOpens [IsFiniteMeasureOnCompacts V]
    (hV : HasLocallyBoundedFirstVariation V) (h : W' ≤ W) :
    HasLocallyBoundedFirstVariation (restrictOpens V h) := by
  rw [hasLocallyBoundedFirstVariation_iff_hasLocallyFiniteMass, firstVariation_restrictOpens h,
    ContinuousLinearMap.coe_comp]
  exact hV.hasLocallyFiniteMass.comp_monoCLM

/-- **Restriction to open `W'` gives the restriction of `‖δV‖`.** If `V` has locally bounded first
variation, the total variation measure of `V ⌞ W'` is the pullback of `‖δV‖` along the inclusion
`W' → W`. -/
theorem firstVariationMeasure_restrictOpens [IsFiniteMeasureOnCompacts V]
    (hV : HasLocallyBoundedFirstVariation V) (h : W' ≤ W) :
    firstVariationMeasure (restrictOpens V h) =
      (firstVariationMeasure V).comap (inclusion h) := by
  -- `Distribution.massMeasure_comp_monoCLM` is stated for linear maps; pass to them.
  rw [firstVariationMeasure_def, firstVariationMeasure_def, firstVariation_restrictOpens h,
    massMeasure_congr (S := (firstVariation V : 𝓓^{1}(W, E) →ₗ[ℝ] ℝ).comp
      (monoCLM (n₁ := 1) ℝ : 𝓓^{1}(W', E) →L[ℝ] 𝓓^{1}(W, E)).toLinearMap)
      (by simp [ContinuousLinearMap.coe_comp]),
    massMeasure_congr (T := firstVariation V) (ContinuousLinearMap.coe_coe _).symm]
  exact massMeasure_comp_monoCLM hV.hasLocallyFiniteMass h

/-- In particular `‖δ(V ⌞ W')‖` and `‖δV‖` agree on every subset of `W'`. -/
theorem firstVariationMeasure_restrictOpens_apply [IsFiniteMeasureOnCompacts V]
    (hV : HasLocallyBoundedFirstVariation V) (h : W' ≤ W) (s : Set W') :
    firstVariationMeasure (restrictOpens V h) s = firstVariationMeasure V (inclusion h '' s) := by
  rw [firstVariationMeasure_restrictOpens hV h,
    (W'.isOpen.measurableSet.measurableEmbedding_inclusion h).comap_apply]

end Euclidean

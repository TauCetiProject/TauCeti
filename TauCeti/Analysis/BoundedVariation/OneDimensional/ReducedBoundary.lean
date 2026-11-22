/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.Analysis.BoundedVariation.OneDimensional.Perimeter
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace

/-!
# The reduced and essential boundaries in dimension at most one

Let `E` be a finite-dimensional real inner product space of dimension at most one carrying an
additive Haar measure `μ`, and let `s` be a set of locally finite perimeter in an open set `Ω ⊆ E`.

* In dimension `0`, `E` is a subsingleton, so both `∂*s` and `∂ᵉs` are empty and `∂*s = Ω ∩ ∂ᵉs`
  holds trivially.
* In dimension `1`, `s` agrees `μ`-almost everywhere locally with a constant (`∅` or `univ`) or a
  single half-line around every point `x ∈ Ω`
  (`TauCeti.exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one`): on a sufficiently
  small ball `ball x r ⊆ Ω`, `s` has perimeter strictly smaller than the Haar scalar factor of `μ`
  in the punctured ball `ball x r \ {x}`, so on each of the two open half-intervals meeting at `x`
  either `s` or its complement is null
  (`TauCeti.Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one`).

In dimension `1`, in the first two local cases `s` has perimeter zero in `ball x r` and density `0`
or `1` at `x`, so `x` belongs neither to `∂*s` nor to `∂ᵉs`. In the third case `|Dχ_s|` charges
`{x}` (hence `x ∈ ∂*s` by `TauCeti.ae_mem_reducedBoundary`) and `s` has density `1 / 2` at `x`
(hence `x ∈ ∂ᵉs`). Thus:

* every point of `∂*s` has density `1 / 2`
  (`TauCeti.hasDensityAt_of_mem_reducedBoundary_of_finrank_eq_one`);
* `∂*s ⊆ ∂ᵉs` without any finite-perimeter hypothesis
  (`TauCeti.reducedBoundary_subset_essentialBoundary_of_finrank_le_one`);
* when `s` has locally finite perimeter in `Ω`, `∂*s = Ω ∩ ∂ᵉs` literally as sets
  (`TauCeti.reducedBoundary_eq_inter_essentialBoundary_of_finrank_le_one`).

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §15.1 and Theorem 16.2.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 and Theorem 3.61.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric Module
open scoped ENNReal NNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E} {x : E}

/-- In dimension one, if a set `s` agrees `μ`-almost everywhere on `ball x r` (`r > 0`) with a
half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}` (`‖ν‖ = 1`), then `s` has perimeter zero in the punctured ball
`ball x r \ {x}` because the boundary hyperplane meets the punctured ball nowhere. -/
private theorem perimeter_sdiff_singleton_eq_zero_of_ae_eq_setOf_inner_lt
    (hn : finrank ℝ E = 1) {r : ℝ} {ν : E} (hν : ‖ν‖ = 1)
    (hsH : s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫}) :
    perimeter μ ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s = 0 := by
  let U : Opens E := ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (hν ▸ one_ne_zero)
  have hsHU : s =ᵐ[μ.restrict U] {y | ⟪y, ν⟫ < ⟪x, ν⟫} :=
    hsH.filter_mono (ae_mono (Measure.restrict_mono sdiff_subset le_rfl))
  have hdisj : (U : Set E) ∩ {y | ⟪y, ν⟫ = ⟪x, ν⟫} = ∅ :=
    eq_empty_of_forall_notMem fun _ ⟨hyU, heq⟩ =>
      hyU.2 (inner_left_injective_of_finrank_eq_one hn hν0 heq)
  rw [perimeter_congr_ae (Ω := U) hsHU]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ volume]
  rw [perimeter_smul_measure, perimeter_setOf_inner_lt hν _ U, hdisj, measure_empty, mul_zero]

/-- In dimension one, if a set `s` of locally finite perimeter in `Ω` agrees `μ`-almost everywhere
on `ball x r ⊆ Ω` (`r > 0`) with a half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}` (`‖ν‖ = 1`), then `|Dχ_s|`
charges `{x}`, so `x ∈ ∂*s` by `TauCeti.ae_mem_reducedBoundary`. -/
private theorem mem_reducedBoundary_of_ae_eq_setOf_inner_lt_of_finrank_eq_one
    (hn : finrank ℝ E = 1) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    {r : ℝ} (hr : 0 < r) (hrΩ : ball x r ⊆ Ω) {ν : E} (hν : ‖ν‖ = 1)
    (hsH : s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫}) :
    x ∈ reducedBoundary μ Ω s := by
  have hx : x ∈ Ω := hrΩ (mem_ball_self hr)
  have hlam0 : variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' (ball x r \ {x})) = 0 :=
    (variationMeasure_preimage_coe hu hfin
      (U := ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩)
      (sdiff_subset.trans hrΩ)).trans
      (perimeter_def.symm.trans (perimeter_sdiff_singleton_eq_zero_of_ae_eq_setOf_inner_lt
        hn hν hsH))
  have hlamB : variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' ball x r) ≠ 0 := by
    have hval : variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' ball x r) =
        perimeter μ ⟨ball x r, isOpen_ball⟩ s := by
      simpa only [Opens.coe_mk, ← perimeter_def] using
        variationMeasure_preimage_coe hu hfin (U := ⟨ball x r, isOpen_ball⟩) hrΩ
    have hper : perimeter μ ⟨ball x r, isOpen_ball⟩ s =
        (Measure.addHaarScalarFactor μ volume : ℝ≥0∞) *
          perimeter volume ⟨ball x r, isOpen_ball⟩ {y | ⟪y, ν⟫ < ⟪x, ν⟫} := by
      rw [perimeter_congr_ae (Ω := ⟨ball x r, isOpen_ball⟩) hsH]
      conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ volume]
      exact perimeter_smul_measure _
    rw [hval, hper, perimeter_ball_setOf_inner_lt hν x hr, hn]
    exact mul_ne_zero (ENNReal.coe_ne_zero.2
        (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne')
      (mul_ne_zero (by simp) (measure_ball_pos volume _ one_pos).ne')
  by_contra hxrb
  have hatom : variationMeasure μ Ω (s.indicator 1) {(⟨x, hx⟩ : Ω)} = 0 :=
    measure_mono_null (singleton_subset_iff.2 hxrb) (ae_iff.1 ae_mem_reducedBoundary)
  have hcov : ((↑) : Ω → E) ⁻¹' ball x r ⊆
      {(⟨x, hx⟩ : Ω)} ∪ ((↑) : Ω → E) ⁻¹' (ball x r \ {x}) :=
    fun y hy => (em ((y : E) = x)).imp (fun heq => Subtype.ext heq) fun hne => ⟨hy, hne⟩
  exact hlamB (measure_mono_null hcov (measure_union_null hatom hlam0))

/-- **Points of the reduced boundary have density one half in dimension one.** Against an additive
Haar measure on a one-dimensional real inner product space, every point of `∂*s` has density
`1 / 2`. -/
theorem hasDensityAt_of_mem_reducedBoundary_of_finrank_eq_one (hn : finrank ℝ E = 1)
    (hx : x ∈ reducedBoundary μ Ω s) : HasDensityAt μ s x (1 / 2) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨r, hr, _, hcases⟩ :=
    exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one hn hu hfin
      (reducedBoundary_subset hx)
  rcases hcases with he | hu' | ⟨ν, hν, hsH⟩
  · exact (perimeter_ball_ne_zero hx hr (by rw [perimeter_congr_ae he, perimeter_empty])).elim
  · exact (perimeter_ball_ne_zero hx hr (by rw [perimeter_congr_ae hu', perimeter_univ])).elim
  · have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (hν ▸ one_ne_zero)
    rw [hasDensityAt_congr_ae_of_mem_nhds (ball_mem_nhds x hr) hsH]
    exact hasDensityAt_setOf_inner_lt hν0 rfl

/-- **The reduced boundary lies in the essential boundary in dimension at most one.** -/
theorem reducedBoundary_subset_essentialBoundary_of_finrank_le_one (hn : finrank ℝ E ≤ 1) :
    reducedBoundary μ Ω s ⊆ essentialBoundary μ s := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with h0 | h1
  · have : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).1 h0
    simp
  · intro x hx
    exact (hasDensityAt_of_mem_reducedBoundary_of_finrank_eq_one h1 hx).mem_essentialBoundary
      (by simp) (by
        intro h
        have h' := congrArg (2 * ·) h
        rw [ENNReal.mul_div_cancel (by simp) (by simp), mul_one] at h'
        norm_num at h')

/-- **Exact agreement of reduced and essential boundaries in dimension at most one.** For a set `s`
of locally finite perimeter in `Ω` and `finrank ℝ E ≤ 1`, `∂*s = Ω ∩ ∂ᵉs` literally as sets. -/
theorem reducedBoundary_eq_inter_essentialBoundary_of_finrank_le_one (hn : finrank ℝ E ≤ 1)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    reducedBoundary μ Ω s = (Ω : Set E) ∩ essentialBoundary μ s := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with h0 | h1
  · have : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).1 h0
    simp
  · refine Subset.antisymm (subset_inter reducedBoundary_subset
      (reducedBoundary_subset_essentialBoundary_of_finrank_le_one hn)) fun x ⟨hxΩ, hxeb⟩ => ?_
    obtain ⟨r, hr, hrΩ, hcases⟩ :=
      exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one h1 hu hfin hxΩ
    rcases hcases with he | hu' | ⟨ν, hν, hsH⟩
    · have hd0 : HasDensityAt μ s x 0 :=
        (hasDensityAt_congr_ae_of_mem_nhds (ball_mem_nhds x hr) he).2 hasDensityAt_empty
      exact ((mem_essentialBoundary.1 hxeb).2 (mem_essentialExterior.2 hd0)).elim
    · have hd1 : HasDensityAt μ s x 1 :=
        (hasDensityAt_congr_ae_of_mem_nhds (ball_mem_nhds x hr) hu').2
          (hasDensityAt_univ (eventually_measure_closedBall_ne_zero_ne_top μ x))
      exact ((mem_essentialBoundary.1 hxeb).1 (mem_essentialInterior.2 hd1)).elim
    · exact mem_reducedBoundary_of_ae_eq_setOf_inner_lt_of_finrank_eq_one h1 hu hfin hr hrΩ
        hν hsH

end TauCeti

end

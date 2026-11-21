/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.Analysis.BoundedVariation.Isometry
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# The reduced and essential boundaries in dimension at most one

Let `E` be a finite-dimensional real inner product space of dimension at most one carrying an
additive Haar measure `μ`, and let `s` be a set of locally finite perimeter in an open set `Ω ⊆ E`.

* In dimension `0`, `E` is a subsingleton, so both `∂*s` and `∂ᵉs` are empty and `∂*s = Ω ∩ ∂ᵉs`
  holds trivially.
* In dimension `1`, `s` agrees `μ`-almost everywhere locally with a constant (`∅` or `univ`) or a
  single half-line around every point `x ∈ Ω`
  (`TauCeti.exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one`): on a sufficiently
  small ball `ball x r ⊆ Ω`, the punctured ball `ball x r \ {x}` has perimeter strictly smaller than
  the Haar scalar factor of `μ`, so on each of the two open half-intervals meeting at `x` either `s`
  or its complement is null
  (`TauCeti.Real.measure_inter_Ioo_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one`).

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

/-- Around any `x ∈ Ω`, a set `s` of locally finite perimeter in `Ω` has volume-perimeter strictly
below `1` on a punctured ball `ball x r \ {x} ⊆ Ω`, by applying `tendsto_measure_ball_nhdsGT_zero`
to `|Dχ_s|` restricted away from `x`. -/
private theorem exists_ball_subset_and_perimeter_sdiff_singleton_lt_one
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hx : x ∈ Ω) :
    ∃ r > 0, ball x r ⊆ Ω ∧
      perimeter volume ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s < 1 := by
  obtain ⟨δ, hδ, hδΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hx)
  set lam := variationMeasure μ Ω (s.indicator 1)
  set a := Measure.addHaarScalarFactor μ volume
  have ha0 : (a : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  have hK : IsCompact (((↑) : Ω → E) ⁻¹' closedBall x δ) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall x δ)
      (by rwa [Subtype.range_coe])
  let x' : Ω := ⟨x, hx⟩
  let lam' := lam.restrict {x'}ᶜ
  have hfinB : ∃ R > 0, lam' (ball x' R) ≠ ⊤ := by
    refine ⟨δ, hδ, ne_top_of_le_ne_top (hK.measure_lt_top (μ := lam)).ne ?_⟩
    exact (Measure.restrict_apply_le _ _).trans
      (measure_mono (preimage_mono ball_subset_closedBall))
  have hlim := tendsto_measure_ball_nhdsGT_zero hfinB
  have hx' : lam' {x'} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton _), inter_compl_self, measure_empty]
  rw [hx'] at hlim
  obtain ⟨r, hlt, hr, hrδ⟩ := ((hlim.eventually (gt_mem_nhds ha0.bot_lt)).and
    (Ioo_mem_nhdsGT hδ)).exists
  have hrΩ : ball x r ⊆ Ω := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall hrδ.le)).trans hδΩ
  have hlam : lam' (ball x' r) = lam (((↑) : Ω → E) ⁻¹' (ball x r \ {x})) := by
    rw [Measure.restrict_apply measurableSet_ball]
    congr 1
    ext y
    simp [x', Subtype.dist_eq, Subtype.ext_iff, sdiff_eq_compl_inter, inter_comm]
  have hP : lam (((↑) : Ω → E) ⁻¹' (ball x r \ {x})) = (a : ℝ≥0∞) *
      perimeter volume ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s :=
    (variationMeasure_preimage_coe hu hfin
      (U := ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩)
      (sdiff_subset.trans hrΩ)).trans <| by
      rw [← perimeter_def, Measure.isAddLeftInvariant_eq_smul μ volume,
        perimeter_smul_measure]
  refine ⟨r, hr, hrΩ, ?_⟩
  rw [← ENNReal.mul_lt_mul_iff_left ha0 ENNReal.coe_ne_top, one_mul, mul_comm, ← hP, ← hlam]
  exact hlt

/-- Along a linear isometry `e : E ≃ₗᵢ[ℝ] ℝ`, if `s` is null-measurable on `ball x r` (`r > 0`)
and has volume-perimeter strictly below `1` on `ball x r \ {x}`, then on the open half-ball
`ball x r ∩ {y | e y < e x}` either `s` or its complement is `μ`-null. -/
private theorem measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero (e : E ≃ₗᵢ[ℝ] ℝ) {r : ℝ}
    (hr : 0 < r) (hs : NullMeasurableSet s (μ.restrict (ball x r)))
    (hP : perimeter volume ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s < 1) :
    μ (s ∩ (ball x r ∩ {y | e y < e x})) = 0 ∨ μ ((ball x r ∩ {y | e y < e x}) \ s) = 0 := by
  set I := Ioo (e x - r) (e x)
  have hI : ball (e x) r ∩ Iio (e x) = I := by
    rw [Real.ball_eq_Ioo, Set.Ioo_inter_Iio, min_eq_right (le_add_of_nonneg_right hr.le)]
  have hpre : e ⁻¹' I = ball x r ∩ {y | e y < e x} := by
    rw [← hI, preimage_inter, e.preimage_ball, e.symm_apply_apply]
    rfl
  have hmaps : MapsTo e.symm (⟨I, isOpen_Ioo⟩ : Opens ℝ)
      (⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ : Opens E) := fun t ht => by
    have hmem : e.symm t ∈ ball x r ∩ {y | e y < e x} := by
      rw [← hpre]; simpa using ht
    exact ⟨hmem.1, fun h => (ne_of_lt hmem.2) (congrArg e h)⟩
  have hsB : NullMeasurableSet (s ∩ ball x r) volume := by
    have hsm : NullMeasurableSet (s ∩ ball x r) μ :=
      (nullMeasurableSet_restrict measurableSet_ball.nullMeasurableSet).1 hs
    rw [Measure.isAddLeftInvariant_eq_smul μ volume] at hsm
    exact hsm.mono_ac (Measure.absolutelyContinuous_smul
      (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'))
  have hsI : NullMeasurableSet (e.symm ⁻¹' s) (volume.restrict I) := by
    have h1 := (hsB.preimage e.symm.measurePreserving.quasiMeasurePreserving).mono
      (Measure.restrict_le_self : volume.restrict I ≤ volume)
    refine h1.congr (eventuallyEqSet_iff.2 ?_)
    exact (ae_restrict_mem measurableSet_Ioo).mono fun t ht => and_iff_left (hmaps ht).1
  have hPI : perimeter volume ⟨I, isOpen_Ioo⟩ (e.symm ⁻¹' s) < 1 :=
    (e.symm.perimeter_preimage_le e.symm.measurePreserving hmaps).trans_lt hP
  have hvol (A : Set ℝ) : volume (e ⁻¹' A) = volume A :=
    e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding A
  rcases Real.measure_inter_Ioo_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one hsI hPI with h0 | h0
  · refine Or.inl ?_
    have heq : s ∩ (ball x r ∩ {y | e y < e x}) = e ⁻¹' (e.symm ⁻¹' s ∩ I) := by
      rw [preimage_inter, ← hpre]; ext y; simp
    rw [Measure.isAddLeftInvariant_eq_smul μ volume, _root_.smul_apply, heq, hvol, h0, smul_zero]
  · refine Or.inr ?_
    have heq : (ball x r ∩ {y | e y < e x}) \ s = e ⁻¹' (I \ e.symm ⁻¹' s) := by
      rw [preimage_sdiff, ← hpre]; ext y; simp
    rw [Measure.isAddLeftInvariant_eq_smul μ volume, _root_.smul_apply, heq, hvol, h0, smul_zero]

/-- Combining constancy on the two half-balls around `x` along `e : E ≃ₗᵢ[ℝ] ℝ` yields `∅`, `univ`,
or a half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}` almost everywhere on `ball x r`. -/
private theorem ae_eq_empty_or_univ_or_setOf_inner_lt_of_halves (e : E ≃ₗᵢ[ℝ] ℝ) {r : ℝ}
    (hL : μ (s ∩ (ball x r ∩ {y | e y < e x})) = 0 ∨ μ ((ball x r ∩ {y | e y < e x}) \ s) = 0)
    (hR : μ (s ∩ (ball x r ∩ {y | e x < e y})) = 0 ∨ μ ((ball x r ∩ {y | e x < e y}) \ s) = 0) :
    s =ᵐ[μ.restrict (ball x r)] (∅ : Set E) ∨ s =ᵐ[μ.restrict (ball x r)] univ ∨
      ∃ ν : E, ‖ν‖ = 1 ∧ s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫} := by
  have : Nontrivial E := ⟨⟨e.symm 1, 0, norm_ne_zero_iff.1 (by simp)⟩⟩
  have hnull (f : E ≃ₗᵢ[ℝ] ℝ) {A : Set E}
      (h₁ : μ (A ∩ (ball x r ∩ {y | f y < f x})) = 0)
      (h₂ : μ (A ∩ (ball x r ∩ {y | f x < f y})) = 0) :
      μ.restrict (ball x r) A = 0 := by
    rw [Measure.restrict_apply' measurableSet_ball]
    have hsub : A ∩ ball x r ⊆
        A ∩ (ball x r ∩ {y | f y < f x}) ∪ A ∩ (ball x r ∩ {y | f x < f y}) ∪ {x} :=
      fun y ⟨hyA, hyB⟩ => (lt_trichotomy (f y) (f x)).elim (fun h => .inl (.inl ⟨hyA, hyB, h⟩))
        fun h => h.elim (fun heq => .inr (f.injective heq)) fun hgt => .inl (.inr ⟨hyA, hyB, hgt⟩)
    exact measure_mono_null hsub (measure_union_null (measure_union_null h₁ h₂)
      (measure_singleton x))
  have hstep (f : E ≃ₗᵢ[ℝ] ℝ)
      (hlt : μ ((ball x r ∩ {y | f y < f x}) \ s) = 0)
      (hgt : μ (s ∩ (ball x r ∩ {y | f x < f y})) = 0) :
      ∃ ν : E, ‖ν‖ = 1 ∧ s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫} := by
    have hinner (y : E) : ⟪y, f.symm 1⟫ = f y := by simp [← f.inner_map_map]
    refine ⟨f.symm 1, by simp, ae_eq_set.2 ⟨?_, ?_⟩⟩
    · refine hnull f ?_ ?_
      · refine measure_mono_null ?_ measure_empty
        exact fun _ ⟨⟨_, hy⟩, _, h⟩ => hy (by simpa [hinner] using h)
      · refine measure_mono_null ?_ hgt
        exact fun _ ⟨hy, hyB⟩ => ⟨hy.1, hyB⟩
    · refine hnull f ?_ ?_
      · refine measure_mono_null ?_ hlt
        exact fun _ ⟨hy, hyB⟩ => ⟨hyB, hy.2⟩
      · refine measure_mono_null ?_ measure_empty
        exact fun _ ⟨⟨hy, _⟩, _, h⟩ => lt_asymm (by simpa [hinner] using hy) h
  rcases hL with hL0 | hL1 <;> rcases hR with hR0 | hR1
  · exact .inl (ae_eq_empty.2 (hnull e hL0 hR0))
  · refine .inr (.inr (hstep (e.trans (LinearIsometryEquiv.neg ℝ)) ?_ ?_))
    · simpa [neg_lt_neg_iff] using hR1
    · simpa [neg_lt_neg_iff] using hL0
  · exact .inr (.inr (hstep e hL1 hR0))
  · exact .inr (.inl (ae_eq_univ.2 (hnull e
      (by simpa [sdiff_eq_compl_inter, inter_comm] using hL1)
      (by simpa [sdiff_eq_compl_inter, inter_comm] using hR1))))

/-- **Local classification in dimension one.** Around every `x ∈ Ω`, a set `s` of locally finite
perimeter in `Ω` agrees `μ`-almost everywhere on some `ball x r ⊆ Ω` (`r > 0`) with `∅`, `univ`, or
a half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}` (`‖ν‖ = 1`). -/
theorem exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one
    (hn : finrank ℝ E = 1) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hx : x ∈ Ω) :
    ∃ r > 0, ball x r ⊆ Ω ∧
      (s =ᵐ[μ.restrict (ball x r)] (∅ : Set E) ∨ s =ᵐ[μ.restrict (ball x r)] univ ∨
        ∃ ν : E, ‖ν‖ = 1 ∧ s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫}) := by
  obtain ⟨r, hr, hrΩ, hP⟩ := exists_ball_subset_and_perimeter_sdiff_singleton_lt_one hu hfin hx
  let e : E ≃ₗᵢ[ℝ] ℝ :=
    (stdOrthonormalBasis ℝ E).equiv (stdOrthonormalBasis ℝ ℝ)
      (finCongr (hn.trans (Module.finrank_self ℝ).symm))
  have hs : NullMeasurableSet s (μ.restrict (ball x r)) :=
    ((aemeasurable_indicator_const_iff (1 : ℝ)).1
      hu.aestronglyMeasurable.aemeasurable).mono (Measure.restrict_mono hrΩ le_rfl)
  have hL := measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero e hr hs hP
  have hR := measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero
    (e.trans (LinearIsometryEquiv.neg ℝ)) hr hs hP
  have hR' : μ (s ∩ (ball x r ∩ {y | e x < e y})) = 0 ∨
      μ ((ball x r ∩ {y | e x < e y}) \ s) = 0 := by
    simpa only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_neg, neg_lt_neg_iff]
      using hR
  exact ⟨r, hr, hrΩ, ae_eq_empty_or_univ_or_setOf_inner_lt_of_halves e hL hR'⟩

/-- In dimension one, if a set `s` of locally finite perimeter in `Ω` agrees `μ`-almost everywhere
on `ball x r ⊆ Ω` (`r > 0`) with a half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}` (`‖ν‖ = 1`), then `|Dχ_s|`
charges `{x}`, so `x ∈ ∂*s` by `TauCeti.ae_mem_reducedBoundary`. -/
private theorem mem_reducedBoundary_of_ae_eq_setOf_inner_lt_of_finrank_eq_one
    (hn : finrank ℝ E = 1) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r) (hrΩ : ball x r ⊆ Ω) {ν : E} (hν : ‖ν‖ = 1)
    (hsH : s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫}) :
    x ∈ reducedBoundary μ Ω s := by
  set H : Set E := {y | ⟪y, ν⟫ < ⟪x, ν⟫}
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (hν ▸ one_ne_zero)
  let U₁ : Opens E := ⟨ball x r ∩ H, isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const)⟩
  let U₂ : Opens E := ⟨ball x r ∩ {y | ⟪x, ν⟫ < ⟪y, ν⟫},
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))⟩
  let U : Opens E := ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩
  have hUeq : U = U₁ ⊔ U₂ :=
    Opens.ext (sdiff_singleton_eq_union_setOf_inner_lt_of_finrank_eq_one hn hν0 (ball x r) x)
  have hsH' {A : Set E} : s =ᵐ[μ.restrict (ball x r ∩ A)] H :=
    hsH.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
  have hPU₁ : perimeter μ U₁ s = 0 := by
    rw [perimeter_congr_ae (Ω := U₁) hsH',
      perimeter_congr_of_inter_eq (Ω := U₁) (t := univ) (by ext y; simp [U₁, H]),
      perimeter_univ]
  have hPU₂ : perimeter μ U₂ s = 0 := by
    rw [perimeter_congr_ae (Ω := U₂) hsH',
      perimeter_congr_of_inter_eq (Ω := U₂) (t := ∅) (ext fun y =>
        ⟨fun ⟨h1, _, h2⟩ => (lt_asymm (a := ⟪y, ν⟫) h1 h2).elim, fun ⟨h, _⟩ => h.elim⟩),
      perimeter_empty]
  have hPU : perimeter μ U s = 0 := by
    rw [← nonpos_iff_eq_zero, hUeq, perimeter_def]
    refine (totalVariationOn_sup_le (hu.mono_set
      (union_subset (inter_subset_left.trans hrΩ) (inter_subset_left.trans hrΩ)))).trans ?_
    simp [← perimeter_def, hPU₁, hPU₂]
  have hlam0 : variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' (ball x r \ {x})) = 0 :=
    (variationMeasure_preimage_coe hu hfin (U := U) (sdiff_subset.trans hrΩ)).trans
      (perimeter_def.symm.trans hPU)
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
    have hd := hasDensityAt_of_mem_reducedBoundary_of_finrank_eq_one h1 hx
    rw [mem_essentialBoundary, mem_essentialInterior, mem_essentialExterior]
    refine ⟨fun h1' => ?_, fun h0' => ?_⟩
    · have h : (2 : ℝ≥0∞) * (1 / 2) = 2 * 1 := congrArg (2 * ·) (hd.unique h1')
      rw [ENNReal.mul_div_cancel (by simp) (by simp), mul_one] at h
      norm_num at h
    · have h := hd.unique h0'
      simp at h

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
    · exact mem_reducedBoundary_of_ae_eq_setOf_inner_lt_of_finrank_eq_one h1 hu hfin hxΩ hr hrΩ
        hν hsH

end TauCeti

end

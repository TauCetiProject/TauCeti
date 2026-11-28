/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.BoundedVariation.Isometry
import TauCeti.Analysis.BoundedVariation.OneDimensional.Perimeter
import TauCeti.Analysis.BoundedVariation.VariationMeasure
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Dimension

/-!
# Local classification of finite-perimeter sets in dimension one

Let `E` be a one-dimensional real inner product space carrying an additive Haar measure `μ`, and let
`s ⊆ E` be a set of locally finite perimeter in an open set `Ω ⊆ E`. Around every `x ∈ Ω`, the
perimeter of `s` in a sufficiently small punctured ball `ball x r \ {x} ⊆ Ω` is strictly below the
Haar scalar factor of `μ` with respect to Lebesgue measure (`volume`). Pulling back to `ℝ` along a
linear isometry `E ≃ₗᵢ[ℝ] ℝ` and applying
`TauCeti.Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one` on each of the two open
half-balls meeting at `x` shows that on `ball x r` the set `s` agrees `μ`-almost everywhere with
`∅`, `univ`, or a single half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}`
(`TauCeti.exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one`).

On a full open ball `ball x r`, if `s` has perimeter strictly below the Haar scalar factor of `μ`,
the same pullback yields `s =ᵐ[μ.restrict (ball x r)] ∅` or `univ`
(`TauCeti.ae_eq_empty_or_univ_of_perimeter_ball_lt`).

## Main results

* `TauCeti.ae_eq_empty_or_univ_of_perimeter_ball_lt`: a set of sub-unit normalized perimeter on a
  ball in dimension one is null or conull on that ball.
* `TauCeti.exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one`: local classification
  of sets of locally finite perimeter in dimension one.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.10.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §15.1.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2.
-/

public section

namespace TauCeti

open Filter Set MeasureTheory Metric TopologicalSpace Module
open scoped Topology ENNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E} {x : E}

/-- Rescaling perimeter by `addHaarScalarFactor μ volume` turns
`perimeter μ U s < addHaarScalarFactor μ volume` into `perimeter volume U s < 1`. -/
private theorem perimeter_lt_addHaarScalarFactor_iff {U : Opens E} :
    perimeter μ U s < Measure.addHaarScalarFactor μ volume ↔ perimeter volume U s < 1 := by
  have ha0 : (Measure.addHaarScalarFactor μ volume : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  rw [perimeter_eq_addHaarScalarFactor_mul volume]
  simpa only [mul_one] using
    ENNReal.mul_lt_mul_iff_right ha0 ENNReal.coe_ne_top (b := perimeter volume U s) (c := 1)

/-- Around any `x ∈ Ω`, a set `s` of locally finite perimeter in `Ω` has volume-perimeter strictly
below `1` on a punctured ball `ball x r \ {x} ⊆ Ω`, by applying
`TauCeti.tendsto_totalVariationOn_ball_sdiff_singleton` to `|Dχ_s|`. -/
private theorem exists_ball_subset_and_perimeter_sdiff_singleton_lt_one
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hx : x ∈ Ω) :
    ∃ r > 0, ball x r ⊆ Ω ∧
      perimeter volume ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s < 1 := by
  obtain ⟨δ, hδ, hδΩ⟩ := nhds_basis_ball.mem_iff.1 (Ω.isOpen.mem_nhds hx)
  have ha0 : (0 : ℝ≥0∞) < Measure.addHaarScalarFactor μ volume :=
    ENNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume)
  have hlim := tendsto_totalVariationOn_ball_sdiff_singleton hu hfin hx
  obtain ⟨r, hlt, hr, hrδ⟩ := ((hlim.eventually (gt_mem_nhds ha0)).and
    (Ioo_mem_nhdsGT hδ)).exists
  exact ⟨r, hr, (ball_subset_ball hrδ.le).trans hδΩ,
    perimeter_lt_addHaarScalarFactor_iff.1 (by rwa [perimeter_def])⟩

/-- Transporting `TauCeti.Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one` along a
linear isometry `e : E ≃ₗᵢ[ℝ] ℝ`: if `e⁻¹(I) ⊆ U` for an open interval `I ⊆ ℝ` and `s` has
volume-perimeter strictly below `1` in `U`, then `s` or its complement is `μ`-null on `e⁻¹(I)`. -/
private theorem measure_inter_preimage_eq_zero_or_sdiff_eq_zero (e : E ≃ₗᵢ[ℝ] ℝ)
    {I : Opens ℝ} (hI : (I : Set ℝ).OrdConnected) {U : Opens E}
    (hmaps : MapsTo e.symm I U) (hs : NullMeasurableSet s (μ.restrict U))
    (hP : perimeter volume U s < 1) :
    μ (s ∩ e ⁻¹' I) = 0 ∨ μ (e ⁻¹' I \ s) = 0 := by
  have hsU : NullMeasurableSet (s ∩ U) volume :=
    ((nullMeasurableSet_restrict U.isOpen.measurableSet.nullMeasurableSet).1 hs).mono_ac
      (Measure.absolutelyContinuous_isAddHaarMeasure volume μ)
  have hsI : NullMeasurableSet (e.symm ⁻¹' s) (volume.restrict I) := by
    have h1 := (hsU.preimage e.symm.measurePreserving.quasiMeasurePreserving).mono
      (Measure.restrict_le_self : volume.restrict I ≤ volume)
    refine h1.congr (eventuallyEqSet_iff.2 ?_)
    exact (ae_restrict_mem I.isOpen.measurableSet).mono fun t ht => and_iff_left (hmaps ht)
  have hPI : perimeter volume I (e.symm ⁻¹' s) < 1 :=
    (e.symm.perimeter_preimage_le e.symm.measurePreserving e.symm.symm.continuous.measurable
      hmaps).trans_lt hP
  have hvol (A : Set ℝ) : volume (e ⁻¹' A) = volume A :=
    e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding A
  have hsymm : e ⁻¹' (e.symm ⁻¹' s) = s := e.toEquiv.preimage_symm_preimage s
  rcases Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one hI hsI hPI with h0 | h0
  · refine Or.inl (Measure.absolutelyContinuous_isAddHaarMeasure μ volume ?_)
    have heq : s ∩ e ⁻¹' I = e ⁻¹' (e.symm ⁻¹' s ∩ I) := by rw [preimage_inter, hsymm]
    rw [heq, hvol, h0]
  · refine Or.inr (Measure.absolutelyContinuous_isAddHaarMeasure μ volume ?_)
    have heq : e ⁻¹' I \ s = e ⁻¹' (I \ e.symm ⁻¹' s) := by rw [preimage_sdiff, hsymm]
    rw [heq, hvol, h0]

/-- Along a linear isometry `e : E ≃ₗᵢ[ℝ] ℝ`, if `s` is null-measurable on `ball x r` and has
volume-perimeter strictly below `1` on `ball x r \ {x}`, then on the open half-ball
`ball x r ∩ {y | e y < e x}` either `s` or its complement is `μ`-null. -/
private theorem measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero (e : E ≃ₗᵢ[ℝ] ℝ) {r : ℝ}
    (hs : NullMeasurableSet s (μ.restrict (ball x r)))
    (hP : perimeter volume ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s < 1) :
    μ (s ∩ (ball x r ∩ {y | e y < e x})) = 0 ∨ μ ((ball x r ∩ {y | e y < e x}) \ s) = 0 := by
  set I : Opens ℝ := ⟨Ioo (e x - r) (e x), isOpen_Ioo⟩
  have hpre : e ⁻¹' I = ball x r ∩ {y | e y < e x} := by
    ext y
    simp only [I, mem_preimage, Opens.coe_mk, mem_Ioo, mem_inter_iff, mem_ball,
      ← e.isometry.dist_eq y x, Real.dist_eq, abs_sub_lt_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, by linarith⟩, h2⟩
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨by linarith, h3⟩
  have hmaps : MapsTo e.symm I
      (⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ : Opens E) := fun t ht => by
    have hmem : e.symm t ∈ ball x r ∩ {y | e y < e x} := by
      rw [← hpre]; simpa using ht
    exact ⟨hmem.1, fun h => (ne_of_lt hmem.2) (congrArg e h)⟩
  have hs' : NullMeasurableSet s
      (μ.restrict (⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ : Opens E)) :=
    hs.mono (Measure.restrict_mono sdiff_subset le_rfl)
  simpa only [hpre] using
    measure_inter_preimage_eq_zero_or_sdiff_eq_zero e ordConnected_Ioo hmaps hs' hP

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma setOf_trans_neg_lt (e : E ≃ₗᵢ[ℝ] ℝ) (x : E) :
    {y | (e.trans (LinearIsometryEquiv.neg ℝ)) y <
        (e.trans (LinearIsometryEquiv.neg ℝ)) x} = {y | e x < e y} := by
  ext y; simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma setOf_lt_trans_neg (e : E ≃ₗᵢ[ℝ] ℝ) (x : E) :
    {y | (e.trans (LinearIsometryEquiv.neg ℝ)) x <
        (e.trans (LinearIsometryEquiv.neg ℝ)) y} = {y | e y < e x} := by
  ext y; simp

/-- Along a linear isometry `e : E ≃ₗᵢ[ℝ] ℝ`, if `s` is null-measurable on `ball x r` and has
volume-perimeter strictly below `1` on `ball x r \ {x}`, then on the open half-ball
`ball x r ∩ {y | e x < e y}` either `s` or its complement is `μ`-null. -/
private theorem measure_inter_ball_inter_gt_eq_zero_or_sdiff_eq_zero (e : E ≃ₗᵢ[ℝ] ℝ) {r : ℝ}
    (hs : NullMeasurableSet s (μ.restrict (ball x r)))
    (hP : perimeter volume ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s < 1) :
    μ (s ∩ (ball x r ∩ {y | e x < e y})) = 0 ∨ μ ((ball x r ∩ {y | e x < e y}) \ s) = 0 := by
  have h := measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero
    (e.trans (LinearIsometryEquiv.neg ℝ)) hs hP
  rwa [setOf_trans_neg_lt] at h

/-- Combining constancy on the two open half-balls around `x` along `e : E ≃ₗᵢ[ℝ] ℝ` yields `∅`,
`univ`, or a half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}` almost everywhere on `ball x r`. -/
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
    · rwa [setOf_trans_neg_lt]
    · rwa [setOf_lt_trans_neg]
  · exact .inr (.inr (hstep e hL1 hR0))
  · exact .inr (.inl (ae_eq_univ.2 (hnull e
      (by simpa [sdiff_eq_compl_inter, inter_comm] using hL1)
      (by simpa [sdiff_eq_compl_inter, inter_comm] using hR1))))

/-- **Local constancy below unit normalized perimeter on a ball in dimension one.** Against an
additive Haar measure `μ` on a one-dimensional real inner product space, if `s` is null-measurable
on `ball x r` and `perimeter μ ⟨ball x r, isOpen_ball⟩ s < addHaarScalarFactor μ volume`,
then `s` agrees `μ`-almost everywhere on `ball x r` with `∅` or `univ`. -/
theorem ae_eq_empty_or_univ_of_perimeter_ball_lt (hn : finrank ℝ E = 1) {r : ℝ}
    (hs : NullMeasurableSet s (μ.restrict (ball x r)))
    (hP : perimeter μ ⟨ball x r, isOpen_ball⟩ s < Measure.addHaarScalarFactor μ volume) :
    s =ᵐ[μ.restrict (ball x r)] (∅ : Set E) ∨ s =ᵐ[μ.restrict (ball x r)] univ := by
  have hPvol : perimeter volume ⟨ball x r, isOpen_ball⟩ s < 1 :=
    perimeter_lt_addHaarScalarFactor_iff.1 hP
  obtain ⟨e⟩ := (nonempty_linearIsometryEquiv_iff_finrank_eq (𝕜 := ℝ) (E := E) (F := ℝ)).2
    (hn.trans (Module.finrank_self ℝ).symm)
  set I : Opens ℝ := ⟨Ioo (e x - r) (e x + r), isOpen_Ioo⟩
  have hpre : e ⁻¹' I = ball x r := by
    rw [Opens.coe_mk, ← Real.ball_eq_Ioo, e.preimage_ball, e.symm_apply_apply]
  have hmaps : MapsTo e.symm I (⟨ball x r, isOpen_ball⟩ : Opens E) := fun t ht => by
    simp only [Opens.coe_mk]
    rw [← hpre]
    simpa using ht
  rcases measure_inter_preimage_eq_zero_or_sdiff_eq_zero e ordConnected_Ioo hmaps hs hPvol with
      h0 | h0 <;>
    rw [hpre] at h0
  · refine Or.inl (ae_eq_empty.2 ?_)
    rwa [Measure.restrict_apply' measurableSet_ball]
  · refine Or.inr (ae_eq_univ.2 ?_)
    rwa [Measure.restrict_apply' measurableSet_ball, ← sdiff_eq_compl_inter]

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
  obtain ⟨e⟩ := (nonempty_linearIsometryEquiv_iff_finrank_eq (𝕜 := ℝ) (E := E) (F := ℝ)).2
    (hn.trans (Module.finrank_self ℝ).symm)
  have hs : NullMeasurableSet s (μ.restrict (ball x r)) :=
    ((aemeasurable_indicator_const_iff (1 : ℝ)).1
      hu.aestronglyMeasurable.aemeasurable).mono (Measure.restrict_mono hrΩ le_rfl)
  have hL := measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero e hs hP
  have hR := measure_inter_ball_inter_gt_eq_zero_or_sdiff_eq_zero e hs hP
  exact ⟨r, hr, hrΩ, ae_eq_empty_or_univ_or_setOf_inner_lt_of_halves e hL hR⟩

end TauCeti

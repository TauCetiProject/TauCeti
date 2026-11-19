/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.FlatTrace
public import TauCeti.Analysis.Sobolev.W1p.Translation
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension

/-!
# Locality of the flat trace of the half-disc

The trace `TauCeti.W1p.halfDiscFlatTrace hp r` on the flat segment of the half-disc
`TauCeti.halfDisc r` is defined for one radius and the centre `0`. This file relates the traces
of different half-discs. In the complex coordinate `z = s + it` of
`TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic`, the first coordinate is `t = Im z`
and the shift `(0, c)` moves the centre along the real axis to `c`.

If `|c| + ρ ≤ r`, translation by `(0, c)` maps the half-disc of radius `ρ` into the half-disc of
radius `r`, and its flat segment `[-ρ, ρ]` onto the subsegment `[c - ρ, c + ρ]` of `[-r, r]`.
The flat trace of the translated function `x ↦ u (x + (0, c))` is then the translate of the
flat trace of `u` (`TauCeti.W1p.halfDiscFlatTrace_translate_ae`). In particular the zero-trace
condition passes to every smaller and shifted half-disc, and it is local: a function has zero
trace on the flat segment as soon as every point of the open segment `(-r, r)` is the centre of
such a sub-half-disc on which the translated function has zero trace
(`TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_forall_translate`). Totally real boundary
conditions on a relatively open subset of the closed upper half-plane can therefore be read off
on small half-discs around each real point.

## Main declarations

* `TauCeti.W1p.halfDiscFlatTrace_translate_ae`: the flat trace commutes with these translations;
  `TauCeti.W1p.halfDiscFlatTrace_restrictL_ae` is the centred case `c = 0`.
* `TauCeti.W1p.translate_mem_halfDiscFlatTraceZeroSubmodule_iff`: the translated function has
  zero trace exactly when the trace of `u` vanishes on the shifted subsegment.
* `TauCeti.W1p.translate_mem_halfDiscFlatTraceZeroSubmodule`,
  `TauCeti.W1p.restrictL_mem_halfDiscFlatTraceZeroSubmodule`: zero trace passes to smaller and
  shifted half-discs.
* `TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_of_forall_translate`,
  `TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_forall_translate`: the local-to-global
  converse.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B.4
  (boundary conditions on the half-disc).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {r ρ c : ℝ}

/-! ### Translating half-discs along the flat segment -/

/-- Under `|c| + ρ ≤ r`, translation by `(0, c)` carries surface measure on the flat segment of
radius `ρ` to surface measure on its image in the flat segment of radius `r`, for the measures of
the codomains of `TauCeti.W1p.halfDiscFlatTrace`. -/
private theorem measurePreserving_add_halfDiscFlatSegment (hc : |c| + ρ ≤ r) :
    MeasurePreserving (· + WithLp.toLp 2 ((0 : ℝ), c))
      (((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc ρ : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment ρ))
      ((((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment r)).restrict
          ((· + WithLp.toLp 2 ((0 : ℝ), c)) '' halfDiscFlatSegment ρ)) := by
  refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
  have hS : MeasurableSet ((· + WithLp.toLp 2 ((0 : ℝ), c)) '' halfDiscFlatSegment ρ) :=
    ((Homeomorph.addRight _).isClosedMap _ (isClosed_halfDiscFlatSegment ρ)).measurableSet
  rw [restrict_frontier_restrict_halfDiscFlatSegment,
    restrict_frontier_restrict_halfDiscFlatSegment, Measure.restrict_restrict hS,
    inter_eq_left.2 (image_subset_iff.2 (mapsTo_add_halfDiscFlatSegment hc)),
    (isometry_add_right (WithLp.toLp 2 ((0 : ℝ), c))).map_euclideanHausdorffMeasure_restrict]

/-- Under `|c| + ρ ≤ r`, sets of zero surface measure on the flat segment of radius `r` pull back
to sets of zero surface measure on the flat segment of radius `ρ` under translation by
`(0, c)`. -/
private theorem quasiMeasurePreserving_add_halfDiscFlatSegment (hc : |c| + ρ ≤ r) :
    QuasiMeasurePreserving (· + WithLp.toLp 2 ((0 : ℝ), c))
      ((μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment ρ))
      ((μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r)) := by
  have h := (measurePreserving_add_halfDiscFlatSegment hc).quasiMeasurePreserving
  rw [restrict_frontier_restrict_halfDiscFlatSegment,
    restrict_frontier_restrict_halfDiscFlatSegment] at h
  exact h.mono_right Measure.restrict_le_self.absolutelyContinuous

/-! ### The flat trace of a translate -/

section Trace

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The flat trace commutes with translation along the flat segment.** If `|c| + ρ ≤ r`, the
flat trace of the translate `x ↦ u (x + (0, c))` on `halfDisc ρ` is, almost everywhere on the flat
segment of radius `ρ`, the translate of the flat trace of `u` on `halfDisc r`. -/
theorem W1p.halfDiscFlatTrace_translate_ae (hp : p ≠ (∞ : ℝ≥0∞)) (hc : |c| + ρ ≤ r)
    (u : W1p volume (halfDisc r) p) :
    W1p.halfDiscFlatTrace hp ρ (W1p.translate (mapsTo_add_halfDisc hc) u) =ᵐ[
      (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment ρ)]
      fun w => W1p.halfDiscFlatTrace hp r u (w + WithLp.toLp 2 ((0 : ℝ), c)) := by
  -- Both sides are bounded linear in `u` and agree on restrictions of test functions,
  -- which are dense in `W^{1,p}(halfDisc r)`.
  set h : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 ((0 : ℝ), c)
  set S := (· + h) '' halfDiscFlatSegment ρ
  have hτ := measurePreserving_add_halfDiscFlatSegment hc
  -- The right-hand side as a bounded linear operator in `u`.
  let B : W1p volume (halfDisc r) p →L[ℝ] Lp ℝ p
      (((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc ρ : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment ρ)) :=
    (Lp.compMeasurePreservingₗᵢ ℝ (· + h) hτ).toContinuousLinearMap.comp
      ((LpToLpRestrictCLM (WithLp 2 (ℝ × ℝ)) ℝ ℝ _ p S).comp (W1p.halfDiscFlatTrace hp r))
  have hB (v : W1p volume (halfDisc r) p) :
      B v =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment ρ)]
        fun w => W1p.halfDiscFlatTrace hp r v (w + h) := by
    rw [← congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment ρ)]
    exact (Lp.coeFn_compMeasurePreserving _ hτ).trans
      (hτ.quasiMeasurePreserving.ae_eq_comp (LpToLpRestrictCLM_coeFn ℝ S _))
  obtain ⟨L, hΩ⟩ := exists_isLipschitzDomainWith_halfDisc r
  have hAB : (W1p.halfDiscFlatTrace hp ρ).comp (W1p.translateL (mapsTo_add_halfDisc hc)) = B := by
    refine DFunLike.coe_injective <|
      (W1p.denseRange_restrictL_ofTestFunctionₗ_top hp hΩ (isBounded_halfDisc r)).equalizer
        (ContinuousLinearMap.continuous _) B.continuous (funext fun φ => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, W1p.translateL_apply]
    refine Lp.ext ?_
    have hv := W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := p)
      (le_top : halfDisc r ≤ ⊤) φ
    -- The value of the translate is the translated test function.
    have htr : W1p.value (W1p.translate (mapsTo_add_halfDisc hc)
          (W1p.restrictL (le_top : halfDisc r ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ)))
        =ᵐ[volume.restrict (halfDisc ρ : Set (WithLp 2 (ℝ × ℝ)))] fun x => φ (x + h) := by
      refine (W1p.value_translate_ae _ _).trans ?_
      have hmp := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae
        ((ae_restrict_iff' (halfDisc r).isOpen.measurableSet).1 hv)
      filter_upwards [ae_restrict_of_ae hmp, ae_restrict_mem (halfDisc ρ).isOpen.measurableSet]
        with x hx hxρ
      exact hx (mapsTo_add_halfDisc hc hxρ)
    have hA := W1p.halfDiscFlatTrace_ae_eq_of_continuousOn hp
      (φ.continuous.comp (continuous_id.add continuous_const)).continuousOn htr
    have hφ := W1p.halfDiscFlatTrace_ae_eq_of_continuousOn hp φ.continuous.continuousOn hv
    have key := hA.trans <| Filter.EventuallyEq.trans
      ((quasiMeasurePreserving_add_halfDiscFlatSegment hc).ae_eq_comp hφ).symm (hB _).symm
    rwa [← congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment ρ)] at key
  have hu := congrArg (· u) hAB
  simp only [ContinuousLinearMap.comp_apply, W1p.translateL_apply] at hu
  rw [hu]
  exact hB u

/-- **The flat trace of a restriction.** For `ρ ≤ r`, the flat trace of the restriction of `u` to
`halfDisc ρ` is the flat trace of `u`, almost everywhere on the flat segment of radius `ρ`. -/
theorem W1p.halfDiscFlatTrace_restrictL_ae (hp : p ≠ (∞ : ℝ≥0∞)) (hρr : ρ ≤ r)
    (u : W1p volume (halfDisc r) p) :
    W1p.halfDiscFlatTrace hp ρ (W1p.restrictL (halfDisc_mono hρr) u) =ᵐ[
      (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment ρ)]
      W1p.halfDiscFlatTrace hp r u := by
  have hc : |(0 : ℝ)| + ρ ≤ r := by simpa using hρr
  have h0 : WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)) = 0 :=
    WithLp.toLp_zero 2 (V := ℝ × ℝ)
  have heq : W1p.restrictL (halfDisc_mono hρr) u = W1p.translate (mapsTo_add_halfDisc hc) u := by
    refine W1p.ext_value (Lp.ext ((W1p.value_restrictL_ae _ u).trans ?_))
    refine Filter.EventuallyEq.trans ?_ (W1p.value_translate_ae _ u).symm
    simp only [h0, add_zero]
    rfl
  rw [heq]
  simpa only [h0, add_zero] using W1p.halfDiscFlatTrace_translate_ae hp hc u

/-- **Zero trace on a shifted half-disc.** If `|c| + ρ ≤ r`, the translate `x ↦ u (x + (0, c))`
has zero trace on the flat segment of radius `ρ` exactly when the trace of `u` vanishes almost
everywhere on the shifted subsegment `[c - ρ, c + ρ]` of the flat segment of radius `r`. -/
theorem W1p.translate_mem_halfDiscFlatTraceZeroSubmodule_iff (hp : p ≠ (∞ : ℝ≥0∞))
    (hc : |c| + ρ ≤ r) {u : W1p volume (halfDisc r) p} :
    W1p.translate (mapsTo_add_halfDisc hc) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ ↔
      ∀ᵐ x ∂(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        ((· + WithLp.toLp 2 ((0 : ℝ), c)) '' halfDiscFlatSegment ρ),
        W1p.halfDiscFlatTrace hp r u x = 0 := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_eq_zero,
    Lp.eq_zero_iff_ae_eq_zero, Filter.EventuallyEq,
    congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment ρ),
    ← Isometry.map_euclideanHausdorffMeasure_restrict
      (isometry_add_right (WithLp.toLp 2 ((0 : ℝ), c))) (halfDiscFlatSegment ρ),
    (measurableEmbedding_addRight _).ae_map_iff]
  have htr := W1p.halfDiscFlatTrace_translate_ae hp hc u
  constructor
  · intro h
    filter_upwards [htr, h] with x hx hx'
    rw [← hx, hx', Pi.zero_apply]
  · intro h
    filter_upwards [htr, h] with x hx hx'
    rw [hx, hx', Pi.zero_apply]

/-- **Zero trace passes to shifted half-discs.** If `u` has zero trace on the flat segment of
`halfDisc r` and `|c| + ρ ≤ r`, its translate `x ↦ u (x + (0, c))` has zero trace on the flat
segment of `halfDisc ρ`. -/
theorem W1p.translate_mem_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞))
    (hc : |c| + ρ ≤ r) {u : W1p volume (halfDisc r) p}
    (hu : u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r) :
    W1p.translate (mapsTo_add_halfDisc hc) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_eq_zero,
    Lp.eq_zero_iff_ae_eq_zero, Filter.EventuallyEq,
    congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment ρ)]
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_eq_zero,
    Lp.eq_zero_iff_ae_eq_zero, Filter.EventuallyEq,
    congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment r)] at hu
  filter_upwards [W1p.halfDiscFlatTrace_translate_ae hp hc u,
    (quasiMeasurePreserving_add_halfDiscFlatSegment hc).ae hu] with x hx hx'
  rw [hx, hx']
  rfl

/-- **Zero trace passes to smaller half-discs.** If `u` has zero trace on the flat segment of
`halfDisc r` and `ρ ≤ r`, its restriction to `halfDisc ρ` has zero trace on the flat segment of
`halfDisc ρ`. -/
theorem W1p.restrictL_mem_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (hρr : ρ ≤ r)
    {u : W1p volume (halfDisc r) p} (hu : u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r) :
    W1p.restrictL (halfDisc_mono hρr) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_eq_zero,
    Lp.eq_zero_iff_ae_eq_zero, Filter.EventuallyEq,
    congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment ρ)]
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_eq_zero,
    Lp.eq_zero_iff_ae_eq_zero, Filter.EventuallyEq,
    congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment r)] at hu
  filter_upwards [W1p.halfDiscFlatTrace_restrictL_ae hp hρr u,
    ae_restrict_of_ae_restrict_of_subset (halfDiscFlatSegment_mono hρr) hu] with x hx hx'
  rw [hx, hx']

/-! ### From small half-discs to the whole flat segment -/

/-- Almost everywhere on the flat segment, for surface measure, is almost everywhere on
`[-r, r]` along `t ↦ (0, t)`. -/
private theorem ae_restrict_halfDiscFlatSegment_iff {P : WithLp 2 (ℝ × ℝ) → Prop} :
    (∀ᵐ x ∂(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r), P x) ↔
      ∀ᵐ t ∂volume.restrict (Icc (-r) r), P (WithLp.toLp 2 ((0 : ℝ), t)) := by
  rw [euclideanHausdorffMeasure_restrict_halfDiscFlatSegment,
    (WithLp.isometry_toLp_prodMk_left 2 (β := ℝ) (0 : ℝ)).isClosedEmbedding.measurableEmbedding
      |>.ae_map_iff]

/-- **The zero-trace condition is local.** If every point of the open flat segment `(-r, r)`
lies in a shifted subsegment `(c - ρ, c + ρ)`, with `|c| + ρ ≤ r`, on whose half-disc the
translate `x ↦ u (x + (0, c))` has zero trace, then `u` has zero trace on the flat segment of
`halfDisc r`. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_of_forall_translate (hp : p ≠ (∞ : ℝ≥0∞))
    {u : W1p volume (halfDisc r) p}
    (H : ∀ t ∈ Ioo (-r) r, ∃ c ρ : ℝ, ∃ hc : |c| + ρ ≤ r, |t - c| < ρ ∧
      W1p.translate (mapsTo_add_halfDisc hc) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ) :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_eq_zero,
    Lp.eq_zero_iff_ae_eq_zero, Filter.EventuallyEq,
    congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment r),
    ae_restrict_halfDiscFlatSegment_iff, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  choose! c ρ hc hct hmem using H
  -- On each shifted subsegment the trace vanishes.
  have hpiece (t : Ioo (-r) r) : ∀ᵐ s ∂volume.restrict (Ioo (c t - ρ t) (c t + ρ t)),
      W1p.halfDiscFlatTrace hp r u (WithLp.toLp 2 ((0 : ℝ), s)) = 0 := by
    refine ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self ?_
    have h := (W1p.translate_mem_halfDiscFlatTraceZeroSubmodule_iff hp (hc t t.2)).1 (hmem t t.2)
    rw [← Isometry.map_euclideanHausdorffMeasure_restrict
        (isometry_add_right (WithLp.toLp 2 ((0 : ℝ), c t))) (halfDiscFlatSegment (ρ t)),
      (measurableEmbedding_addRight _).ae_map_iff,
      ae_restrict_halfDiscFlatSegment_iff] at h
    have hshift : ∀ᵐ s ∂volume.restrict (Icc (-ρ t) (ρ t)),
        W1p.halfDiscFlatTrace hp r u (WithLp.toLp 2 ((0 : ℝ), s + c t)) = 0 := by
      filter_upwards [h] with s hs
      simpa [← WithLp.toLp_add] using hs
    simpa only [sub_eq_add_neg, add_comm] using
      (ae_restrict_Icc_add_iff (a := -ρ t) (b := ρ t) (c := c t)).2 hshift
  -- Countably many of the subsegments cover `(-r, r)`.
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable
    (fun t : Ioo (-r) r => Ioo (c t - ρ t) (c t + ρ t)) fun _ => isOpen_Ioo
  refine ae_restrict_of_ae_restrict_of_subset (t := ⋃ t ∈ T, Ioo (c t - ρ t) (c t + ρ t))
    (fun t ht => ?_) ((ae_restrict_biUnion_iff _ hT _).2 fun t _ => hpiece t)
  rw [hTU, mem_iUnion]
  have := abs_sub_lt_iff.1 (hct t ht)
  exact ⟨⟨t, ht⟩, by constructor <;> linarith⟩

/-- **Zero trace on the flat segment is a local condition.** A function on `halfDisc r` has zero
trace on its flat segment exactly when every point of the open flat segment `(-r, r)` lies in a
shifted subsegment `(c - ρ, c + ρ)`, with `|c| + ρ ≤ r`, on whose half-disc the translate
`x ↦ u (x + (0, c))` has zero trace. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_forall_translate (hp : p ≠ (∞ : ℝ≥0∞))
    {u : W1p volume (halfDisc r) p} :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔
      ∀ t ∈ Ioo (-r) r, ∃ c ρ : ℝ, ∃ hc : |c| + ρ ≤ r, |t - c| < ρ ∧
        W1p.translate (mapsTo_add_halfDisc hc) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ := by
  refine ⟨fun hu t ht => ?_, W1p.mem_halfDiscFlatTraceZeroSubmodule_of_forall_translate hp⟩
  have hc : |(0 : ℝ)| + r ≤ r := by simp
  exact ⟨0, r, hc, by simpa [abs_lt] using ht,
    W1p.translate_mem_halfDiscFlatTraceZeroSubmodule hp hc hu⟩

end Trace

end TauCeti

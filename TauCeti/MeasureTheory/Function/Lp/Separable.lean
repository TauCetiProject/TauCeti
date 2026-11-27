/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp
import Mathlib.Topology.MetricSpace.Antilipschitz
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Separability of Bochner spaces

A measure `μ` is separable (`MeasureTheory.IsSeparable μ`) when a countable family of measurable
sets approximates every measurable set of finite measure, in the measure of the symmetric
difference. For `1 ≤ p < ∞`, Mathlib shows that `Lᵖ(μ; E)` is second countable when `μ` and `E`
are separable (`MeasureTheory.Lp.SecondCountableTopology`). This file proves the converse: a
nonzero Bochner space `Lᵖ(μ; E)` with `1 ≤ p < ∞` is separable exactly when `E` and `μ` are
separable.

Both necessary conditions come from indicator classes. For a measurable set `s` of finite positive
measure, `c ↦ [𝟙_s c]` multiplies distances by `μ(s) ^ (1 / p)`, so it embeds `E` into `Lᵖ(μ; E)`.
For a fixed `x ≠ 0`, the distance between `[𝟙_s x]` and `[𝟙_t x]` is `‖x‖ μ(s ∆ t) ^ (1 / p)`, so
a countable dense subset of these classes yields a countable measure-dense family of sets. These
two arguments work for every `1 ≤ p ≤ ∞`.

Separability of `μ` is also the separability of the space of measurable sets of finite measure with
the pseudo-distance `μ(s ∆ t)`, the finite-measure part of Mathlib's `MeasureTheory.MeasuredSets`.

## Main results

* `TauCeti.nontrivial_Lp_iff`: for `0 < p < ∞`, `Lᵖ(μ; E)` is nonzero exactly when `E` is nonzero
  and some measurable set has finite positive measure.
* `TauCeti.separableSpace_of_separableSpace_Lp`: if `Lᵖ(μ; E)` is separable and some measurable set
  has finite positive measure, then `E` is separable.
* `TauCeti.isSeparable_of_separableSpace_Lp`: if `Lᵖ(μ; E)` is separable and `E` is nonzero, then
  `μ` is separable.
* `TauCeti.separableSpace_Lp_iff`: for `1 ≤ p < ∞` and nonzero `Lᵖ(μ; E)`, separability of
  `Lᵖ(μ; E)` is equivalent to separability of `E` and of `μ`.
* `TauCeti.isSeparable_iff_separableSpace_measuredSets`: `μ` is separable exactly when the
  measurable sets of finite measure, with the pseudo-distance `μ(s ∆ t)`, form a separable space.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I:
  Martingales and Littlewood–Paley Theory*, Definition 1.2.27 and Proposition 1.2.29.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal symmDiff

namespace TauCeti

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [NormedAddCommGroup E]

/-- For `0 < p < ∞`, the Bochner space `Lᵖ(μ; E)` is nonzero exactly when `E` is nonzero and some
measurable set has finite positive measure. -/
theorem nontrivial_Lp_iff (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Nontrivial (Lp E p μ) ↔ Nontrivial E ∧ ∃ s, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ∞ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hE
      rw [not_nontrivial_iff_subsingleton] at hE
      obtain ⟨f, g, hfg⟩ := h
      exact hfg (Lp.ext (.of_forall fun _ ↦ Subsingleton.elim _ _))
    obtain ⟨f, hf⟩ := exists_ne (0 : Lp E p μ)
    obtain ⟨s, hs, hμs0, hμs⟩ := ((Lp.memLp f).aefinStronglyMeasurable hp0 hp)
      |>.exists_measurableSet_measure_pos_lt_top fun h ↦ hf (Lp.eq_zero_iff_ae_eq_zero.2 h)
    exact ⟨s, hs, hμs0.ne', hμs.ne⟩
  · rintro ⟨⟨c, d, hcd⟩, s, hs, hμs0, hμs⟩
    refine ⟨indicatorConstLp p hs hμs (c - d), 0, ?_⟩
    simp [hμs0, sub_eq_zero, hcd]

/-- For `0 < p < ∞`, the Bochner space `Lᵖ(μ; E)` is zero exactly when `E` is zero or every
measurable set of finite measure is null. -/
theorem subsingleton_Lp_iff (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Subsingleton (Lp E p μ) ↔
      Subsingleton E ∨ ∀ s, MeasurableSet s → μ s ≠ ∞ → μ s = 0 := by
  rw [← not_nontrivial_iff_subsingleton, nontrivial_Lp_iff hp0 hp,
    ← not_nontrivial_iff_subsingleton, not_and_or, not_exists]
  refine or_congr_right (forall_congr' fun s ↦ ?_)
  tauto

variable (p) in
/-- Separability of a Bochner space `Lᵖ(μ; E)` forces separability of `E`, as soon as some
measurable set `s` has finite positive measure: `c ↦ [𝟙_s c]` multiplies distances by
`μ(s) ^ (1 / p)`. -/
theorem separableSpace_of_separableSpace_Lp [Fact (1 ≤ p)] [SeparableSpace (Lp E p μ)]
    {s : Set α} (hs : MeasurableSet s) (hμs0 : μ s ≠ 0) (hμs : μ s ≠ ∞) : SeparableSpace E := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  set C := μ.real s ^ (1 / p.toReal)
  have hC : 0 < C := Real.rpow_pos_of_pos (ENNReal.toReal_pos hμs0 hμs) _
  have hdist (a b : E) :
      dist (indicatorConstLp p hs hμs a) (indicatorConstLp p hs hμs b) = C * dist a b := by
    rw [dist_eq_norm, indicatorConstLp_sub, norm_indicatorConstLp' hp0 hμs0, dist_eq_norm,
      mul_comm]
  have hlip : LipschitzWith (Real.toNNReal C) (indicatorConstLp p hs hμs (E := E)) :=
    .of_dist_le_mul fun a b ↦ by rw [hdist, Real.coe_toNNReal _ hC.le]
  have hanti : AntilipschitzWith (Real.toNNReal C⁻¹) (indicatorConstLp p hs hμs (E := E)) :=
    .of_le_mul_dist fun a b ↦ by
      rw [hdist, Real.coe_toNNReal _ (inv_nonneg.2 hC.le), inv_mul_cancel_left₀ hC.ne']
  have : SecondCountableTopology (Lp E p μ) := UniformSpace.secondCountable_of_separable _
  have := (hanti.isInducing hlip.continuous).secondCountableTopology
  infer_instance

/-- Indicator classes of a fixed nonzero vector that are close in `Lᵖ` come from sets whose
symmetric difference has small measure. -/
private lemma exists_measure_symmDiff_lt_of_dist_lt [Fact (1 ≤ p)] {x : E} (hx : x ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃s t : Set α⦄ (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t)
      (hμt : μ t ≠ ∞), dist (indicatorConstLp p hs hμs x) (indicatorConstLp p ht hμt x) < δ →
        μ (s ∆ t) < ENNReal.ofReal ε := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  refine ⟨‖x‖ * ε ^ (1 / p.toReal), by positivity, fun s t hs hμs ht hμt h ↦ ?_⟩
  by_cases h0 : μ (s ∆ t) = 0
  · rw [h0]
    exact ENNReal.ofReal_pos.2 hε
  rw [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp' hp0 h0] at h
  have h' := lt_of_mul_lt_mul_left h (norm_nonneg x)
  rcases (ENNReal.toReal_nonneg (a := p)).eq_or_lt with hp | hp
  · simp [← hp] at h'
  · rw [ENNReal.lt_ofReal_iff_toReal_lt (measure_symmDiff_ne_top hμs hμt), ← measureReal_def]
    exact (Real.rpow_lt_rpow_iff measureReal_nonneg hε.le (by positivity)).1 h'

variable (E p) in
/-- Separability of a Bochner space `Lᵖ(μ; E)` with nonzero `E` forces separability of the
measure `μ`: for `x ≠ 0`, the distance between `[𝟙_s x]` and `[𝟙_t x]` controls `μ(s ∆ t)`. -/
theorem isSeparable_of_separableSpace_Lp [Fact (1 ≤ p)] [Nontrivial E]
    [SeparableSpace (Lp E p μ)] : IsSeparable μ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  let T := {s : Set α | MeasurableSet s ∧ μ s ≠ ∞}
  let F : T → Lp E p μ := fun s ↦ indicatorConstLp p s.property.1 s.property.2 x
  obtain ⟨D, hDF, hDc, hFD⟩ :=
    (IsSeparable.of_separableSpace (range F)).exists_countable_dense_subset
  choose g hg using fun d : D ↦ hDF d.property
  have := hDc.to_subtype
  refine ⟨⟨range fun d ↦ (g d : Set α), countable_range _, ?_, ?_⟩⟩
  · rintro - ⟨d, rfl⟩
    exact (g d).property.1
  · intro s hs hμs ε hε
    obtain ⟨δ, hδ, hδε⟩ := exists_measure_symmDiff_lt_of_dist_lt (p := p) (μ := μ) hx hε
    obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 (hFD ⟨⟨s, hs, hμs⟩, rfl⟩) δ hδ
    set t := g ⟨d, hdD⟩
    have hFt : F t = d := hg ⟨d, hdD⟩
    rw [← hFt] at hd
    exact ⟨t, ⟨⟨d, hdD⟩, rfl⟩, hδε hs hμs t.property.1 t.property.2 hd⟩

/-- **Separability of Bochner spaces.** For `1 ≤ p < ∞`, a nonzero Bochner space `Lᵖ(μ; E)` is
separable exactly when `E` is separable and the measure `μ` is separable. -/
theorem separableSpace_Lp_iff [Fact (1 ≤ p)] (hp : p ≠ ∞) [Nontrivial (Lp E p μ)] :
    SeparableSpace (Lp E p μ) ↔ SeparableSpace E ∧ IsSeparable μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  obtain ⟨hE, s, hs, hμs0, hμs⟩ := (nontrivial_Lp_iff (E := E) (μ := μ) hp0 hp).1 inferInstance
  constructor
  · intro _
    exact ⟨separableSpace_of_separableSpace_Lp p hs hμs0 hμs, isSeparable_of_separableSpace_Lp E p⟩
  · rintro ⟨_, _⟩
    have : Fact (p ≠ ∞) := ⟨hp⟩
    infer_instance

/-- A measure `μ` is separable exactly when the measurable sets of finite measure, with the
pseudo-distance `μ(s ∆ t)` of `MeasureTheory.MeasuredSets`, form a separable space. -/
theorem isSeparable_iff_separableSpace_measuredSets :
    IsSeparable μ ↔ SeparableSpace {s : MeasuredSets μ // μ s ≠ ∞} := by
  constructor
  · intro _
    obtain ⟨𝒜, h𝒜c, h𝒜⟩ := exists_countable_measureDense μ
    refine ⟨{s | ((s : MeasuredSets μ) : Set α) ∈ 𝒜}, ?_, ?_⟩
    · exact h𝒜c.preimage (SetLike.coe_injective.comp Subtype.val_injective)
    · refine fun s ↦ EMetric.mem_closure_iff.2 fun ε hε ↦ ?_
      obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
      obtain ⟨t, ht𝒜, hμt, hst⟩ := h𝒜.fin_meas_approx s.val.property s.property r
        (ENNReal.ofReal_pos.1 hr0)
      refine ⟨⟨⟨t, h𝒜.measurable t ht𝒜⟩, hμt⟩, ht𝒜, ?_⟩
      rw [Subtype.edist_eq, MeasuredSets.edist_def]
      exact hst.trans hrε
  · rintro ⟨D, hDc, hD⟩
    refine ⟨⟨(fun s : {s : MeasuredSets μ // μ s ≠ ∞} ↦ (s.val : Set α)) '' D, hDc.image _, ?_,
      ?_⟩⟩
    · rintro - ⟨s, -, rfl⟩
      exact s.val.property
    · intro s hs hμs ε hε
      obtain ⟨t, htD, hst⟩ := EMetric.mem_closure_iff.1 (hD ⟨⟨s, hs⟩, hμs⟩) _
        (ENNReal.ofReal_pos.2 hε)
      rw [Subtype.edist_eq, MeasuredSets.edist_def] at hst
      exact ⟨_, ⟨t, htD, rfl⟩, hst⟩

end TauCeti

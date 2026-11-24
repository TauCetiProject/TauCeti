/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.MaximalMultiplication.Basic
public import TauCeti.MeasureTheory.Function.Lp.Norm
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Resolvent and essential-range spectrum of maximal multiplication operators on `Lᵖ`

This file characterizes the resolvent set, resolvent operator, and spectrum of the maximal
unbounded multiplication operator `MeasureTheory.Lp.maximalMultiplication p μ f` on `Lp E p μ`
for `1 ≤ p ≤ ∞`.

When `f : α → 𝕜` is almost-everywhere strongly measurable and satisfies `ε ≤ ‖f x - z‖` almost
everywhere for some `ε > 0`, bounded multiplication by the essentially bounded reciprocal
`(z - f)⁻¹` is the resolvent at `z`. Conversely, on a sigma-finite measure space with nontrivial
fiber `E`, membership of `z` in the resolvent set forces `f` to be almost-everywhere strongly
measurable and bounded away from `z` almost everywhere, identifying the spectrum with the
measure-theoretic essential range of `f`.

## Main results

* `MeasureTheory.Lp.isResolventAt_maximalMultiplication_of_ae_le_norm_sub` and
  `MeasureTheory.Lp.resolvent_maximalMultiplication_eq_multiplicationOperator_of_ae_le_norm_sub`:
  if `f` is almost-everywhere strongly measurable and `ε ≤ ‖f x - z‖` almost everywhere with
  `ε > 0`, then bounded multiplication by `(z - f)⁻¹` is the resolvent of
  `maximalMultiplication p μ f` at `z`.
* `MeasureTheory.Lp.resolvent_maximalMultiplication_ae`: at any `z` in the resolvent set, the
  resolvent acts almost everywhere as pointwise scalar multiplication by `(z - f)⁻¹`.
* `MeasureTheory.Lp.norm_resolvent_maximalMultiplication_le`: over a nontrivially normed field,
  the operator norm of the resolvent at `z` is at most `ε⁻¹` when `ε ≤ ‖f x - z‖` almost
  everywhere.
* `MeasureTheory.Lp.aestronglyMeasurable_of_mem_resolventSet_maximalMultiplication`: on a
  sigma-finite measure space with nontrivial fiber, nonempty resolvent set implies `f` is
  almost-everywhere strongly measurable.
* `MeasureTheory.Lp.mem_resolventSet_maximalMultiplication_iff` and
  `MeasureTheory.Lp.spectrum_maximalMultiplication`: on a sigma-finite space with nontrivial
  fiber and `1 ≤ p ≤ ∞`, for an almost-everywhere strongly measurable symbol `f`, the spectrum of
  `maximalMultiplication p μ f` is the measure-theoretic essential range
  `{z : 𝕜 | ∀ ε > 0, μ {x | ‖f x - z‖ < ε} ≠ 0}`.
* `MeasureTheory.Lp.isResolventAt_maximalMultiplication` and
  `MeasureTheory.Lp.resolvent_maximalMultiplication_eq_multiplicationOperator`: on a sigma-finite
  space with nontrivial fiber, at any `z` in the resolvent set, `(z - f)⁻¹` is essentially bounded
  and the resolvent at `z` is `multiplicationOperator` of `(z - f)⁻¹`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 3.1 and Theorem 3.18.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Section VIII.3, Example 1.
-/

public section

noncomputable section

open Filter
open scoped ENNReal

namespace MeasureTheory.Lp

section Resolvent

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- When an almost-everywhere strongly measurable symbol `f` satisfies `ε ≤ ‖f x - z‖` almost
everywhere for some `ε > 0`, bounded multiplication by `(z - f)⁻¹` is the resolvent of
`maximalMultiplication p μ f` at `z`. -/
theorem isResolventAt_maximalMultiplication_of_ae_le_norm_sub {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) {z : 𝕜} {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    LinearPMap.IsResolventAt (maximalMultiplication (E := E) p μ f) z
      (multiplicationOperator (E := E) (p := p)
        ((memLp_top_inv_sub_of_ae_le_norm_sub hf hε hbound).toLp (fun x ↦ (z - f x)⁻¹))) := by
  set hg := memLp_top_inv_sub_of_ae_le_norm_sub hf hε hbound
  set R := multiplicationOperator (E := E) (p := p) (hg.toLp (fun x ↦ (z - f x)⁻¹))
  refine LinearPMap.isResolventAt_iff_forall_mem_graph.2 ⟨fun y ↦ ?_, fun ⟨u₀, v₀⟩ hq ↦ ?_⟩
  · rw [mem_graph_maximalMultiplication_iff]
    filter_upwards [multiplicationOperator_ae (hg.toLp _) y, hg.coeFn_toLp,
      Lp.coeFn_sub (z • R y) y, Lp.coeFn_smul z (R y), hbound]
      with x hRy hgx hsub hsmul hx
    have hne : z - f x ≠ 0 := norm_pos_iff.1 (hε.trans_le (norm_sub_rev (f x) z ▸ hx))
    rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hRy, hgx]
    calc z • ((z - f x)⁻¹ • y x) - y x
        = (z * (z - f x)⁻¹ - (z - f x) * (z - f x)⁻¹) • y x := by
          rw [mul_inv_cancel₀ hne, sub_smul, one_smul, mul_smul]
      _ = f x • ((z - f x)⁻¹ • y x) := by
          rw [← sub_mul, sub_sub_cancel, mul_smul]
  · refine Lp.ext ?_
    filter_upwards [multiplicationOperator_ae (hg.toLp _) (z • u₀ - v₀),
      hg.coeFn_toLp, Lp.coeFn_sub (z • u₀) v₀, Lp.coeFn_smul z u₀,
      mem_graph_maximalMultiplication_iff.1 hq, hbound]
      with x hRw hgx hsub hsmul hqx hx
    have hne : z - f x ≠ 0 := norm_pos_iff.1 (hε.trans_le (norm_sub_rev (f x) z ▸ hx))
    rw [hRw, hgx, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hqx]
    calc (z - f x)⁻¹ • (z • u₀ x - f x • u₀ x)
        = ((z - f x)⁻¹ * (z - f x)) • u₀ x := by rw [← sub_smul, smul_smul]
      _ = u₀ x := by rw [inv_mul_cancel₀ hne, one_smul]

/-- When an almost-everywhere strongly measurable symbol `f` satisfies `ε ≤ ‖f x - z‖` almost
everywhere for some `ε > 0`, `z` belongs to the resolvent set of `maximalMultiplication p μ f`. -/
theorem mem_resolventSet_maximalMultiplication_of_ae_le_norm_sub {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) {z : 𝕜} {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    z ∈ (maximalMultiplication (E := E) p μ f).resolventSet :=
  (isResolventAt_maximalMultiplication_of_ae_le_norm_sub hf hε hbound).mem_resolventSet

/-- When an almost-everywhere strongly measurable symbol `f` satisfies `ε ≤ ‖f x - z‖` almost
everywhere for some `ε > 0`, the resolvent of `maximalMultiplication p μ f` at `z` equals
`multiplicationOperator` of the `L∞` reciprocal `(z - f)⁻¹`. -/
theorem resolvent_maximalMultiplication_eq_multiplicationOperator_of_ae_le_norm_sub {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) {z : 𝕜} {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    (maximalMultiplication (E := E) p μ f).resolvent z =
      multiplicationOperator (E := E) (p := p)
        ((memLp_top_inv_sub_of_ae_le_norm_sub hf hε hbound).toLp (fun x ↦ (z - f x)⁻¹)) :=
  LinearPMap.resolvent_eq_of_isResolventAt
    (isResolventAt_maximalMultiplication_of_ae_le_norm_sub hf hε hbound)

/-- At any `z` in the resolvent set of `maximalMultiplication p μ f`, the resolvent acts almost
everywhere as pointwise scalar multiplication by `(z - f)⁻¹`. -/
theorem resolvent_maximalMultiplication_ae {f : α → 𝕜} {z : 𝕜}
    (hz : z ∈ (maximalMultiplication (E := E) p μ f).resolventSet) (y : Lp E p μ) :
    (maximalMultiplication (E := E) p μ f).resolvent z y =ᵐ[μ]
      fun x ↦ (z - f x)⁻¹ • y x := by
  set T := maximalMultiplication (E := E) p μ f
  set r : Lp E p μ := T.resolvent z y
  have hr_eq : ∀ᵐ x ∂μ, (z - f x) • r x = y x := by
    have hres : z • r - T ⟨r, LinearPMap.resolvent_mem_domain hz y⟩ = y :=
      LinearPMap.smul_sub_apply_resolvent hz y
    filter_upwards [hres ▸ Lp.coeFn_sub (z • r) (T ⟨r, LinearPMap.resolvent_mem_domain hz y⟩),
      Lp.coeFn_smul z r,
      coeFn_maximalMultiplication ⟨r, LinearPMap.resolvent_mem_domain hz y⟩]
      with x hsub hsmul hTr
    rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hTr, ← sub_smul]
  let r_mk := (Lp.aestronglyMeasurable r).mk r
  let y_mk := (Lp.aestronglyMeasurable y).mk y
  set s : Set α := {x | ‖r_mk x‖ ≠ 0 ∧ ‖y_mk x‖ = 0}
  have hs : MeasurableSet s :=
    ((Lp.aestronglyMeasurable r).stronglyMeasurable_mk.norm.measurable
      (measurableSet_singleton (0 : ℝ)).compl).inter
      ((Lp.aestronglyMeasurable y).stronglyMeasurable_mk.norm.measurable
        (measurableSet_singleton (0 : ℝ)))
  let w : Lp E p μ := ((Lp.memLp r).indicator hs.nullMeasurableSet).toLp (s.indicator r)
  have hw_ae : (fun x ↦ f x • w x) =ᵐ[μ] ((z • w : Lp E p μ) : α → E) := by
    filter_upwards [((Lp.memLp r).indicator hs.nullMeasurableSet).coeFn_toLp,
      Lp.coeFn_smul z w, hr_eq, (Lp.aestronglyMeasurable r).ae_eq_mk,
      (Lp.aestronglyMeasurable y).ae_eq_mk] with x hw hzw hsol hrmk hymk
    rw [hzw, Pi.smul_apply, hw]
    by_cases hxs : x ∈ s
    · have hrx : r x ≠ 0 := by rw [hrmk]; exact norm_ne_zero_iff.1 hxs.1
      have hyx : y x = 0 := by rw [hymk]; exact norm_eq_zero.1 hxs.2
      have hfz : f x = z :=
        (sub_eq_zero.1 ((smul_eq_zero.1 (hsol.trans hyx)).resolve_right hrx)).symm
      rw [Set.indicator_of_mem hxs, hfz]
    · rw [Set.indicator_of_notMem hxs, smul_zero, smul_zero]
  have hw0 : w = 0 := by
    have hgraph : (w, z • w) ∈ T.graph := mem_graph_maximalMultiplication_iff.2 hw_ae.symm
    obtain ⟨u, huw, hTu⟩ := T.mem_graph_iff.1 hgraph
    exact huw.symm.trans (congrArg Subtype.val
      (LinearPMap.eq_zero_of_apply_eq_smul hz u (hTu.trans (congrArg (z • ·) huw.symm))))
  filter_upwards [hr_eq, hw0 ▸ Lp.coeFn_zero E p μ,
    ((Lp.memLp r).indicator hs.nullMeasurableSet).coeFn_toLp,
    (Lp.aestronglyMeasurable r).ae_eq_mk, (Lp.aestronglyMeasurable y).ae_eq_mk]
    with x hsol hw_zero hw hrmk hymk
  by_cases hne : z - f x = 0
  · rw [hne, inv_zero, zero_smul]
    have hy0 : y x = 0 := by rw [← hsol, hne, zero_smul]
    by_contra hrx
    have hxs : x ∈ s :=
      ⟨norm_ne_zero_iff.2 fun h ↦ hrx (hrmk.trans h), norm_eq_zero.2 (hymk.symm.trans hy0)⟩
    exact hrx ((Set.indicator_of_mem hxs r).symm.trans (hw.symm.trans hw_zero))
  · rw [← hsol, inv_smul_smul₀ hne]

omit [Fact (1 ≤ p)] in
private theorem norm_smul_sub_indicatorConstLp_le {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    {z : 𝕜} {ε : ℝ} {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (hts : ∀ x ∈ t, ‖hf.mk f x - z‖ < ε) (v : E)
    (hu_dom : indicatorConstLp p ht hμt v ∈ (maximalMultiplication (E := E) p μ f).domain) :
    ‖z • indicatorConstLp p ht hμt v -
        maximalMultiplication p μ f ⟨indicatorConstLp p ht hμt v, hu_dom⟩‖ ≤
      ε * ‖indicatorConstLp p ht hμt v‖ := by
  set u : Lp E p μ := indicatorConstLp p ht hμt v
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_sub (z • u) (maximalMultiplication p μ f ⟨u, hu_dom⟩),
    Lp.coeFn_smul z u, coeFn_maximalMultiplication ⟨u, hu_dom⟩,
    indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt) (c := v),
    hf.ae_eq_mk] with x hsub hsmul hMf hux hmk
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hMf, ← sub_smul, norm_smul, norm_sub_rev]
  by_cases hxt : x ∈ t
  · exact mul_le_mul_of_nonneg_right (hmk ▸ (hts x hxt).le) (norm_nonneg _)
  · rw [hux, Set.indicator_of_notMem hxt]
    simp

end Resolvent

section NontrivialFieldResolvent

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- When an almost-everywhere strongly measurable symbol `f` satisfies `ε ≤ ‖f x - z‖` almost
everywhere for some `ε > 0` over a nontrivially normed field, the operator norm of the resolvent at
`z` is at most `ε⁻¹`. -/
theorem norm_resolvent_maximalMultiplication_le {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    {z : 𝕜} {ε : ℝ} (hε : 0 < ε) (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    ‖(maximalMultiplication (E := E) p μ f).resolvent z‖ ≤ ε⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hε.le) fun y ↦
    Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [resolvent_maximalMultiplication_ae
      (mem_resolventSet_maximalMultiplication_of_ae_le_norm_sub hf hε hbound) y, hbound]
    with x hRy hx
  rw [hRy, norm_smul, norm_inv, norm_sub_rev]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hε hx) (norm_nonneg _)

private theorem exists_measure_lt_norm_sub_eq_zero_of_nontrivial [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) {z : 𝕜} {R : Lp E p μ →L[𝕜] Lp E p μ}
    (hR : ∀ u : (maximalMultiplication (E := E) p μ f).domain,
      R (z • (u : Lp E p μ) - maximalMultiplication p μ f u) = u) :
    ∃ ε > 0, μ {x | ‖f x - z‖ < ε} = 0 := by
  have hR_pos : 0 < ‖R‖ + 1 := add_pos_of_nonneg_of_pos (norm_nonneg R) zero_lt_one
  set ε : ℝ := (‖R‖ + 1)⁻¹
  refine ⟨ε, inv_pos.2 hR_pos, ?_⟩
  by_contra hμ
  set s : Set α := {x | ‖hf.mk f x - z‖ < ε}
  have hs : MeasurableSet s :=
    measurableSet_lt
      (hf.stronglyMeasurable_mk.sub stronglyMeasurable_const).norm.measurable measurable_const
  have hs_ae : s =ᵐ[μ] {x | ‖f x - z‖ < ε} :=
    eventuallyEqSet_iff.2 (hf.ae_eq_mk.symm.mono fun x hx ↦ by dsimp [s]; rw [hx])
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.2 (measure_congr hs_ae ▸ hμ))
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set u : Lp E p μ := indicatorConstLp p ht hμt_top.ne v
  have hu_pos : 0 < ‖u‖ :=
    norm_pos_iff.2 fun hu0 ↦ (TauCeti.indicatorConstLp_eq_zero_iff.1 hu0).elim hμt_pos.ne' hv
  have hu_dom : u ∈ (maximalMultiplication (E := E) p μ f).domain := by
    refine boundedOnSupportSubmodule_le_domain_maximalMultiplication hf
      (mem_boundedOnSupportSubmodule_iff.2 ⟨ε + ‖z‖, ?_⟩)
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt_top.ne) (c := v),
      hf.ae_eq_mk] with x hux hmk hne
    rw [hux] at hne
    have htri : ‖hf.mk f x‖ ≤ ‖hf.mk f x - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (hf.mk f x - z) z
    rw [hmk]
    exact htri.trans (add_le_add (hts (Set.mem_of_indicator_ne_zero hne)).le le_rfl)
  have hshift := norm_smul_sub_indicatorConstLp_le hf ht hμt_top.ne (fun _ hx ↦ hts hx) v hu_dom
  have hround : 1 * ‖u‖ ≤ (‖R‖ * ε) * ‖u‖ := by
    calc 1 * ‖u‖ = ‖R (z • u - maximalMultiplication p μ f ⟨u, hu_dom⟩)‖ := by
          rw [one_mul, hR ⟨u, hu_dom⟩]
      _ ≤ ‖R‖ * ‖z • u - maximalMultiplication p μ f ⟨u, hu_dom⟩‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (ε * ‖u‖) := mul_le_mul_of_nonneg_left hshift (norm_nonneg R)
      _ = (‖R‖ * ε) * ‖u‖ := (mul_assoc _ _ _).symm
  exact not_lt_of_ge (le_of_mul_le_mul_right hround hu_pos)
    ((mul_inv_lt_iff₀ hR_pos).2 (by linarith))

end NontrivialFieldResolvent

section Spectrum

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- On a sigma-finite measure space with nontrivial fiber `E`, if `maximalMultiplication p μ f` has
nonempty resolvent set (`z ∈ resolventSet`), then the symbol `f` is automatically almost-everywhere
strongly measurable. -/
theorem aestronglyMeasurable_of_mem_resolventSet_maximalMultiplication
    [SigmaFinite μ] [Nontrivial E] {f : α → 𝕜} {z : 𝕜}
    (hz : z ∈ (maximalMultiplication (E := E) p μ f).resolventSet) :
    AEStronglyMeasurable f μ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hemb : Topology.IsEmbedding (fun c : 𝕜 ↦ c • v) :=
    Topology.IsEmbedding.subtypeVal.comp
      (ContinuousLinearEquiv.toSpanNonzeroSingleton 𝕜 v hv).toHomeomorph.isEmbedding
  set g : α → 𝕜 := fun x ↦ (z - f x)⁻¹
  have hg_ind (n : ℕ) : AEStronglyMeasurable ((spanningSets μ n).indicator g) μ := by
    have hs := measurableSet_spanningSets μ n
    have hμs := (measure_spanningSets_lt_top μ n).ne
    let y : Lp E p μ := indicatorConstLp p hs hμs v
    let r : Lp E p μ := (maximalMultiplication (E := E) p μ f).resolvent z y
    have hr_ae : (spanningSets μ n).indicator r =ᵐ[μ]
        (fun c : 𝕜 ↦ c • v) ∘ (spanningSets μ n).indicator g := by
      filter_upwards [resolvent_maximalMultiplication_ae hz y,
        indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := v)] with x hrx hyx
      by_cases hx : x ∈ spanningSets μ n
      · simp only [Function.comp_apply, Set.indicator_of_mem hx]
        rw [hrx, hyx, Set.indicator_of_mem hx]
      · simp only [Function.comp_apply, Set.indicator_of_notMem hx, zero_smul]
    exact hemb.aestronglyMeasurable_comp_iff.1
      (((Lp.aestronglyMeasurable r).indicator hs).congr hr_ae)
  have hg : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hg_ind
      (Eventually.of_forall fun x ↦
        tendsto_atTop_of_eventually_const (i₀ := spanningSetsIndex μ x) fun n hn ↦
          Set.indicator_of_mem (monotone_spanningSets μ hn (mem_spanningSetsIndex μ x)) g)
  have hfg : (fun x ↦ z - (g x)⁻¹) = f := funext fun x ↦ by simp [g]
  exact hfg ▸ aestronglyMeasurable_const.sub hg.inv₀

/-- On a sigma-finite measure space with nontrivial fiber `E`, `z` belongs to the resolvent set of
`maximalMultiplication p μ f` for an almost-everywhere strongly measurable symbol `f` if and only
if `{x | ‖f x - z‖ < ε}` is `μ`-null for some `ε > 0`. -/
theorem mem_resolventSet_maximalMultiplication_iff [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) (z : 𝕜) :
    z ∈ (maximalMultiplication (E := E) p μ f).resolventSet ↔
      ∃ ε > 0, μ {x | ‖f x - z‖ < ε} = 0 := by
  refine ⟨fun hz ↦ ?_, fun ⟨ε, hε, hμ⟩ ↦ ?_⟩
  · by_cases htriv : ∀ a : 𝕜, a ≠ 0 → ‖a‖ = 1
    · refine ⟨1 / 2, by positivity, ?_⟩
      have hset : {x | ‖f x - z‖ < 1 / 2} = {x | f x = z} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        refine ⟨fun hlt ↦ sub_eq_zero.1 ?_, fun heq ↦ by simp [heq]⟩
        by_contra hne
        linarith [htriv _ hne]
      rw [hset, ← ker_smulSub_maximalMultiplication_eq_bot_iff (E := E) (p := p) hf z,
        LinearMap.ker_eq_bot']
      intro u hu
      rw [LinearPMap.smulSub_apply, sub_eq_zero] at hu
      exact LinearPMap.eq_zero_of_apply_eq_smul hz u hu.symm
    · push Not at htriv
      let _ : NontriviallyNormedField 𝕜 := .ofNormNeOne htriv
      exact exists_measure_lt_norm_sub_eq_zero_of_nontrivial (𝕜 := 𝕜) hf
        (LinearPMap.isResolventAt_resolvent hz).apply_smul_sub
  · refine mem_resolventSet_maximalMultiplication_of_ae_le_norm_sub hf hε ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
    exact not_lt.1 hx

/-- On a sigma-finite measure space with nontrivial fiber `E`, whenever `z` belongs to the
resolvent set of `maximalMultiplication p μ f`, the reciprocal `x ↦ (z - f x)⁻¹` is essentially
bounded (`MemLp · ∞ μ`). -/
theorem memLp_top_inv_sub_of_mem_resolventSet_maximalMultiplication [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} {z : 𝕜} (hz : z ∈ (maximalMultiplication (E := E) p μ f).resolventSet) :
    MemLp (fun x ↦ (z - f x)⁻¹) ∞ μ := by
  have hf := aestronglyMeasurable_of_mem_resolventSet_maximalMultiplication hz
  obtain ⟨ε, hε, hμ⟩ := (mem_resolventSet_maximalMultiplication_iff (E := E) hf z).1 hz
  refine memLp_top_inv_sub_of_ae_le_norm_sub hf hε ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
  exact not_lt.1 hx

/-- On a sigma-finite measure space with nontrivial fiber `E`, whenever `z` belongs to the
resolvent set of `maximalMultiplication p μ f`, bounded multiplication by the `L∞` reciprocal
`(z - f)⁻¹` is the resolvent at `z`. -/
theorem isResolventAt_maximalMultiplication [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} {z : 𝕜} (hz : z ∈ (maximalMultiplication (E := E) p μ f).resolventSet) :
    LinearPMap.IsResolventAt (maximalMultiplication (E := E) p μ f) z
      (multiplicationOperator (E := E) (p := p)
        ((memLp_top_inv_sub_of_mem_resolventSet_maximalMultiplication hz).toLp
          (fun x ↦ (z - f x)⁻¹))) := by
  have hf := aestronglyMeasurable_of_mem_resolventSet_maximalMultiplication hz
  obtain ⟨ε, hε, hμ⟩ := (mem_resolventSet_maximalMultiplication_iff (E := E) hf z).1 hz
  have hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖ :=
    (measure_eq_zero_iff_ae_notMem.1 hμ).mono fun _ hx ↦ not_lt.1 hx
  exact isResolventAt_maximalMultiplication_of_ae_le_norm_sub hf hε hbound

/-- On a sigma-finite measure space with nontrivial fiber `E`, whenever `z` belongs to the
resolvent set of `maximalMultiplication p μ f`, the resolvent at `z` equals `multiplicationOperator`
of the `L∞` reciprocal `(z - f)⁻¹`. -/
theorem resolvent_maximalMultiplication_eq_multiplicationOperator [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} {z : 𝕜} (hz : z ∈ (maximalMultiplication (E := E) p μ f).resolventSet) :
    (maximalMultiplication (E := E) p μ f).resolvent z =
      multiplicationOperator (E := E) (p := p)
        ((memLp_top_inv_sub_of_mem_resolventSet_maximalMultiplication hz).toLp
          (fun x ↦ (z - f x)⁻¹)) :=
  LinearPMap.resolvent_eq_of_isResolventAt (isResolventAt_maximalMultiplication hz)

/-- **Essential-range spectrum of a maximal multiplication operator.** On a sigma-finite measure
space with nontrivial fiber `E`, for every `1 ≤ p ≤ ∞` and almost-everywhere strongly measurable
symbol `f : α → 𝕜`, the spectrum of `maximalMultiplication p μ f` is the measure-theoretic
essential range `{z : 𝕜 | ∀ ε > 0, μ {x | ‖f x - z‖ < ε} ≠ 0}`. -/
theorem spectrum_maximalMultiplication [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    (maximalMultiplication (E := E) p μ f).spectrum =
      {z : 𝕜 | ∀ ε > 0, μ {x | ‖f x - z‖ < ε} ≠ 0} := by
  ext z
  simp only [LinearPMap.mem_spectrum_iff, mem_resolventSet_maximalMultiplication_iff (E := E) hf,
    Set.mem_ofPred_eq, not_exists, not_and]

end Spectrum

end MeasureTheory.Lp

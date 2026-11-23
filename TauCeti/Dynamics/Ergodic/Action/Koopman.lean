/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Action
public import TauCeti.Analysis.Semigroups.Group.Unitary
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The Koopman group of a measurable action of `ℝ`

Let `ℝ` act on a measurable space `X`, jointly measurably (`MeasurableVAdd₂ ℝ X`), preserving a
finite measure `μ`. Each translate `(t +ᵥ ·)` is measure preserving, so it pulls `Lᵖ(μ)` back to
itself (`MeasureTheory.Lp.compMeasurePreserving`). For `1 ≤ p < ∞` the orbit
`t ↦ f ∘ (t +ᵥ ·)` of every `f ∈ Lᵖ(μ)` is continuous. No topology on `X` and no separability
are assumed.

The proof reduces to indicators of measurable sets, where it says that
`μ (((t +ᵥ ·) ⁻¹' A) ∆ A) → 0` as `t → 0`. For `g = 1_A` the orbit averages
`A_h g x = h⁻¹ ∫₀ʰ g (r +ᵥ x) dr` satisfy `|A_h g (t +ᵥ x) - A_h g x| ≤ 2 |t| / h`, and
`∫ |A_h g - g| dμ → 0` as `h → 0⁺`: by invariance of `μ` and Fubini this integral is the
`μ`-average over `x` of `∫₀¹ |A_h g (s +ᵥ x) - g (s +ᵥ x)| ds`, which tends to `0` for every `x` by
the Lebesgue differentiation theorem along the orbit of `x` and dominated convergence.

## Main results

* `MeasureTheory.tendsto_measure_preimage_vadd_symmDiff`: the measure of `((t +ᵥ ·) ⁻¹' A) ∆ A`
  tends to `0` as `t → 0`;
* `MeasureTheory.Lp.continuous_compMeasurePreserving_vadd`: the Koopman orbits are continuous
  from `ℝ` to `Lᵖ(μ)` for `p ≠ ∞`;
* `TauCeti.koopmanGroup`: the Koopman operators as a strongly continuous group on `Lᵖ(μ)`;
  `TauCeti.koopmanGroup_isUnitary`: on complex `L²(μ)` it is unitary.

The finiteness of `μ` cannot be dropped: for the action of `ℝ` on itself by translation with
counting measure, `‖1_{{-t}} - 1_{{0}}‖₂ = √2` for every `t ≠ 0`. Joint measurability cannot be
dropped either: translating `AddCircle 1` by `φ t` for a discontinuous additive `φ : ℝ → ℝ`
preserves Haar measure, but the orbit `t ↦ exp(2πiφ(t)) e₁` of the unit mode is discontinuous.

## References

* MathematicalBilliards roadmap (TauCetiRoadmap), §12.3, The Koopman group.
-/

public section

noncomputable section

open Filter Set
open scoped Topology ENNReal symmDiff

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] [MeasurableVAdd₂ ℝ X] {μ : Measure X}

section OrbitAverage

variable {g : X → ℝ}

private theorem norm_abs_sub_le_two {a b : ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖|a - b|‖ ≤ 2 := by
  rw [Real.norm_eq_abs, abs_abs]
  rw [Real.norm_eq_abs] at ha hb
  linarith [abs_sub a b]

/-- The average of `g` over the time interval `[0, h]` along the orbit of `x`. -/
private def orbitAverage (g : X → ℝ) (h : ℝ) (x : X) : ℝ :=
  h⁻¹ * ∫ r in (0 : ℝ)..h, g (r +ᵥ x)

private theorem intervalIntegrable_orbit (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) (x : X)
    (a b : ℝ) : IntervalIntegrable (fun r : ℝ => g (r +ᵥ x)) volume a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    (hg.comp (measurable_vadd_const x)).aestronglyMeasurable (ae_of_all _ fun _ => hg1 _)

omit [MeasurableSpace X] [MeasurableVAdd₂ ℝ X] in
private theorem orbitAverage_vadd (g : X → ℝ) (h t : ℝ) (x : X) :
    orbitAverage g h (t +ᵥ x) = h⁻¹ * ∫ r in t..t + h, g (r +ᵥ x) := by
  simp only [orbitAverage, ← add_vadd]
  rw [intervalIntegral.integral_comp_add_right (fun r => g (r +ᵥ x)) t, zero_add, add_comm h]

private theorem measurable_orbitAverage (hg : Measurable g) (h : ℝ) :
    Measurable (orbitAverage g h) := by
  have hF : StronglyMeasurable fun p : X × ℝ => g (p.2 +ᵥ p.1) :=
    (hg.comp (measurable_snd.vadd measurable_fst)).stronglyMeasurable
  have h₁ := (hF.integral_prod_right' (ν := volume.restrict (Ioc 0 h))).measurable
  have h₂ := (hF.integral_prod_right' (ν := volume.restrict (Ioc h 0))).measurable
  exact (h₁.sub h₂).const_mul _

omit [MeasurableSpace X] [MeasurableVAdd₂ ℝ X] in
private theorem norm_orbitAverage_le (hg1 : ∀ x, ‖g x‖ ≤ 1) {h : ℝ} (hh : 0 < h) (x : X) :
    ‖orbitAverage g h x‖ ≤ 1 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
    (f := fun r => g (r +ᵥ x)) fun r _ => hg1 _
  rw [orbitAverage, norm_mul, norm_inv, Real.norm_of_nonneg hh.le]
  rw [sub_zero, abs_of_pos hh, one_mul] at this
  calc h⁻¹ * ‖∫ r in (0 : ℝ)..h, g (r +ᵥ x)‖ ≤ h⁻¹ * h := by gcongr
    _ = 1 := inv_mul_cancel₀ hh.ne'

private theorem abs_orbitAverage_vadd_sub_le (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) {h : ℝ}
    (hh : 0 < h) (t : ℝ) (x : X) :
    |orbitAverage g h (t +ᵥ x) - orbitAverage g h x| ≤ 2 * |t| / h := by
  have hi := intervalIntegrable_orbit hg hg1 x
  rw [orbitAverage_vadd, orbitAverage, ← mul_sub,
    intervalIntegral.integral_interval_sub_interval_comm' (hi _ _) (hi _ _) (hi _ _)]
  have h₁ := intervalIntegral.norm_integral_le_of_norm_le_const (a := h) (b := t + h)
    (f := fun r => g (r +ᵥ x)) fun r _ => hg1 _
  have h₂ := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun r => g (r +ᵥ x)) fun r _ => hg1 _
  simp only [add_sub_cancel_right, sub_zero, one_mul, Real.norm_eq_abs] at h₁ h₂
  rw [abs_mul, abs_inv, abs_of_pos hh, inv_mul_eq_div]
  gcongr
  exact (abs_sub _ _).trans (by linarith)

/-- Integrating the invariance `∫ F dμ = ∫ F (s +ᵥ ·) dμ` over `s ∈ (0, 1]` and applying Fubini. -/
private theorem integral_eq_integral_integral_Ioc [IsFiniteMeasure μ]
    [VAddInvariantMeasure ℝ X μ] {F : X → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    ∫ x, F x ∂μ = ∫ x, (∫ s in Ioc (0 : ℝ) 1, F (s +ᵥ x)) ∂μ := by
  have hint : Integrable (Function.uncurry fun x (s : ℝ) => F (s +ᵥ x))
      (μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    .of_bound (hF.comp (measurable_snd.vadd measurable_fst)).aestronglyMeasurable C
      (ae_of_all _ fun _ => hC _)
  rw [integral_integral_swap hint]
  simp [integral_vadd_eq_self]

/-- The orbit averages of a bounded measurable function converge to it in `L¹(μ)`. -/
private theorem tendsto_integral_abs_orbitAverage_sub [IsFiniteMeasure μ]
    [VAddInvariantMeasure ℝ X μ] (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) :
    Tendsto (fun h => ∫ x, |orbitAverage g h x - g x| ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hmeas (h : ℝ) : Measurable fun p : X × ℝ =>
      |orbitAverage g h (p.2 +ᵥ p.1) - g (p.2 +ᵥ p.1)| :=
    continuous_abs.measurable.comp (((measurable_orbitAverage hg h).sub hg).comp
      (measurable_snd.vadd measurable_fst))
  have hbound {h : ℝ} (hh : 0 < h) (y : X) : ‖|orbitAverage g h y - g y|‖ ≤ 2 :=
    norm_abs_sub_le_two (norm_orbitAverage_le hg1 hh y) (hg1 y)
  have key : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∫ x, |orbitAverage g h x - g x| ∂μ =
      ∫ x, (∫ s in Ioc (0 : ℝ) 1, |orbitAverage g h (s +ᵥ x) - g (s +ᵥ x)|) ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact integral_eq_integral_integral_Ioc
      (continuous_abs.measurable.comp ((measurable_orbitAverage hg h).sub hg))
      (hbound hh)
  rw [tendsto_congr' key]
  rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _x : X, (0 : ℝ) ∂μ) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2) ?_ ?_
    (integrable_const _) (ae_of_all _ fun x => ?_)
  · exact .of_forall fun h =>
      ((hmeas h).stronglyMeasurable.integral_prod_right' (ν := _)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    refine ae_of_all _ fun x => ?_
    have := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ae_of_all _ fun s => hbound hh (s +ᵥ x))
    simpa using this
  rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _s in Ioc (0 : ℝ) 1, (0 : ℝ)) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2)
    (.of_forall fun h => ((hmeas h).comp measurable_prodMk_left).aestronglyMeasurable)
    ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact ae_of_all _ fun s => hbound hh (s +ᵥ x)
  have hi := intervalIntegrable_orbit hg hg1 x
  filter_upwards [ae_restrict_of_ae (hi 0 1).ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Ioc] with s hs hsI
  have hd := hasDerivAt_iff_tendsto_slope_zero.1
    (hs (Ioc_subset_Icc_self.trans Icc_subset_uIcc hsI) 0 left_mem_uIcc)
  have hd' := (hd.mono_left (nhdsWithin_mono _
    (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun _ hu => ne_of_gt hu))).sub_const
    (g (s +ᵥ x)) |>.abs
  rw [sub_self, abs_zero] at hd'
  refine hd'.congr' ?_
  filter_upwards with h
  rw [orbitAverage_vadd, intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _),
    smul_eq_mul]

/-- Comparing `g` and its translate through the orbit average `A_h g`. -/
private theorem integral_abs_vadd_sub_le [IsFiniteMeasure μ] [VAddInvariantMeasure ℝ X μ]
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ∫ x, |g (t +ᵥ x) - g x| ∂μ ≤
      2 * ∫ x, |orbitAverage g h x - g x| ∂μ + 2 * |t| / h * μ.real univ := by
  set a := orbitAverage g h
  have ha := measurable_orbitAverage hg h
  have hint {F : X → ℝ} (hF : Measurable F) (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) : Integrable F μ :=
    .of_bound hF.aestronglyMeasurable C (ae_of_all _ hC)
  have hshift : ∫ x, |a (t +ᵥ x) - g (t +ᵥ x)| ∂μ = ∫ x, |a x - g x| ∂μ :=
    integral_vadd_eq_self (fun y => |a y - g y|)
  have hb (y : X) : ‖|a y - g y|‖ ≤ 2 := norm_abs_sub_le_two (norm_orbitAverage_le hg1 hh y) (hg1 y)
  have iM : Integrable (fun x => |a x - g x|) μ :=
    hint (continuous_abs.measurable.comp (ha.sub hg)) 2 hb
  have iT : Integrable (fun x => |a (t +ᵥ x) - g (t +ᵥ x)|) μ :=
    (measurePreserving_vadd t μ).integrable_comp_of_integrable iM
  have iD : Integrable (fun x => |a (t +ᵥ x) - a x|) μ :=
    hint (continuous_abs.measurable.comp ((ha.comp (measurable_const_vadd t)).sub ha)) 2
      fun x => norm_abs_sub_le_two (norm_orbitAverage_le hg1 hh _) (norm_orbitAverage_le hg1 hh x)
  have iTD : Integrable (fun x => |a (t +ᵥ x) - g (t +ᵥ x)| + |a (t +ᵥ x) - a x|) μ := iT.add iD
  have iG : Integrable (fun x => |g (t +ᵥ x) - g x|) μ :=
    hint (continuous_abs.measurable.comp ((hg.comp (measurable_const_vadd t)).sub hg)) 2
      fun x => norm_abs_sub_le_two (hg1 _) (hg1 x)
  have hD : ∫ x, |a (t +ᵥ x) - a x| ∂μ ≤ 2 * |t| / h * μ.real univ := by
    calc ∫ x, |a (t +ᵥ x) - a x| ∂μ ≤ ∫ _x, 2 * |t| / h ∂μ :=
          integral_mono iD (integrable_const _) fun x => abs_orbitAverage_vadd_sub_le hg hg1 hh t x
      _ = 2 * |t| / h * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  calc ∫ x, |g (t +ᵥ x) - g x| ∂μ
      ≤ ∫ x, (|a (t +ᵥ x) - g (t +ᵥ x)| + |a (t +ᵥ x) - a x|) + |a x - g x| ∂μ := by
        refine integral_mono iG (iTD.add iM) fun x => ?_
        have := dist_triangle4 (g (t +ᵥ x)) (a (t +ᵥ x)) (a x) (g x)
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq,
          abs_sub_comm (g (t +ᵥ x)) (a (t +ᵥ x))] at this
        exact this
    _ = ∫ x, |a x - g x| ∂μ + ∫ x, |a (t +ᵥ x) - a x| ∂μ + ∫ x, |a x - g x| ∂μ := by
        rw [integral_add iTD iM, integral_add iT iD, hshift]
    _ = 2 * ∫ x, |a x - g x| ∂μ + ∫ x, |a (t +ᵥ x) - a x| ∂μ := by ring
    _ ≤ 2 * ∫ x, |a x - g x| ∂μ + 2 * |t| / h * μ.real univ := by gcongr

end OrbitAverage

variable [IsFiniteMeasure μ] [VAddInvariantMeasure ℝ X μ]

/-- For a jointly measurable action of `ℝ` preserving a finite measure `μ`, the measure of the
symmetric difference of a measurable set `A` and its translate `(t +ᵥ ·) ⁻¹' A` tends to `0` as
`t → 0`. -/
theorem tendsto_measure_preimage_vadd_symmDiff {A : Set X} (hA : MeasurableSet A) :
    Tendsto (fun t : ℝ => μ (((t +ᵥ ·) ⁻¹' A) ∆ A)) (𝓝 0) (𝓝 0) := by
  set g : X → ℝ := A.indicator 1
  have hg : Measurable g := measurable_one.indicator hA
  have hg1 (x : X) : ‖g x‖ ≤ 1 := by
    by_cases hx : x ∈ A <;> simp [g, hx]
  have hS (t : ℝ) : MeasurableSet (((t +ᵥ ·) ⁻¹' A) ∆ A) :=
    (measurable_const_vadd t hA).symmDiff hA
  have hreal (t : ℝ) : μ.real (((t +ᵥ ·) ⁻¹' A) ∆ A) = ∫ x, |g (t +ᵥ x) - g x| ∂μ := by
    rw [← integral_indicator_one (hS t)]
    congr 1 with x
    have h := Set.apply_indicator_symmDiff abs_neg ((t +ᵥ ·) ⁻¹' A) A (fun _ ↦ (1 : ℝ)) x
    rw [abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x)] at h
    exact h
  rw [← ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top _ _) ENNReal.zero_ne_top,
    ENNReal.toReal_zero]
  simp only [← measureReal_def, hreal]
  refine tendsto_order.2 ⟨fun a ha => .of_forall fun t =>
    ha.trans_le (integral_nonneg fun _ => abs_nonneg _), fun ε hε => ?_⟩
  obtain ⟨h, hlt, hh⟩ := ((tendsto_integral_abs_orbitAverage_sub (μ := μ) hg hg1).eventually
    (gt_mem_nhds (by positivity : 0 < ε / 4))).and self_mem_nhdsWithin |>.exists
  have hlin : Tendsto (fun t : ℝ => 2 * |t| / h * μ.real univ) (𝓝 0) (𝓝 0) := by
    simpa using (((continuous_abs.tendsto (0 : ℝ)).const_mul 2).div_const h).mul_const
      (μ.real univ)
  filter_upwards [hlin.eventually (gt_mem_nhds (half_pos hε))] with t ht
  calc ∫ x, |g (t +ᵥ x) - g x| ∂μ
      ≤ 2 * ∫ x, |orbitAverage g h x - g x| ∂μ + 2 * |t| / h * μ.real univ :=
        integral_abs_vadd_sub_le hg hg1 hh t
    _ < ε := by linarith

namespace Lp

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Strong continuity of the Koopman representation.** For a jointly measurable action of `ℝ`
preserving a finite measure `μ` and `p ≠ ∞`, the orbit `t ↦ f ∘ (t +ᵥ ·)` of every `f ∈ Lᵖ(μ)`
is continuous from `ℝ` to `Lᵖ(μ)`. -/
theorem continuous_compMeasurePreserving_vadd (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun t : ℝ => compMeasurePreserving (t +ᵥ ·) (measurePreserving_vadd t μ) f := by
  have hp₀ : p ≠ 0 := (one_pos.trans_le Fact.out).ne'
  have H : Continuous fun ft : Lp E p μ × ℝ =>
      compMeasurePreserving (ft.2 +ᵥ ·) (measurePreserving_vadd ft.2 μ) ft.1 := by
    refine continuous_prod_of_dense_continuous_lipschitzWith _ 1 (simpleFunc.dense hp) ?_
      fun t => (isometry_compMeasurePreserving (measurePreserving_vadd t μ)).lipschitzWith
    intro f hf
    lift f to simpleFunc E p μ using hf
    induction f using simpleFunc.induction hp₀ hp with
    | add hfp hgp _ ihf ihg => exact ihf.add ihg
    | @indicatorConst c s hs hμs =>
      dsimp only [simpleFunc.coe_indicatorConst, indicatorConstLp_compMeasurePreserving]
      refine continuous_indicatorConstLp_set hp fun t₀ => ?_
      have hpre (t : ℝ) : ((t +ᵥ ·) ⁻¹' s) ∆ ((t₀ +ᵥ ·) ⁻¹' s) =
          (t₀ +ᵥ ·) ⁻¹' ((((t - t₀) +ᵥ ·) ⁻¹' s) ∆ s) := by
        ext x
        simp [Set.mem_symmDiff, vadd_vadd]
      simp_rw [hpre, (measurePreserving_vadd t₀ μ).measure_preimage
        ((measurable_const_vadd _ hs).symmDiff hs).nullMeasurableSet]
      exact (tendsto_measure_preimage_vadd_symmDiff hs).comp
        (tendsto_sub_nhds_zero_iff.2 tendsto_id)
  exact H.comp (continuous_const.prodMk continuous_id)

end Lp

end MeasureTheory

namespace TauCeti

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] [MeasurableVAdd₂ ℝ X]
  (μ : Measure X) [IsFiniteMeasure μ] [VAddInvariantMeasure ℝ X μ]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The Koopman group `U_t f = f ∘ (t +ᵥ ·)` of a jointly measurable action of `ℝ` preserving a
finite measure `μ`, as a strongly continuous group on `Lᵖ(μ)` for `p ≠ ∞`. -/
def koopmanGroup (hp : p ≠ ∞) : Semigroups.StronglyContinuousGroup (Lp E p μ) where
  toFun t :=
    (Lp.compMeasurePreservingₗᵢ ℝ (t +ᵥ ·) (measurePreserving_vadd t μ)).toContinuousLinearMap
  map_zero' := by
    ext f : 1
    exact (Subtype.ext (f.val.compMeasurePreserving_congr (measurePreserving_vadd 0 μ)
      measurable_id (.of_forall fun x => zero_vadd ℝ x))).trans
      (Lp.compMeasurePreserving_id_apply f)
  map_add' s t := by
    ext f : 1
    have h : (fun x : X => (s + t) +ᵥ x) = (t +ᵥ ·) ∘ (s +ᵥ ·) := by
      ext x
      rw [add_comm s t, add_vadd]
      rfl
    exact (Subtype.ext (f.val.compMeasurePreserving_congr (measurePreserving_vadd (s + t) μ)
      ((measurable_const_vadd t).comp (measurable_const_vadd s)) (.of_forall (congrFun h)))).trans
      (Lp.compMeasurePreserving_comp_apply f _ _)
  continuousAt_zero' f := (Lp.continuous_compMeasurePreserving_vadd hp f).continuousAt

/-- The Koopman operator at time `t` is the pullback along `(t +ᵥ ·)`. -/
theorem koopmanGroup_apply (hp : p ≠ ∞) (t : ℝ) (f : Lp E p μ) :
    koopmanGroup μ E p hp t f = Lp.compMeasurePreserving (t +ᵥ ·) (measurePreserving_vadd t μ) f :=
  (rfl)

/-- On complex `L²(μ)` the Koopman group is unitary. -/
theorem koopmanGroup_isUnitary :
    Semigroups.StronglyContinuousGroup.IsUnitary (H := Lp ℂ 2 μ)
      (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) :=
  .intro fun t f g =>
    (Lp.compMeasurePreservingₗᵢ ℂ (t +ᵥ ·) (measurePreserving_vadd t μ)).inner_map_map f g

end TauCeti

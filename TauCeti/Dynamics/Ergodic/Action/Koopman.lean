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
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv
import TauCeti.MeasureTheory.Group.Integral

/-!
# The Koopman group of a measurable action of `ℝ`

Let `ℝ` act on a measurable space `X`, jointly measurably (`MeasurableVAdd₂ ℝ X`), preserving an
s-finite measure `μ`. Each translate `(t +ᵥ ·)` is measure preserving, so it pulls `Lᵖ(μ)` back to
itself (`MeasureTheory.Lp.compMeasurePreserving`). For `1 ≤ p < ∞` the orbit
`t ↦ f ∘ (t +ᵥ ·)` of every `f ∈ Lᵖ(μ)` is continuous. No topology on `X` and no separability
are assumed.

The density argument reducing to indicators of measurable sets follows the proof of Mathlib's
`MeasureTheory.Lp.compMeasurePreserving_continuous`. For a measurable set `A` of finite measure it
remains to show `μ (((t +ᵥ ·) ⁻¹' A) ∆ A) → 0` as `t → 0`. For `g = 1_A` the orbit averages
`A_h g x = h⁻¹ ∫₀ʰ g (r +ᵥ x) dr` satisfy `∫ |A_h g (t +ᵥ x) - A_h g x| dμ ≤ 2 |t| μ(A) / h` by
invariance of `μ` and Fubini, and `∫ |A_h g - g| dμ → 0` as `h → 0⁺`: by invariance and Fubini this
integral is the integral over `x` of `∫₀¹ |A_h g (s +ᵥ x) - g (s +ᵥ x)| ds`, which tends to `0` for
every `x` by the Lebesgue differentiation theorem along the orbit of `x` and dominated convergence,
and is dominated by `2 ∫₀² g (u +ᵥ x) du`.

## Main results

* `MeasureTheory.tendsto_measure_preimage_vadd_symmDiff`: the measure of `((t +ᵥ ·) ⁻¹' A) ∆ A`
  tends to `0` as `t → 0`;
* `MeasureTheory.Lp.continuous_compMeasurePreserving_vadd`: the Koopman orbits are continuous
  from `ℝ` to `Lᵖ(μ)` for `p ≠ ∞`;
* `TauCeti.koopmanGroup`: the Koopman operators as a strongly continuous group on `Lᵖ(μ)`;
  `TauCeti.koopmanGroup_isUnitary`: on `L²(μ)` with values in a complex inner product space,
  such as complex `L²(μ)`, it is unitary;
* `TauCeti.koopmanGroup_indicatorConstLp`: the Koopman operator at time `t` sends the indicator
  of `A` to the indicator of `(t +ᵥ ·)⁻¹' A`.

The s-finiteness of `μ` cannot be dropped: for the action of `ℝ` on itself by translation with
counting measure, which is not s-finite, `‖1_{{-t}} - 1_{{0}}‖₂ = √2` for every `t ≠ 0`. Joint
measurability cannot be dropped either: translating `AddCircle 1` by `φ t` for a discontinuous
additive `φ : ℝ → ℝ` preserves Haar measure, but the orbit `t ↦ exp(2πiφ(t)) e₁` of the unit mode
is discontinuous.
-/

public section

noncomputable section

open Filter Set
open scoped Topology ENNReal symmDiff Interval

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

/-- A measurable function bounded by `1` is integrable along every orbit over a set of times of
finite measure. -/
private theorem integrableOn_orbit (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) (x : X)
    {s : Set ℝ} (hs : volume s ≠ ∞) : IntegrableOn (fun r : ℝ => g (r +ᵥ x)) s :=
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hs
  (integrable_const (1 : ℝ)).mono' (hg.comp (measurable_vadd_const x)).aestronglyMeasurable
    (ae_of_all _ fun _ => hg1 _)

private theorem intervalIntegrable_orbit (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) (x : X)
    (a b : ℝ) : IntervalIntegrable (fun r : ℝ => g (r +ᵥ x)) volume a b :=
  ⟨integrableOn_orbit hg hg1 x measure_Ioc_lt_top.ne,
    integrableOn_orbit hg hg1 x measure_Ioc_lt_top.ne⟩

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
  have heq : orbitAverage g h = fun x =>
      h⁻¹ * ((∫ r in Ioc 0 h, g (r +ᵥ x)) - ∫ r in Ioc h 0, g (r +ᵥ x)) := by
    funext x
    rw [orbitAverage, intervalIntegral]
  rw [heq]
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

/-- The orbit averages of `g` are integrable along every orbit over a set of times of finite
measure. -/
private theorem integrableOn_orbitAverage (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) {h : ℝ}
    (hh : 0 < h) (x : X) {s : Set ℝ} (hs : volume s ≠ ∞) :
    IntegrableOn (fun r : ℝ => orbitAverage g h (r +ᵥ x)) s :=
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hs
  (integrable_const (1 : ℝ)).mono' ((measurable_orbitAverage hg h).comp
    (measurable_vadd_const x)).aestronglyMeasurable
    (ae_of_all _ fun _ => norm_orbitAverage_le hg1 hh _)

/-- Moving the time window by `t` changes the orbit average by at most the mass of `g` on two
time windows of length `|t|`. -/
private theorem abs_orbitAverage_vadd_sub_le (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) {h : ℝ}
    (hh : 0 < h) (t : ℝ) (x : X) :
    |orbitAverage g h (t +ᵥ x) - orbitAverage g h x| ≤
      h⁻¹ * ((∫ r in Ι h (t + h), ‖g (r +ᵥ x)‖) + ∫ r in Ι 0 t, ‖g (r +ᵥ x)‖) := by
  have hi := intervalIntegrable_orbit hg hg1 x
  rw [orbitAverage_vadd, orbitAverage, ← mul_sub,
    intervalIntegral.integral_interval_sub_interval_comm' (hi _ _) (hi _ _) (hi _ _),
    abs_mul, abs_inv, abs_of_pos hh]
  gcongr
  exact (abs_sub _ _).trans (add_le_add
    ((Real.norm_eq_abs _).symm.trans_le intervalIntegral.norm_integral_le_integral_norm_uIoc)
    ((Real.norm_eq_abs _).symm.trans_le intervalIntegral.norm_integral_le_integral_norm_uIoc))

/-- The orbit averages of an integrable function are integrable. -/
private theorem integrable_orbitAverage [SFinite μ] [VAddInvariantMeasure ℝ X μ]
    (hgi : Integrable g μ) {h : ℝ} (hh : 0 < h) :
    Integrable (orbitAverage g h) μ := by
  refine (((TauCeti.integrable_vadd_prod (ν := volume.restrict (Ioc 0 h)) hgi).integral_prod_left
    ).const_mul h⁻¹).congr (ae_of_all _ fun x => ?_)
  simp [orbitAverage, intervalIntegral.integral_of_le hh.le]

/-- For `0 ≤ g` and `h ≤ 1`, the orbit averages over the times `(0, 1]` carry at most the mass of
`g` over the times `(0, 2]`. -/
private theorem integral_orbitAverage_vadd_le (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x, ‖g x‖ ≤ 1) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (x : X) :
    ∫ s in Ioc (0 : ℝ) 1, orbitAverage g h (s +ᵥ x) ≤ ∫ u in Ioc (0 : ℝ) 2, g (u +ᵥ x) := by
  have hG : Measurable fun u : ℝ => g (u +ᵥ x) := hg.comp (measurable_vadd_const x)
  have hA (s : ℝ) : orbitAverage g h (s +ᵥ x) = h⁻¹ * ∫ r in Ioc 0 h, g ((r + s) +ᵥ x) := by
    simp only [orbitAverage, intervalIntegral.integral_of_le hh.le, add_vadd]
  have hswap : ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc 0 h, g ((r + s) +ᵥ x) =
      ∫ r in Ioc 0 h, ∫ s in Ioc (0 : ℝ) 1, g ((r + s) +ᵥ x) :=
    integral_integral_swap <| (integrable_const (1 : ℝ)).mono'
      (hG.comp (measurable_snd.add measurable_fst)).aestronglyMeasurable
      (ae_of_all _ fun _ => hg1 _)
  have hin (r : ℝ) (hr : r ∈ Ioc 0 h) :
      ∫ s in Ioc (0 : ℝ) 1, g ((r + s) +ᵥ x) ≤ ∫ u in Ioc (0 : ℝ) 2, g (u +ᵥ x) := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_add_left (fun u => g (u +ᵥ x)), add_zero,
      intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set (integrableOn_orbit hg hg1 x measure_Ioc_lt_top.ne)
      (.of_forall fun _ => hg0 _)
      (.of_forall fun _ hu => Ioc_subset_Ioc (by linarith [hr.1]) (by linarith [hr.2]) hu)
  calc ∫ s in Ioc (0 : ℝ) 1, orbitAverage g h (s +ᵥ x)
      = h⁻¹ * ∫ r in Ioc 0 h, ∫ s in Ioc (0 : ℝ) 1, g ((r + s) +ᵥ x) := by
        simp_rw [hA]
        rw [integral_const_mul, hswap]
    _ ≤ h⁻¹ * ∫ _r in Ioc 0 h, ∫ u in Ioc (0 : ℝ) 2, g (u +ᵥ x) :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (.of_forall fun _ => integral_nonneg fun _ => hg0 _) (integrable_const _)
          ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall hin))) (inv_nonneg.2 hh.le)
    _ = ∫ u in Ioc (0 : ℝ) 2, g (u +ᵥ x) := by
        rw [setIntegral_const, smul_eq_mul, ← mul_assoc]
        simp [Real.volume_real_Ioc_of_le hh.le, hh.ne']

/-- Lebesgue differentiation along the orbit of `x`: the orbit averages of `g` converge to `g` in
`L¹` over the times `(0, 1]`. -/
private theorem tendsto_integral_abs_orbitAverage_vadd_sub (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ 1) (x : X) :
    Tendsto (fun h => ∫ s in Ioc (0 : ℝ) 1, |orbitAverage g h (s +ᵥ x) - g (s +ᵥ x)|)
      (𝓝[>] 0) (𝓝 0) := by
  rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _s in Ioc (0 : ℝ) 1, (0 : ℝ)) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2)
    (.of_forall fun h => (continuous_abs.measurable.comp (((measurable_orbitAverage hg h).sub
      hg).comp (measurable_vadd_const x))).aestronglyMeasurable) ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact ae_of_all _ fun s => norm_abs_sub_le_two (norm_orbitAverage_le hg1 hh _) (hg1 _)
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

/-- The orbit averages of an integrable function with values in `[0, 1]` converge to it in
`L¹(μ)`. -/
private theorem tendsto_integral_abs_orbitAverage_sub [SFinite μ] [VAddInvariantMeasure ℝ X μ]
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, ‖g x‖ ≤ 1) (hgi : Integrable g μ) :
    Tendsto (fun h => ∫ x, |orbitAverage g h x - g x| ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hmeas (h : ℝ) : Measurable fun y => |orbitAverage g h y - g y| :=
    continuous_abs.measurable.comp ((measurable_orbitAverage hg h).sub hg)
  have key : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∫ x, |orbitAverage g h x - g x| ∂μ =
      ∫ x, (∫ s in Ioc (0 : ℝ) 1, |orbitAverage g h (s +ᵥ x) - g (s +ᵥ x)|) ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [TauCeti.integral_integral_vadd_eq (F := fun y => |orbitAverage g h y - g y|)
      ((integrable_orbitAverage hgi hh).sub hgi).abs]
    simp
  rw [tendsto_congr' key, show (𝓝 (0 : ℝ)) = 𝓝 (∫ _x : X, (0 : ℝ) ∂μ) by simp]
  have hmeas' (h : ℝ) : StronglyMeasurable fun p : X × ℝ =>
      |orbitAverage g h (p.2 +ᵥ p.1) - g (p.2 +ᵥ p.1)| :=
    ((hmeas h).comp (measurable_snd.vadd measurable_fst)).stronglyMeasurable
  -- Dominate by twice the mass of `g` along the orbit over the times `(0, 2]`.
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => 2 * ∫ u in Ioc (0 : ℝ) 2, g (u +ᵥ x))
    (.of_forall fun h => ((hmeas' h).integral_prod_right' (ν := _)).aestronglyMeasurable) ?_
    (((TauCeti.integrable_vadd_prod hgi).integral_prod_left).const_mul 2)
    (ae_of_all _ fun x => tendsto_integral_abs_orbitAverage_vadd_sub hg hg1 x)
  filter_upwards [Ioo_mem_nhdsGT one_pos] with h hh
  refine ae_of_all _ fun x => ?_
  have hA0 (s : ℝ) : 0 ≤ orbitAverage g h (s +ᵥ x) :=
    mul_nonneg (inv_nonneg.2 hh.1.le) (intervalIntegral.integral_nonneg hh.1.le fun _ _ => hg0 _)
  have iA := integrableOn_orbitAverage hg hg1 hh.1 x (measure_Ioc_lt_top (a := (0 : ℝ)) (b := 1)).ne
  have iG (b : ℝ) : IntegrableOn (fun s : ℝ => g (s +ᵥ x)) (Ioc 0 b) :=
    integrableOn_orbit hg hg1 x measure_Ioc_lt_top.ne
  have h₁ := integral_orbitAverage_vadd_le hg hg0 hg1 hh.1 hh.2.le x
  have h₂ : ∫ s in Ioc (0 : ℝ) 1, g (s +ᵥ x) ≤ ∫ u in Ioc (0 : ℝ) 2, g (u +ᵥ x) :=
    setIntegral_mono_set (iG 2) (.of_forall fun _ => hg0 _)
      (.of_forall fun _ hu => Ioc_subset_Ioc_right one_le_two hu)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  calc ∫ s in Ioc (0 : ℝ) 1, |orbitAverage g h (s +ᵥ x) - g (s +ᵥ x)|
      ≤ ∫ s in Ioc (0 : ℝ) 1, (orbitAverage g h (s +ᵥ x) + g (s +ᵥ x)) :=
        integral_mono (iA.sub (iG 1)).abs (iA.add (iG 1)) fun s =>
          abs_sub_le_iff.2 ⟨by linarith [hg0 (s +ᵥ x)], by linarith [hA0 s]⟩
    _ ≤ 2 * ∫ u in Ioc (0 : ℝ) 2, g (u +ᵥ x) := by
        rw [integral_add iA (iG 1)]
        linarith

/-- Integrating `abs_orbitAverage_vadd_sub_le` over `x` with Fubini and invariance. -/
private theorem integral_abs_orbitAverage_vadd_sub_le [SFinite μ] [VAddInvariantMeasure ℝ X μ]
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) (hgi : Integrable g μ) {h : ℝ} (hh : 0 < h)
    (t : ℝ) :
    ∫ x, |orbitAverage g h (t +ᵥ x) - orbitAverage g h x| ∂μ ≤ 2 * |t| / h * ∫ x, ‖g x‖ ∂μ := by
  have (c d : ℝ) : IsFiniteMeasure (volume.restrict (Ι c d)) :=
    Real.isFiniteMeasure_restrict_Ioc _ _
  have iA := integrable_orbitAverage hgi hh
  have i₁ := (TauCeti.integrable_vadd_prod (ν := volume.restrict (Ι h (t + h)))
    hgi.norm).integral_prod_left
  have i₂ := (TauCeti.integrable_vadd_prod (ν := volume.restrict (Ι 0 t))
    hgi.norm).integral_prod_left
  calc ∫ x, |orbitAverage g h (t +ᵥ x) - orbitAverage g h x| ∂μ
      ≤ ∫ x, h⁻¹ * ((∫ r in Ι h (t + h), ‖g (r +ᵥ x)‖) + ∫ r in Ι 0 t, ‖g (r +ᵥ x)‖) ∂μ :=
        integral_mono (((measurePreserving_vadd t μ).integrable_comp_of_integrable iA).sub iA).abs
          ((i₁.add i₂).const_mul _) fun x => abs_orbitAverage_vadd_sub_le hg hg1 hh t x
    _ = 2 * |t| / h * ∫ x, ‖g x‖ ∂μ := by
        rw [integral_const_mul, integral_add i₁ i₂, TauCeti.integral_integral_vadd_eq hgi.norm,
          TauCeti.integral_integral_vadd_eq hgi.norm]
        simp only [smul_eq_mul, Measure.real, Real.volume_uIoc, Measure.restrict_apply_univ,
          ENNReal.toReal_ofReal (abs_nonneg _), sub_zero, add_sub_cancel_right]
        ring

/-- Comparing `g` and its translate through the orbit average `A_h g`. -/
private theorem integral_abs_vadd_sub_le [SFinite μ] [VAddInvariantMeasure ℝ X μ]
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ 1) (hgi : Integrable g μ) {h : ℝ} (hh : 0 < h)
    (t : ℝ) :
    ∫ x, |g (t +ᵥ x) - g x| ∂μ ≤
      2 * ∫ x, |orbitAverage g h x - g x| ∂μ + 2 * |t| / h * ∫ x, ‖g x‖ ∂μ := by
  set a := orbitAverage g h
  have hT := measurePreserving_vadd t μ
  have hshift : ∫ x, |a (t +ᵥ x) - g (t +ᵥ x)| ∂μ = ∫ x, |a x - g x| ∂μ :=
    integral_vadd_eq_self (fun y => |a y - g y|)
  have iA := integrable_orbitAverage hgi hh
  have iM : Integrable (fun x => |a x - g x|) μ := (iA.sub hgi).abs
  have iT : Integrable (fun x => |a (t +ᵥ x) - g (t +ᵥ x)|) μ :=
    hT.integrable_comp_of_integrable iM
  have iD : Integrable (fun x => |a (t +ᵥ x) - a x|) μ :=
    ((hT.integrable_comp_of_integrable iA).sub iA).abs
  have iTD : Integrable (fun x => |a (t +ᵥ x) - g (t +ᵥ x)| + |a (t +ᵥ x) - a x|) μ := iT.add iD
  have iG : Integrable (fun x => |g (t +ᵥ x) - g x|) μ :=
    ((hT.integrable_comp_of_integrable hgi).sub hgi).abs
  have hD := integral_abs_orbitAverage_vadd_sub_le hg hg1 hgi hh t
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
    _ ≤ 2 * ∫ x, |a x - g x| ∂μ + 2 * |t| / h * ∫ x, ‖g x‖ ∂μ := by gcongr

end OrbitAverage

variable [SFinite μ] [VAddInvariantMeasure ℝ X μ]

/-- For a jointly measurable action of `ℝ` preserving an s-finite measure `μ`, the measure of the
symmetric difference of a measurable set `A` of finite measure and its translate `(t +ᵥ ·) ⁻¹' A`
tends to `0` as `t → 0`. -/
theorem tendsto_measure_preimage_vadd_symmDiff {A : Set X} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) : Tendsto (fun t : ℝ => μ (((t +ᵥ ·) ⁻¹' A) ∆ A)) (𝓝 0) (𝓝 0) := by
  set g : X → ℝ := A.indicator 1
  have hg : Measurable g := measurable_one.indicator hA
  have hg0 (x : X) : 0 ≤ g x := Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hg1 (x : X) : ‖g x‖ ≤ 1 := by
    by_cases hx : x ∈ A <;> simp [g, hx]
  have hgi : Integrable g μ := (integrable_indicator_iff hA).2 (integrableOn_const hμA)
  have hS (t : ℝ) : MeasurableSet (((t +ᵥ ·) ⁻¹' A) ∆ A) :=
    (measurable_const_vadd t hA).symmDiff hA
  have hfin (t : ℝ) : μ (((t +ᵥ ·) ⁻¹' A) ∆ A) ≠ ∞ := by
    refine ((measure_mono symmDiff_subset_union).trans_lt (measure_union_lt_top ?_
      hμA.lt_top)).ne
    rw [(measurePreserving_vadd t μ).measure_preimage hA.nullMeasurableSet]
    exact hμA.lt_top
  have hreal (t : ℝ) : μ.real (((t +ᵥ ·) ⁻¹' A) ∆ A) = ∫ x, |g (t +ᵥ x) - g x| ∂μ := by
    rw [← integral_indicator_one (hS t)]
    congr 1 with x
    have h := Set.apply_indicator_symmDiff abs_neg ((t +ᵥ ·) ⁻¹' A) A (fun _ ↦ (1 : ℝ)) x
    rw [abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x)] at h
    exact h
  rw [← ENNReal.tendsto_toReal_iff hfin ENNReal.zero_ne_top, ENNReal.toReal_zero]
  simp only [← measureReal_def, hreal]
  refine tendsto_order.2 ⟨fun a ha => .of_forall fun t =>
    ha.trans_le (integral_nonneg fun _ => abs_nonneg _), fun ε hε => ?_⟩
  obtain ⟨h, hlt, hh⟩ := ((tendsto_integral_abs_orbitAverage_sub (μ := μ) hg hg0 hg1
    hgi).eventually (gt_mem_nhds (by positivity : 0 < ε / 4))).and self_mem_nhdsWithin |>.exists
  have hlin : Tendsto (fun t : ℝ => 2 * |t| / h * ∫ x, ‖g x‖ ∂μ) (𝓝 0) (𝓝 0) := by
    simpa using (((continuous_abs.tendsto (0 : ℝ)).const_mul 2).div_const h).mul_const
      (∫ x, ‖g x‖ ∂μ)
  filter_upwards [hlin.eventually (gt_mem_nhds (half_pos hε))] with t ht
  calc ∫ x, |g (t +ᵥ x) - g x| ∂μ
      ≤ 2 * ∫ x, |orbitAverage g h x - g x| ∂μ + 2 * |t| / h * ∫ x, ‖g x‖ ∂μ :=
        integral_abs_vadd_sub_le hg hg1 hgi hh t
    _ < ε := by linarith

namespace Lp

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Strong continuity of the Koopman representation.** For a jointly measurable action of `ℝ`
preserving an s-finite measure `μ` and `p ≠ ∞`, the orbit `t ↦ f ∘ (t +ᵥ ·)` of every
`f ∈ Lᵖ(μ)` is continuous from `ℝ` to `Lᵖ(μ)`. The density argument follows the proof of Mathlib's
`MeasureTheory.Lp.compMeasurePreserving_continuous`. -/
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
      exact (tendsto_measure_preimage_vadd_symmDiff hs hμs.ne).comp
        (tendsto_sub_nhds_zero_iff.2 tendsto_id)
  exact H.comp (continuous_const.prodMk continuous_id)

end Lp

end MeasureTheory

namespace TauCeti

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] [MeasurableVAdd₂ ℝ X]
  (μ : Measure X) [SFinite μ] [VAddInvariantMeasure ℝ X μ]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The Koopman group `U_t f = f ∘ (t +ᵥ ·)` of a jointly measurable action of `ℝ` preserving an
s-finite measure `μ`, as a strongly continuous group on `Lᵖ(μ)` for `p ≠ ∞`. -/
def koopmanGroup (hp : p ≠ ∞) : Semigroups.StronglyContinuousGroup (Lp E p μ) where
  toFun t :=
    (Lp.compMeasurePreservingₗᵢ ℝ (t +ᵥ ·) (measurePreserving_vadd t μ)).toContinuousLinearMap
  map_zero' := by
    ext f : 1
    simp only [LinearIsometry.coe_toContinuousLinearMap, Lp.compMeasurePreservingₗᵢ_apply,
      zero_vadd, ContinuousLinearMap.id_apply]
    exact Lp.compMeasurePreserving_id_apply f
  map_add' s t := by
    ext f : 1
    have h : (fun x : X => (s + t) +ᵥ x) = (t +ᵥ ·) ∘ (s +ᵥ ·) := by
      ext x
      rw [add_comm s t, add_vadd]
      rfl
    simp only [LinearIsometry.coe_toContinuousLinearMap, Lp.compMeasurePreservingₗᵢ_apply, h,
      ContinuousLinearMap.comp_apply]
    exact Lp.compMeasurePreserving_comp_apply f _ _
  continuousAt_zero' f := (Lp.continuous_compMeasurePreserving_vadd hp f).continuousAt

/-- The Koopman operator at time `t` is the pullback along `(t +ᵥ ·)`. -/
@[simp]
theorem koopmanGroup_apply (hp : p ≠ ∞) (t : ℝ) (f : Lp E p μ) :
    koopmanGroup μ E p hp t f = Lp.compMeasurePreserving (t +ᵥ ·) (measurePreserving_vadd t μ) f :=
  (rfl)

/-- The Koopman operator at time `t` sends the indicator of `A` to the indicator of
`(t +ᵥ ·)⁻¹' A`. -/
theorem koopmanGroup_indicatorConstLp (hp : p ≠ ∞) {A : Set X} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : E) (t : ℝ) :
    koopmanGroup μ E p hp t (indicatorConstLp p hA hμA c) =
      indicatorConstLp p (hA.preimage (measurable_const_vadd t))
        (by rwa [(measurePreserving_vadd t μ).measure_preimage hA.nullMeasurableSet]) c :=
  Lp.indicatorConstLp_compMeasurePreserving hA hμA c (measurePreserving_vadd t μ)

/-- On `L²(μ)` with values in a complex inner product space, such as complex `L²(μ)`, the Koopman
group is unitary. -/
theorem koopmanGroup_isUnitary (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Semigroups.StronglyContinuousGroup.IsUnitary (H := Lp F 2 μ)
      (koopmanGroup μ F 2 ENNReal.ofNat_ne_top) :=
  .intro fun t f g =>
    (Lp.compMeasurePreservingₗᵢ ℂ (t +ᵥ ·) (measurePreserving_vadd t μ)).inner_map_map f g

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Data.Set.SymmDiff
-- Proof-only: integrability of a real power on a bounded interval.
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- Proof-only: the layer-cake formula for a power and the power integral on `(0, a)`.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
-- Proof-only: the integrability of indicators of bounded intervals.
import TauCeti.MeasureTheory.Integral.Bochner.Set
-- Proof-only: a subsequence of functions with vanishing integrals tends to `0` a.e.
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence

/-!
# Layer-cake formulas for products, distances, and moments

For two nonnegative measurable functions, their product integral is the double integral of the
measures of intersections of their strict superlevel sets. This is the two-function form of the
layer-cake formula and is useful for comparing pairings through level-set geometry.

This file expresses the `L¹` distance between two almost everywhere measurable real functions as
the integral, over all levels, of the measure of the symmetric difference of their sublevel sets.
Consequently, along a subsequence of an `L¹`-convergent sequence the superlevel sets converge in
measure at almost every level. Averaging the same identity over the levels shows that, if finitely
many functions are close in `L¹` to a nonnegative function `p`, then some superlevel set of `p` has
small total boundary relative to its measure; for counting measure this produces Følner sets from
almost invariant finitely supported functions.
Thresholding a real function at a level `t` with `δ ≤ t ≤ 1 - δ`, where `δ > 0`,
approximates a set in measure with error at most its `L¹` distance from the set's indicator
divided by `δ`.
It also expresses the integral of the positive part `(g - f)⁺` as the integral, over all levels
`s`, of the measure of the set where `f ≤ s < g`: the one-sided form, which sees which of the two
functions lies above the level. Its extended version expresses the integral of the truncated
difference `f - g` of two `ℝ≥0∞`-valued functions through the differences of their strict
superlevel sets.

For `1 < p` it writes the power `|x - y| ^ p` as a mixture of *hinges*: it is the
integral over the thresholds `r > 0`, with weight `p (p - 1) r ^ (p - 2)`, of
`(y - x - r)⁺ + (x - y - r)⁺`. Integrated against a measure, this turns the `p`-th moment of a
difference into a mixture of one-sided integrals of the form above. The same mixture represents
`d ^ p` for every `d : ℝ≥0∞`, with truncated subtraction.

Finally, it records the signed layer-cake representation of a real number,
`a = ∫ (1_{t < a} - 1_{t < 0}) dt`, which applied pointwise to a real function `u` writes it as
the integral over all levels `t` of the indicators of its superlevel sets `{u > t}`, corrected by
`1_{t < 0}` so that the integrand is integrable.

The truncated power formula `∫ min(f, k) ^ p = p ∫_0^k m {f > t} t ^ (p - 1) dt` is recorded
together with the measurability of the distribution function `t ↦ m {f > t}`. The truncation lets
a layer-cake argument work with finite quantities; monotone convergence removes it again, and the
truncated integrals `∫ g ^ q min(g, k) ^ δ` increase to `∫ g ^ (q + δ)` as `k → ∞`.

For positive real powers on a finite measure space, it also characterizes integrability by the
weighted strict tail `μ.real {x | t < f x} * t ^ (p - 1)`, either on `(0, ∞)` or at infinity.
The weighted tail is measurable without any measurability assumption on `f`, and its contribution
from bounded thresholds is integrable. For measures on the nonnegative half-line, the integral
of the shifted tail is the extended integral of a truncated difference. A finite first moment
therefore makes every shifted tail integrable.

## Main statements

* `TauCeti.lintegral_mul_eq_lintegral_lintegral_measure_inter` — the integral of a product of
  nonnegative functions, as a double integral of intersections of superlevel sets;
* `TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff` — the `L¹` distance of two real
  functions, level by level;
* `MeasureTheory.Measure.lintegral_enorm_sub_eq_lintegral_measure_symmDiff_setOf_lt` — the same
  identity with strict superlevel sets;
* `MeasureTheory.Measure.measure_symmDiff_setOf_lt_indicator_le` — a uniform bound on the
  measure error of thresholding at levels separated from `0` and `1`, in terms of the `L¹`
  distance from a set's indicator;
* `MeasureTheory.Measure.exists_pos_sum_measure_symmDiff_lt_mul_measure` — a superlevel set of
  `p` whose total boundary relative to finitely many `L¹`-close functions is small compared with
  its measure;
* `MeasureTheory.Measure.exists_strictMono_ae_tendsto_measure_symmDiff_setOf_lt` — along a
  subsequence of an `L¹`-convergent sequence, the superlevel sets converge in measure at almost
  every level;
* `MeasureTheory.Measure.measurable_measure_ofReal_lt` — the distribution function
  `t ↦ m {f > t}` is measurable;
* `MeasureTheory.Measure.lintegral_min_rpow_eq` — the integral of a truncated power
  `min f k ^ p`, level by level up to the cap `k`;
* `MeasureTheory.Measure.tendsto_lintegral_mul_min_rpow` — the truncated integrals
  `∫ g ^ q min(g, k) ^ δ` increase to `∫ g ^ (q + δ)` as `k → ∞`;
* `TauCeti.lintegral_ofReal_sub_eq_lintegral_measure` — the integral of a positive part
  `(g - f)⁺`, level by level;
* `TauCeti.lintegral_sub_eq_lintegral_measure_sdiff` — the integral of a truncated difference
  `f - g` of extended functions, level by level;
* `TauCeti.ofReal_rpow_eq_lintegral_mul_ofReal_sub`, `TauCeti.rpow_eq_lintegral_mul_sub` and
  `TauCeti.edist_rpow_eq_lintegral` — a real or extended power `d ^ p`, and the power
  `|x - y| ^ p` of a distance, as mixtures of hinges.
* `TauCeti.lintegral_ofReal_sub_sub_eq` and `TauCeti.lintegral_edist_rpow_eq` — their integrated
  forms for a measure on pairs of real variables;
* `TauCeti.integral_indicator_Iio_sub_indicator_Iio_zero` — the signed layer-cake representation
  `a = ∫ (1_{t < a} - 1_{t < 0}) dt` of a real number, with
  `TauCeti.integral_abs_indicator_Iio_sub_indicator_Iio_zero` computing the `L¹` norm `|a|` of
  its integrand;
* `TauCeti.integrable_rpow_iff_integrableOn_weighted_tail` and
  `TauCeti.integrable_rpow_iff_integrableAtFilter_weighted_tail` — the weighted-tail
  integrability criteria for positive real-power moments.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal symmDiff

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-- **Two-function layer cake.** The integral of the product of two nonnegative functions is the
double integral of the measures of the intersections of their strict superlevel sets:

`∫⁻ x, f x * g x ∂m = ∫⁻ t > 0, ∫⁻ s > 0, m ({ofReal t < f} ∩ {ofReal s < g})`.

The formula allows infinite values and requires no finiteness or σ-finiteness assumption on the
measure. -/
theorem lintegral_mul_eq_lintegral_lintegral_measure_inter (m : Measure α)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    ∫⁻ x, f x * g x ∂m =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        m ({x | ENNReal.ofReal t < f x} ∩ {x | ENNReal.ofReal s < g x}) := by
  let F := hf.mk f
  let G := hg.mk g
  have hF : Measurable F := hf.measurable_mk
  have hG : Measurable G := hg.measurable_mk
  have hfg : (fun x => f x * g x) =ᵐ[m] fun x => F x * G x :=
    hf.ae_eq_mk.fun_mul hg.ae_eq_mk
  have hlevels (s t : ℝ) :
      m ({x | ENNReal.ofReal t < f x} ∩ {x | ENNReal.ofReal s < g x}) =
        m ({x | ENNReal.ofReal t < F x} ∩ {x | ENNReal.ofReal s < G x}) := by
    apply measure_congr
    filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
    simp only [mem_inter_iff, mem_ofPred_eq]
    rw [hfx, hgx]
  have hR :
      (∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        m ({x | ENNReal.ofReal t < f x} ∩ {x | ENNReal.ofReal s < g x})) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        m ({x | ENNReal.ofReal t < F x} ∩ {x | ENNReal.ofReal s < G x}) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    exact setLIntegral_congr_fun measurableSet_Ioi fun t _ => hlevels s t
  rw [lintegral_congr_ae hfg]
  rw [hR]
  have hdensity : (∫⁻ x, F x * G x ∂m) = ∫⁻ x, G x ∂m.withDensity F := by
    symm
    simpa only [Pi.mul_apply] using lintegral_withDensity_eq_lintegral_mul m hF hG
  rw [hdensity]
  have hlayer (ν : Measure α) {u : α → ℝ≥0∞} (hu : AEMeasurable u ν) :
      ∫⁻ x, u x ∂ν = ∫⁻ t in Ioi (0 : ℝ), ν {x | ENNReal.ofReal t < u x} := by
    simpa using lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul ν hu one_pos
  rw [hlayer (m.withDensity F) hG.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  have hGs : MeasurableSet {x | ENNReal.ofReal s < G x} :=
    measurableSet_lt measurable_const hG
  rw [withDensity_apply _ hGs, hlayer (m.restrict {x | ENNReal.ofReal s < G x})
    hF.aemeasurable.restrict]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [Measure.restrict_apply (measurableSet_lt measurable_const hF), inter_comm]

/-- A level lies between two reals exactly when exactly one of them is at most that level. -/
private theorem mem_Ico_min_max_iff {x y s : ℝ} :
    s ∈ Ico (min x y) (max x y) ↔ ((x ≤ s ∧ ¬ y ≤ s) ∨ (y ≤ s ∧ ¬ x ≤ s)) := by
  rw [mem_Ico]
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h]
    refine ⟨fun hs ↦ Or.inl ⟨hs.1, not_le.2 hs.2⟩, ?_⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, not_le.1 h2⟩
    · exact absurd (h.trans h1) h2
  · rw [min_eq_right h, max_eq_left h]
    refine ⟨fun hs ↦ Or.inr ⟨hs.1, not_le.2 hs.2⟩, ?_⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact absurd (h.trans h1) h2
    · exact ⟨h1, not_le.1 h2⟩

private theorem lintegral_enorm_sub_eq_lintegral_measure_symmDiff_of_measurable
    (m : Measure α) [SFinite m] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
  set F : Set (α × ℝ) := {q | min (f q.1) (g q.1) ≤ q.2 ∧ q.2 < max (f q.1) (g q.1)} with hFdef
  have hF : MeasurableSet F :=
    (measurableSet_le ((hf.comp measurable_fst).min (hg.comp measurable_fst)) measurable_snd).inter
      (measurableSet_lt measurable_snd ((hf.comp measurable_fst).max (hg.comp measurable_fst)))
  have hmem_Ico : ∀ (a : α) (s : ℝ),
      (a, s) ∈ F ↔ s ∈ Ico (min (f a) (g a)) (max (f a) (g a)) := by
    intro a s
    simp [hFdef, mem_Ico]
  have hmem_symmDiff : ∀ (a : α) (s : ℝ),
      (a, s) ∈ F ↔ a ∈ ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
    intro a s
    rw [hmem_Ico, Set.mem_symmDiff]
    exact mem_Ico_min_max_iff
  have hlevel : ∀ a : α, (∫⁻ s, F.indicator 1 (a, s)) = ‖f a - g a‖ₑ := by
    intro a
    have hfun : (fun s ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
        = (Ico (min (f a) (g a)) (max (f a) (g a))).indicator 1 := by
      funext s
      by_cases hs : s ∈ Ico (min (f a) (g a)) (max (f a) (g a))
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((hmem_Ico a s).mpr hs), Pi.one_apply,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (fun hq ↦ hs ((hmem_Ico a s).mp hq))]
    rw [hfun, lintegral_indicator_one measurableSet_Ico, Real.volume_Ico, max_sub_min_eq_abs,
      abs_sub_comm, Real.enorm_eq_ofReal_abs]
  have hsection : ∀ s : ℝ,
      (∫⁻ a, F.indicator 1 (a, s) ∂m) = m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
    intro s
    have hmeas : MeasurableSet ({a | f a ≤ s} ∆ {a | g a ≤ s}) :=
      (measurableSet_le hf measurable_const).symmDiff (measurableSet_le hg measurable_const)
    have hfun : (fun a ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
        = ({a | f a ≤ s} ∆ {a | g a ≤ s}).indicator 1 := by
      funext a
      by_cases ha : a ∈ ({a | f a ≤ s} ∆ {a | g a ≤ s})
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ((hmem_symmDiff a s).mpr ha),
          Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem ha,
          Set.indicator_of_notMem (fun hq ↦ ha ((hmem_symmDiff a s).mp hq))]
    rw [hfun, lintegral_indicator_one hmeas]
  calc ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ a, (∫⁻ s, F.indicator 1 (a, s)) ∂m := by
        simp_rw [hlevel]
    _ = ∫⁻ s, (∫⁻ a, F.indicator 1 (a, s) ∂m) :=
        lintegral_lintegral_swap
          (f := fun (a : α) (s : ℝ) ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
          (measurable_const.indicator hF).aemeasurable
    _ = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by simp_rw [hsection]

/-- **The area between two graphs.** The `L¹` distance of two almost everywhere measurable real
functions is the integral, over the levels `s`, of the measure of the set where exactly one of the
two functions is at most `s`. -/
theorem lintegral_enorm_sub_eq_lintegral_measure_symmDiff (m : Measure α) [SFinite m]
    {f g : α → ℝ} (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
  calc
    ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ a, ‖hf.mk f a - hg.mk g a‖ₑ ∂m := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a hfa hga
      rw [hfa, hga]
    _ = ∫⁻ s, m ({a | hf.mk f a ≤ s} ∆ {a | hg.mk g a ≤ s}) :=
      lintegral_enorm_sub_eq_lintegral_measure_symmDiff_of_measurable m hf.measurable_mk
        hg.measurable_mk
    _ = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
      apply lintegral_congr
      intro s
      apply measure_congr
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a hfa hga
      simp only [Set.mem_symmDiff, Set.mem_ofPred_eq]
      rw [hfa, hga]

end TauCeti

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- **The layer cake formula for a truncation.** For `p > 0` and a cap `k`, the integral of
`min f k ^ p` is `p` times the integral of `m {t < f} t ^ (p - 1)` over the heights `0 < t < k`. -/
theorem lintegral_min_rpow_eq (m : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f m) (k : ℝ≥0)
    {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, min (f x) k ^ p ∂m = ENNReal.ofReal p *
      ∫⁻ t in Ioo 0 (k : ℝ), m {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (t ^ (p - 1)) := by
  rw [TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul m (hf.min aemeasurable_const) hp,
    ← Ioi_inter_Iio, inter_comm, ← setLIntegral_indicator measurableSet_Iio]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rcases lt_or_ge t k with htk | htk
  · -- Below the cap, `min (f x) k` exceeds `t` exactly when `f x` does.
    have hk : ENNReal.ofReal t < k := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans ht htk)).2 htk
    rw [indicator_of_mem (by exact htk)]
    simp only [lt_min_iff, hk, and_true]
  · -- At or above the cap, `min (f x) k` never exceeds `t`.
    have hk : (k : ℝ≥0∞) ≤ ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal htk
    have hempty : {x | ENNReal.ofReal t < min (f x) k} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun x hx => not_lt.2 ((min_le_right _ _).trans hk) hx
    rw [indicator_of_notMem (by simpa using htk), hempty, measure_empty, zero_mul]

/-- The distribution function `t ↦ m {f > t}` is measurable, being antitone. -/
theorem measurable_measure_ofReal_lt (m : Measure α) (f : α → ℝ≥0∞) :
    Measurable fun t : ℝ => m {x | ENNReal.ofReal t < f x} :=
  Antitone.measurable fun _ _ htt' =>
    measure_mono fun _ hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htt') hx

open Filter Topology in
/-- **Removing a truncation.** As `k → ∞`, the integrals of `g ^ q min(g, k) ^ δ` increase to the
integral of `g ^ (q + δ)`. -/
theorem tendsto_lintegral_mul_min_rpow (m : Measure α) {g : α → ℝ≥0∞} (hg : Measurable g)
    {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => ∫⁻ x, g x ^ q * min (g x) (k : ℝ≥0) ^ δ ∂m) atTop
      (𝓝 (∫⁻ x, g x ^ (q + δ) ∂m)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun k => ((hg.pow_const q).mul ((hg.min measurable_const).pow_const δ)).aemeasurable)
    (ae_of_all _ fun x k k' hkk' => ?_) (ae_of_all _ fun x => ?_)
  · dsimp only
    gcongr
  · have hmin : Tendsto (fun k : ℕ => min (g x) ((k : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 (g x)) := by
      simpa using tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top
    have hpow := (ENNReal.continuous_rpow_const (y := δ)).tendsto (g x) |>.comp hmin
    rw [ENNReal.rpow_add_of_nonneg _ _ hq hδ.le]
    refine ENNReal.Tendsto.const_mul hpow ?_
    by_cases hgx : g x = ∞
    · left
      simp [hgx, hδ]
    · right
      exact ENNReal.rpow_ne_top_of_nonneg hq hgx

/-- Thresholding a real function at a level separated from `0` and `1` by `δ > 0`
approximates a set in measure, with error at most its `L¹` distance from the indicator
divided by `δ`. The function need not take values in `[0, 1]`. -/
theorem measure_symmDiff_setOf_lt_indicator_le (m : Measure α) {u : α → ℝ} {s : Set α}
    (hu : AEStronglyMeasurable u m) (hs : NullMeasurableSet s m) {δ t : ℝ}
    (hδ : 0 < δ) (hδt : δ ≤ t) (htδ : t ≤ 1 - δ) :
    m ({x | t < u x} ∆ s) ≤ (∫⁻ x, ‖u x - s.indicator 1 x‖ₑ ∂m) / ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans
    (meas_ge_le_lintegral_div
      (hu.sub ((aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hs)).enorm
      (ne_of_gt (ENNReal.ofReal_pos.mpr hδ)) ENNReal.ofReal_ne_top)
  intro x hx
  rw [mem_symmDiff] at hx
  rw [mem_ofPred_eq, Pi.sub_apply, Real.enorm_eq_ofReal_abs]
  apply ENNReal.ofReal_le_ofReal
  rcases hx with ⟨hx, hxs⟩ | ⟨hxs, hx⟩
  · rw [indicator_of_notMem hxs, sub_zero]
    exact hδt.trans (hx.le.trans (le_abs_self _))
  · rw [indicator_of_mem hxs]
    simp only [mem_ofPred_eq, not_lt] at hx
    have h : δ ≤ 1 - u x := by linarith
    exact h.trans (by simpa only [neg_sub] using neg_le_abs (u x - 1))

/-- **The area between two graphs, through superlevel sets.** The `L¹` distance of two almost
everywhere measurable real functions is the integral, over the levels `s`, of the measure of the
set where exactly one of the two functions exceeds `s`. -/
theorem lintegral_enorm_sub_eq_lintegral_measure_symmDiff_setOf_lt (m : Measure α) [SFinite m]
    {f g : α → ℝ} (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ s, m ({a | s < f a} ∆ {a | s < g a}) := by
  rw [TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff m hf hg]
  refine lintegral_congr fun s ↦ ?_
  simp only [← compl_symmDiff_compl (a := {a | s < f a}), compl_ofPred, not_lt]

/-- The measure of the set where exactly one of two almost everywhere measurable real functions
exceeds the level `s` is a measurable function of `s`. -/
theorem measurable_measure_symmDiff_setOf_lt (m : Measure α) [SFinite m] {f g : α → ℝ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    Measurable fun s ↦ m ({a | s < f a} ∆ {a | s < g a}) := by
  have hcongr : (fun s ↦ m ({a | s < f a} ∆ {a | s < g a})) =
      fun s ↦ m ({a | s < hf.mk f a} ∆ {a | s < hg.mk g a}) := by
    refine funext fun s ↦ measure_congr ?_
    filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a hfa hga
    simp only [Set.mem_symmDiff, Set.mem_ofPred_eq]
    rw [hfa, hga]
  rw [hcongr]
  exact measurable_measure_prodMk_right ((measurableSet_lt measurable_snd
    (hf.measurable_mk.comp measurable_fst)).symmDiff
    (measurableSet_lt measurable_snd (hg.measurable_mk.comp measurable_fst)))

/-- **A superlevel set with small boundary.** Let `p` be an almost everywhere measurable real
function and let `q i`, for `i ∈ K`, be finitely many functions whose total `L¹` distance to `p`
is less than `ε` times the integral of `p`. Then at some level `t > 0` the superlevel set `{p > t}`
has total boundary `∑ i ∈ K, m ({q i > t} ∆ {p > t})` less than `ε` times its measure. -/
theorem exists_pos_sum_measure_symmDiff_lt_mul_measure (m : Measure α) [SFinite m] {ι : Type*}
    (K : Finset ι) {p : α → ℝ} {q : ι → α → ℝ} (hp : AEMeasurable p m)
    (hq : ∀ i ∈ K, AEMeasurable (q i) m) {ε : ℝ≥0∞}
    (h : ∑ i ∈ K, ∫⁻ x, ‖q i x - p x‖ₑ ∂m < ε * ∫⁻ x, ENNReal.ofReal (p x) ∂m) :
    ∃ t > 0, ∑ i ∈ K, m ({x | t < q i x} ∆ {x | t < p x}) < ε * m {x | t < p x} := by
  by_contra! hle
  refine h.not_ge ?_
  have hlay : ∫⁻ x, ENNReal.ofReal (p x) ∂m = ∫⁻ t in Ioi 0, m {x | t < p x} := by
    have h1 := lintegral_eq_lintegral_meas_lt (f := fun x ↦ max (p x) 0) m
      (ae_of_all _ fun x ↦ le_max_right _ _) (hp.max aemeasurable_const)
    have h2 (x : α) : ENNReal.ofReal (max (p x) 0) = ENNReal.ofReal (p x) := by
      simp [ENNReal.ofReal_max]
    simp only [h2] at h1
    rw [h1]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht' : 0 < t := ht
    congr 1
    ext x
    simp [lt_max_iff, ht'.not_gt]
  calc ε * ∫⁻ x, ENNReal.ofReal (p x) ∂m = ε * ∫⁻ t in Ioi 0, m {x | t < p x} := by
        rw [hlay]
    _ ≤ ∫⁻ t in Ioi 0, ε * m {x | t < p x} := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ t in Ioi 0, ∑ i ∈ K, m ({x | t < q i x} ∆ {x | t < p x}) :=
        setLIntegral_mono' measurableSet_Ioi hle
    _ ≤ ∫⁻ t, ∑ i ∈ K, m ({x | t < q i x} ∆ {x | t < p x}) := setLIntegral_le_lintegral _ _
    _ = ∑ i ∈ K, ∫⁻ x, ‖q i x - p x‖ₑ ∂m := by
        rw [lintegral_finsetSum' K fun i hi ↦
          (measurable_measure_symmDiff_setOf_lt m (hq i hi) hp).aemeasurable]
        exact Finset.sum_congr rfl fun i hi ↦
          (lintegral_enorm_sub_eq_lintegral_measure_symmDiff_setOf_lt m (hq i hi) hp).symm

open Filter Topology in
/-- **Superlevel sets along an `L¹`-convergent sequence.** If `f n → g` in `L¹(m)`, then along a
subsequence the strict superlevel sets `{f n > s}` converge in measure to `{g > s}` at almost every
level `s`: `m ({f (ns j) > s} ∆ {g > s}) → 0`. -/
theorem exists_strictMono_ae_tendsto_measure_symmDiff_setOf_lt (m : Measure α) [SFinite m]
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, AEMeasurable (f n) m) (hg : AEMeasurable g m)
    (h : Tendsto (fun n ↦ ∫⁻ a, ‖f n a - g a‖ₑ ∂m) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ s, Tendsto (fun j ↦ m ({a | s < f (ns j) a} ∆ {a | s < g a})) atTop (𝓝 0) := by
  -- The defect at level `s` is measurable in `s` and integrates to `∫ |f n - g|`.
  refine TauCeti.exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral
    (fun n ↦ (measurable_measure_symmDiff_setOf_lt m (hf n) hg).aemeasurable) ?_
  simpa only [← lintegral_enorm_sub_eq_lintegral_measure_symmDiff_setOf_lt m (hf _) hg] using h

end MeasureTheory.Measure

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

private theorem lintegral_ofReal_sub_eq_lintegral_measure_of_measurable (m : Measure α) [SFinite m]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, ENNReal.ofReal (g a - f a) ∂m = ∫⁻ s, m {a | f a ≤ s ∧ s < g a} := by
  set F : Set (α × ℝ) := {q | f q.1 ≤ q.2 ∧ q.2 < g q.1} with hFdef
  have hF : MeasurableSet F :=
    (measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hg.comp measurable_fst))
  calc ∫⁻ a, ENNReal.ofReal (g a - f a) ∂m = ∫⁻ a, volume (Prod.mk a ⁻¹' F) ∂m := by
        refine lintegral_congr fun a ↦ ?_
        have hsection : Prod.mk a ⁻¹' F = Ico (f a) (g a) := by
          ext s
          simp [hFdef]
        rw [hsection, Real.volume_Ico]
    _ = m.prod volume F := (Measure.prod_apply hF).symm
    _ = ∫⁻ s, m {a | f a ≤ s ∧ s < g a} := Measure.prod_apply_symm hF

/-- **The positive part of a difference, level by level.** For two almost everywhere measurable
real functions `f` and `g`, the integral of the positive part of `g - f` is the integral, over the
levels `s`, of the measure of the set where `f ≤ s < g`. -/
theorem lintegral_ofReal_sub_eq_lintegral_measure (m : Measure α) [SFinite m] {f g : α → ℝ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    ∫⁻ a, ENNReal.ofReal (g a - f a) ∂m = ∫⁻ s, m {a | f a ≤ s ∧ s < g a} := by
  calc
    ∫⁻ a, ENNReal.ofReal (g a - f a) ∂m = ∫⁻ a, ENNReal.ofReal (hg.mk g a - hf.mk f a) ∂m := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a hfa hga
      rw [hfa, hga]
    _ = ∫⁻ s, m {a | hf.mk f a ≤ s ∧ s < hg.mk g a} :=
      lintegral_ofReal_sub_eq_lintegral_measure_of_measurable m hf.measurable_mk
        hg.measurable_mk
    _ = ∫⁻ s, m {a | f a ≤ s ∧ s < g a} := by
      apply lintegral_congr
      intro s
      apply measure_congr
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a hfa hga
      rw [hfa, hga]

/-- Against Lebesgue measure on `(0, ∞)`, the set of levels `s` with `ofReal s < a` has measure
`a`. -/
private theorem volume_restrict_Ioi_setOf_ofReal_lt (a : ℝ≥0∞) :
    volume.restrict (Ioi (0 : ℝ)) {s : ℝ | ENNReal.ofReal s < a} = a := by
  rw [Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  · have hset : {s : ℝ | ENNReal.ofReal s < a} ∩ Ioi 0 = Ioo 0 a.toReal := by
      ext s
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨hs, h0⟩
        exact ⟨h0, (ENNReal.ofReal_lt_iff_lt_toReal h0.le ha).1 hs⟩
      · rintro ⟨h0, hs⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal h0.le ha).2 hs, h0⟩
    rw [hset, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha]

/-- Against Lebesgue measure on `(0, ∞)`, the set of levels `s` with `b ≤ ofReal s < a` has
measure `a - b`. -/
private theorem volume_restrict_Ioi_setOf_ofReal_lt_sdiff (a b : ℝ≥0∞) :
    volume.restrict (Ioi (0 : ℝ))
      ({s : ℝ | ENNReal.ofReal s < a} \ {s | ENNReal.ofReal s < b}) = a - b := by
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, sdiff_eq_empty.2 fun s hs ↦ lt_of_lt_of_le hs h, measure_empty]
  rcases eq_or_ne b ∞ with rfl | hb
  · rw [top_le_iff.1 h, sdiff_self, measure_empty, tsub_self]
  rw [measure_sdiff (fun s hs ↦ lt_of_lt_of_le hs h)
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const).nullMeasurableSet
      (by rwa [volume_restrict_Ioi_setOf_ofReal_lt]),
    volume_restrict_Ioi_setOf_ofReal_lt, volume_restrict_Ioi_setOf_ofReal_lt]

private theorem lintegral_sub_eq_lintegral_measure_sdiff_of_measurable (m : Measure α) [SFinite m]
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, (f x - g x) ∂m =
      ∫⁻ s in Ioi (0 : ℝ), m ({x | ENNReal.ofReal s < f x} \ {x | ENNReal.ofReal s < g x}) := by
  set F : Set (α × ℝ) :=
    {q | ENNReal.ofReal q.2 < f q.1} \ {q | ENNReal.ofReal q.2 < g q.1} with hFdef
  have hF : MeasurableSet F :=
    (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      (hf.comp measurable_fst)).diff
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hg.comp measurable_fst))
  calc ∫⁻ x, (f x - g x) ∂m = ∫⁻ x, volume.restrict (Ioi (0 : ℝ)) (Prod.mk x ⁻¹' F) ∂m := by
        refine lintegral_congr fun x ↦ ?_
        have hsection : Prod.mk x ⁻¹' F =
            {s : ℝ | ENNReal.ofReal s < f x} \ {s | ENNReal.ofReal s < g x} := by
          ext; simp [hFdef]
        rw [hsection, volume_restrict_Ioi_setOf_ofReal_lt_sdiff]
    _ = m.prod (volume.restrict (Ioi (0 : ℝ))) F := (Measure.prod_apply hF).symm
    _ = ∫⁻ s in Ioi (0 : ℝ),
          m ({x | ENNReal.ofReal s < f x} \ {x | ENNReal.ofReal s < g x}) :=
        Measure.prod_apply_symm hF

/-- **Truncated difference, level by level.** For two almost everywhere measurable functions
`f g : α → ℝ≥0∞`, the integral of the truncated difference `f - g` is the integral, over the
levels `s > 0`, of the measure of the set where `g ≤ ofReal s < f`. Infinite values are allowed;
in particular `∞ - ∞ = 0` is matched by the empty level sets. -/
theorem lintegral_sub_eq_lintegral_measure_sdiff (m : Measure α) [SFinite m] {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    ∫⁻ x, (f x - g x) ∂m =
      ∫⁻ s in Ioi (0 : ℝ), m ({x | ENNReal.ofReal s < f x} \ {x | ENNReal.ofReal s < g x}) := by
  calc
    ∫⁻ x, (f x - g x) ∂m = ∫⁻ x, (hf.mk f x - hg.mk g x) ∂m := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
      rw [hfx, hgx]
    _ = ∫⁻ s in Ioi (0 : ℝ),
          m ({x | ENNReal.ofReal s < hf.mk f x} \ {x | ENNReal.ofReal s < hg.mk g x}) :=
      lintegral_sub_eq_lintegral_measure_sdiff_of_measurable m hf.measurable_mk hg.measurable_mk
    _ = ∫⁻ s in Ioi (0 : ℝ),
          m ({x | ENNReal.ofReal s < f x} \ {x | ENNReal.ofReal s < g x}) := by
      refine lintegral_congr fun s ↦ measure_congr ?_
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
      simp only [mem_sdiff, mem_ofPred_eq]
      rw [hfx, hgx]

/-- The expected hinge cost `(y - x - r)⁺` is the integral, over the levels `a`, of the mass
given to the quadrant `Iic a ×ˢ Ioi (a + r)`. -/
theorem lintegral_ofReal_sub_sub_eq (m : Measure (ℝ × ℝ)) [SFinite m] (r : ℝ) :
    ∫⁻ z, ENNReal.ofReal (z.2 - z.1 - r) ∂m = ∫⁻ a, m (Iic a ×ˢ Ioi (a + r)) := by
  simp_rw [sub_right_comm _ _ r]
  rw [lintegral_ofReal_sub_eq_lintegral_measure m measurable_fst.aemeasurable
      (measurable_snd.sub_const r).aemeasurable]
  refine lintegral_congr fun a ↦ congrArg m ?_
  ext z
  simp [lt_sub_iff_add_lt]

/-- For a nonnegative threshold `r`, the two hinges of a pair of reals add up to the single hinge
`(|x - y| - r)⁺` of their distance, since at most one of `y - x - r` and `x - y - r` is positive. -/
theorem ofReal_sub_sub_add_ofReal_sub_sub {r : ℝ} (hr : 0 ≤ r) (x y : ℝ) :
    ENNReal.ofReal (y - x - r) + ENNReal.ofReal (x - y - r) = ENNReal.ofReal (|x - y| - r) := by
  rcases le_total x y with h | h
  · rw [ENNReal.ofReal_of_nonpos (by linarith : x - y - r ≤ 0), add_zero, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 h)]
  · rw [ENNReal.ofReal_of_nonpos (by linarith : y - x - r ≤ 0), zero_add,
      abs_of_nonneg (sub_nonneg.2 h)]

/-- **Powers are mixtures of hinges.** For `1 < p` and `d ≥ 0`,
`d ^ p = ∫_{r > 0} p (p - 1) r ^ (p - 2) (d - r)⁺ dr`. -/
theorem ofReal_rpow_eq_lintegral_mul_ofReal_sub {p d : ℝ} (hp : 1 < p) (hd : 0 ≤ d) :
    ENNReal.ofReal (d ^ p)
      = ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) * ENNReal.ofReal (d - r) := by
  -- The layer-cake formula for `s ^ (p - 1)` against Lebesgue measure on `(0, d)`.
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul (volume.restrict (Ioo 0 d)) (f := id)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs ↦ hs.1.le) aemeasurable_id
    (by linarith : 0 < p - 1)
  simp only [id_eq] at hlayer
  calc ENNReal.ofReal (d ^ p)
      = ENNReal.ofReal p * ∫⁻ s in Ioo 0 d, ENNReal.ofReal (s ^ (p - 1)) := by
        rw [lintegral_ofReal_rpow_Ioo (by linarith) hd, sub_add_cancel,
          ← ENNReal.ofReal_mul (by linarith), mul_div_cancel₀ _ (by linarith)]
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1))
          * (volume.restrict (Ioo 0 d) {s | r < s} * ENNReal.ofReal (r ^ (p - 1 - 1))) := by
        rw [hlayer, ← mul_assoc, ← ENNReal.ofReal_mul (by linarith),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) * ENNReal.ofReal (d - r) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        -- Against Lebesgue measure on `(0, d)`, the mass above a level `r > 0` is `d - r`.
        have hset : {s | r < s} ∩ Ioo 0 d = Ioo r d := by
          ext s
          simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioo]
          exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hr.trans h.1, h.2⟩⟩
        rw [Measure.restrict_apply' measurableSet_Ioo, hset, Real.volume_Ioo,
          ENNReal.ofReal_mul (by nlinarith : 0 ≤ p * (p - 1)), show p - 1 - 1 = p - 2 by ring]
        ring

/-- **Extended powers are mixtures of hinges.** For `1 < p` and `d : ℝ≥0∞`,
`d ^ p = ∫_{r > 0} p (p - 1) r ^ (p - 2) (d - r) dr`, with truncated subtraction. -/
theorem rpow_eq_lintegral_mul_sub {p : ℝ} (hp : 1 < p) (d : ℝ≥0∞) :
    d ^ p = ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) * (d - ENNReal.ofReal r) := by
  rcases eq_or_ne d ∞ with rfl | hd
  · rw [ENNReal.top_rpow_of_pos (by linarith)]
    symm
    calc ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2)) * (∞ - ENNReal.ofReal r)
        = ∫⁻ _ in Ioi (0 : ℝ), ∞ := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
          have hw : 0 < p * (p - 1) * r ^ (p - 2) := by
            have := Real.rpow_pos_of_pos hr (p - 2)
            have : 0 < p - 1 := by linarith
            positivity
          rw [ENNReal.top_sub ENNReal.ofReal_ne_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hw).ne']
      _ = ∞ := by simp
  · rw [← ENNReal.ofReal_toReal hd, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      (by linarith), ofReal_rpow_eq_lintegral_mul_ofReal_sub hp ENNReal.toReal_nonneg]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
    rw [ENNReal.ofReal_sub _ hr.le]

/-- **The power of a distance as a mixture of hinges.** For `1 < p`, the power `|x - y| ^ p` is
the integral, over the thresholds `r > 0` with weight `p (p - 1) r ^ (p - 2)`, of the two hinges
`(y - x - r)⁺ + (x - y - r)⁺`. -/
theorem edist_rpow_eq_lintegral {p : ℝ} (hp : 1 < p) (x y : ℝ) :
    edist x y ^ p = ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2))
      * (ENNReal.ofReal (y - x - r) + ENNReal.ofReal (x - y - r)) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith),
    ofReal_rpow_eq_lintegral_mul_ofReal_sub hp (abs_nonneg _)]
  exact setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by
    rw [ofReal_sub_sub_add_ofReal_sub_sub hr.le]

/-- The `p`-th moment of the distance between pairs of real variables, for `1 < p`, is the
corresponding mixture of their two expected hinge costs. -/
theorem lintegral_edist_rpow_eq {p : ℝ} (hp : 1 < p) (m : Measure (ℝ × ℝ)) [SFinite m] :
    ∫⁻ z, edist z.1 z.2 ^ p ∂m = ∫⁻ r in Ioi 0, ENNReal.ofReal (p * (p - 1) * r ^ (p - 2))
      * (∫⁻ z, ENNReal.ofReal (z.2 - z.1 - r) ∂m + ∫⁻ z, ENNReal.ofReal (z.1 - z.2 - r) ∂m) := by
  simp_rw [edist_rpow_eq_lintegral hp]
  rw [lintegral_lintegral_swap (by fun_prop)]
  refine lintegral_congr fun r ↦ ?_
  rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop)]

/-! ### The signed layer-cake representation of a real number -/

/-- `1_{t < a} - 1_{t < 0}`, as a function of `t`, is the signed indicator of the interval
between `0` and `a`. -/
theorem indicator_Iio_sub_indicator_Iio_zero (a : ℝ) :
    (fun t => (Iio a).indicator (1 : ℝ → ℝ) t - (Iio 0).indicator 1 t) =
      (Ico 0 a).indicator 1 - (Ico a 0).indicator 1 := by
  ext t
  simp only [Pi.sub_apply, indicator_apply, mem_Iio, mem_Ico, Pi.one_apply]
  split_ifs <;> grind

/-- The signed indicator `t ↦ 1_{t < a} - 1_{t < 0}` is Lebesgue integrable. -/
theorem integrable_indicator_Iio_sub_indicator_Iio_zero (a : ℝ) :
    Integrable (fun t => (Iio a).indicator (1 : ℝ → ℝ) t - (Iio 0).indicator 1 t) := by
  rw [indicator_Iio_sub_indicator_Iio_zero]
  exact (integrable_indicator_Ico_one _ _).sub (integrable_indicator_Ico_one _ _)

/-- **The signed layer-cake representation of a real number:**
`∫ (1_{t < a} - 1_{t < 0}) dt = a`. -/
@[simp]
theorem integral_indicator_Iio_sub_indicator_Iio_zero (a : ℝ) :
    ∫ t, ((Iio a).indicator (1 : ℝ → ℝ) t - (Iio 0).indicator 1 t) = a := by
  rw [indicator_Iio_sub_indicator_Iio_zero, integral_sub' (integrable_indicator_Ico_one _ _)
    (integrable_indicator_Ico_one _ _)]
  simp [integral_indicator_one measurableSet_Ico]

/-- The `L¹` norm of the signed indicator `t ↦ 1_{t < a} - 1_{t < 0}` is `|a|`:
`∫ |1_{t < a} - 1_{t < 0}| dt = |a|`. This is stated with `|·|`, the simp-normal form of the norm
on `ℝ`, so that `simp` also evaluates the `‖·‖` form of the integral. -/
@[simp]
theorem integral_abs_indicator_Iio_sub_indicator_Iio_zero (a : ℝ) :
    ∫ t, |(Iio a).indicator (1 : ℝ → ℝ) t - (Iio 0).indicator 1 t| = |a| := by
  have h : (fun t => |(Iio a).indicator (1 : ℝ → ℝ) t - (Iio 0).indicator 1 t|) =
      (Ico 0 a).indicator 1 + (Ico a 0).indicator 1 := by
    ext t
    simp only [Pi.add_apply, indicator_apply, mem_Iio, mem_Ico, Pi.one_apply]
    split_ifs <;> grind
  rw [h, integral_add' (integrable_indicator_Ico_one _ _) (integrable_indicator_Ico_one _ _)]
  simp [integral_indicator_one measurableSet_Ico]

/-! ### Real-power moments and weighted tails -/

section WeightedTail

open Filter Real
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω → ℝ} {p : ℝ}

omit [IsFiniteMeasure μ] in
/-- The real-valued strict tail weighted by a real power is measurable in the threshold.
No measurability of `f` or finiteness of `μ` is required. -/
theorem measurable_weighted_tail (f : Ω → ℝ) (p : ℝ) :
    Measurable fun t : ℝ ↦ μ.real {x | t < f x} * t ^ (p - 1) := by
  have hm : Measurable fun t : ℝ ↦ μ {x | t < f x} :=
    Antitone.measurable fun _ _ h ↦ measure_mono fun _ hx ↦ h.trans_lt hx
  exact hm.ennreal_toReal.mul (by fun_prop)

/-- The layer-cake integrability test for positive real powers on a finite measure space.
The function may be nonnegative only almost everywhere. -/
theorem integrable_rpow_iff_integrableOn_weighted_tail
    (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f) (hp : 0 < p) :
    Integrable (fun x ↦ f x ^ p) μ ↔
      IntegrableOn (fun t : ℝ ↦ μ.real {x | t < f x} * t ^ (p - 1)) (Ioi 0) := by
  have hpow : AEStronglyMeasurable (fun x ↦ f x ^ p) μ :=
    (hf.pow_const p).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[μ] fun x ↦ f x ^ p := hfn.mono fun _ hx ↦ rpow_nonneg hx _
  rw [← lintegral_ofReal_ne_top_iff_integrable hpow hnonneg,
    ← lt_top_iff_ne_top,
    lintegral_rpow_eq_lintegral_meas_lt_mul μ hfn hf hp]
  have heq : (∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x} * ENNReal.ofReal (t ^ (p - 1))) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (μ.real {x | t < f x} * t ^ (p - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ _)]
  rw [heq, ENNReal.mul_lt_top_iff]
  have htail : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t ↦ μ.real {x | t < f x} * t ^ (p - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg measureReal_nonneg (rpow_nonneg ht.le _)
  rw [IntegrableOn, ← lintegral_ofReal_ne_top_iff_integrable
    (measurable_weighted_tail f p).aestronglyMeasurable htail, ← lt_top_iff_ne_top]
  simp only [ENNReal.ofReal_lt_top, true_and, ENNReal.ofReal_eq_zero, not_le.mpr hp,
    false_or, or_iff_left_iff_imp]
  intro hz
  rw [hz]
  exact ENNReal.zero_lt_top

/-- On a finite measure space, the tail weighted by `t ^ (p - 1)` is integrable over every
bounded interval `(0, b]` when `0 < p`, without any measurability assumption on `f`. -/
theorem integrableOn_weighted_tail_Ioc (f : Ω → ℝ) (hp : 0 < p) {b : ℝ} :
    IntegrableOn (fun t : ℝ ↦ μ.real {x | t < f x} * t ^ (p - 1)) (Ioc 0 b) := by
  have hpow : IntegrableOn (fun t : ℝ ↦ t ^ (p - 1)) (Ioc 0 b) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p - 1)).1
  refine (hpow.const_mul (μ.real univ)).mono'
    (measurable_weighted_tail f p).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg measureReal_nonneg (rpow_nonneg ht.1.le _))]
  exact mul_le_mul_of_nonneg_right (measureReal_mono (subset_univ _)) (rpow_nonneg ht.1.le _)

/-- On a finite measure space, only the behavior of the weighted tail at infinity matters
for the existence of a positive real-power moment. -/
theorem integrable_rpow_iff_integrableAtFilter_weighted_tail
    (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f) (hp : 0 < p) :
    Integrable (fun x ↦ f x ^ p) μ ↔
      IntegrableAtFilter (fun t : ℝ ↦ μ.real {x | t < f x} * t ^ (p - 1)) atTop := by
  rw [integrable_rpow_iff_integrableOn_weighted_tail hf hfn hp]
  constructor
  · intro h
    exact ⟨Ioi 0, Ioi_mem_atTop 0, h⟩
  · rintro ⟨s, hs, hint⟩
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hs
    have htail : IntegrableOn (fun t : ℝ ↦ μ.real {x | t < f x} * t ^ (p - 1))
        (Ioi (max b 0)) :=
      hint.mono_set fun t ht ↦ hb t ((le_max_left b 0).trans ht.le)
    have hbounded := integrableOn_weighted_tail_Ioc (μ := μ) (b := max b 0) f hp
    have hcover : Ioc 0 (max b 0) ∪ Ioi (max b 0) = Ioi 0 :=
      Ioc_union_Ioi_eq_Ioi (le_max_right b 0)
    rw [← hcover]
    exact hbounded.union htail

end WeightedTail

end TauCeti

namespace MeasureTheory.Measure

/-- The integral of the shifted tail of a half-line measure is the extended integral of
its truncated distance above the threshold. No finiteness or normalization is required. -/
theorem lintegral_Ioi_tail_add (F : Measure ℝ≥0) (x : ℝ≥0) :
    (∫⁻ t : ℝ in Ioi 0, F (Ioi (t.toNNReal + x))) =
      ∫⁻ u, ((u - x : ℝ≥0) : ℝ≥0∞) ∂F := by
  have hlayer := lintegral_eq_lintegral_meas_lt F
    (f := fun u : ℝ≥0 => ((u - x : ℝ≥0) : ℝ))
    (ae_of_all _ fun u => NNReal.coe_nonneg _) (by fun_prop)
  simp only [ENNReal.ofReal_coe_nnreal] at hlayer
  rw [hlayer]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  congr 1
  ext u
  simp only [mem_Ioi, mem_ofPred_eq, ← Real.toNNReal_lt_iff_lt_coe ht.le,
    lt_tsub_iff_right]

/-- A finite extended first moment makes every shifted tail integrable on the positive
half-line. The measure need not be finite or normalized. -/
theorem integrableOn_Ioi_measureReal_tail_add (F : Measure ℝ≥0) (x : ℝ≥0)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) ≠ ∞) :
    IntegrableOn (fun t : ℝ => F.real (Ioi (t.toNNReal + x))) (Ioi 0) := by
  have hm : Measurable fun t : ℝ => F (Ioi (t.toNNReal + x)) :=
    Antitone.measurable fun _ _ h => measure_mono (Ioi_subset_Ioi (by gcongr))
  apply integrable_toReal_of_lintegral_ne_top hm.aemeasurable
  rw [lintegral_Ioi_tail_add]
  exact ne_top_of_le_ne_top hmean
    (lintegral_mono fun u => ENNReal.coe_le_coe.mpr (tsub_le_self : u - x ≤ u))

end MeasureTheory.Measure

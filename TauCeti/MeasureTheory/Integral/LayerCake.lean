/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Data.Set.SymmDiff
-- Proof-only: the layer-cake formula for a power and the power integral on `(0, a)`.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
-- Proof-only: the integrability of indicators of bounded intervals.
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Layer-cake formulas for products and distances

For two nonnegative measurable functions, their product integral is the double integral of the
measures of intersections of their strict superlevel sets. This is the two-function form of the
layer-cake formula and is useful for comparing pairings through level-set geometry.

This file expresses the `L¹` distance between two almost everywhere measurable real functions as
the integral, over all levels, of the measure of the symmetric difference of their sublevel sets.
Consequently, along a subsequence of an `L¹`-convergent sequence the superlevel sets converge in
measure at almost every level.
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

## Main statements

* `TauCeti.lintegral_mul_eq_lintegral_lintegral_measure_inter` — the integral of a product of
  nonnegative functions, as a double integral of intersections of superlevel sets;
* `TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff` — the `L¹` distance of two real
  functions, level by level;
* `MeasureTheory.Measure.exists_strictMono_ae_tendsto_measure_symmDiff_setOf_lt` — along a
  subsequence of an `L¹`-convergent sequence, the superlevel sets converge in measure at almost
  every level;
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
  its integrand.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal symmDiff

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

open Filter Topology in
/-- **Superlevel sets along an `L¹`-convergent sequence.** If `f n → g` in `L¹(m)`, then along a
subsequence the strict superlevel sets `{f n > s}` converge in measure to `{g > s}` at almost every
level `s`: `m ({f (ns j) > s} ∆ {g > s}) → 0`. -/
theorem exists_strictMono_ae_tendsto_measure_symmDiff_setOf_lt (m : Measure α) [SFinite m]
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, AEMeasurable (f n) m) (hg : AEMeasurable g m)
    (h : Tendsto (fun n ↦ ∫⁻ a, ‖f n a - g a‖ₑ ∂m) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ s, Tendsto (fun j ↦ m ({a | s < f (ns j) a} ∆ {a | s < g a})) atTop (𝓝 0) := by
  -- The defect `F n s` at level `s` is measurable in `s` and integrates to `∫ |f n - g|`.
  set F : ℕ → ℝ → ℝ≥0∞ := fun n s ↦ m ({a | s < f n a} ∆ {a | s < g a})
  have hF (n : ℕ) : ∫⁻ s, F n s = ∫⁻ a, ‖f n a - g a‖ₑ ∂m := by
    rw [TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff m (hf n) hg]
    refine lintegral_congr fun s ↦ ?_
    simp only [F, ← compl_symmDiff_compl (a := {a | s < f n a}), compl_ofPred, not_lt]
  have hFm (n : ℕ) : Measurable (F n) := by
    have hcongr : F n = fun s ↦ m ({a | s < (hf n).mk _ a} ∆ {a | s < hg.mk g a}) := by
      refine funext fun s ↦ measure_congr ?_
      filter_upwards [(hf n).ae_eq_mk, hg.ae_eq_mk] with a hfa hga
      simp only [Set.mem_symmDiff, Set.mem_ofPred_eq]
      rw [hfa, hga]
    rw [hcongr]
    exact measurable_measure_prodMk_right ((measurableSet_lt measurable_snd
      ((hf n).measurable_mk.comp measurable_fst)).symmDiff
      (measurableSet_lt measurable_snd (hg.measurable_mk.comp measurable_fst)))
  -- Along a subsequence with `∫ F (ns j) < 2⁻ʲ`, the sum `∑ⱼ F (ns j) s` is finite for almost
  -- every `s`, so its terms tend to zero.
  obtain ⟨ns, hns, hlt⟩ := extraction_forall_of_eventually fun j ↦
    h.eventually (gt_mem_nhds (ENNReal.pow_pos (a := 2⁻¹) (by simp) j))
  refine ⟨ns, hns, ?_⟩
  have hsum : ∫⁻ s, ∑' j, F (ns j) s ≠ ∞ := by
    rw [lintegral_tsum fun j ↦ (hFm (ns j)).aemeasurable]
    simp_rw [hF]
    exact ((ENNReal.tsum_le_tsum fun j ↦ (hlt j).le).trans_lt (by simp)).ne
  filter_upwards [ae_lt_top (Measurable.tsum fun j ↦ hFm (ns j)) hsum] with s hs
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hs.ne

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

end TauCeti

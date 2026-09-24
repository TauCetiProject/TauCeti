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

/-!
# A layer-cake formula for the distance between real functions

This file expresses the `L¹` distance between two almost everywhere measurable real functions as
the integral, over all levels, of the measure of the symmetric difference of their sublevel sets.
It also expresses the integral of the positive part `(g - f)⁺` as the integral, over all levels
`s`, of the measure of the set where `f ≤ s < g`: the one-sided form, which sees which of the two
functions lies above the level.

Finally, for `1 < p` it writes the power `|x - y| ^ p` as a mixture of *hinges*: it is the
integral over the thresholds `r > 0`, with weight `p (p - 1) r ^ (p - 2)`, of
`(y - x - r)⁺ + (x - y - r)⁺`. Integrated against a measure, this turns the `p`-th moment of a
difference into a mixture of one-sided integrals of the form above.

## Main statements

* `TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff` — the `L¹` distance of two real
  functions, level by level;
* `TauCeti.lintegral_ofReal_sub_eq_lintegral_measure` — the integral of a positive part
  `(g - f)⁺`, level by level;
* `TauCeti.ofReal_rpow_eq_lintegral_mul_ofReal_sub` and `TauCeti.edist_rpow_eq_lintegral` — a
  power `d ^ p`, and the power `|x - y| ^ p` of a distance, as mixtures of hinges.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

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

end TauCeti

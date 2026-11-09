/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- Proof-only: the layer-cake formula for powers of an `ℝ≥0∞`-valued function.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
-- Proof-only: right continuity of the distribution function `t ↦ μ {t < f}`.
import TauCeti.MeasureTheory.Function.SchwarzRearrangement

/-!
# The decreasing rearrangement of a function on a measure space

For a measure `μ` on `α` and `f : α → ℝ≥0∞`, the decreasing rearrangement
`μ.decreasingRearrangement f : ℝ → ℝ≥0∞` is the nonincreasing function on `(0, ∞)` with the same
distribution as `f`:

`f* s = sup {c | s < μ {f > c}} = inf {c | μ {f > c} ≤ s}`.

The measure `μ` is arbitrary: no σ-finiteness, measurability or finiteness hypothesis enters the
definition, and `f* s = ∞` exactly when `μ {f > c} > s` for every level `c`. For `s ≤ 0` the value
is the essential supremum of `f`, which is also the limit of `f* s` as `s ↓ 0`. For the counting
measure on a finite type, `f* s` is the entry of index `⌊s⌋` in the list of values of `f` sorted
in decreasing order, and `0` beyond its length. The decreasing rearrangement is the commutative
case of the generalized singular numbers `μ_t(x)` of Fack and Kosaki.

The defining property is the generalized-inverse relation `c < f* s ↔ s < μ {f > c}`
(`MeasureTheory.Measure.lt_decreasingRearrangement_iff`). It makes `f*` antitone and right
continuous, and equimeasurable with `f` for Lebesgue measure on `(0, ∞)`, so that `f*` has the same
`Lᵖ` norms as `f`. Sums and products obey the shifted bounds `(f + g)* (s + t) ≤ f* s + g* t` and
`(f g)* (s + t) ≤ f* s g* t`, and rearrangement commutes with multiplication by and subtraction
of constants.

The main result is the formula for Peetre's `K`-functional of the couple `(L¹, L∞)`:

`∫₀ᵗ f* = inf {‖f₀‖₁ + t ‖f₁‖_∞ | f = f₀ + f₁}`.

The infimum is attained by the radial truncation of `f` at the level `f* t`, and equals the
infimum over `c ≥ 0` of `∫ (f - c)⁺ + t c`. This identifies the `K`-functional of `(L¹, L∞)` with
the integral of the rearrangement; the real interpolation spaces of `(L¹, L∞)` are computed
from it.

## Main declarations

* `MeasureTheory.Measure.decreasingRearrangement`: the decreasing rearrangement `f*`.
* `MeasureTheory.Measure.lt_decreasingRearrangement_iff`,
  `MeasureTheory.Measure.decreasingRearrangement_le_iff`: the generalized-inverse relation with
  the distribution function.
* `MeasureTheory.Measure.antitone_decreasingRearrangement`,
  `MeasureTheory.Measure.continuousWithinAt_decreasingRearrangement`: `f*` is antitone and right
  continuous.
* `MeasureTheory.Measure.decreasingRearrangement_of_nonpos`,
  `MeasureTheory.Measure.tendsto_decreasingRearrangement_nhdsGT_zero`: the value at `0` is the
  essential supremum.
* `MeasureTheory.Measure.decreasingRearrangement_mono_ae`,
  `MeasureTheory.Measure.decreasingRearrangement_congr_ae`: monotonicity in `f` and independence
  of the representative.
* `MeasureTheory.Measure.decreasingRearrangement_indicator`,
  `MeasureTheory.Measure.decreasingRearrangement_const_mul`,
  `MeasureTheory.Measure.decreasingRearrangement_sub_const`: indicators, and multiplication by and
  subtraction of constants.
* `MeasureTheory.Measure.volume_restrict_setOf_lt_decreasingRearrangement`: equimeasurability,
  with the consequences `lintegral_rpow_decreasingRearrangement`,
  `eLpNorm_decreasingRearrangement`, `memLp_decreasingRearrangement_iff` and
  `essSup_decreasingRearrangement`.
* `MeasureTheory.Measure.decreasingRearrangement_add_le`,
  `MeasureTheory.Measure.decreasingRearrangement_mul_le`: the shifted subadditivity and
  submultiplicativity, and `decreasingRearrangement_le_add_essSup`, the stability under a
  bounded perturbation.
* `MeasureTheory.Measure.lintegral_decreasingRearrangement_eq_iInf_lintegral_sub`: the formula
  `∫₀ᵗ f* = inf_c (∫ (f - c) + t c)`.
* `MeasureTheory.Measure.lintegral_decreasingRearrangement_enorm_eq_iInf_eLpNorm`: the
  `K`-functional formula for `(L¹, L∞)`.

## References

* T. Fack and H. Kosaki, *Generalized s-numbers of τ-measurable operators*, Pacific J. Math.
  **123** (1986), 269–300, §2 (Definition 2.1, Lemma 2.5).
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.3 and §5.2 (Theorem 5.2.1).
-/

public noncomputable section

open Filter Set Topology
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞} {s t : ℝ} {c : ℝ≥0∞}

/-- The **decreasing rearrangement** `f* s = sup {c | s < μ {f > c}}` of `f : α → ℝ≥0∞` with
respect to `μ`. It is the nonincreasing right-continuous function on `(0, ∞)` with the same
distribution as `f`, and equals `inf {c | μ {f > c} ≤ s}` (`decreasingRearrangement_le_iff`).
For `s ≤ 0` its value is the essential supremum of `f`. -/
def decreasingRearrangement (f : α → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ⨆ (c : ℝ≥0∞) (_ : ENNReal.ofReal s < μ {y | c < f y}), c

theorem decreasingRearrangement_def (f : α → ℝ≥0∞) (s : ℝ) :
    μ.decreasingRearrangement f s = ⨆ (c : ℝ≥0∞) (_ : ENNReal.ofReal s < μ {y | c < f y}), c :=
  (rfl)

/-- The generalized-inverse relation: `c < f* s` exactly when the superlevel set `{f > c}` has
measure larger than `s`. -/
theorem lt_decreasingRearrangement_iff :
    c < μ.decreasingRearrangement f s ↔ ENNReal.ofReal s < μ {y | c < f y} := by
  constructor
  · intro h
    simp only [decreasingRearrangement, lt_iSup_iff] at h
    obtain ⟨d, hd, hcd⟩ := h
    exact hd.trans_le (measure_mono fun y hy ↦ hcd.trans hy)
  · intro h
    obtain ⟨d, hcd, hd⟩ := TauCeti.exists_lt_lt_measure_setOf_lt μ h
    exact hcd.trans_le (le_iSup₂_of_le d hd le_rfl)

/-- The generalized-inverse relation: `f* s ≤ c` exactly when the superlevel set `{f > c}` has
measure at most `s`. -/
theorem decreasingRearrangement_le_iff :
    μ.decreasingRearrangement f s ≤ c ↔ μ {y | c < f y} ≤ ENNReal.ofReal s := by
  simpa only [not_lt] using (μ.lt_decreasingRearrangement_iff (f := f) (s := s) (c := c)).not

theorem setOf_lt_decreasingRearrangement (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    {s | c < μ.decreasingRearrangement f s} = {s | ENNReal.ofReal s < μ {y | c < f y}} := by
  ext s
  exact μ.lt_decreasingRearrangement_iff

/-- The infimum defining `f* s` is attained: the superlevel set of `f` at the level `f* s` has
measure at most `s`. -/
theorem measure_setOf_decreasingRearrangement_lt_le (f : α → ℝ≥0∞) (s : ℝ) :
    μ {y | μ.decreasingRearrangement f s < f y} ≤ ENNReal.ofReal s :=
  μ.decreasingRearrangement_le_iff.1 le_rfl

theorem antitone_decreasingRearrangement (f : α → ℝ≥0∞) :
    Antitone (μ.decreasingRearrangement f) := fun s _ hst ↦
  μ.decreasingRearrangement_le_iff.2 <|
    (μ.measure_setOf_decreasingRearrangement_lt_le f s).trans (ENNReal.ofReal_le_ofReal hst)

@[fun_prop]
theorem measurable_decreasingRearrangement (f : α → ℝ≥0∞) :
    Measurable (μ.decreasingRearrangement f) :=
  (μ.antitone_decreasingRearrangement f).measurable

/-- The decreasing rearrangement is right continuous. -/
theorem continuousWithinAt_decreasingRearrangement (f : α → ℝ≥0∞) (s : ℝ) :
    ContinuousWithinAt (μ.decreasingRearrangement f) (Ici s) s := by
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · rw [lt_decreasingRearrangement_iff] at hc
    have : ∀ᶠ t in 𝓝 s, ENNReal.ofReal t < μ {y | c < f y} :=
      ENNReal.continuous_ofReal.continuousAt.eventually (gt_mem_nhds hc)
    exact (this.filter_mono nhdsWithin_le_nhds).mono fun t ht ↦
      μ.lt_decreasingRearrangement_iff.2 ht
  · exact eventually_nhdsWithin_of_forall fun t (ht : s ≤ t) ↦
      (μ.antitone_decreasingRearrangement f ht).trans_lt hc

/-- At nonpositive arguments the decreasing rearrangement is the essential supremum. -/
theorem decreasingRearrangement_of_nonpos (f : α → ℝ≥0∞) (hs : s ≤ 0) :
    μ.decreasingRearrangement f s = essSup f μ := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  rw [decreasingRearrangement_le_iff, ENNReal.ofReal_of_nonpos hs, nonpos_iff_eq_zero]
  constructor
  · intro h
    exact essSup_le_of_ae_le c (measure_eq_zero_iff_ae_notMem.1 h |>.mono fun y hy ↦ not_lt.1 hy)
  · intro h
    exact measure_mono_null (fun y (hy : c < f y) ↦ h.trans_lt hy) (meas_essSup_lt (f := f))

@[simp]
theorem decreasingRearrangement_zero (f : α → ℝ≥0∞) :
    μ.decreasingRearrangement f 0 = essSup f μ :=
  μ.decreasingRearrangement_of_nonpos f le_rfl

/-- As `s ↓ 0`, the decreasing rearrangement tends to the essential supremum. -/
theorem tendsto_decreasingRearrangement_nhdsGT_zero (f : α → ℝ≥0∞) :
    Tendsto (μ.decreasingRearrangement f) (𝓝[>] 0) (𝓝 (essSup f μ)) := by
  rw [← μ.decreasingRearrangement_zero f]
  exact (μ.continuousWithinAt_decreasingRearrangement f 0).mono Ioi_subset_Ici_self

theorem decreasingRearrangement_le_essSup (f : α → ℝ≥0∞) (s : ℝ) :
    μ.decreasingRearrangement f s ≤ essSup f μ := by
  rcases le_total s 0 with hs | hs
  · exact (μ.decreasingRearrangement_of_nonpos f hs).le
  · exact (μ.antitone_decreasingRearrangement f hs).trans (μ.decreasingRearrangement_zero f).le

/-! ### Dependence on the function -/

theorem decreasingRearrangement_mono_ae (h : f ≤ᵐ[μ] g) :
    μ.decreasingRearrangement f ≤ μ.decreasingRearrangement g := fun s ↦ by
  refine le_of_forall_lt fun c hc ↦ ?_
  rw [lt_decreasingRearrangement_iff] at hc ⊢
  exact hc.trans_le <| measure_mono_ae <| h.mono fun y hy (hcy : c < f y) ↦ hcy.trans_le hy

theorem decreasingRearrangement_mono (h : f ≤ g) :
    μ.decreasingRearrangement f ≤ μ.decreasingRearrangement g :=
  μ.decreasingRearrangement_mono_ae (ae_of_all _ h)

theorem decreasingRearrangement_congr_ae (h : f =ᵐ[μ] g) :
    μ.decreasingRearrangement f = μ.decreasingRearrangement g :=
  (μ.decreasingRearrangement_mono_ae h.le).antisymm (μ.decreasingRearrangement_mono_ae h.symm.le)

/-- The decreasing rearrangement of `c 1_A` is `c` on `(0, μ A)` and `0` beyond. -/
theorem decreasingRearrangement_indicator (A : Set α) (c : ℝ≥0∞) (s : ℝ) :
    μ.decreasingRearrangement (A.indicator fun _ ↦ c) s =
      if ENNReal.ofReal s < μ A then c else 0 := by
  refine eq_of_forall_lt_iff fun b ↦ ?_
  rw [lt_decreasingRearrangement_iff]
  by_cases hbc : b < c
  · have : {y | b < A.indicator (fun _ ↦ c) y} = A := by
      ext y
      by_cases hy : y ∈ A <;> simp [hy, hbc]
    rw [this]
    split_ifs with hA
    · simp [hA, hbc]
    · simp [hA]
  · have : {y | b < A.indicator (fun _ ↦ c) y} = ∅ := by
      ext y
      by_cases hy : y ∈ A <;> simp [hy, hbc]
    rw [this, measure_empty]
    split_ifs <;> simp [hbc]

/-- Multiplication by a finite constant commutes with rearrangement. -/
theorem decreasingRearrangement_const_mul (f : α → ℝ≥0∞) {a : ℝ≥0∞} (ha : a ≠ ∞) (s : ℝ) :
    μ.decreasingRearrangement (fun y ↦ a * f y) s = a * μ.decreasingRearrangement f s := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp only [zero_mul]
    exact le_antisymm (μ.decreasingRearrangement_le_iff.2 (by simp)) bot_le
  refine eq_of_forall_lt_iff fun b ↦ ?_
  have key : ∀ x : ℝ≥0∞, b < a * x ↔ b / a < x := fun x ↦ by
    rw [ENNReal.div_lt_iff (Or.inl ha₀) (Or.inl ha), mul_comm]
  simp only [lt_decreasingRearrangement_iff, key]

/-- Subtracting a constant commutes with rearrangement. -/
@[simp]
theorem decreasingRearrangement_sub_const (f : α → ℝ≥0∞) (c : ℝ≥0∞) (s : ℝ) :
    μ.decreasingRearrangement (fun y ↦ f y - c) s = μ.decreasingRearrangement f s - c := by
  refine eq_of_forall_lt_iff fun b ↦ ?_
  simp only [lt_decreasingRearrangement_iff, lt_tsub_iff_right]

/-- **Shifted subadditivity** `(f + g)* (s + t) ≤ f* s + g* t`. -/
theorem decreasingRearrangement_add_le (f g : α → ℝ≥0∞) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    μ.decreasingRearrangement (f + g) (s + t) ≤
      μ.decreasingRearrangement f s + μ.decreasingRearrangement g t := by
  rw [decreasingRearrangement_le_iff, ENNReal.ofReal_add hs ht]
  refine (measure_mono fun y hy ↦ ?_).trans ((measure_union_le _ _).trans
    (add_le_add (μ.measure_setOf_decreasingRearrangement_lt_le f s)
      (μ.measure_setOf_decreasingRearrangement_lt_le g t)))
  by_contra h
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at h
  exact (add_le_add h.1 h.2).not_gt hy

/-- **Shifted submultiplicativity** `(f g)* (s + t) ≤ f* s g* t`. -/
theorem decreasingRearrangement_mul_le (f g : α → ℝ≥0∞) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    μ.decreasingRearrangement (f * g) (s + t) ≤
      μ.decreasingRearrangement f s * μ.decreasingRearrangement g t := by
  rw [decreasingRearrangement_le_iff, ENNReal.ofReal_add hs ht]
  refine (measure_mono fun y hy ↦ ?_).trans ((measure_union_le _ _).trans
    (add_le_add (μ.measure_setOf_decreasingRearrangement_lt_le f s)
      (μ.measure_setOf_decreasingRearrangement_lt_le g t)))
  by_contra h
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at h
  exact (mul_le_mul' h.1 h.2).not_gt hy

/-- A perturbation `h` moves the decreasing rearrangement by at most its essential supremum. -/
theorem decreasingRearrangement_le_add_essSup {h : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g + h) (s : ℝ) :
    μ.decreasingRearrangement f s ≤ μ.decreasingRearrangement g s + essSup h μ := by
  rcases le_total s 0 with hs | hs
  · rw [μ.decreasingRearrangement_of_nonpos f hs, μ.decreasingRearrangement_of_nonpos g hs]
    exact (essSup_mono_ae hfg).trans (ENNReal.essSup_add_le g h)
  · calc μ.decreasingRearrangement f s ≤ μ.decreasingRearrangement (g + h) (s + 0) := by
          rw [add_zero]; exact μ.decreasingRearrangement_mono_ae hfg s
      _ ≤ _ := by
          rw [← μ.decreasingRearrangement_zero h]
          exact μ.decreasingRearrangement_add_le g h hs le_rfl

/-! ### Equimeasurability -/

/-- **Equimeasurability.** For Lebesgue measure on `(0, ∞)`, the superlevel sets of `f*` have the
same measures as those of `f`. -/
theorem volume_restrict_setOf_lt_decreasingRearrangement (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    volume.restrict (Ioi 0) {s | c < μ.decreasingRearrangement f s} = μ {y | c < f y} := by
  rw [setOf_lt_decreasingRearrangement,
    restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
  rcases eq_or_ne (μ {y | c < f y}) ∞ with htop | htop
  · rw [htop]
    simp only [ENNReal.ofReal_lt_top, ofPred_true, univ_inter, Real.volume_Ioi]
  · have : {s : ℝ | ENNReal.ofReal s < μ {y | c < f y}} ∩ Ioi 0 =
        Ioo 0 (μ {y | c < f y}).toReal := by
      ext s
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h, hs⟩
        exact ⟨hs, (ENNReal.ofReal_lt_iff_lt_toReal hs.le htop).1 h⟩
      · rintro ⟨hs, h⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal hs.le htop).2 h, hs⟩
    rw [this, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal htop]

/-- The decreasing rearrangement has the same essential supremum on `(0, ∞)` as `f`. -/
@[simp]
theorem essSup_decreasingRearrangement (f : α → ℝ≥0∞) :
    essSup (μ.decreasingRearrangement f) (volume.restrict (Ioi 0)) = essSup f μ := by
  simp only [essSup_eq_sInf, volume_restrict_setOf_lt_decreasingRearrangement]

/-- **Layer cake for the decreasing rearrangement.** For `0 < p`, the decreasing rearrangement
has the same integral of `p`-th powers on `(0, ∞)` as `f`. -/
@[simp]
theorem lintegral_rpow_decreasingRearrangement (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ s in Ioi 0, μ.decreasingRearrangement f s ^ p = ∫⁻ y, f y ^ p ∂μ := by
  rw [TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul _
      (μ.measurable_decreasingRearrangement f).aemeasurable hp,
    TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul μ hf hp]
  simp only [volume_restrict_setOf_lt_decreasingRearrangement]

/-- The decreasing rearrangement has the same integral on `(0, ∞)` as `f`. -/
@[simp]
theorem lintegral_decreasingRearrangement (hf : AEMeasurable f μ) :
    ∫⁻ s in Ioi 0, μ.decreasingRearrangement f s = ∫⁻ y, f y ∂μ := by
  simpa using μ.lintegral_rpow_decreasingRearrangement hf one_pos

/-- The decreasing rearrangement has the same `Lᵖ` seminorm on `(0, ∞)` as `f`, for every
exponent `p ∈ [0, ∞]`. -/
@[simp]
theorem eLpNorm_decreasingRearrangement (hf : AEMeasurable f μ) (p : ℝ≥0∞) :
    eLpNorm (μ.decreasingRearrangement f) p (volume.restrict (Ioi 0)) = eLpNorm f p μ := by
  have hf' := hf.aestronglyMeasurable
  have hg : AEStronglyMeasurable (μ.decreasingRearrangement f) (volume.restrict (Ioi 0)) :=
    (μ.measurable_decreasingRearrangement f).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hg, eLpNorm_exponent_zero hf']
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLpNorm_exponent_top hg, eLpNorm_exponent_top hf']
    simp only [eLpNormEssSup_eq_essSup_enorm, enorm_eq_self, essSup_decreasingRearrangement]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf']
  simp only [enorm_eq_self]
  rw [μ.lintegral_rpow_decreasingRearrangement hf (ENNReal.toReal_pos hp0 hptop)]

/-- The decreasing rearrangement lies in `Lᵖ(0, ∞)` exactly when `f` lies in `Lᵖ(μ)`, for every
exponent `p ∈ [0, ∞]`. -/
@[simp]
theorem memLp_decreasingRearrangement_iff (hf : AEMeasurable f μ) {p : ℝ≥0∞} :
    MemLp (μ.decreasingRearrangement f) p (volume.restrict (Ioi 0)) ↔ MemLp f p μ := by
  rw [memLp_iff, memLp_iff, eLpNorm_decreasingRearrangement μ hf]

/-! ### The `K`-functional of `(L¹, L∞)` -/

/-- For every level `c`, `∫₀ᵗ f* ≤ ∫ (f - c) + t c`. -/
theorem lintegral_decreasingRearrangement_le_lintegral_sub (hf : AEMeasurable f μ) (t : ℝ)
    (c : ℝ≥0∞) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement f s ≤
      ∫⁻ y, (f y - c) ∂μ + ENNReal.ofReal t * c := by
  calc ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement f s
      ≤ ∫⁻ s in Ioc 0 t, (μ.decreasingRearrangement f s - c + c) :=
        lintegral_mono fun _ ↦ le_tsub_add
    _ = (∫⁻ s in Ioc 0 t, (μ.decreasingRearrangement f s - c)) + ENNReal.ofReal t * c := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc, sub_zero,
          mul_comm]
    _ ≤ (∫⁻ s in Ioi 0, (μ.decreasingRearrangement f s - c)) + ENNReal.ofReal t * c := by
        gcongr
        exact Ioc_subset_Ioi_self
    _ = ∫⁻ y, (f y - c) ∂μ + ENNReal.ofReal t * c := by
        simp_rw [← μ.decreasingRearrangement_sub_const f c]
        rw [μ.lintegral_decreasingRearrangement (hf.sub_const c)]

/-- The level `c = f* t` attains `∫₀ᵗ f* = ∫ (f - c) + t c`. -/
theorem lintegral_decreasingRearrangement_eq_lintegral_sub (hf : AEMeasurable f μ) (t : ℝ) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement f s =
      ∫⁻ y, (f y - μ.decreasingRearrangement f t) ∂μ +
        ENNReal.ofReal t * μ.decreasingRearrangement f t := by
  rcases le_or_gt t 0 with ht | ht
  · -- For `t ≤ 0` both sides vanish, since `f* t` is the essential supremum of `f`.
    rw [Ioc_eq_empty_of_le ht, Measure.restrict_empty, lintegral_zero_measure,
      ENNReal.ofReal_of_nonpos ht, zero_mul, add_zero, μ.decreasingRearrangement_of_nonpos f ht,
      lintegral_congr_ae ((ENNReal.ae_le_essSup f).mono fun y hy ↦ tsub_eq_zero_of_le hy),
      lintegral_zero]
  set c := μ.decreasingRearrangement f t
  have hanti := μ.antitone_decreasingRearrangement f
  -- Beyond `t` the function `f* - c` vanishes, and on `(0, t]` it is `f* - c ≥ 0`.
  have htail : ∫⁻ s in Ioi t, (μ.decreasingRearrangement f s - c) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (g := fun _ ↦ 0) fun s (hs : t < s) ↦ tsub_eq_zero_of_le (hanti hs.le), lintegral_zero]
  have hhead : ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement f s =
      (∫⁻ s in Ioc 0 t, (μ.decreasingRearrangement f s - c)) + ENNReal.ofReal t * c := by
    rw [← setLIntegral_congr_fun measurableSet_Ioc
      fun s (hs : s ∈ Ioc 0 t) ↦ tsub_add_cancel_of_le (hanti hs.2),
      lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc, sub_zero,
      mul_comm]
  rw [hhead, ← μ.lintegral_decreasingRearrangement (hf.sub_const c), ← Ioc_union_Ioi_eq_Ioi ht.le,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  simp_rw [μ.decreasingRearrangement_sub_const f c, htail, add_zero]

/-- `∫₀ᵗ f*` is the infimum over levels `c` of `∫ (f - c) + t c`. -/
theorem lintegral_decreasingRearrangement_eq_iInf_lintegral_sub (hf : AEMeasurable f μ)
    (t : ℝ) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement f s =
      ⨅ c : ℝ≥0∞, ∫⁻ y, (f y - c) ∂μ + ENNReal.ofReal t * c :=
  le_antisymm (le_iInf (μ.lintegral_decreasingRearrangement_le_lintegral_sub hf t))
    (iInf_le_of_le _ (μ.lintegral_decreasingRearrangement_eq_lintegral_sub hf t).ge)

/-- For any splitting `f ≤ g + h`, `∫₀ᵗ f* ≤ ∫ g + t ess sup h`: this is the lower bound for the
`K`-functional of `(L¹, L∞)`. -/
theorem lintegral_decreasingRearrangement_le_lintegral_add_mul_essSup (hf : AEMeasurable f μ)
    (t : ℝ) {h : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g + h) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement f s ≤
      ∫⁻ y, g y ∂μ + ENNReal.ofReal t * essSup h μ := by
  refine (μ.lintegral_decreasingRearrangement_le_lintegral_sub hf t (essSup h μ)).trans ?_
  gcongr ?_ + _
  refine lintegral_mono_ae ((hfg.and (ENNReal.ae_le_essSup h)).mono fun y hy ↦ ?_)
  exact tsub_le_iff_right.2 (hy.1.trans (add_le_add le_rfl hy.2))

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial truncation `x ↦ min 1 (r / ‖x‖) • x` onto the closed ball of radius `r ≥ 0`
leaves a remainder of norm `‖x‖ - r`. -/
private theorem enorm_sub_truncation (x : E) {r : ℝ} (hr : 0 ≤ r) :
    ‖x - min 1 (r / ‖x‖) • x‖ₑ = ‖x‖ₑ - ENNReal.ofReal r ∧
      ‖min 1 (r / ‖x‖) • x‖ₑ ≤ ENNReal.ofReal r := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_sub _ hr]
  rcases le_total ‖x‖ r with hxr | hxr
  · have h1 : min 1 (r / ‖x‖) = 1 := min_eq_left ((one_le_div hx').2 hxr)
    refine ⟨by simp [h1, sub_nonpos.2 hxr], ?_⟩
    rw [h1, one_smul]
    exact ENNReal.ofReal_le_ofReal hxr
  · have h1 : min 1 (r / ‖x‖) = r / ‖x‖ := min_eq_right ((div_le_one hx').2 hxr)
    have hnorm : ‖(r / ‖x‖) • x‖ = r := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hr hx'.le), div_mul_cancel₀ _ hx'.ne']
    have hsub : x - (r / ‖x‖) • x = (1 - r / ‖x‖) • x := by rw [sub_smul, one_smul]
    refine ⟨congrArg ENNReal.ofReal ?_, by rw [h1, hnorm]⟩
    rw [h1, hsub, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 ((div_le_one hx').2 hxr)), sub_mul,
      one_mul, div_mul_cancel₀ _ hx'.ne']

/-- **The `K`-functional of `(L¹, L∞)`.** For an a.e. strongly measurable `f`,
`∫₀ᵗ ‖f‖* = inf {‖f₀‖₁ + t ‖f₁‖_∞ | f₀ + f₁ = f}`, the infimum being attained by the radial
truncation of `f` at the level `‖f‖* t`. -/
theorem lintegral_decreasingRearrangement_enorm_eq_iInf_eLpNorm {f : α → E}
    (hf : AEStronglyMeasurable f μ) (t : ℝ) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s =
      ⨅ (f₀ : α → E) (f₁ : α → E) (_ : f₀ + f₁ = f),
        eLpNorm f₀ 1 μ + ENNReal.ofReal t * eLpNorm f₁ ∞ μ := by
  refine le_antisymm (le_iInf fun f₀ ↦ le_iInf fun f₁ ↦ le_iInf fun hsum ↦ ?_) ?_
  · subst hsum
    by_cases h₀ : AEStronglyMeasurable f₀ μ
    · have h₁ : AEStronglyMeasurable f₁ μ := by simpa using hf.sub h₀
      rw [eLpNorm_one_eq_lintegral_enorm h₀, eLpNorm_exponent_top h₁,
        eLpNormEssSup_eq_essSup_enorm]
      exact μ.lintegral_decreasingRearrangement_le_lintegral_add_mul_essSup hf.enorm t
        (ae_of_all _ fun y ↦ enorm_add_le (f₀ y) (f₁ y))
    · simp [eLpNorm_of_not_aestronglyMeasurable h₀]
  · set c := μ.decreasingRearrangement (‖f ·‖ₑ) t
    rcases eq_or_ne c ∞ with hc | hc
    · -- No truncation: `f₀ = 0` and `f₁ = f`. Here `‖f‖* = ∞` on `(0, t]`.
      refine iInf_le_of_le 0 (iInf_le_of_le f (iInf_le_of_le (zero_add f) ?_))
      rw [eLpNorm_zero, zero_add]
      calc ENNReal.ofReal t * eLpNorm f ∞ μ ≤ ∫⁻ _ in Ioc 0 t, c := by
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm, hc]
            gcongr
            exact le_top
        _ ≤ ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s :=
            setLIntegral_mono (by fun_prop) fun s hs ↦
              μ.antitone_decreasingRearrangement _ hs.2
    · -- Radial truncation of `f` at the level `c = ‖f‖* t`.
      set f₁ : α → E := fun y ↦ min 1 (c.toReal / ‖f y‖) • f y
      have hf₁ : AEStronglyMeasurable f₁ μ :=
        (((measurable_const.min (measurable_const.div measurable_id)).comp_aemeasurable
          hf.norm.aemeasurable).aestronglyMeasurable).smul hf
      refine iInf_le_of_le (f - f₁) (iInf_le_of_le f₁ (iInf_le_of_le (sub_add_cancel f f₁) ?_))
      have htrunc := fun y ↦ enorm_sub_truncation (f y) (ENNReal.toReal_nonneg (a := c))
      simp only [ENNReal.ofReal_toReal hc] at htrunc
      rw [eLpNorm_one_eq_lintegral_enorm (hf.sub hf₁), eLpNorm_exponent_top hf₁,
        eLpNormEssSup_eq_essSup_enorm,
        μ.lintegral_decreasingRearrangement_eq_lintegral_sub hf.enorm t]
      gcongr ?_ + _ * ?_
      · exact (lintegral_congr fun y ↦ (htrunc y).1).le
      · exact essSup_le_of_ae_le c (ae_of_all _ fun y ↦ (htrunc y).2)

end Normed

end MeasureTheory.Measure

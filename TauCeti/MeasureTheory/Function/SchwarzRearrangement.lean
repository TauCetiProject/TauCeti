/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.EMetricSpace.Weak
-- Proof-only: one- and two-function layer-cake formulas.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Integral.LayerCake
-- Proof-only: the measure of the set where the centered Haar ball is small.
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Schwarz rearrangement

For a measure `μ` on a normed space and `f : E → ℝ≥0∞`, the Schwarz rearrangement
`schwarzRearrangement μ f` is the radially nonincreasing function whose strict superlevel set
`{t < f*}` is `{x | μ (ball 0 ‖x‖) < μ {t < f}}`:

`schwarzRearrangement μ f x = ⨆ {t | μ (ball 0 ‖x‖) < μ {f > t}}, t`.

For an additive Haar measure on a nontrivial finite-dimensional real normed space, a superlevel
set of finite measure is the centered open ball with the same measure, while one of infinite
measure is the whole space. Equimeasurability also holds in dimension zero. For Lebesgue measure
on a Euclidean space this is the symmetric decreasing rearrangement.
The definition is made directly from the distribution function `t ↦ μ {f > t}`, with no
measurability, integrability or finiteness hypotheses. For an additive Haar measure, a superlevel
set of infinite measure is replaced by the whole space, and one of measure zero by the empty set.
Consequently the rearrangement depends only on the a.e. class of `f`, and it is defined pointwise
at every point, so no further choice of representative is involved.

Its strict superlevel sets are `{x | μ (ball 0 ‖x‖) < μ {f > t}}`
(`TauCeti.setOf_lt_schwarzRearrangement`). For an additive Haar measure on a
finite-dimensional real normed space these sets have the same measure as `{f > t}`:
the rearrangement is **equimeasurable** with `f` (`TauCeti.addHaar_setOf_lt_schwarzRearrangement`).
For a.e.-measurable `f`, the layer-cake formula then gives equality of all `∫⁻ f ^ p` for
`0 < p`, hence of every `eLpNorm` with finite exponent, while equality of essential suprema gives
the case `p = ∞`. Rearrangement is monotone under a.e. inequality, idempotent, and it sends the
indicator of a set `s` to the indicator of `{x | μ (ball 0 ‖x‖) < μ s}`. In a nontrivial
finite-dimensional real normed space with additive Haar measure, this set is the centered open
ball of measure `μ s` when that measure is finite, and the whole space when it is infinite.
The Hardy--Littlewood inequality says that rearranging two nonnegative functions can only increase
the integral of their product.

Schwarz rearrangement is a contraction for every `Lᵖ` distance with `1 ≤ p ≤ ∞`, measured by the
extended distance on `ℝ≥0∞`. Two rearranged superlevel sets are concentric, so the measure of
their difference is the truncated difference of the original level measures. A level-by-level
formula for `∫⁻ (f - g)` then gives the one-sided `L¹` contraction, and writing `(f - g) ^ p` as a
mixture of the hinges `f - g - r` extends it to `1 < p`; adding a constant commutes with
rearrangement, which gives the case `p = ∞`.

## Main definitions and results

* `TauCeti.schwarzRearrangement`: the Schwarz rearrangement of an `ℝ≥0∞`-valued function.
* `TauCeti.lt_schwarzRearrangement_iff`: its superlevel sets.
* `TauCeti.measurable_schwarzRearrangement`: it is always measurable.
* `TauCeti.schwarzRearrangement_mono_ae`, `TauCeti.schwarzRearrangement_congr_ae`: order
  preservation and independence of the representative.
* `TauCeti.addHaar_setOf_lt_schwarzRearrangement`: equimeasurability.
* `TauCeti.addHaar_inter_setOf_lt_schwarzRearrangement`: intersections of two rearranged
  superlevel sets have the smaller of the original level measures.
* `TauCeti.lintegral_rpow_schwarzRearrangement`, `TauCeti.eLpNorm_schwarzRearrangement`,
  `TauCeti.memLp_schwarzRearrangement_iff`: equality of integrals of powers and of `Lᵖ`
  seminorms, and preservation of every `Lᵖ` class.
* `TauCeti.lintegral_mul_le_lintegral_schwarzRearrangement_mul`: the Hardy--Littlewood
  rearrangement inequality.
* `TauCeti.schwarzRearrangement_add_const`: rearrangement commutes with adding a constant.
* `TauCeti.addHaar_sdiff_setOf_lt_schwarzRearrangement`: differences of two rearranged
  superlevel sets have the truncated difference of the original level measures.
* `TauCeti.lintegral_sub_rpow_schwarzRearrangement_le`,
  `TauCeti.lintegral_edist_rpow_schwarzRearrangement_le`,
  `TauCeti.edist_schwarzRearrangement_le_essSup`, `TauCeti.eLpNorm_edist_schwarzRearrangement_le`:
  one-sided and two-sided `Lᵖ` contraction for `1 ≤ p ≤ ∞`.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics **14**, AMS,
  2001, Sections 3.3--3.5; Theorem 3.5 is the nonexpansivity of rearrangement.
-/

public noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace TauCeti

section Distribution

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}

/-- **Right continuity of the distribution function.** The measure of a strict superlevel set
`{t < f}` is approached by those of strictly higher levels, so anything below it is already below
`μ {s < f}` for some `s > t`. -/
theorem exists_lt_lt_measure_setOf_lt {t c : ℝ≥0∞} (h : c < μ {y | t < f y}) :
    ∃ s, t < s ∧ c < μ {y | s < f y} := by
  have ht : t ≠ ∞ := by
    rintro rfl
    simp at h
  obtain ⟨u, hu, hut, hlim⟩ := exists_seq_strictAnti_tendsto' (lt_top_iff_ne_top.2 ht)
  have hunion : {y | t < f y} = ⋃ n, {y | u n < f y} := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion]
    exact ⟨fun hy ↦ (hlim.eventually (gt_mem_nhds hy)).exists,
      fun ⟨n, hn⟩ ↦ (hut n).1.trans hn⟩
  have hmono : Monotone fun n ↦ {y | u n < f y} :=
    fun m n hmn y hy ↦ (hu.antitone hmn).trans_lt hy
  rw [hunion, hmono.measure_iUnion, lt_iSup_iff] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨u n, (hut n).1, hn⟩

end Distribution

section Measure

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (μ : Measure E)
  {f g : E → ℝ≥0∞}

/-- The **Schwarz rearrangement** of `f : E → ℝ≥0∞` with respect to `μ`: the radially
nonincreasing function whose superlevel set `{t < f*}` is `{x | μ (ball 0 ‖x‖) < μ {t < f}}`.
For an additive Haar measure on a nontrivial finite-dimensional real normed space, this is the
centered open ball of the same measure when `μ {t < f}` is finite, and the whole space when it is
infinite. -/
def schwarzRearrangement (f : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ⨆ (t : ℝ≥0∞) (_ : μ (ball (0 : E) ‖x‖) < μ {y | t < f y}), t

/-- The defining formula of the Schwarz rearrangement. -/
theorem schwarzRearrangement_def (f : E → ℝ≥0∞) (x : E) :
    schwarzRearrangement μ f x = ⨆ (t : ℝ≥0∞) (_ : μ (ball (0 : E) ‖x‖) < μ {y | t < f y}), t :=
  (rfl)

/-- **Superlevel sets of the Schwarz rearrangement.** -/
theorem lt_schwarzRearrangement_iff {x : E} {t : ℝ≥0∞} :
    t < schwarzRearrangement μ f x ↔ μ (ball (0 : E) ‖x‖) < μ {y | t < f y} := by
  rw [schwarzRearrangement_def, lt_iSup_iff]
  constructor
  · rintro ⟨s, hs⟩
    rw [lt_iSup_iff] at hs
    obtain ⟨hball, hts⟩ := hs
    exact hball.trans_le (measure_mono fun y hy ↦ hts.trans hy)
  · intro h
    obtain ⟨s, hts, hs⟩ := exists_lt_lt_measure_setOf_lt μ h
    exact ⟨s, lt_iSup_iff.2 ⟨hs, hts⟩⟩

/-- The strict superlevel sets of the Schwarz rearrangement, as sets. -/
theorem setOf_lt_schwarzRearrangement (f : E → ℝ≥0∞) (t : ℝ≥0∞) :
    {x | t < schwarzRearrangement μ f x} = {x | μ (ball (0 : E) ‖x‖) < μ {y | t < f y}} := by
  ext x
  exact lt_schwarzRearrangement_iff μ

/-- Superlevel sets of Schwarz rearrangements are nested according to the measures of the original
superlevel sets. -/
theorem setOf_lt_schwarzRearrangement_subset {s t : ℝ≥0∞}
    (h : μ {x | s < f x} ≤ μ {x | t < g x}) :
    {x | s < schwarzRearrangement μ f x} ⊆ {x | t < schwarzRearrangement μ g x} := by
  intro x hx
  rw [mem_ofPred_eq, lt_schwarzRearrangement_iff] at hx ⊢
  exact hx.trans_le h

/-- The Schwarz rearrangement is radially nonincreasing. -/
theorem schwarzRearrangement_le_of_norm_le (f : E → ℝ≥0∞) {x y : E} (h : ‖x‖ ≤ ‖y‖) :
    schwarzRearrangement μ f y ≤ schwarzRearrangement μ f x := by
  refine le_of_forall_lt fun t ht ↦ ?_
  rw [lt_schwarzRearrangement_iff] at ht ⊢
  exact (measure_mono (ball_subset_ball h)).trans_lt ht

/-- The Schwarz rearrangement is radial. -/
theorem schwarzRearrangement_eq_of_norm_eq (f : E → ℝ≥0∞) {x y : E} (h : ‖x‖ = ‖y‖) :
    schwarzRearrangement μ f x = schwarzRearrangement μ f y :=
  le_antisymm (schwarzRearrangement_le_of_norm_le μ f h.ge)
    (schwarzRearrangement_le_of_norm_le μ f h.le)

/-- The Schwarz rearrangement is always measurable: its superlevel sets are preimages under the
norm of sublevel sets of the monotone function `r ↦ μ (ball 0 r)`. -/
@[fun_prop]
theorem measurable_schwarzRearrangement [OpensMeasurableSpace E] (f : E → ℝ≥0∞) :
    Measurable (schwarzRearrangement μ f) := by
  refine measurable_of_Ioi fun t ↦ ?_
  have hball : Monotone fun r : ℝ ↦ μ (ball (0 : E) r) :=
    fun r s hrs ↦ measure_mono (ball_subset_ball hrs)
  have hset : schwarzRearrangement μ f ⁻¹' Ioi t =
      (fun x : E ↦ μ (ball (0 : E) ‖x‖)) ⁻¹' Iio (μ {y | t < f y}) :=
    setOf_lt_schwarzRearrangement μ f t
  rw [hset]
  exact (hball.measurable.comp measurable_norm) measurableSet_Iio

/-- **Order preservation.** An a.e. inequality between functions gives a pointwise inequality
between their Schwarz rearrangements. -/
theorem schwarzRearrangement_mono_ae (h : f ≤ᵐ[μ] g) :
    schwarzRearrangement μ f ≤ schwarzRearrangement μ g := by
  intro x
  refine le_of_forall_lt fun t ht ↦ ?_
  rw [lt_schwarzRearrangement_iff] at ht ⊢
  exact ht.trans_le (measure_mono_ae (h.mono fun y hy hty ↦ hty.trans_le hy))

/-- **Order preservation**, pointwise form. -/
theorem schwarzRearrangement_mono (h : f ≤ g) :
    schwarzRearrangement μ f ≤ schwarzRearrangement μ g :=
  schwarzRearrangement_mono_ae μ (.of_forall h)

/-- The Schwarz rearrangement depends only on the a.e. class of the function. -/
theorem schwarzRearrangement_congr_ae (h : f =ᵐ[μ] g) :
    schwarzRearrangement μ f = schwarzRearrangement μ g :=
  le_antisymm (schwarzRearrangement_mono_ae μ h.le) (schwarzRearrangement_mono_ae μ h.symm.le)

/-- The Schwarz rearrangement is unchanged when the measure is multiplied by a nonzero finite
constant: both sides of each defining comparison scale by that constant. -/
theorem schwarzRearrangement_smul_measure {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    (f : E → ℝ≥0∞) : schwarzRearrangement (c • μ) f = schwarzRearrangement μ f := by
  ext x
  simp only [schwarzRearrangement_def, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_lt_mul_iff_right hc₀ hc]

/-- The Schwarz rearrangement of the indicator of a set is the indicator of
`{x | μ (ball 0 ‖x‖) < μ s}`. For an additive Haar measure on a nontrivial finite-dimensional real
normed space, this is the centered open ball of measure `μ s` when that measure is finite, and the
whole space when it is infinite. -/
theorem schwarzRearrangement_indicator (s : Set E) (c : ℝ≥0∞) :
    schwarzRearrangement μ (s.indicator fun _ ↦ c) =
      {x | μ (ball (0 : E) ‖x‖) < μ s}.indicator fun _ ↦ c := by
  ext x
  refine eq_of_forall_lt_iff fun t ↦ ?_
  have hset : {y | t < s.indicator (fun _ ↦ c) y} = if t < c then s else ∅ := by
    ext y
    by_cases hy : y ∈ s <;> split_ifs with htc <;> simp [hy, htc]
  rw [lt_schwarzRearrangement_iff, hset]
  by_cases htc : t < c <;> by_cases hx : μ (ball (0 : E) ‖x‖) < μ s <;> simp [htc, hx]

/-- At the origin the Schwarz rearrangement takes the value `essSup f μ`. -/
@[simp]
theorem schwarzRearrangement_apply_zero (f : E → ℝ≥0∞) :
    schwarzRearrangement μ f 0 = essSup f μ := by
  refine eq_of_forall_lt_iff fun t ↦ ?_
  rw [lt_schwarzRearrangement_iff, norm_zero, ball_zero, measure_empty, pos_iff_ne_zero]
  constructor
  · intro h
    by_contra hle
    exact h (measure_mono_null (fun y hy ↦ (not_lt.1 hle).trans_lt hy) (meas_essSup_lt (f := f)))
  · intro h h0
    refine h.not_ge (essSup_le_of_ae_le t ?_)
    rw [EventuallyLE, ae_iff]
    simpa only [not_le] using h0

/-- The Schwarz rearrangement is bounded by the essential supremum of `f`. -/
theorem schwarzRearrangement_le_essSup (f : E → ℝ≥0∞) (x : E) :
    schwarzRearrangement μ f x ≤ essSup f μ :=
  schwarzRearrangement_apply_zero μ f ▸
    schwarzRearrangement_le_of_norm_le μ f (by simp : ‖(0 : E)‖ ≤ ‖x‖)

end Measure

section AddHaar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {f : E → ℝ≥0∞}

/-- **Equimeasurability.** For an additive Haar measure, every strict superlevel set of the
Schwarz rearrangement has the same measure as the corresponding superlevel set of `f`. No
measurability or finiteness hypothesis is needed. -/
@[simp]
theorem addHaar_setOf_lt_schwarzRearrangement (f : E → ℝ≥0∞) (t : ℝ≥0∞) :
    μ {x | t < schwarzRearrangement μ f x} = μ {y | t < f y} := by
  rw [setOf_lt_schwarzRearrangement]
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension zero every ball `ball 0 ‖x‖` is empty and every nonempty set is everything.
    congr 1
    ext x
    simp only [norm_of_subsingleton, ball_zero, measure_empty, mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero h.ne'
      rwa [Subsingleton.elim x y]
    · intro hx
      rw [Subsingleton.eq_univ_of_nonempty (s := {y | t < f y}) ⟨x, hx⟩]
      exact isOpen_univ.measure_pos μ univ_nonempty
  · exact μ.addHaar_setOf_addHaar_ball_norm_lt _

/-- Two superlevel sets of Schwarz rearrangements are concentric, so their intersection has the
smaller of the two original superlevel measures. No measurability or finiteness hypothesis is
needed. -/
@[simp]
theorem addHaar_inter_setOf_lt_schwarzRearrangement (f g : E → ℝ≥0∞) (s t : ℝ≥0∞) :
    μ ({x | s < schwarzRearrangement μ f x} ∩
        {x | t < schwarzRearrangement μ g x}) =
      min (μ {x | s < f x}) (μ {x | t < g x}) := by
  rcases le_total (μ {x | s < f x}) (μ {x | t < g x}) with h | h
  · rw [inter_eq_left.2 (setOf_lt_schwarzRearrangement_subset μ h),
      addHaar_setOf_lt_schwarzRearrangement, min_eq_left h]
  · rw [inter_eq_right.2 (setOf_lt_schwarzRearrangement_subset μ h),
      addHaar_setOf_lt_schwarzRearrangement, min_eq_right h]

/-- The Schwarz rearrangement is idempotent. -/
@[simp]
theorem schwarzRearrangement_schwarzRearrangement (f : E → ℝ≥0∞) :
    schwarzRearrangement μ (schwarzRearrangement μ f) = schwarzRearrangement μ f := by
  ext x
  refine eq_of_forall_lt_iff fun t ↦ ?_
  rw [lt_schwarzRearrangement_iff, lt_schwarzRearrangement_iff,
    addHaar_setOf_lt_schwarzRearrangement]

/-- The Schwarz rearrangement has the same essential supremum as `f`. -/
@[simp]
theorem essSup_schwarzRearrangement (f : E → ℝ≥0∞) :
    essSup (schwarzRearrangement μ f) μ = essSup f μ := by
  simp only [essSup_eq_sInf, addHaar_setOf_lt_schwarzRearrangement]

/-- **Layer cake for the Schwarz rearrangement.** For `0 < p`, the Schwarz rearrangement has the
same integral of `p`-th powers as `f`. -/
@[simp]
theorem lintegral_rpow_schwarzRearrangement (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, schwarzRearrangement μ f x ^ p ∂μ = ∫⁻ x, f x ^ p ∂μ := by
  rw [lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul μ
      (measurable_schwarzRearrangement μ f).aemeasurable hp,
    lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul μ hf hp]
  simp only [addHaar_setOf_lt_schwarzRearrangement]

/-- The Schwarz rearrangement has the same integral as `f`. -/
@[simp]
theorem lintegral_schwarzRearrangement (hf : AEMeasurable f μ) :
    ∫⁻ x, schwarzRearrangement μ f x ∂μ = ∫⁻ x, f x ∂μ := by
  simpa using lintegral_rpow_schwarzRearrangement μ hf one_pos

/-- The Schwarz rearrangement has the same `Lᵖ` seminorm as `f`, for every exponent
`p ∈ [0, ∞]`. -/
@[simp]
theorem eLpNorm_schwarzRearrangement (hf : AEMeasurable f μ) (p : ℝ≥0∞) :
    eLpNorm (schwarzRearrangement μ f) p μ = eLpNorm f p μ := by
  have hf' := hf.aestronglyMeasurable
  have hg : AEStronglyMeasurable (schwarzRearrangement μ f) μ :=
    (measurable_schwarzRearrangement μ f).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hg, eLpNorm_exponent_zero hf']
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLpNorm_exponent_top hg, eLpNorm_exponent_top hf']
    simp only [eLpNormEssSup_eq_essSup_enorm, enorm_eq_self, essSup_schwarzRearrangement]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf']
  simp only [enorm_eq_self]
  rw [lintegral_rpow_schwarzRearrangement μ hf (ENNReal.toReal_pos hp0 hptop)]

/-- The Schwarz rearrangement of an a.e.-measurable function lies in `Lᵖ` exactly when the function
does, for every exponent `p ∈ [0, ∞]`. -/
@[simp]
theorem memLp_schwarzRearrangement_iff (hf : AEMeasurable f μ) {p : ℝ≥0∞} :
    MemLp (schwarzRearrangement μ f) p μ ↔ MemLp f p μ := by
  rw [memLp_iff, memLp_iff, eLpNorm_schwarzRearrangement μ hf]

private theorem lintegral_mul_le_lintegral_schwarzRearrangement_mul_of_measurable
    {f g : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂μ) ≤
      ∫⁻ x, schwarzRearrangement μ f x * schwarzRearrangement μ g x ∂μ := by
  rw [lintegral_mul_eq_lintegral_lintegral_measure_inter μ hf.aemeasurable hg.aemeasurable,
    lintegral_mul_eq_lintegral_lintegral_measure_inter μ
      (measurable_schwarzRearrangement μ f).aemeasurable
      (measurable_schwarzRearrangement μ g).aemeasurable]
  refine lintegral_mono fun t => lintegral_mono fun s => ?_
  let A : Set E := {x | ENNReal.ofReal s < f x}
  let B : Set E := {x | ENNReal.ofReal t < g x}
  let A' : Set E := {x | ENNReal.ofReal s < schwarzRearrangement μ f x}
  let B' : Set E := {x | ENNReal.ofReal t < schwarzRearrangement μ g x}
  calc
    μ (A ∩ B) ≤ min (μ A) (μ B) :=
      le_min (measure_mono inter_subset_left) (measure_mono inter_subset_right)
    _ = μ (A' ∩ B') := by
      simp only [A, B, A', B', addHaar_inter_setOf_lt_schwarzRearrangement]

/-- **Hardy--Littlewood rearrangement inequality.** For two nonnegative a.e.-measurable
functions on a finite-dimensional real normed space, Schwarz rearrangement can only increase the
integral of their product. The statement includes infinite integrals and dimension zero. -/
theorem lintegral_mul_le_lintegral_schwarzRearrangement_mul {f g : E → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ≤
      ∫⁻ x, schwarzRearrangement μ f x * schwarzRearrangement μ g x ∂μ := by
  let F := hf.mk f
  let G := hg.mk g
  calc
    (∫⁻ x, f x * g x ∂μ) = ∫⁻ x, F x * G x ∂μ :=
      lintegral_congr_ae (hf.ae_eq_mk.fun_mul hg.ae_eq_mk)
    _ ≤ ∫⁻ x, schwarzRearrangement μ F x * schwarzRearrangement μ G x ∂μ :=
      lintegral_mul_le_lintegral_schwarzRearrangement_mul_of_measurable μ
        hf.measurable_mk hg.measurable_mk
    _ = ∫⁻ x, schwarzRearrangement μ f x * schwarzRearrangement μ g x ∂μ := by
      rw [schwarzRearrangement_congr_ae μ hf.ae_eq_mk.symm,
        schwarzRearrangement_congr_ae μ hg.ae_eq_mk.symm]

/-- The centered ball `ball 0 ‖x‖` has measure strictly smaller than the whole space. In positive
dimension the ball has finite measure and the space infinite measure; in dimension zero the ball is
empty. -/
private theorem addHaar_ball_norm_lt_univ (x : E) : μ (ball (0 : E) ‖x‖) < μ univ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [norm_of_subsingleton, ball_zero, measure_empty]
    exact isOpen_univ.measure_pos μ univ_nonempty
  · rw [measure_univ_of_isAddLeftInvariant]
    exact measure_ball_lt_top

/-- Adding a constant commutes with Schwarz rearrangement. -/
@[simp]
theorem schwarzRearrangement_add_const (f : E → ℝ≥0∞) (c : ℝ≥0∞) :
    schwarzRearrangement μ (fun x ↦ f x + c) = fun x ↦ schwarzRearrangement μ f x + c := by
  ext x
  refine eq_of_forall_lt_iff fun t ↦ ?_
  rw [lt_schwarzRearrangement_iff]
  rcases lt_or_ge t c with htc | hct
  · have huniv : {y | t < f y + c} = univ :=
      eq_univ_of_forall fun y ↦ htc.trans_le le_add_self
    rw [huniv]
    exact iff_of_true (addHaar_ball_norm_lt_univ μ x) (htc.trans_le le_add_self)
  rcases eq_or_ne c ∞ with rfl | hc
  · rw [top_le_iff.1 hct]
    simp
  have hlt (u : ℝ≥0∞) : t < u + c ↔ t - c < u := (ENNReal.sub_lt_iff_lt_right hc hct).symm
  simp only [hlt, ← lt_schwarzRearrangement_iff]

/-- The difference of two superlevel sets of Schwarz rearrangements has measure equal to the
truncated difference of the two original level measures, since the two sets are concentric. No
measurability or finiteness hypothesis is needed. -/
@[simp]
theorem addHaar_sdiff_setOf_lt_schwarzRearrangement (f g : E → ℝ≥0∞) (s t : ℝ≥0∞) :
    μ ({x | s < schwarzRearrangement μ f x} \ {x | t < schwarzRearrangement μ g x}) =
      μ {x | s < f x} - μ {x | t < g x} := by
  rcases le_total (μ {x | s < f x}) (μ {x | t < g x}) with h | h
  · rw [sdiff_eq_empty.2 (setOf_lt_schwarzRearrangement_subset μ h), measure_empty,
      tsub_eq_zero_of_le h]
  rcases eq_or_ne (μ {x | t < g x}) ∞ with hg | hg
  · -- Both level measures are infinite, so the two rearranged superlevel sets coincide.
    have hf : μ {x | s < f x} = ∞ := top_le_iff.1 (hg ▸ h)
    rw [setOf_lt_schwarzRearrangement, setOf_lt_schwarzRearrangement, hf, hg, sdiff_self,
      measure_empty, tsub_self]
  rw [measure_sdiff (setOf_lt_schwarzRearrangement_subset μ h)
      (measurableSet_lt measurable_const (measurable_schwarzRearrangement μ g)).nullMeasurableSet
      (by rwa [addHaar_setOf_lt_schwarzRearrangement]),
    addHaar_setOf_lt_schwarzRearrangement, addHaar_setOf_lt_schwarzRearrangement]

/-- One-sided `L¹` contraction: the integral of the truncated difference `f - g` can only decrease
under Schwarz rearrangement. -/
private theorem lintegral_sub_schwarzRearrangement_le {f g : E → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) :
    ∫⁻ x, (schwarzRearrangement μ f x - schwarzRearrangement μ g x) ∂μ ≤
      ∫⁻ x, (f x - g x) ∂μ := by
  rw [lintegral_sub_eq_lintegral_measure_sdiff μ
      (measurable_schwarzRearrangement μ f).aemeasurable
      (measurable_schwarzRearrangement μ g).aemeasurable,
    lintegral_sub_eq_lintegral_measure_sdiff μ hf hg]
  refine lintegral_mono fun s ↦ ?_
  rw [addHaar_sdiff_setOf_lt_schwarzRearrangement]
  exact le_measure_sdiff

/-- One-sided `L¹` contraction for the hinge `(f - g - c)⁺`, by rearranging `g + c`. -/
private theorem lintegral_sub_sub_schwarzRearrangement_le {f g : E → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (c : ℝ≥0∞) :
    ∫⁻ x, (schwarzRearrangement μ f x - schwarzRearrangement μ g x - c) ∂μ ≤
      ∫⁻ x, (f x - g x - c) ∂μ := by
  simp_rw [tsub_tsub]
  have h := lintegral_sub_schwarzRearrangement_le μ hf (hg.add_const c)
  rwa [schwarzRearrangement_add_const] at h

/-- **One-sided `Lᵖ` contraction of Schwarz rearrangement.** For `1 ≤ p`, the integral of the
`p`-th power of the truncated difference `f - g` can only decrease under Schwarz rearrangement. -/
theorem lintegral_sub_rpow_schwarzRearrangement_le {f g : E → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (schwarzRearrangement μ f x - schwarzRearrangement μ g x) ^ p ∂μ ≤
      ∫⁻ x, (f x - g x) ^ p ∂μ := by
  rcases hp.eq_or_lt with rfl | hp
  · simpa only [ENNReal.rpow_one] using lintegral_sub_schwarzRearrangement_le μ hf hg
  -- Pass to measurable representatives, so that the hinge integrals can be swapped.
  have hfg : ∫⁻ x, (f x - g x) ^ p ∂μ = ∫⁻ x, (hf.mk f x - hg.mk g x) ^ p ∂μ :=
    lintegral_congr_ae <| by
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
      rw [hfx, hgx]
  rw [schwarzRearrangement_congr_ae μ hf.ae_eq_mk, schwarzRearrangement_congr_ae μ hg.ae_eq_mk,
    hfg]
  set F := hf.mk f
  set G := hg.mk g
  have hF : Measurable F := hf.measurable_mk
  have hG : Measurable G := hg.measurable_mk
  have hF' := measurable_schwarzRearrangement μ F
  have hG' := measurable_schwarzRearrangement μ G
  -- Write the power as a mixture of the hinges `f - g - r`, each of which contracts.
  simp_rw [rpow_eq_lintegral_mul_sub hp]
  rw [lintegral_lintegral_swap (by fun_prop)]
  conv_rhs => rw [lintegral_lintegral_swap (by fun_prop)]
  refine lintegral_mono fun r ↦ ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_right
    (lintegral_sub_sub_schwarzRearrangement_le μ hF.aemeasurable hG.aemeasurable _) _

/-- **`Lᵖ` contraction of Schwarz rearrangement**, integral form. For `1 ≤ p`, the integral of
the `p`-th power of the extended distance between two nonnegative functions can only decrease
under Schwarz rearrangement. -/
theorem lintegral_edist_rpow_schwarzRearrangement_le {f g : E → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, edist (schwarzRearrangement μ f x) (schwarzRearrangement μ g x) ^ p ∂μ ≤
      ∫⁻ x, edist (f x) (g x) ^ p ∂μ := by
  -- Of the two truncated differences `a - b` and `b - a`, one vanishes and the other is the
  -- extended distance.
  have hsplit (a b : ℝ≥0∞) : edist a b ^ p = (a - b) ^ p + (b - a) ^ p := by
    have hp0 : 0 < p := zero_lt_one.trans_le hp
    rw [ENNReal.edist_eq_max]
    rcases le_total a b with h | h
    · rw [tsub_eq_zero_of_le h, max_eq_right zero_le, ENNReal.zero_rpow_of_pos hp0, zero_add]
    · rw [tsub_eq_zero_of_le h, max_eq_left zero_le, ENNReal.zero_rpow_of_pos hp0, add_zero]
  simp_rw [hsplit]
  rw [lintegral_add_left (by fun_prop), lintegral_add_left' (by fun_prop)]
  exact add_le_add (lintegral_sub_rpow_schwarzRearrangement_le μ hf hg hp)
    (lintegral_sub_rpow_schwarzRearrangement_le μ hg hf hp)

/-- **`L^∞` contraction of Schwarz rearrangement.** The extended distance between two Schwarz
rearrangements is bounded everywhere by the essential supremum of the distance between the two
functions. No measurability hypothesis is needed. -/
theorem edist_schwarzRearrangement_le_essSup (f g : E → ℝ≥0∞) (x : E) :
    edist (schwarzRearrangement μ f x) (schwarzRearrangement μ g x) ≤
      essSup (fun y ↦ edist (f y) (g y)) μ := by
  set c := essSup (fun y ↦ edist (f y) (g y)) μ
  have h := ENNReal.ae_le_essSup (μ := μ) fun y ↦ edist (f y) (g y)
  have hfg : schwarzRearrangement μ f ≤ fun x ↦ schwarzRearrangement μ g x + c := by
    rw [← schwarzRearrangement_add_const]
    exact schwarzRearrangement_mono_ae μ
      (h.mono fun y hy ↦ ((ENNReal.edist_le_iff_le_add_right _ _ _).1 hy).1)
  have hgf : schwarzRearrangement μ g ≤ fun x ↦ schwarzRearrangement μ f x + c := by
    rw [← schwarzRearrangement_add_const]
    exact schwarzRearrangement_mono_ae μ
      (h.mono fun y hy ↦ ((ENNReal.edist_le_iff_le_add_right _ _ _).1 hy).2)
  exact (ENNReal.edist_le_iff_le_add_right _ _ _).2 ⟨hfg x, hgf x⟩

/-- **`Lᵖ` contraction of Schwarz rearrangement.** For every exponent `1 ≤ p ≤ ∞`, the `Lᵖ`
seminorm of the extended distance between two nonnegative functions can only decrease under
Schwarz rearrangement. -/
theorem eLpNorm_edist_schwarzRearrangement_le {f g : E → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ edist (schwarzRearrangement μ f x) (schwarzRearrangement μ g x)) p μ ≤
      eLpNorm (fun x ↦ edist (f x) (g x)) p μ := by
  -- The extended distance on `ℝ≥0∞` is the maximum of the two truncated differences.
  have hmeas {u v : E → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
      AEStronglyMeasurable (fun x ↦ edist (u x) (v x)) μ := by
    simp_rw [ENNReal.edist_eq_max]
    exact ((hu.sub hv).max (hv.sub hu)).aestronglyMeasurable
  have hf' := (measurable_schwarzRearrangement μ f).aemeasurable (μ := μ)
  have hg' := (measurable_schwarzRearrangement μ g).aemeasurable (μ := μ)
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLpNorm_exponent_top (hmeas hf' hg'), eLpNorm_exponent_top (hmeas hf hg),
      eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
    simp only [enorm_eq_self]
    exact essSup_le_of_ae_le _
      (.of_forall (edist_schwarzRearrangement_le_essSup μ f g))
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hmeas hf' hg'),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hmeas hf hg)]
  simp only [enorm_eq_self]
  exact ENNReal.rpow_le_rpow (lintegral_edist_rpow_schwarzRearrangement_le μ hf hg
    (by simpa using ENNReal.toReal_mono hptop hp)) (by positivity)

end AddHaar

end TauCeti

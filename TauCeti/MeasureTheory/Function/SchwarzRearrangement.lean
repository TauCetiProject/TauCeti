/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
-- Proof-only: the layer-cake formula for powers of `ℝ≥0∞`-valued functions.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
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

## Main definitions and results

* `TauCeti.schwarzRearrangement`: the Schwarz rearrangement of an `ℝ≥0∞`-valued function.
* `TauCeti.lt_schwarzRearrangement_iff`: its superlevel sets.
* `TauCeti.measurable_schwarzRearrangement`: it is always measurable.
* `TauCeti.schwarzRearrangement_mono_ae`, `TauCeti.schwarzRearrangement_congr_ae`: order
  preservation and independence of the representative.
* `TauCeti.addHaar_setOf_lt_schwarzRearrangement`: equimeasurability.
* `TauCeti.lintegral_rpow_schwarzRearrangement`, `TauCeti.eLpNorm_schwarzRearrangement`,
  `TauCeti.memLp_schwarzRearrangement_iff`: equality of integrals of powers and of `Lᵖ`
  seminorms, and preservation of every `Lᵖ` class.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics **14**, AMS,
  2001, Section 3.3.
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

end AddHaar

end TauCeti

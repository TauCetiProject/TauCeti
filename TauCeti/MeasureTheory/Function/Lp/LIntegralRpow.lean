/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# `Lᵖ` seminorm bounds out of bounds between the integrals `∫⁻ ‖·‖ₑ ^ p`

For `0 < p < ∞` the `Lᵖ` seminorm of an a.e. strongly measurable `v` is the `p`-th root of
`∫⁻ ‖v x‖ₑ ^ p ∂μ` (a function that is not a.e. strongly measurable has seminorm `∞`), so a
bound `∫⁻ ‖v‖ₑ ^ p ≤ c ^ p * ∫⁻ ‖w‖ₑ ^ p` between those integrals implies the bound
`‖v‖_p ≤ c * ‖w‖_p` between the seminorms. This file records that implication, which is the
direction an estimate proved by integration produces.

The two functions are allowed to take values in different spaces, and those spaces need carry
nothing beyond an extended norm, since that is all `eLpNorm` reads. In particular the statement
covers comparing a function with its derivative.

## Main declarations

* `TauCeti.eLpNorm_rpow_eq_lintegral`: for an a.e. measurable `ℝ≥0∞`-valued function, the `p`-th
  power of the `Lᵖ` seminorm is the integral `∫⁻ f ^ p`; `TauCeti.eLpNorm_eq_lintegral_rpow` is
  the same identity solved for the seminorm.
* `TauCeti.eLpNorm_ennreal_le_of_ae_tendsto`: the `ℝ≥0∞`-valued Fatou lemma for the `Lᵖ` seminorm,
  along any countably generated filter at arbitrary `p : ℝ≥0∞`.
* `TauCeti.ae_lt_top_of_eLpNorm_ne_top`: at any nonzero exponent, an `ℝ≥0∞`-valued function with
  finite `Lᵖ` seminorm is finite almost everywhere.
* `TauCeti.eLpNorm_le_eLpNorm_of_lintegral_rpow_le`: for an a.e. strongly measurable `v`, from
  `∫⁻ ‖v‖ₑ ^ p ≤ c ^ p * ∫⁻ ‖w‖ₑ ^ p` conclude `‖v‖_p ≤ c * ‖w‖_p`; no measurability of `w` is
  needed.
* `TauCeti.rpow_lintegral_le_measure_univ_rpow_mul`: Hölder's extended-valued integral inequality
  `(∫⁻ u) ^ r ≤ μ univ ^ (r - 1) * ∫⁻ u ^ r` for `u : α → ℝ≥0∞`.  On a finite measure space it
  expresses the nesting `L^r ⊆ L¹`; for a general `μ` it is only the inequality.
-/

public section

namespace TauCeti

open Filter
open MeasureTheory
open scoped ENNReal Topology

/-- For a finite nonzero exponent, the `p`-th power of the `Lᵖ` seminorm of an a.e. measurable
`ℝ≥0∞`-valued function is the integral of the `p`-th power of that function. This is
`MeasureTheory.lintegral_rpow_eNorm_eq_rpow_eLpNorm'` read at an `ℝ≥0∞`-valued exponent and at a
function whose enorm is the identity, which is the shape the extended-valued estimates use. -/
theorem eLpNorm_rpow_eq_lintegral {α : Type*} [MeasurableSpace α]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : α → ℝ≥0∞} {μ : Measure α}
    (hf : AEMeasurable f μ) :
    eLpNorm f p μ ^ p.toReal = ∫⁻ a, f a ^ p.toReal ∂μ := by
  rw [eLpNorm_eq_eLpNorm' hp0 hp hf.aestronglyMeasurable,
    ← lintegral_rpow_eNorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]
  simp

/-- For a finite nonzero exponent, the `Lᵖ` seminorm of an a.e. measurable `ℝ≥0∞`-valued function
is the `p`-th root of the integral of the `p`-th power of that function. -/
theorem eLpNorm_eq_lintegral_rpow {α : Type*} [MeasurableSpace α]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : α → ℝ≥0∞} {μ : Measure α}
    (hf : AEMeasurable f μ) :
    eLpNorm f p μ = (∫⁻ a, f a ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hf.aestronglyMeasurable]
  simp only [eNorm_eq_self]

/-- **Fatou's lemma for the `Lᵖ` seminorm of `ℝ≥0∞`-valued functions**, at every exponent
`p : ℝ≥0∞` (including `0` and `∞`) and along any countably generated filter: an almost everywhere
pointwise limit of functions whose `Lᵖ` seminorms are frequently at most `C` also has `Lᵖ`
seminorm at most `C`. Almost everywhere measurability of the limit is deduced from the pointwise
convergence. -/
theorem eLpNorm_ennreal_le_of_ae_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {ι : Type*} {u : Filter ι} [IsCountablyGenerated u]
    {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞} {C : ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ f i x) u (𝓝 (g x)))
    (hle : ∃ᶠ i in u, eLpNorm (f i) p μ ≤ C) :
    eLpNorm g p μ ≤ C := by
  -- Pass to a sequence along which the bound holds at every index.
  obtain ⟨v, hv, hle⟩ := exists_seq_forall_of_frequently hle
  replace hf (n : ℕ) : AEMeasurable (f (v n)) μ := hf (v n)
  replace hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f (v n) x) atTop (𝓝 (g x)) :=
    hlim.mono fun x hx ↦ hx.comp hv
  have hg : AEMeasurable g μ := ENNReal.aemeasurable_of_tendsto hf hlim
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm_exponent_zero hg.aestronglyMeasurable]
  rcases eq_or_ne p ∞ with rfl | hp
  · simp only [eLpNorm_exponent_top, hg.aestronglyMeasurable, (hf _).aestronglyMeasurable,
      eLpNormEssSup_eq_essSup_eNorm, eNorm_eq_self] at hle ⊢
    rw [essSup_congr_ae (hlim.mono fun x hx ↦ hx.liminf_eq.symm)]
    exact (ENNReal.essSup_liminf_le _).trans (liminf_le_of_frequently_le' (.of_forall hle))
  · have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [← ENNReal.rpow_le_rpow_iff hr, eLpNorm_rpow_eq_lintegral hp0 hp hg]
    calc ∫⁻ x, g x ^ p.toReal ∂μ
        = ∫⁻ x, atTop.liminf (fun n ↦ f (v n) x ^ p.toReal) ∂μ :=
          lintegral_congr_ae <| hlim.mono fun x hx ↦
            ((ENNReal.continuous_rpow_const.tendsto (g x)).comp hx).liminf_eq.symm
      _ ≤ atTop.liminf fun n ↦ ∫⁻ x, f (v n) x ^ p.toReal ∂μ :=
          lintegral_liminf_le' fun n ↦ (hf n).pow_const _
      _ ≤ C ^ p.toReal := by
          refine liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_)
          rw [← eLpNorm_rpow_eq_lintegral hp0 hp (hf n)]
          exact ENNReal.rpow_le_rpow (hle n) hr.le

/-- At any nonzero exponent (including `∞`), an `ℝ≥0∞`-valued function with finite `Lᵖ` seminorm is
finite almost everywhere. -/
theorem ae_lt_top_of_eLpNorm_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) {f : α → ℝ≥0∞} (h : eLpNorm f p μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ := by
  have hf : AEMeasurable f μ := (aestronglyMeasurable_of_eLpNorm_ne_top h).aemeasurable
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top hf.aestronglyMeasurable, eLpNormEssSup_eq_essSup_eNorm] at h
    simp only [eNorm_eq_self] at h
    exact ae_lt_of_essSup_lt h.lt_top
  · have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    have hint : ∫⁻ x, f x ^ p.toReal ∂μ ≠ ∞ := by
      rw [← eLpNorm_rpow_eq_lintegral hp0 hp hf]
      exact (ENNReal.rpow_lt_top_of_nonneg hr.le h).ne
    filter_upwards [ae_lt_top' (hf.pow_const p.toReal) hint] with x hx
    rwa [← ENNReal.lt_rpow_inv_iff hr, ENNReal.top_rpow_of_pos (inv_pos.2 hr)] at hx

/-- Turn a bound between the `∫⁻ ‖·‖ₑ ^ p` integrals into a bound between the `Lᵖ` seminorms.
The two functions may have different codomains, which is what lets such a bound compare a
function with its derivative; only a topology and an extended norm on each is needed.

Only the function on the left has to be a.e. strongly measurable: without that its `Lᵖ` seminorm
is `∞` by definition, whatever the integral bound says, while a non-measurable `w` only makes the
right-hand side larger. The exponent `0` is allowed, where the left-hand side vanishes. The two
integrals may be taken against different measures `μ` and `ν`, as when an estimate is transported
by a change of variables. -/
theorem eLpNorm_le_eLpNorm_of_lintegral_rpow_le {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    {G H : Type*} [ENorm G] [TopologicalSpace G] [ENorm H] [TopologicalSpace H]
    {v : α → G} {w : α → H} {c : ℝ}
    (hc : 0 ≤ c) {p : ℝ≥0∞} (hp : p ≠ ∞) (hv : AEStronglyMeasurable v μ)
    (h : ∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ ≤
      ENNReal.ofReal (c ^ p.toReal) * ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂ν) :
    eLpNorm v p μ ≤ ENNReal.ofReal c * eLpNorm w p ν := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · rw [eLpNorm_exponent_zero hv]
    exact zero_le
  have hr0 : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp₀ hp
  have hwle : (∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal) ≤ eLpNorm w p ν := by
    by_cases hw : AEStronglyMeasurable w ν
    · exact (eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp hw).ge
    · simp [eLpNorm_of_not_aestronglyMeasurable hw]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp hv]
  calc (∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal (c ^ p.toReal) * ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal c * (∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg hc hr0.le, ← ENNReal.rpow_mul,
          mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
    _ ≤ ENNReal.ofReal c * eLpNorm w p ν := by gcongr

/-- **Hölder's inequality in extended-valued `∫⁻` form**, raised to the power `r`: the `L¹`
integral of `u : α → ℝ≥0∞` is controlled by its `L^r` integral at the cost of the factor
`μ univ ^ (r - 1)`.  Stated for an `ℝ≥0∞`-valued `u`, so a norm-valued application passes
`fun x => ‖f x‖ₑ`; no measurability of `u` is needed.

On a finite measure space this is the nesting `L^r ⊆ L¹`; for a general `μ` it is only the
displayed inequality, which does not by itself give that inclusion.  No finiteness is assumed, and
the bound is not vacuous when `μ univ = ∞`: arithmetic in `ℝ≥0∞` makes the right-hand side `0`
rather than `∞` whenever `∫⁻ ‖f‖ₑ ^ r = 0`, and the inequality still holds there: a zero lower
integral of `u ^ r` forces a zero lower integral of `u`.  (This does not make a nonmeasurable `u`
vanish almost everywhere.) -/
theorem rpow_lintegral_le_measure_univ_rpow_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : α → ℝ≥0∞} {r : ℝ} (hr : 1 ≤ r) :
    (∫⁻ x, u x ∂μ) ^ r ≤ μ Set.univ ^ (r - 1) * ∫⁻ x, u x ^ r ∂μ := by
  have main (g : α → ℝ≥0∞) (hu : AEMeasurable g μ) :
      (∫⁻ x, g x ∂μ) ^ r ≤ μ Set.univ ^ (r - 1) * ∫⁻ x, g x ^ r ∂μ := by
    have hf : AEStronglyMeasurable g μ := hu.aestronglyMeasurable
    have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
    have hCr : eLpNorm g (ENNReal.ofReal r) μ = (∫⁻ x, g x ^ r ∂μ) ^ (1 / r) := by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top hf,
        ENNReal.toReal_ofReal hr0.le]
      simp only [eNorm_eq_self]
    have holder : ∫⁻ x, g x ∂μ
        ≤ (∫⁻ x, g x ^ r ∂μ) ^ (1 / r) * μ Set.univ ^ (1 - 1 / r) := by
      have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
      have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := g) (μ := μ) hle hf
      rw [eLpNorm_one_eq_lintegral_eNorm hf, hCr, ENNReal.toReal_one,
        ENNReal.toReal_ofReal hr0.le, div_one] at this
      simpa only [eNorm_eq_self] using this
    have hinv : 1 / r * r = 1 := by field_simp
    have hexp : (1 - 1 / r) * r = r - 1 := by field_simp
    calc (∫⁻ x, g x ∂μ) ^ r
        ≤ ((∫⁻ x, g x ^ r ∂μ) ^ (1 / r) * μ Set.univ ^ (1 - 1 / r)) ^ r :=
          ENNReal.rpow_le_rpow holder hr0.le
      _ = ((∫⁻ x, g x ^ r ∂μ) ^ (1 / r)) ^ r * (μ Set.univ ^ (1 - 1 / r)) ^ r :=
          ENNReal.mul_rpow_of_nonneg _ _ hr0.le
      _ = (∫⁻ x, g x ^ r ∂μ) * μ Set.univ ^ (r - 1) := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hinv, hexp, ENNReal.rpow_one]
      _ = μ Set.univ ^ (r - 1) * ∫⁻ x, g x ^ r ∂μ := mul_comm _ _
  -- Replace `u` by a measurable minorant `g ≤ u` with the same lower integral.
  obtain ⟨g, hgm, hgu, hg⟩ := exists_measurable_le_lintegral_eq μ u
  calc (∫⁻ x, u x ∂μ) ^ r = (∫⁻ x, g x ∂μ) ^ r := by rw [hg]
    _ ≤ μ Set.univ ^ (r - 1) * ∫⁻ x, g x ^ r ∂μ := main g hgm.aemeasurable
    _ ≤ μ Set.univ ^ (r - 1) * ∫⁻ x, u x ^ r ∂μ := by
        gcongr with x
        exact hgu x

end TauCeti

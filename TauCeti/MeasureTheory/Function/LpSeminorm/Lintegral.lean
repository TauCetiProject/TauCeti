/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The `Lᵖ` integral is bounded by the `p`-th power of the `Lᵖ` seminorm

For a finite exponent `p ≠ 0`, Mathlib's `MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral` identifies
`eLpNorm f p μ ^ p` with `∫⁻ ‖f‖ₑ ^ p ∂μ` for an almost everywhere strongly measurable `f`. Without
measurability the seminorm is `∞` by convention, so the inequality
`∫⁻ ‖f‖ₑ ^ p ∂μ ≤ eLpNorm f p μ ^ p` holds for every `f`
(`TauCeti.lintegral_rpow_enorm_le_rpow_eLpNorm`). This is the form in which a bound on the `Lᵖ`
seminorm is used to bound an integral, with no measurability side condition. For a natural
exponent `n ≠ 0` and measurable `f` the identity reads `∫⁻ ‖f‖ₑ ^ n ∂μ = eLpNorm f n μ ^ n`
(`TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow`). For an almost everywhere strongly measurable `f`
and `p ≠ 0, ∞` in `ℝ≥0∞`, the two sides agree
(`MeasureTheory.lintegral_rpow_enorm_eq_eLpNorm_rpow`), so `∫⁻ ‖f‖ₑ ^ p ∂μ ≤ t ^ p` gives
`eLpNorm f p μ ≤ t` (`MeasureTheory.eLpNorm_le_of_lintegral_rpow_le`). In particular a pointwise
bound `‖k x‖ ^ q ≤ t ^ (q - p) ‖f x‖ ^ p` with `t = ‖f‖_p` integrates to `‖k‖_q ≤ t`
(`MeasureTheory.eLpNorm_le_of_rpow_le_rpow_mul`). For `p ≠ 0`, dividing by a constant `c`
divides the seminorm by `c`: `eLpNorm (‖f‖ₑ / c) p μ = eLpNorm f p μ / c`
(`MeasureTheory.eLpNorm_enorm_div_const`).

Consequently a function in `Lᵖ` for `p ≠ 0` is finite almost everywhere
(`MeasureTheory.MemLp.ae_enorm_lt_top`), including for `p = ∞`.

For an almost everywhere strongly measurable function, square integrability is equivalent to
finiteness of the lower integral of its squared extended norm
(`MeasureTheory.AEStronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top`).

The same identification gives monotone convergence for the seminorm: the `Lᵖ` seminorm of the
supremum of an increasing sequence of functions with values in `[0, ∞]` is the supremum of their
seminorms (`MeasureTheory.eLpNorm_iSup_eq_iSup_eLpNorm`), also for `p = ∞`. Fatou's lemma bounds
the seminorm of an almost everywhere limit of such functions by the `liminf` of their seminorms
(`MeasureTheory.eLpNorm_le_liminf_eLpNorm_of_ae_tendsto`), also for `p = ∞`. With the triangle
inequality the identification gives Minkowski's inequality for series: for `1 ≤ p` the `Lᵖ`
seminorm of the sum of a countable family of functions with values in `[0, ∞]` is at most the sum
of their seminorms (`MeasureTheory.eLpNorm_tsum_le`). In particular a step function `∑ᵢ cᵢ 1_{Aᵢ}`
has `Lᵖ` seminorm at most `∑ᵢ cᵢ μ(Aᵢ) ^ (1 / p)` (`MeasureTheory.eLpNorm_tsum_indicator_const_le`).
-/

public section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

variable {α ε : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε] [ContinuousENorm ε]

namespace TauCeti

/-- For `p ≠ 0`, the integral `∫⁻ ‖f‖ₑ ^ p ∂μ` is at most `eLpNorm f p μ ^ p`, whether or not `f` is
almost everywhere strongly measurable. -/
theorem lintegral_rpow_enorm_le_rpow_eLpNorm {p : ℝ≥0} (hp : p ≠ 0) (f : α → ε) :
    ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ ≤ eLpNorm f p μ ^ (p : ℝ) := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact (eLpNorm_nnreal_pow_eq_lintegral hp hf).ge
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.top_rpow_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hp))]
    exact le_top

/-- For `n ≠ 0`, the `n`-th power of the `Lⁿ` seminorm of an almost everywhere strongly measurable
function is the integral of `‖f‖ₑ ^ n`. -/
theorem lintegral_enorm_pow_eq_eLpNorm_pow {n : ℕ} (hn : n ≠ 0) {f : α → ε}
    (hf : AEStronglyMeasurable f μ) : ∫⁻ x, ‖f x‖ₑ ^ n ∂μ = eLpNorm f n μ ^ n := by
  simpa only [ENNReal.coe_natCast, NNReal.coe_natCast, ENNReal.rpow_natCast] using
    (eLpNorm_nnreal_pow_eq_lintegral (p := (n : ℝ≥0)) (Nat.cast_ne_zero.2 hn) hf).symm

end TauCeti

namespace MeasureTheory

/-- An almost everywhere strongly measurable function is in `L²` exactly when the lower
integral of its squared extended norm is finite. -/
theorem AEStronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top
    {ε : Type*} [TopologicalSpace ε] [ENorm ε] {f : α → ε}
    (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ∞ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- For `p ≠ 0, ∞`, the integral of `‖f‖ₑ ^ p` is the `p`-th power of the `Lᵖ` seminorm of `f`. -/
theorem lintegral_rpow_enorm_eq_eLpNorm_rpow {f : α → ε} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = eLpNorm f p μ ^ p.toReal := by
  rw [eLpNorm_eq_eLpNorm' hp0 hp hf,
    lintegral_rpow_eNorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]

/-- If `∫ ‖k‖ ^ q ≤ t ^ q` then `‖k‖_q ≤ t`. -/
theorem eLpNorm_le_of_lintegral_rpow_le {k : α → ε} {q : ℝ≥0∞} {t : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hk : AEStronglyMeasurable k μ) (h : ∫⁻ x, ‖k x‖ₑ ^ q.toReal ∂μ ≤ t ^ q.toReal) :
    eLpNorm k q μ ≤ t := by
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [← ENNReal.rpow_le_rpow_iff hq', ← lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hk]
  exact h

/-- For `p ≠ 0`, the `Lᵖ` seminorm of `x ↦ ‖f x‖ₑ / c` is `eLpNorm f p μ / c`. -/
theorem eLpNorm_enorm_div_const {f : α → ε} {p : ℝ≥0∞} (hp : p ≠ 0)
    (hf : AEStronglyMeasurable f μ) (c : ℝ≥0∞) :
    eLpNorm (fun x => ‖f x‖ₑ / c) p μ = eLpNorm f p μ / c := by
  simp_rw [div_eq_mul_inv, mul_comm _ c⁻¹]
  rw [eLpNorm_const_mul_ennreal_of_pos (pos_iff_ne_zero.2 hp), eLpNorm_eNorm _ hf]

/-- If `‖f‖_q ≤ M` for `M ≠ 0, ∞`, then `∫ M ^ (r - q) ‖f‖ ^ q ≤ M ^ r` for every real `r`. -/
theorem lintegral_rpow_sub_mul_rpow_enorm_le {f : α → ε} {q M : ℝ≥0∞} (r : ℝ) (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hM0 : M ≠ 0) (hM : M ≠ ∞) (hf : AEStronglyMeasurable f μ)
    (hfM : eLpNorm f q μ ≤ M) :
    ∫⁻ x, M ^ (r - q.toReal) * ‖f x‖ₑ ^ q.toReal ∂μ ≤ M ^ r := by
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hM0 hM),
    lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hf]
  calc M ^ (r - q.toReal) * eLpNorm f q μ ^ q.toReal
      ≤ M ^ (r - q.toReal) * M ^ q.toReal := by gcongr
    _ = M ^ r := by rw [← ENNReal.rpow_add _ _ hM0 hM, sub_add_cancel]

/-- If `‖k x‖ ^ q ≤ t ^ (q - p) ‖f x‖ ^ p` pointwise, where `t = ‖f‖_p`, then `‖k‖_q ≤ t`. -/
theorem eLpNorm_le_of_rpow_le_rpow_mul {f k : α → ε} {p q : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hq0 : q ≠ 0) (hq : q ≠ ∞) (hf : AEStronglyMeasurable f μ)
    (hk : AEStronglyMeasurable k μ) (ht0 : eLpNorm f p μ ≠ 0) (ht : eLpNorm f p μ ≠ ∞)
    (hkf : ∀ x, ‖k x‖ₑ ^ q.toReal ≤
      eLpNorm f p μ ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal) :
    eLpNorm k q μ ≤ eLpNorm f p μ :=
  eLpNorm_le_of_lintegral_rpow_le hq0 hq hk <| (lintegral_mono hkf).trans <|
    lintegral_rpow_sub_mul_rpow_enorm_le _ hp0 hp ht0 ht hf le_rfl

/-- **Monotone convergence for the `Lᵖ` seminorm.** The `Lᵖ` seminorm of the pointwise supremum
of an almost everywhere increasing sequence of almost everywhere measurable functions with values
in `[0, ∞]` is the supremum of their `Lᵖ` seminorms. -/
theorem eLpNorm_iSup_eq_iSup_eLpNorm {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x) {p : ℝ≥0∞} :
    eLpNorm (fun x ↦ ⨆ n, f n x) p μ = ⨆ n, eLpNorm (f n) p μ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · -- At `p = ∞` each `f n` is bounded almost everywhere by its essential supremum.
    refine le_antisymm ?_ (iSup_le fun n ↦
      eLpNorm_mono_eNorm (hf n).aestronglyMeasurable fun x ↦ ?_)
    · rw [eLpNorm_exponent_top (AEMeasurable.iSup hf).aestronglyMeasurable, eLpNormEssSup]
      refine essSup_le_of_ae_le _ ?_
      filter_upwards [ae_all_iff.2 fun n ↦ ae_le_eLpNormEssSup (f := f n) (μ := μ)] with x hx
      simp only [eNorm_eq_self] at hx ⊢
      exact iSup_mono fun n ↦
        (hx n).trans_eq (eLpNorm_exponent_top (hf n).aestronglyMeasurable).symm
    · simpa only [eNorm_eq_self] using le_iSup (fun n ↦ f n x) n
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [eLpNorm_exponent_zero (AEMeasurable.iSup hf).aestronglyMeasurable,
      eLpNorm_exponent_zero (hf _).aestronglyMeasurable, iSup_const]
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp
      (AEMeasurable.iSup hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (hf _).aestronglyMeasurable, eNorm_eq_self,
    ENNReal.iSup_rpow_of_pos hr]
  rw [lintegral_iSup' (fun n ↦ (hf n).pow_const _)
    (hmono.mono fun x hx m n hmn ↦ ENNReal.rpow_le_rpow (hx hmn) hr.le),
    ENNReal.iSup_rpow_of_pos (by positivity)]

/-- **Minkowski's inequality for series.** For `1 ≤ p`, the `Lᵖ` seminorm of the pointwise sum of
a countable family of almost everywhere measurable functions with values in `[0, ∞]` is at most the
sum of their `Lᵖ` seminorms. -/
theorem eLpNorm_tsum_le {ι : Type*} [Countable ι] {f : ι → α → ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∑' i, f i x) p μ ≤ ∑' i, eLpNorm (f i) p μ := by
  have := Encodable.ofCountable ι
  -- The indices of code below `n` form an increasing sequence of finite sets exhausting `ι`.
  set s : ℕ → Finset ι := fun n ↦
    (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn
  have hs : ∀ t : Finset ι, ∃ n, t ⊆ s n := fun t ↦
    ⟨t.sup Encodable.encode + 1, fun i hi ↦ by
      simpa [s, Nat.lt_succ_iff] using Finset.le_sup (f := Encodable.encode) hi⟩
  have hmono : Monotone s := fun m n hmn i ↦ by
    simpa [s] using fun h ↦ h.trans_le hmn
  simp_rw [tsum_eq_iSup_sum' s hs]
  rw [eLpNorm_iSup_eq_iSup_eLpNorm (fun n ↦ Finset.aemeasurable_fun_sum _ fun i _ ↦ hf i)
    (ae_of_all _ fun x m n hmn ↦ Finset.sum_le_sum_of_subset (hmono hmn))]
  exact iSup_mono fun n ↦ by
    simpa only [Finset.sum_fn] using eLpNorm_sum_le (s := s n) (f := f) (μ := μ) hp

/-- For `1 ≤ p`, the `Lᵖ` seminorm of a step function `∑ᵢ cᵢ 1_{Aᵢ}` over countably many null
measurable sets is at most `∑ᵢ cᵢ μ(Aᵢ) ^ (1 / p)`. -/
theorem eLpNorm_tsum_indicator_const_le {ι : Type*} [Countable ι] {A : ι → Set α}
    (hA : ∀ i, NullMeasurableSet (A i) μ) (c : ι → ℝ≥0∞) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∑' i, (A i).indicator (fun _ ↦ c i) x) p μ ≤
      ∑' i, c i * μ (A i) ^ (1 / p.toReal) :=
  (eLpNorm_tsum_le (fun i ↦ aemeasurable_const.indicator₀ (hA i)) hp).trans <|
    tsum_le_tsum fun i ↦ by
      simpa only [eNorm_eq_self] using eLpNorm_indicator_const_le (c i) p (hA i)

/-- **Fatou's lemma for the `Lᵖ` seminorm.** If functions `h n` with values in `[0, ∞]` converge
almost everywhere to `H`, then `‖H‖_q ≤ liminf ‖h n‖_q`, for every exponent `q`. -/
theorem eLpNorm_le_liminf_eLpNorm_of_ae_tendsto {q : ℝ≥0∞} {h : ℕ → α → ℝ≥0∞} {H : α → ℝ≥0∞}
    (hh : ∀ n, AEMeasurable (h n) μ) (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ h n x) atTop (𝓝 (H x))) :
    eLpNorm H q μ ≤ liminf (fun n ↦ eLpNorm (h n) q μ) atTop := by
  have hH : AEMeasurable H μ := aemeasurable_of_tendsto_metrizable_ae' hh hlim
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [eLpNorm_exponent_zero hH.aestronglyMeasurable]
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [eLpNorm_exponent_top hH.aestronglyMeasurable]
    have hbd : ∀ᵐ x ∂μ, ∀ n, h n x ≤ eLpNorm (h n) ∞ μ := ae_all_iff.2 fun n ↦ by
      simpa only [eLpNorm_exponent_top (hh n).aestronglyMeasurable, eNorm_eq_self] using
        ae_le_eLpNormEssSup (f := h n) (μ := μ)
    refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
    filter_upwards [hlim, hbd] with x hx hb
    rw [eNorm_eq_self, ← hx.liminf_eq]
    exact liminf_le_liminf (.of_forall hb)
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hpow {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
      ∫⁻ x, f x ^ q.toReal ∂μ = eLpNorm f q μ ^ q.toReal := by
    simpa only [eNorm_eq_self] using
      lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hf.aestronglyMeasurable
  have hmono : Monotone fun t : ℝ≥0∞ ↦ t ^ q.toReal := fun _ _ hst ↦ ENNReal.rpow_le_rpow hst hq'.le
  rw [← ENNReal.rpow_le_rpow_iff hq', ← hpow hH,
    hmono.map_liminf_of_continuousAt _ (ENNReal.continuous_rpow_const.continuousAt)]
  calc ∫⁻ x, H x ^ q.toReal ∂μ = ∫⁻ x, liminf (fun n ↦ h n x ^ q.toReal) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun x hx ↦
          ((ENNReal.continuous_rpow_const.tendsto _).comp hx).liminf_eq.symm)
    _ ≤ liminf (fun n ↦ ∫⁻ x, h n x ^ q.toReal ∂μ) atTop :=
        lintegral_liminf_le' fun n ↦ (hh n).pow_const _
    _ = _ := by simp only [hpow (hh _), Function.comp_def]

end MeasureTheory

namespace MeasureTheory.MemLp

/-- A function in `Lᵖ` with `p ≠ 0` is finite almost everywhere. -/
theorem ae_enorm_lt_top {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp : p ≠ 0) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
    exact hx.trans_lt (eLpNormEssSup_le_eLpNorm_top.trans_lt hf.eLpNorm_lt_top)
  have hlt := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp hp_top hf.eLpNorm_lt_top
  filter_upwards [ae_lt_top' (hf.aestronglyMeasurable.eNorm.pow_const _) hlt.ne] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos hp hp_top)).1 hx

end MeasureTheory.MemLp

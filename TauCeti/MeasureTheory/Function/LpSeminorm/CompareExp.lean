/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Comparison of `Lᵖ` seminorms

On a finite measure space, Mathlib's exponent comparison
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` bounds the `L¹` seminorm by the `Lᵖ` seminorm (for
`1 ≤ p`) times a finite constant. This file packages that comparison as a convergence statement
both for the `L¹` seminorm and for the Bochner integral `∫ ‖f i‖ ∂μ`, the form in which `L¹`
convergence of a difference `f i = W i - a` is usually consumed.

It also contains the comparison of seminorms of exponents related by `1 / s = r / p` for pointwise
bounds `‖u‖ ≤ ‖f‖ ^ r`.

On an arbitrary measure space, a common bound for the `Lᵖ` seminorm and the essential supremum
also bounds every intermediate `Lᵠ` seminorm (`MeasureTheory.eLpNorm_le_of_exponent_le`).
This comparison is useful for embeddings of real interpolation spaces.

## Main declarations

* `TauCeti.eLpNorm_le_eLpNorm_rpow`: if `‖u‖ ≤ ‖f‖ ^ r`, then `‖u‖_s ≤ ‖f‖_p ^ r` when
  `1 / s = r / p`.
* `TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one`: its form for Hölder conjugate exponents.
* `TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm`: convergence to zero in `Lᵖ`
  for `1 ≤ p` implies convergence to zero in `L¹`.
* `TauCeti.MeasureTheory.tendsto_integral_norm_of_tendsto_eLpNorm`: if `eLpNorm (f i) p μ → 0`
  for some `1 ≤ p`, then `∫ ‖f i‖ ∂μ → 0`.
* `TauCeti.MeasureTheory.not_tendsto_eLpNorm_sub_of_separated`: a sequence whose terms stay a
  definite `L¹` distance apart has no subsequence converging in `Lᵖ` for any `1 ≤ p`.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

section Rpow

variable {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- If `‖u‖ ≤ ‖f‖ ^ r` almost everywhere with `r ≥ 0`, then `‖u‖_s ≤ ‖f‖_p ^ r` for the exponent
`1 / s = r / p`. For `r = 0` this reads `‖u‖_∞ ≤ 1`. -/
theorem eLpNorm_le_eLpNorm_rpow {f : α → E} {u : α → F} {p s : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r)
    (hf : AEStronglyMeasurable f μ) (hu : AEStronglyMeasurable u μ)
    (hs : s⁻¹ = ENNReal.ofReal r * p⁻¹) (hle : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖f x‖ ^ r) :
    eLpNorm u s μ ≤ eLpNorm f p μ ^ r := by
  rcases hr.eq_or_lt with rfl | hr
  · have hs : s = ∞ := by simpa using hs
    subst hs
    rw [ENNReal.rpow_zero, eLpNorm_exponent_top hu]
    simpa using eLpNormEssSup_le_of_ae_bound (C := 1) (by simpa using hle)
  · calc eLpNorm u s μ ≤ eLpNorm (fun x => ‖f x‖ ^ r) s μ := eLpNorm_mono_ae_real hu hle
      _ = eLpNorm f (s * ENNReal.ofReal r) μ ^ r := eLpNorm_norm_rpow f hf hr
      _ = eLpNorm f p μ ^ r := by
        congr 2
        have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
        rw [← inv_inv s, hs, ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top), inv_inv,
          mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_mul]

/-- If `‖g‖ ≤ ‖f‖ ^ (q - 1)` almost everywhere, then `‖g‖_{q'} ≤ ‖f‖_q ^ (q - 1)` for Hölder
conjugate exponents `q < ∞` and `q'`. -/
theorem eLpNorm_le_eLpNorm_rpow_toReal_sub_one {q q' : ℝ≥0∞} [hqq : q.HolderConjugate q']
    (hq : q ≠ ∞) {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hle : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖ ^ (q.toReal - 1)) :
    eLpNorm g q' μ ≤ eLpNorm f q μ ^ (q.toReal - 1) := by
  have hr1 : 1 ≤ q.toReal := by simpa using ENNReal.toReal_mono hq hqq.one_le
  refine eLpNorm_le_eLpNorm_rpow (by linarith) hf hg ?_ hle
  rw [← ENNReal.HolderConjugate.sub_one_mul_inv q q' hq, ENNReal.ofReal_sub _ zero_le_one,
    ENNReal.ofReal_toReal hq, ENNReal.ofReal_one]

end Rpow

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The exponent `1 / 1 - 1 / p` comparing `L¹` with `Lᵖ` on a finite measure is nonnegative
when `1 ≤ p`. -/
theorem sub_one_div_toReal_nonneg {p : ℝ≥0∞} (hp : 1 ≤ p) :
    0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
  rcases eq_or_ne p ⊤ with rfl | hp'
  · simp
  · have : 1 ≤ p.toReal := by
      simpa using ENNReal.toReal_mono hp' hp
    simpa using inv_le_one_of_one_le₀ this

/-- On a finite measure space, convergence to zero in `Lᵖ` for `1 ≤ p` implies convergence
to zero in `L¹`. No measurability hypothesis or finiteness assumption on `p` is needed. -/
theorem tendsto_eLpNorm_one_of_tendsto_eLpNorm {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 1 μ) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
    fun _ => eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hp one_pos
  simpa using ENNReal.Tendsto.mul_const h
    (.inr (ENNReal.rpow_ne_top_of_nonneg (sub_one_div_toReal_nonneg hp)
      (measure_ne_top μ Set.univ)))

/-- **`Lᵖ` convergence implies `L¹` convergence on a finite measure space.** If `1 ≤ p` and a
family `f` tends to `0` in `Lᵖ` along a filter `l`, then `∫ ‖f i‖` tends to `0` along `l`.
No measurability hypothesis is needed: `eLpNorm (f i) p μ` is finite eventually along `l`, which
forces `f i` to be a.e. strongly measurable. -/
theorem tendsto_integral_norm_of_tendsto_eLpNorm {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, ‖f i ω‖ ∂μ) l (𝓝 0) := by
  have hL1 := tendsto_eLpNorm_one_of_tendsto_eLpNorm hp h
  have hreal : Tendsto (fun i => (eLpNorm (f i) 1 μ).toReal) l (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
  refine hreal.congr' ?_
  filter_upwards [h.eventually_lt_const ENNReal.zero_lt_top] with i hi
  have hf := aestronglyMeasurable_of_eLpNorm_ne_top hi.ne
  rw [eLpNorm_one_eq_lintegral_enorm hf, integral_norm_eq_lintegral_enorm hf]

/-- If, for all large `m`, the terms `f n` with `n` large stay at `L¹` distance at least `ε` from
`f m`, then no subsequence of `f` converges in `Lᵖ` for any `1 ≤ p`, on a finite measure. -/
theorem not_tendsto_eLpNorm_sub_of_separated {E : Type*} [NormedAddCommGroup E] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → E} {ε : ℝ≥0∞} (hε : 0 < ε)
    (hsep : ∀ᶠ m in atTop, ∀ᶠ n in atTop, ε ≤ eLpNorm (f m - f n) 1 μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {φ : ℕ → ℕ} (hφ : StrictMono φ) {g : Ω → E} :
    ¬ Tendsto (fun k => eLpNorm (f (φ k) - g) p μ) atTop (𝓝 0) := by
  intro h
  have h1 := tendsto_eLpNorm_one_of_tendsto_eLpNorm hp h
  have hsep' : ∀ᶠ k in atTop, ∀ᶠ k' in atTop, ε ≤ eLpNorm (f (φ k) - f (φ k')) 1 μ :=
    (hφ.tendsto_atTop.eventually hsep).mono fun _ hk => hφ.tendsto_atTop.eventually hk
  have hsmall : ∀ᶠ k in atTop, eLpNorm (f (φ k) - g) 1 μ < ε / 2 :=
    h1.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))
  obtain ⟨k₀, hk₀, hk₀small⟩ := (hsep'.and hsmall).exists
  obtain ⟨k, hk, hksmall⟩ := (hk₀.and hsmall).exists
  have htri : eLpNorm (f (φ k₀) - f (φ k)) 1 μ ≤
      eLpNorm (f (φ k₀) - g) 1 μ + eLpNorm (f (φ k) - g) 1 μ := by
    have : f (φ k₀) - f (φ k) = (f (φ k₀) - g) - (f (φ k) - g) := by abel
    rw [this]
    exact eLpNorm_sub_le le_rfl
  have := (hk.trans htri).trans_lt (ENNReal.add_lt_add hk₀small hksmall)
  rw [ENNReal.add_halves] at this
  exact lt_irrefl _ this

end MeasureTheory

end TauCeti

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [SeminormedAddCommGroup E]
  {μ : Measure α} {f : α → E} {p q : ℝ≥0∞}

/-- If both the `Lᵖ` seminorm and the essential supremum are at most one, every larger-exponent
`Lᵠ` seminorm is at most one, even on an infinite measure space. -/
theorem eLpNorm_le_one_of_exponent_le (hf : AEStronglyMeasurable f μ) (hp : 0 < p)
    (hpq : p ≤ q) (hfp : eLpNorm f p μ ≤ 1) (hf1 : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ 1) :
    eLpNorm f q μ ≤ 1 := by
  by_cases hq : q = ∞
  · subst q
    rw [eLpNorm_exponent_top hf]
    exact eLpNormEssSup_le_of_ae_enorm_bound hf1
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hq0 : q ≠ 0 := (hp.trans_le hpq).ne'
  have hint : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≤ 1 := by
    rw [eLpNorm_eq_eLpNorm' hp.ne' hp' hf] at hfp
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp.ne' hp')]
    exact ENNReal.rpow_le_one hfp ENNReal.toReal_nonneg
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hf]
  apply ENNReal.rpow_le_one _ (by positivity)
  refine (lintegral_mono_ae ?_).trans hint
  filter_upwards [hf1] with x hx
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx (ENNReal.toReal_mono hq hpq)

/-- A common positive bound for the `Lᵖ` seminorm and the essential supremum bounds every
`Lᵠ` seminorm with `p ≤ q`. No finiteness assumption on the measure is needed. -/
theorem eLpNorm_le_of_exponent_le
    (hf : AEStronglyMeasurable f μ) (hp : 0 < p) (hpq : p ≤ q) {M : ℝ} (hM : 0 < M)
    (hfp : eLpNorm f p μ ≤ ENNReal.ofReal M) (hfM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) :
    eLpNorm f q μ ≤ ENNReal.ofReal M := by
  have hnorm : ∀ r, eLpNorm (M⁻¹ • fun x => ‖f x‖) r μ =
      (ENNReal.ofReal M)⁻¹ * eLpNorm f r μ := by
    intro r
    rw [eLpNorm_const_smul, eLpNorm_congr_enorm_ae hf.norm hf
      (Filter.Eventually.of_forall fun x => enorm_norm (f x)),
      Real.enorm_of_nonneg (by positivity), ENNReal.ofReal_inv_of_pos hM]
  have hscaled : eLpNorm (M⁻¹ • fun x => ‖f x‖) p μ ≤ 1 := by
    rw [hnorm]
    exact (mul_le_mul_right hfp _).trans_eq
      (ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.2 hM) ENNReal.ofReal_ne_top)
  have hbound : ∀ᵐ x ∂μ, ‖(M⁻¹ • fun x => ‖f x‖) x‖ₑ ≤ 1 := by
    filter_upwards [hfM] with x hx
    rw [Pi.smul_apply, ← ofReal_norm, norm_smul, norm_norm,
      Real.norm_of_nonneg (by positivity), ENNReal.ofReal_le_one]
    exact (inv_mul_le_iff₀ hM).2 (by simpa using hx)
  have h := eLpNorm_le_one_of_exponent_le (hf.norm.const_smul _) hp hpq hscaled hbound
  rw [hnorm, ENNReal.inv_mul_le_iff (ENNReal.ofReal_ne_zero_iff.2 hM)
    ENNReal.ofReal_ne_top, mul_one] at h
  exact h

end MeasureTheory

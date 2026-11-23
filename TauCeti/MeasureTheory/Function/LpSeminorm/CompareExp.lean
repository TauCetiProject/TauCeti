/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Data.ENNReal.Inv

/-!
# Comparison of `Lᵖ` seminorms

On a finite measure space, Mathlib's exponent comparison
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` bounds the `L¹` seminorm by the `Lᵖ` seminorm (for
`1 ≤ p`) times a finite constant. This file packages that comparison as a convergence statement
both for the `L¹` seminorm and for the Bochner integral `∫ ‖f i‖ ∂μ`, the form in which `L¹`
convergence of a difference `f i = W i - a` is usually consumed.

It also contains the comparison of seminorms of exponents related by `1 / s = r / p` for pointwise
bounds `‖u‖ ≤ ‖f‖ ^ r`, and Hölder's inequality `MeasureTheory.MemLp.fun_prod` for a product of
functions over a nonempty finset `s` with the common exponent `p * s.card`.

On an arbitrary measure space, a common bound for the `Lᵖ` seminorm and the essential supremum
also bounds every intermediate `Lᵠ` seminorm (`MeasureTheory.eLpNorm_le_of_exponent_le`).
This comparison is useful for embeddings of real interpolation spaces. A function bounded almost
everywhere and vanishing off a set of finite measure lies in every `Lᵖ`
(`MeasureTheory.memLp_of_norm_le_of_measure_support_ne_top`).

## Main declarations

* `TauCeti.eLpNorm_le_eLpNorm_rpow`: if `‖u‖ ≤ ‖f‖ ^ r`, then `‖u‖_s ≤ ‖f‖_p ^ r` when
  `1 / s = r / p`.
* `TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one`: its form for Hölder conjugate exponents.
* `TauCeti.eLpNorm_le_rpow_inv_mul_eLpNorm_of_eLpNorm_norm_rpow_le`: a bound between seminorms of
  `‖f‖ ^ r` and `‖g‖ ^ r` is a bound between seminorms of `f` and `g` at `r` times the exponents.
* `TauCeti.memLp_fun_prod_of_memLp_mul_card`: a product over a nonempty finset `s` of functions
  in `L^(p * s.card)` lies in `Lᵖ`.
* `TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm`: convergence to zero in `Lᵖ`
  for `1 ≤ p` implies convergence to zero in `L¹`.
* `TauCeti.MeasureTheory.tendsto_setLIntegral_enorm_of_tendsto_setLIntegral_ofReal_norm_sq`: on
  sets of bounded measure, convergence to zero of `L²` norms implies that of `L¹` norms.
* `TauCeti.MeasureTheory.tendsto_eLpNorm_of_tendsto_eLpNorm_one`: convergence to zero in `L¹`
  implies convergence to zero in `Lᵖ` for `p ≤ 1`.
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
    (hu : AEStronglyMeasurable u μ)
    (hs : s⁻¹ = ENNReal.ofReal r * p⁻¹) (hle : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖f x‖ ^ r) :
    eLpNorm u s μ ≤ eLpNorm f p μ ^ r := by
  rcases hr.eq_or_lt with rfl | hr
  · have hs : s = ∞ := by simpa using hs
    subst hs
    rw [ENNReal.rpow_zero, eLpNorm_exponent_top hu]
    simpa using eLpNormEssSup_le_of_ae_bound (C := 1) (by simpa using hle)
  · by_cases hf : AEStronglyMeasurable f μ
    · calc eLpNorm u s μ ≤ eLpNorm (fun x => ‖f x‖ ^ r) s μ := eLpNorm_mono_ae_real hu hle
        _ = eLpNorm f (s * ENNReal.ofReal r) μ ^ r := eLpNorm_norm_rpow f hf hr
        _ = eLpNorm f p μ ^ r := by
          congr 2
          have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
          rw [← inv_inv s, hs, ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top),
            inv_inv, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top,
            one_mul]
    · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.top_rpow_of_pos hr]
      exact le_top

/-- If `‖g‖ ≤ ‖f‖ ^ (q - 1)` almost everywhere, then `‖g‖_{q'} ≤ ‖f‖_q ^ (q - 1)` for Hölder
conjugate exponents `q < ∞` and `q'`. -/
theorem eLpNorm_le_eLpNorm_rpow_toReal_sub_one {q q' : ℝ≥0∞} [hqq : q.HolderConjugate q']
    (hq : q ≠ ∞) {f : α → E} {g : α → F} (hg : AEStronglyMeasurable g μ)
    (hle : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖ ^ (q.toReal - 1)) :
    eLpNorm g q' μ ≤ eLpNorm f q μ ^ (q.toReal - 1) := by
  have hr1 : 1 ≤ q.toReal := by simpa using ENNReal.toReal_mono hq hqq.one_le
  refine eLpNorm_le_eLpNorm_rpow (by linarith) hg ?_ hle
  rw [← ENNReal.HolderConjugate.sub_one_mul_inv q q' hq, ENNReal.ofReal_sub _ zero_le_one,
    ENNReal.ofReal_toReal hq, ENNReal.ofReal_one]

/-- **Changing exponents through a power.** For `r > 0`, a bound
`‖‖f‖^r‖_{L^p(μ)} ≤ B ‖‖g‖^r‖_{L^q(ν)}` is the bound
`‖f‖_{L^{pr}(μ)} ≤ B^{1/r} ‖g‖_{L^{qr}(ν)}`. -/
theorem eLpNorm_le_rpow_inv_mul_eLpNorm_of_eLpNorm_norm_rpow_le {ν : Measure α} {f : α → E}
    {g : α → F} {p q B : ℝ≥0∞} {r : ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g ν) (hr : 0 < r)
    (h : eLpNorm (fun x => ‖f x‖ ^ r) p μ ≤ B * eLpNorm (fun x => ‖g x‖ ^ r) q ν) :
    eLpNorm f (p * ENNReal.ofReal r) μ ≤ B ^ r⁻¹ * eLpNorm g (q * ENNReal.ofReal r) ν := by
  rw [eLpNorm_norm_rpow f hf hr, eLpNorm_norm_rpow g hg hr] at h
  have hr' : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
  have hpow := ENNReal.rpow_le_rpow h hr'
  rwa [ENNReal.mul_rpow_of_nonneg _ _ hr', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_inv_cancel₀ hr.ne', ENNReal.rpow_one, ENNReal.rpow_one] at hpow

end Rpow

/-- **Hölder's inequality** for a finite product with a common exponent: a product of functions
indexed by a nonempty finset `s` lies in `Lᵖ` when every factor lies in `L^(p * s.card)`. This is
`MeasureTheory.MemLp.fun_prod` with equal exponents, and it holds for any measure. -/
theorem memLp_fun_prod_of_memLp_mul_card {ι α 𝕜 : Type*} {_ : MeasurableSpace α}
    [NormedCommRing 𝕜] {μ : Measure α} {f : ι → α → 𝕜} {s : Finset ι} (hs : s.Nonempty)
    {p : ℝ≥0∞} (hf : ∀ i ∈ s, MemLp (f i) (p * s.card) μ) :
    MemLp (fun x ↦ ∏ i ∈ s, f i x) p μ := by
  have h := MemLp.fun_prod hf
  rwa [Finset.sum_const, nsmul_eq_mul, ENNReal.inv_mul_inv_mul_cancel
    (Nat.cast_ne_zero.2 hs.card_pos.ne') (ENNReal.natCast_ne_top _)] at h

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- On a finite measure space, convergence to zero in `Lᵖ` for `1 ≤ p` implies convergence
to zero in `L¹`. No measurability hypothesis or finiteness assumption on `p` is needed. -/
theorem tendsto_eLpNorm_one_of_tendsto_eLpNorm {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 1 μ) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
    fun _ => eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hp one_pos
  simpa using ENNReal.Tendsto.mul_const h (.inr (ENNReal.rpow_ne_top_of_nonneg
    (ENNReal.one_div_toReal_sub_one_div_toReal_nonneg one_ne_zero hp) (measure_ne_top μ Set.univ)))

/-- **`L²` control gives `L¹` control on sets of bounded measure.** If the sets `A i` eventually
have measure at most `C < ∞` and the `L²` norms of `g i` over `A i` tend to zero, then so do their
`L¹` norms. -/
theorem tendsto_setLIntegral_enorm_of_tendsto_setLIntegral_ofReal_norm_sq {ι F : Type*}
    [NormedAddCommGroup F] {μ : Measure Ω} {l : Filter ι} {A : ι → Set Ω}
    {g : ι → Ω → F} {C : ℝ≥0∞} (hC : C ≠ ∞) (hA : ∀ᶠ i in l, μ (A i) ≤ C)
    (hg : ∀ᶠ i in l, AEStronglyMeasurable (g i) (μ.restrict (A i)))
    (h : Tendsto (fun i ↦ ∫⁻ x in A i, ENNReal.ofReal (‖g i x‖ ^ 2) ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ x in A i, ‖g i x‖ₑ ∂μ) l (𝓝 0) := by
  have h2 : Tendsto (fun i ↦ (∫⁻ x in A i, ‖g i x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
      C ^ (1 / (2 : ℝ))) l (𝓝 0) := by
    have h' : Tendsto (fun i ↦ ∫⁻ x in A i, ‖g i x‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
      refine h.congr fun i ↦ lintegral_congr fun x ↦ ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two,
        Real.rpow_two]
    have h'' := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h'
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h''
    simpa using ENNReal.Tendsto.mul_const h''
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hA, hg] with i hiA hig
  -- Hölder's inequality on `A i`, which has measure at most `C`.
  have hL := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) one_le_two hig
  rw [eLpNorm_one_eq_lintegral_eNorm hig,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hig,
    Measure.restrict_apply_univ] at hL
  refine hL.trans (mul_le_mul' (le_of_eq ?_) ?_)
  · norm_num
  · rw [show (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2 : ℝ) = 1 / 2 by norm_num]
    exact ENNReal.rpow_le_rpow hiA (by norm_num)

/-- On a finite measure space, convergence to zero in `L¹` implies convergence to zero in `Lᵖ`
for every exponent `p ≤ 1`. No measurability hypothesis is needed: `eLpNorm (F i) 1 μ` is finite
eventually along `l`, which forces `F i` to be a.e. strongly measurable. -/
theorem tendsto_eLpNorm_of_tendsto_eLpNorm_one {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {F : ι → Ω → E} {p : ℝ≥0∞}
    (hp : p ≤ 1) (h : Tendsto (fun i => eLpNorm (F i) 1 μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (F i) p μ) l (𝓝 0) := by
  have hF : ∀ᶠ i in l, AEStronglyMeasurable (F i) μ := by
    filter_upwards [h.eventually_lt_const ENNReal.zero_lt_top] with i hi
    exact aestronglyMeasurable_of_eLpNorm_ne_top hi.ne
  rcases eq_or_ne p 0 with rfl | hp0
  · exact tendsto_const_nhds.congr' (hF.mono fun i hi => (eLpNorm_exponent_zero hi).symm)
  have h_exp : 0 ≤ 1 / p.toReal - 1 / (1 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_one, div_one, sub_nonneg,
      one_le_div (ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top ENNReal.one_ne_top hp))]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp)
  have h_lim := ENNReal.Tendsto.mul_const h
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg h_exp (measure_ne_top μ Set.univ)))
  rw [zero_mul] at h_lim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
    (Filter.Eventually.of_forall fun _ => zero_le)
    (hF.mono fun i hi => eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hi)

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
  rw [eLpNorm_one_eq_lintegral_eNorm hf, integral_norm_eq_lintegral_eNorm hf]

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
    exact eLpNormEssSup_le_of_ae_eNorm_bound hf1
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hq0 : q ≠ 0 := (hp.trans_le hpq).ne'
  have hint : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≤ 1 := by
    rw [eLpNorm_eq_eLpNorm' hp.ne' hp' hf] at hfp
    rw [lintegral_rpow_eNorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp.ne' hp')]
    exact ENNReal.rpow_le_one hfp ENNReal.toReal_nonneg
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq hf]
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
    rw [eLpNorm_const_smul, eLpNorm_congr_eNorm_ae hf.norm hf
      (Filter.Eventually.of_forall fun x => eNorm_norm (f x)),
      Real.eNorm_of_nonneg (by positivity), ENNReal.ofReal_inv_of_pos hM]
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

/-- A function bounded almost everywhere and vanishing off a set of finite measure lies in every
`Lᵖ`. -/
theorem memLp_of_norm_le_of_measure_support_ne_top {F : Type*} [NormedAddCommGroup F]
    {u : α → F} (hu : AEStronglyMeasurable u μ) {c : ℝ} (hc : ∀ᵐ x ∂μ, ‖u x‖ ≤ c) {s : Set α}
    (hs : μ s ≠ ∞) (hsupp : ∀ x, x ∉ s → u x = 0) (p : ℝ≥0∞) : MemLp u p μ :=
  (memLp_top_of_bound hu c hc).mono_exponent_of_measure_support_ne_top hsupp hs le_top

end MeasureTheory

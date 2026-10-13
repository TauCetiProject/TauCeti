/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Minkowski's integral inequality

For `1 ≤ p` and a jointly a.e. measurable `f : α → β → ℝ≥0∞` on a product of a σ-finite and an
s-finite measure space,

`(∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν`:

the `Lᵖ(μ)` seminorm of an integral over `ν` is at most the integral over `ν` of the `Lᵖ(μ)`
seminorms. This is the continuous form of Minkowski's inequality
`ENNReal.lintegral_Lp_add_le` for a sum of two functions. A typical use bounds the `Lᵖ` size of a
quantity accumulated along a time interval, such as the length `∫ |γ'|(t) dt` of a random curve,
by the time integral of the `Lᵖ` sizes of the integrand.

The statement is in `ℝ≥0∞`, so it needs no integrability hypotheses.

The proof is by duality. Write `G x = ∫⁻ y, f x y ∂ν` and let `R` be the right-hand side. Hölder's
inequality in `x` for each `y`, followed by Tonelli's theorem, gives
`∫⁻ x, G x * h x ∂μ ≤ R * (∫⁻ x, h x ^ q ∂μ) ^ (1 / q)` for every measurable `h`, where `q` is the
conjugate exponent. Testing against the indicator of a set of finite measure shows that `G` is
finite almost everywhere when `R` is finite; testing against `G ^ (p - 1)` on the sets where `G` is
bounded and `μ` is finite bounds the truncated integrals of `G ^ p`, and monotone convergence
removes the truncation.

## Main declarations

* `TauCeti.lintegral_Lp_lintegral_le`: Minkowski's integral inequality.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.19.
-/

public section

namespace TauCeti

open MeasureTheory Set Function
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- The duality bound behind Minkowski's integral inequality: by Hölder's inequality in `x` for
each `y` and Tonelli's theorem, pairing `x ↦ ∫⁻ y, f x y ∂ν` with `h` costs at most the right-hand
side of Minkowski's inequality times the `L^q` seminorm of `h`. -/
private lemma lintegral_lintegral_mul_le [SFinite μ] [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) {h : α → ℝ≥0∞} (hh : Measurable h) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∫⁻ x, (∫⁻ y, f x y ∂ν) * h x ∂μ ≤
      (∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν) * (∫⁻ x, h x ^ q ∂μ) ^ (1 / q) := by
  calc ∫⁻ x, (∫⁻ y, f x y ∂ν) * h x ∂μ = ∫⁻ x, ∫⁻ y, f x y * h x ∂ν ∂μ :=
        lintegral_congr fun x ↦ (lintegral_mul_const _ (hf.comp measurable_prodMk_left)).symm
    _ = ∫⁻ y, ∫⁻ x, f x y * h x ∂μ ∂ν :=
        lintegral_lintegral_swap (hf.mul (hh.comp measurable_fst)).aemeasurable
    _ ≤ ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) * (∫⁻ x, h x ^ q ∂μ) ^ (1 / q) ∂ν :=
        lintegral_mono fun y ↦ ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
          (hf.comp measurable_prodMk_right).aemeasurable hh.aemeasurable
    _ = _ := lintegral_mul_const _ (((hf.pow_const p).lintegral_prod_left' (μ := μ)).pow_const _)

/-- Testing against the indicator of a set of finite measure: when the right-hand side of
Minkowski's inequality is finite, so is `∫⁻ y, f x y ∂ν` for almost every `x`. -/
private lemma ae_lintegral_ne_top [SigmaFinite μ] [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hR : ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν ≠ ∞) :
    ∀ᵐ x ∂μ, ∫⁻ y, f x y ∂ν ≠ ∞ := by
  set G : α → ℝ≥0∞ := fun x ↦ ∫⁻ y, f x y ∂ν
  have hG : Measurable G := hf.lintegral_prod_right' (ν := ν)
  have hk (k : ℕ) : μ ({x | G x = ∞} ∩ spanningSets μ k) = 0 := by
    set E := {x | G x = ∞} ∩ spanningSets μ k
    have hE : MeasurableSet E :=
      (hG (measurableSet_singleton ∞)).inter (measurableSet_spanningSets μ k)
    have hEfin : μ E ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ k)).ne
    have h1 : ∫⁻ x, G x * E.indicator 1 x ∂μ ≤
        (∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν) * (∫⁻ x, E.indicator 1 x ^ q ∂μ) ^ (1 / q) :=
      lintegral_lintegral_mul_le hf (measurable_one.indicator hE) hpq
    have hL : ∫⁻ x, G x * E.indicator 1 x ∂μ = ∞ * μ E := by
      rw [← lintegral_indicator_const hE]
      refine lintegral_congr fun x ↦ ?_
      by_cases hx : x ∈ E
      · simp [indicator_of_mem hx, show G x = ∞ from hx.1]
      · simp [indicator_of_notMem hx]
    have hRq : ∫⁻ x, E.indicator 1 x ^ q ∂μ = μ E := by
      rw [← lintegral_indicator_one hE]
      refine lintegral_congr fun x ↦ ?_
      by_cases hx : x ∈ E
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hpq.symm.pos]
    rw [hL, hRq] at h1
    have hlt : ∞ * μ E < ∞ := h1.trans_lt (ENNReal.mul_lt_top hR.lt_top
      (ENNReal.rpow_lt_top_of_nonneg (one_div_pos.2 hpq.symm.pos).le hEfin))
    by_contra hne
    exact (ENNReal.top_mul hne ▸ hlt).ne rfl
  refine measure_mono_null (fun x hx ↦ ?_) (measure_iUnion_null hk)
  exact mem_iUnion.2 ⟨spanningSetsIndex μ x, not_not.1 hx, mem_spanningSetsIndex μ x⟩

/-- Testing against `(∫⁻ y, f x y ∂ν) ^ (p - 1)` on a measurable set `A`: if the integral of
`(∫⁻ y, f x y ∂ν) ^ p` over `A` is finite, it is at most the `p`-th power of the right-hand side
of Minkowski's inequality. -/
private lemma setLIntegral_rpow_lintegral_le [SFinite μ] [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) {p q : ℝ} (hpq : p.HolderConjugate q) {A : Set α}
    (hA : MeasurableSet A) (hfin : ∫⁻ x in A, (∫⁻ y, f x y ∂ν) ^ p ∂μ ≠ ∞) :
    ∫⁻ x in A, (∫⁻ y, f x y ∂ν) ^ p ∂μ ≤ (∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν) ^ p := by
  set R := ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν
  set G : α → ℝ≥0∞ := fun x ↦ ∫⁻ y, f x y ∂ν
  set N := ∫⁻ x in A, G x ^ p ∂μ
  have hG : Measurable G := hf.lintegral_prod_right' (ν := ν)
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hmul (x : α) : G x * A.indicator (fun x ↦ G x ^ (p - 1)) x =
      A.indicator (fun x ↦ G x ^ p) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      conv_rhs => rw [show p = 1 + (p - 1) by ring]
      rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith [hpq.lt]), ENNReal.rpow_one]
    · simp [indicator_of_notMem hx]
  have hpow (x : α) :
      A.indicator (fun x ↦ G x ^ (p - 1)) x ^ q = A.indicator (fun x ↦ G x ^ p) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem hx, ← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
    · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hq0]
  have h1 : N ≤ R * N ^ (1 / q) := by
    have h := lintegral_lintegral_mul_le (μ := μ) (ν := ν) hf
      ((hG.pow_const (p - 1)).indicator hA) hpq
    simp only [hpow, lintegral_indicator hA] at h
    calc N = ∫⁻ x, G x * A.indicator (fun x ↦ G x ^ (p - 1)) x ∂μ := by
          simp only [hmul, lintegral_indicator hA, N]
      _ ≤ _ := h
  -- `N ≤ R * N ^ (1 / q)` with `N` finite gives `N ^ (1 / p) ≤ R`.
  rw [← ENNReal.rpow_inv_le_iff hp0, ← one_div]
  rcases eq_or_ne N 0 with hN0 | hN0
  · rw [hN0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact bot_le
  have hsplit : N ^ (1 / p) * N ^ (1 / q) = N := by
    rw [← ENNReal.rpow_add _ _ hN0 hfin, one_div, one_div, hpq.inv_add_inv_eq_one,
      ENNReal.rpow_one]
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos (pos_iff_ne_zero.2 hN0) hfin).ne'
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin)).1 (hsplit.trans_le h1)

/-- Minkowski's integral inequality for a jointly measurable integrand. -/
private lemma lintegral_Lp_lintegral_le_of_measurable [SigmaFinite μ] [SFinite ν]
    {f : α → β → ℝ≥0∞} (hf : Measurable (uncurry f)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  rcases hp.eq_or_lt with rfl | hp1
  · simpa using (lintegral_lintegral_swap hf.aemeasurable).le
  set R := ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν
  set G : α → ℝ≥0∞ := fun x ↦ ∫⁻ y, f x y ∂ν
  have hG : Measurable G := hf.lintegral_prod_right' (ν := ν)
  have hp0 : 0 < p := one_pos.trans hp1
  have hpq : p.HolderConjugate p.conjExponent := .conjExponent hp1
  rcases eq_or_ne R ∞ with hR | hR
  · rw [hR]
    exact le_top
  -- Truncate to the sets `A n` where `G` is bounded by `n` and `μ` is finite.
  set A : ℕ → Set α := fun n ↦ {x | G x ≤ n} ∩ spanningSets μ n
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurableSet_le hG measurable_const).inter (measurableSet_spanningSets μ n)
  have hAmono : Monotone A := fun n m hnm ↦ inter_subset_inter
    (fun x (hx : G x ≤ n) ↦ hx.trans (by exact_mod_cast hnm)) (monotone_spanningSets μ hnm)
  have hN (n : ℕ) : ∫⁻ x in A n, G x ^ p ∂μ ≤ R ^ p := by
    refine setLIntegral_rpow_lintegral_le hf hpq (hAm n) (ne_top_of_le_ne_top ?_
      (setLIntegral_mono measurable_const fun x hx ↦ ENNReal.rpow_le_rpow hx.1 hp0.le))
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top n))
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
  -- Since `G` is finite almost everywhere, monotone convergence removes the truncation.
  have hsup : ∀ᵐ x ∂μ, ⨆ n, (A n).indicator (fun x ↦ G x ^ p) x = G x ^ p := by
    filter_upwards [ae_lintegral_ne_top hf hpq hR] with x hx
    refine le_antisymm (iSup_le fun n ↦ indicator_le_self _ _ x) ?_
    obtain ⟨n₁, hn₁⟩ := ENNReal.exists_nat_gt hx
    obtain ⟨n₂, hn₂⟩ : ∃ n, x ∈ spanningSets μ n := ⟨_, mem_spanningSetsIndex μ x⟩
    refine le_iSup_of_le (max n₁ n₂) (le_of_eq ?_)
    rw [indicator_of_mem]
    exact ⟨hn₁.le.trans (by exact_mod_cast le_max_left n₁ n₂),
      monotone_spanningSets μ (le_max_right n₁ n₂) hn₂⟩
  rw [one_div, ENNReal.rpow_inv_le_iff hp0, ← lintegral_congr_ae hsup,
    lintegral_iSup (fun n ↦ (hG.pow_const p).indicator (hAm n))
      (fun n m hnm x ↦ indicator_le_indicator_of_subset (hAmono hnm) (fun _ ↦ bot_le) x)]
  exact iSup_le fun n ↦ (lintegral_indicator (hAm n) _).trans_le (hN n)

/-- **Minkowski's integral inequality.** For `1 ≤ p` and a jointly a.e. measurable
`f : α → β → ℝ≥0∞`, the `Lᵖ(μ)` seminorm of `x ↦ ∫⁻ y, f x y ∂ν` is at most the integral over `ν`
of the `Lᵖ(μ)` seminorms of the functions `x ↦ f x y`:
`(∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν`. -/
theorem lintegral_Lp_lintegral_le [SigmaFinite μ] [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  set g : α → β → ℝ≥0∞ := curry (hf.mk _)
  have hg : Measurable (uncurry g) := by simpa [g] using hf.measurable_mk
  have hfg : ∀ᵐ z ∂μ.prod ν, uncurry f z = uncurry g z := by
    filter_upwards [hf.ae_eq_mk] with z hz
    simpa [g] using hz
  -- Replace `f` by its measurable modification `g` on both sides.
  have hL : ∀ᵐ x ∂μ, ∫⁻ y, f x y ∂ν = ∫⁻ y, g x y ∂ν := by
    filter_upwards [Measure.ae_ae_of_ae_prod hfg] with x hx using lintegral_congr_ae hx
  have hR : ∀ᵐ y ∂ν, ∫⁻ x, f x y ^ p ∂μ = ∫⁻ x, g x y ^ p ∂μ := by
    have hswap : ∀ᵐ z ∂ν.prod μ, uncurry f z.swap = uncurry g z.swap :=
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hfg
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with y hy
    exact lintegral_congr_ae (hy.mono fun x hx ↦ by simpa using congrArg (· ^ p) hx)
  rw [lintegral_congr_ae (hL.mono fun x hx ↦ by rw [hx]),
    lintegral_congr_ae (hR.mono fun y hy ↦ by rw [hy])]
  exact lintegral_Lp_lintegral_le_of_measurable hg hp

end TauCeti

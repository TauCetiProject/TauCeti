/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.ParamZeros.UpperTail

/-!
# Real parameter zeros of Tricomi's incomplete Gamma function

This file classifies the real zeros in the parameter `a` of Tricomi's entire incomplete Gamma
function `γ*(a, x)` for a fixed real argument `x` (DLMF §8.13(iii)):

* For `x = 0`, `γ*(a, 0) = 1 / Γ(a + 1)` vanishes precisely at the negative integers
  `a = -1, -2, ...` (`Complex.tricomiIncompleteGamma_zero_right_eq_zero_iff`).
* For `a ≥ 0` and any real `x`, `Re γ*(a, x) > 0`, so `γ*(·, x)` has no nonnegative real zeros
  (`Complex.tricomiIncompleteGamma_ofReal_re_pos_of_nonneg`).
* For `x < 0`, `γ*(·, x)` has a unique simple zero in each unit interval `(-m - 1, -m)` (`m ∈ ℕ`),
  and hence exactly two simple zeros in `(-2n, 2 - 2n)` for every `n ≥ 1`
  (`Complex.tricomiIncompleteGamma_param_zeros_Ioo_neg_nat`,
  `Complex.tricomiIncompleteGamma_param_zeros_of_neg`).
* For `x > 0`, `γ*(·, x)` is strictly positive on every odd band `(1 - 2n, 2 - 2n)`
  (`Complex.tricomiIncompleteGamma_ofReal_re_pos_of_odd_band`), and in each even negative band
  `(-2n, 1 - 2n)` (`n ≥ 1`) there is a threshold `x*_n > 0` where two simple zeros for
  `0 < x < x*_n` coalesce into a single double zero at `x = x*_n` and disappear for `x > x*_n`
  (`Complex.tricomiIncompleteGamma_param_zeros`).

## Implementation notes

The declarations live in the root `Complex` namespace alongside `Complex.tricomiIncompleteGamma`.
For `x > 0`, the analysis passes through the logarithmic potential
`Φ(a, x) = log Γ(a) - a log x - log I_0(a, x)` on `(-2n, 1 - 2n)`, where
`I_0(a, x) = TauCeti.tricomiTailMoment 0 a x`. The splitting identity
`Re γ*(a, x) = x^{-a} (1 - exp(-Φ(a, x)))` reduces the zero count and multiplicity to the sign
of `min_a Φ(a, x)`, while strict convexity of `Φ(·, x)` combines
`TauCeti.tricomiTailMoment_variance_le` with `ψ'(a) = ψ'(a + 1) + 1 / a² > 1 / a²` from
`Real.deriv_digamma_apply_add_nat` and `Real.deriv_digamma_pos`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.13(iii)](https://dlmf.nist.gov/8.13#iii).
* K. S. Kölbig, *On the zeros of the incomplete gamma function*, Math. Comp. 26 (1972), 451–455.
* F. G. Tricomi, *Sulla funzione gamma incompleta*, Ann. Mat. Pura Appl. (4) 31 (1950).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set TauCeti
open scoped Nat Topology Interval

namespace Complex

/-! ### Zeros at `x = 0` and positivity for `a ≥ 0` -/

/-- **DLMF §8.13(iii)(c)**: at `z = 0`, Tricomi's function vanishes precisely at the negative
integers `a = -n` with `n ≥ 1`. -/
theorem tricomiIncompleteGamma_zero_right_eq_zero_iff (a : ℂ) :
    tricomiIncompleteGamma a 0 = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℂ) := by
  rw [tricomiIncompleteGamma_zero_right, inv_eq_zero, Gamma_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m), by push_cast; linear_combination hm⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n - 1, ?_⟩
    have hn' : (n : ℂ) = ((n - 1 : ℕ) : ℂ) + 1 := by exact_mod_cast (Nat.sub_add_cancel hn).symm
    rw [hn']; ring

/-- For every nonnegative real parameter `a` and every real `x`, `Re γ*(a, x) > 0`; in particular,
`γ*(a, x)` has no zeros with real `a ≥ 0`. -/
theorem tricomiIncompleteGamma_ofReal_re_pos_of_nonneg {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    0 < (tricomiIncompleteGamma a x).re := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  · rw [tricomiIncompleteGamma_ofReal_re_eq_integral ha']
    refine mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos ha')) ?_
    have hint_rpow : IntervalIntegrable (fun t : ℝ => t ^ (a - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hint : IntervalIntegrable (fun t : ℝ => t ^ (a - 1) * Real.exp (-(x * t))) volume 0 1 := by
      refine (hint_rpow.const_mul (Real.exp |x|)).mono_fun ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
        refine ContinuousOn.mul (fun t ht => ?_) (Continuous.continuousOn (by fun_prop))
        rw [uIoc_of_le zero_le_one] at ht
        exact (Real.continuousAt_rpow_const t (a - 1) (Or.inl ht.1.ne')).continuousWithinAt
      · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
        rw [uIoc_of_le zero_le_one] at ht
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le),
          Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.1.le _)),
          mul_comm]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg ht.1.le _)
        have h1 : -(x * t) ≤ |x * t| := neg_le_abs _
        rw [abs_mul, abs_of_pos ht.1] at h1
        exact h1.trans (mul_le_of_le_one_right (abs_nonneg x) ht.2)
    have hmono : ∫ t in (0 : ℝ)..1, Real.exp (-|x|) * t ^ (a - 1) ≤
        ∫ t in (0 : ℝ)..1, t ^ (a - 1) * Real.exp (-(x * t)) := by
      refine intervalIntegral.integral_mono_on zero_le_one (hint_rpow.const_mul _) hint
        fun t ht => ?_
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg ht.1 _)
      have h1 : x * t ≤ |x| * t := mul_le_mul_of_nonneg_right (le_abs_self x) ht.1
      have h2 : |x| * t ≤ |x| := mul_le_of_le_one_right (abs_nonneg x) ht.2
      linarith
    have hval : ∫ t in (0 : ℝ)..1, Real.exp (-|x|) * t ^ (a - 1) = Real.exp (-|x|) / a := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
        show a - 1 + 1 = a by ring, Real.one_rpow, Real.zero_rpow ha'.ne', sub_zero,
        div_eq_mul_inv, one_mul, ← div_eq_mul_inv]
    rw [hval] at hmono
    exact lt_of_lt_of_le (div_pos (Real.exp_pos _) ha') hmono

/-! ### Zeros for `x < 0` (DLMF §8.13(iii)(a)) -/

private theorem differentiable_re_tricomiIncompleteGamma_left (x : ℝ) :
    Differentiable ℝ fun a : ℝ => (tricomiIncompleteGamma a x).re := fun a => by
  have hc : HasDerivAt (fun b : ℝ => tricomiIncompleteGamma (b : ℂ) x)
      (deriv (fun w => tricomiIncompleteGamma w x) a) a :=
    (differentiable_tricomiIncompleteGamma_left (x : ℂ) (a : ℂ)).hasDerivAt.comp_ofReal
  exact (reCLM.hasFDerivAt.comp a hc.hasFDerivAt).differentiableAt

private theorem ne_neg_nat_of_mem_Ioo_neg_nat {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-(m : ℝ) - 1) (-(m : ℝ))) : ∀ k : ℕ, a ≠ -(k : ℝ) := by
  intro k hk
  rw [hk] at ha
  have h1 : m < k := by exact_mod_cast (show (m : ℝ) < (k : ℝ) by linarith [ha.2])
  have h2 : k < m + 1 := by exact_mod_cast (show (k : ℝ) < (m : ℝ) + 1 by linarith [ha.1])
  omega

private theorem ne_neg_nat_of_even_band {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha₁ : -2 * (n : ℝ) < a) (ha₂ : a < 1 - 2 * (n : ℝ)) : ∀ m : ℕ, a ≠ -(m : ℝ) := by
  have hcast : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  exact ne_neg_nat_of_mem_Ioo_neg_nat (m := 2 * n - 1) ⟨by linarith, by linarith⟩

private theorem hasSum_Gamma_mul_re_tricomiIncompleteGamma {a : ℝ}
    (ha : ∀ k : ℕ, a ≠ -(k : ℝ)) (x : ℝ) :
    HasSum (fun k : ℕ => (-x) ^ k / (k ! * (a + k)))
      (Real.Gamma a * (tricomiIncompleteGamma a x).re) := by
  have haℂ : ∀ k : ℕ, (a : ℂ) ≠ -(k : ℂ) := fun k h => ha k (by exact_mod_cast h)
  have h := (hasSum_tricomiIncompleteGamma_of_ne_neg_natCast haℂ (x : ℂ)).map
    reCLM.toAddMonoidHom reCLM.continuous
  have h' : HasSum (fun k : ℕ => (Real.Gamma a)⁻¹ * ((-x) ^ k / (k ! * (a + k))))
      (tricomiIncompleteGamma a x).re := by
    refine h.congr_fun fun k => ?_
    simp only [Function.comp_apply, Gamma_ofReal]
    norm_cast
  refine (h'.mul_left (Real.Gamma a)).congr_fun fun k => ?_
  rw [← mul_assoc, mul_inv_cancel₀ (Real.Gamma_ne_zero ha), one_mul]

private theorem Gamma_mul_re_tricomiIncompleteGamma_slope_le {x : ℝ} (hx : x < 0) {m : ℕ}
    {a₁ a₂ : ℝ} (ha₁ : a₁ ∈ Ioo (-(m : ℝ) - 1) (-(m : ℝ)))
    (ha₂ : a₂ ∈ Ioo (-(m : ℝ) - 1) (-(m : ℝ))) (h12 : a₁ < a₂) :
    (Real.Gamma a₂ * (tricomiIncompleteGamma a₂ x).re -
        Real.Gamma a₁ * (tricomiIncompleteGamma a₁ x).re) / (a₂ - a₁) ≤
      -(a₁ * a₂)⁻¹ := by
  have hs₁ := hasSum_Gamma_mul_re_tricomiIncompleteGamma (ne_neg_nat_of_mem_Ioo_neg_nat ha₁) x
  have hs₂ := hasSum_Gamma_mul_re_tricomiIncompleteGamma (ne_neg_nat_of_mem_Ioo_neg_nat ha₂) x
  have hsub : HasSum (fun k : ℕ => (-x) ^ k / (k ! * (a₁ + k) * (a₂ + k)))
      (-(a₂ - a₁)⁻¹ * (Real.Gamma a₂ * (tricomiIncompleteGamma a₂ x).re -
          Real.Gamma a₁ * (tricomiIncompleteGamma a₁ x).re)) := by
    refine ((hs₂.sub hs₁).mul_left (-(a₂ - a₁)⁻¹)).congr_fun fun k => ?_
    have hne1 : a₁ + (k : ℝ) ≠ 0 := fun h => ne_neg_nat_of_mem_Ioo_neg_nat ha₁ k (by linarith)
    have hne2 : a₂ + (k : ℝ) ≠ 0 := fun h => ne_neg_nat_of_mem_Ioo_neg_nat ha₂ k (by linarith)
    have hne12 : a₂ - a₁ ≠ 0 := sub_ne_zero.mpr h12.ne'
    have hfac : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
    ring
  have hdiff : HasSum (fun k : ℕ => (-x) ^ k / (k ! * (a₁ + k) * (a₂ + k)))
      (-(Real.Gamma a₂ * (tricomiIncompleteGamma a₂ x).re -
          Real.Gamma a₁ * (tricomiIncompleteGamma a₁ x).re) / (a₂ - a₁)) := by
    convert hsub using 1
    ring
  have hnonneg : ∀ k : ℕ, 0 ≤ (-x) ^ k / (k ! * (a₁ + k) * (a₂ + k)) := fun k => by
    have hprod : 0 < (a₁ + k) * (a₂ + k) := by
      rcases le_or_gt k m with hk | hk
      · have hk' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
        exact mul_pos_of_neg_of_neg (by linarith [ha₁.2]) (by linarith [ha₂.2])
      · have hk' : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
        exact mul_pos (by linarith [ha₁.1]) (by linarith [ha₂.1])
    have hden : 0 < (k ! : ℝ) * (a₁ + k) * (a₂ + k) := by
      rw [mul_assoc]
      exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)) hprod
    exact div_nonneg (pow_nonneg (by linarith) k) hden.le
  have h0 := hdiff.summable.le_tsum 0 (fun k _ => hnonneg k)
  rw [hdiff.tsum_eq, neg_div] at h0
  have h0' : (a₁ * a₂)⁻¹ ≤ -((Real.Gamma a₂ * (tricomiIncompleteGamma a₂ x).re -
      Real.Gamma a₁ * (tricomiIncompleteGamma a₁ x).re) / (a₂ - a₁)) := by
    simpa [one_div] using h0
  linarith

/-- **DLMF §8.13(iii)(a)** on a single unit interval: for `x < 0` and every `m : ℕ`, `γ*(·, x)`
has a unique zero in `(-m - 1, -m)`, and that zero is simple. -/
theorem tricomiIncompleteGamma_param_zeros_Ioo_neg_nat {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃ a₀ : ℝ,
      {a : ℝ | a ∈ Ioo (-(m : ℝ) - 1) (-(m : ℝ)) ∧ tricomiIncompleteGamma a x = 0} = {a₀} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ ≠ 0 := by
  let f : ℝ → ℝ := fun b => (tricomiIncompleteGamma b x).re
  have hf_diff : Differentiable ℝ f := differentiable_re_tricomiIncompleteGamma_left x
  have hleft : f (-(m : ℝ) - 1) = x ^ (m + 1) := by
    have hcast : ((-(m : ℝ) - 1 : ℝ) : ℂ) = -((m + 1 : ℕ) : ℂ) := by push_cast; ring
    dsimp only [f]
    rw [hcast, tricomiIncompleteGamma_neg_natCast, ← ofReal_pow, ofReal_re]
  have hright : f (-(m : ℝ)) = x ^ m := by
    have hcast : ((-(m : ℝ) : ℝ) : ℂ) = -(m : ℂ) := by push_cast; ring
    dsimp only [f]
    rw [hcast, tricomiIncompleteGamma_neg_natCast, ← ofReal_pow, ofReal_re]
  have hex : ∃ a₀ ∈ Ioo (-(m : ℝ) - 1) (-(m : ℝ)), f a₀ = 0 := by
    rcases Nat.even_or_odd m with hm | hm
    · have hpos : 0 < x ^ m := hm.pow_pos hx.ne
      have hneg : x ^ (m + 1) < 0 := by rw [pow_succ]; nlinarith
      exact intermediate_value_Ioo (by linarith) hf_diff.continuous.continuousOn
        ⟨by rwa [hleft], by rwa [hright]⟩
    · have hneg : x ^ m < 0 := hm.pow_neg hx
      have hpos : 0 < x ^ (m + 1) := by rw [pow_succ]; nlinarith
      exact intermediate_value_Ioo' (by linarith) hf_diff.continuous.continuousOn
        ⟨by rwa [hright], by rwa [hleft]⟩
  obtain ⟨a₀, ha₀, hfa₀⟩ := hex
  refine ⟨a₀, ?_, ?_⟩
  · ext a
    simp only [mem_ofPred_eq, mem_singleton_iff, tricomiIncompleteGamma_ofReal_eq_zero_iff]
    constructor
    · rintro ⟨ha, hfa⟩
      by_contra hne
      have hprod_pos : ∀ {b₁ b₂ : ℝ}, b₁ ∈ Ioo (-(m : ℝ) - 1) (-(m : ℝ)) →
          b₂ ∈ Ioo (-(m : ℝ) - 1) (-(m : ℝ)) → 0 < (b₁ * b₂)⁻¹ := fun hb₁ hb₂ =>
        inv_pos.mpr (mul_pos_of_neg_of_neg (by linarith [hb₁.2]) (by linarith [hb₂.2]))
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hs := Gamma_mul_re_tricomiIncompleteGamma_slope_le hx ha ha₀ hlt
        simp only [f] at hfa hfa₀
        rw [hfa, hfa₀, mul_zero, mul_zero, sub_self, zero_div] at hs
        linarith [hprod_pos ha ha₀]
      · have hs := Gamma_mul_re_tricomiIncompleteGamma_slope_le hx ha₀ ha hgt
        simp only [f] at hfa hfa₀
        rw [hfa, hfa₀, mul_zero, mul_zero, sub_self, zero_div] at hs
        linarith [hprod_pos ha₀ ha]
    · rintro rfl
      exact ⟨ha₀, hfa₀⟩
  · -- Pass the negative slope bound to the right limit at `a₀` to show `deriv (Γ * f) a₀ < 0`.
    let g : ℝ → ℝ := fun b => Real.Gamma b * f b
    have hg_deriv : HasDerivAt g (Real.Gamma a₀ * deriv f a₀) a₀ := by
      have hd := (Real.differentiableAt_Gamma
        (ne_neg_nat_of_mem_Ioo_neg_nat ha₀)).hasDerivAt.fun_mul (hf_diff a₀).hasDerivAt
      rw [hfa₀, mul_zero, zero_add] at hd
      exact hd
    have hslope : Tendsto (fun b => (g b - g a₀) / (b - a₀)) (𝓝[>] a₀)
        (𝓝 (Real.Gamma a₀ * deriv f a₀)) := by
      have h1 := (hasDerivAt_iff_tendsto_slope.mp hg_deriv).mono_left
        (nhdsWithin_mono a₀ fun _ hb => (Set.mem_Ioi.mp hb).ne')
      exact h1.congr fun b => slope_def_field g a₀ b
    have hrhs : Tendsto (fun b => -(a₀ * b)⁻¹) (𝓝[>] a₀) (𝓝 (-(a₀ * a₀)⁻¹)) := by
      have ha₀_ne : a₀ ≠ 0 := by linarith [ha₀.2]
      exact (by fun_prop (disch := exact mul_ne_zero ha₀_ne ha₀_ne) :
        ContinuousAt (fun b : ℝ => -(a₀ * b)⁻¹) a₀).continuousWithinAt
    have hev : ∀ᶠ b in 𝓝[>] a₀, (g b - g a₀) / (b - a₀) ≤ -(a₀ * b)⁻¹ := by
      filter_upwards [Ioo_mem_nhdsGT ha₀.2] with b hb
      exact Gamma_mul_re_tricomiIncompleteGamma_slope_le hx ha₀ ⟨ha₀.1.trans hb.1, hb.2⟩ hb.1
    have hle : Real.Gamma a₀ * deriv f a₀ ≤ -(a₀ * a₀)⁻¹ :=
      le_of_tendsto_of_tendsto hslope hrhs hev
    intro hzero
    rw [hzero, mul_zero] at hle
    have hpos : 0 < (a₀ * a₀)⁻¹ :=
      inv_pos.mpr (mul_pos_of_neg_of_neg (by linarith [ha₀.2]) (by linarith [ha₀.2]))
    linarith

/-- **DLMF §8.13(iii)(a)**: for `x < 0` and `n ≥ 1`, `γ*(·, x)` has exactly two zeros in
`(-2n, 2 - 2n)`, both simple. -/
theorem tricomiIncompleteGamma_param_zeros_of_neg {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x < 0) :
    ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (2 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0} = {a₁, a₂} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0 := by
  obtain ⟨a₁, ha₁_eq, ha₁_deriv⟩ := tricomiIncompleteGamma_param_zeros_Ioo_neg_nat hx (2 * n - 1)
  obtain ⟨a₂, ha₂_eq, ha₂_deriv⟩ := tricomiIncompleteGamma_param_zeros_Ioo_neg_nat hx (2 * n - 2)
  have hcast1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have hcast2 : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * n)]; push_cast; ring
  rw [hcast1] at ha₁_eq
  rw [hcast2] at ha₂_eq
  have ha₁_mem : a₁ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
      tricomiIncompleteGamma a₁ x = 0 := by
    have h := (Set.ext_iff.mp ha₁_eq a₁).mpr rfl
    exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, h.2⟩
  have ha₂_mem : a₂ ∈ Ioo (1 - 2 * (n : ℝ)) (2 - 2 * (n : ℝ)) ∧
      tricomiIncompleteGamma a₂ x = 0 := by
    have h := (Set.ext_iff.mp ha₂_eq a₂).mpr rfl
    exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, h.2⟩
  refine ⟨a₁, a₂, ha₁_mem.1.2.trans ha₂_mem.1.1, ?_, ha₁_deriv, ha₂_deriv⟩
  ext a
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨ha, hγ⟩
    rcases lt_trichotomy a (1 - 2 * (n : ℝ)) with hlt | rfl | hgt
    · exact Or.inl ((Set.ext_iff.mp ha₁_eq a).mp ⟨⟨by linarith [ha.1], by linarith⟩, hγ⟩)
    · exfalso
      have hcast : ((1 - 2 * (n : ℝ) : ℝ) : ℂ) = -((2 * n - 1 : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
      rw [hcast, tricomiIncompleteGamma_neg_natCast] at hγ
      exact pow_ne_zero _ (ofReal_ne_zero.mpr hx.ne) hγ
    · exact Or.inr ((Set.ext_iff.mp ha₂_eq a).mp ⟨⟨by linarith, by linarith [ha.2]⟩, hγ⟩)
  · rintro (rfl | rfl)
    · exact ⟨⟨ha₁_mem.1.1, by linarith [ha₁_mem.1.2]⟩, ha₁_mem.2⟩
    · exact ⟨⟨by linarith [ha₂_mem.1.1], ha₂_mem.1.2⟩, ha₂_mem.2⟩

/-! ### Positivity on odd bands for `x > 0` -/

private theorem Gamma_pos_of_even_band {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha₁ : -2 * (n : ℝ) < a) (ha₂ : a < 1 - 2 * (n : ℝ)) : 0 < Real.Gamma a := by
  have hcast : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have h := Real.neg_one_pow_mul_Gamma_pos (m := 2 * n - 1) ⟨by linarith, by linarith⟩
  have hpow : (-1 : ℝ) ^ (2 * n - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n), pow_mul]; norm_num
  simpa [hpow] using h

/-- **DLMF §8.13(iii)(b)** on odd negative bands: for `x > 0` and every `n : ℕ`,
`Re γ*(a, x) > 0` throughout `(1 - 2n, 2 - 2n)`, so `γ*(·, x)` has no zeros there. -/
theorem tricomiIncompleteGamma_ofReal_re_pos_of_odd_band {n : ℕ} {a : ℝ}
    (ha₁ : 1 - 2 * (n : ℝ) < a) (ha₂ : a < 2 - 2 * (n : ℝ)) {x : ℝ} (hx : 0 < x) :
    0 < (tricomiIncompleteGamma a x).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact tricomiIncompleteGamma_ofReal_re_pos_of_nonneg (by norm_num at ha₁; linarith) x
  · have hcast : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * n)]; push_cast; ring
    have ha_ne : ∀ m : ℕ, a ≠ -(m : ℝ) :=
      ne_neg_nat_of_mem_Ioo_neg_nat (m := 2 * n - 2) ⟨by linarith, by linarith⟩
    have hΓ : Real.Gamma a < 0 := by
      have h := Real.neg_one_pow_mul_Gamma_pos (m := 2 * n - 2) (x := a) ⟨by linarith, by linarith⟩
      have hpow : (-1 : ℝ) ^ (2 * n - 2 + 1) = -1 := by
        rw [show 2 * n - 2 + 1 = 2 * (n - 1) + 1 by omega, pow_succ, pow_mul]; norm_num
      rw [hpow] at h
      linarith
    rw [tricomiIncompleteGamma_ofReal_re_eq_sub_div_Gamma ha_ne hx]
    have h1 : 0 < x ^ (-a) := Real.rpow_pos_of_pos hx (-a)
    have h2 : tricomiTailMoment 0 a x / Real.Gamma a < 0 :=
      div_neg_of_pos_of_neg (tricomiTailMoment_zero_pos a hx) hΓ
    linarith

/-! ### Logarithmic potential `Φ(a, x)` and the threshold `x*_n` (DLMF §8.13(iii)(b)) -/

private def phi (a x : ℝ) : ℝ :=
  Real.log (Real.Gamma a) - a * Real.log x - Real.log (tricomiTailMoment 0 a x)

private def phiDeriv (a x : ℝ) : ℝ :=
  Real.digamma a - Real.log x - tricomiTailMoment 1 a x / tricomiTailMoment 0 a x

private def phiDeriv2 (a x : ℝ) : ℝ :=
  deriv Real.digamma a -
    (tricomiTailMoment 2 a x / tricomiTailMoment 0 a x -
      (tricomiTailMoment 1 a x / tricomiTailMoment 0 a x) ^ 2)

private theorem hasDerivAt_phi_left {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha₁ : -2 * (n : ℝ) < a) (ha₂ : a < 1 - 2 * (n : ℝ)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b => phi b x) (phiDeriv a x) a := by
  have h1 : HasDerivAt (fun b => Real.log (Real.Gamma b)) (Real.digamma a) a :=
    Real.hasDerivAt_log_Gamma (ne_neg_nat_of_even_band hn ha₁ ha₂)
  have h2 : HasDerivAt (fun b => b * Real.log x) (Real.log x) a := by
    simpa using (hasDerivAt_id a).mul_const (Real.log x)
  have h3 : HasDerivAt (fun b => Real.log (tricomiTailMoment 0 b x))
      (tricomiTailMoment 1 a x / tricomiTailMoment 0 a x) a :=
    (hasDerivAt_tricomiTailMoment_left 0 a hx).log (tricomiTailMoment_zero_pos a hx).ne'
  exact (h1.fun_sub h2).fun_sub h3

private theorem hasDerivAt_phiDeriv_left {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha₁ : -2 * (n : ℝ) < a) (ha₂ : a < 1 - 2 * (n : ℝ)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b => phiDeriv b x) (phiDeriv2 a x) a := by
  have h1 : HasDerivAt Real.digamma (deriv Real.digamma a) a :=
    (Real.differentiableAt_digamma (ne_neg_nat_of_even_band hn ha₁ ha₂)).hasDerivAt
  have hI0_ne : tricomiTailMoment 0 a x ≠ 0 := (tricomiTailMoment_zero_pos a hx).ne'
  have hq : HasDerivAt (fun b => tricomiTailMoment 1 b x / tricomiTailMoment 0 b x)
      (tricomiTailMoment 2 a x / tricomiTailMoment 0 a x -
        (tricomiTailMoment 1 a x / tricomiTailMoment 0 a x) ^ 2) a := by
    convert (hasDerivAt_tricomiTailMoment_left 1 a hx).div
      (hasDerivAt_tricomiTailMoment_left 0 a hx) hI0_ne using 1
    field_simp
  exact (h1.sub_const (Real.log x)).fun_sub hq

private theorem phiDeriv2_pos {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha₁ : -2 * (n : ℝ) < a) (ha₂ : a < 1 - 2 * (n : ℝ)) {x : ℝ} (hx : 0 < x) :
    0 < phiDeriv2 a x := by
  have ha_neg : a < 0 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha_ne : ∀ m : ℕ, a ≠ -(m : ℝ) := ne_neg_nat_of_even_band hn ha₁ ha₂
  have hshift := Real.deriv_digamma_apply_add_nat ha_ne 1
  simp only [Nat.cast_one, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero]
    at hshift
  have hpos : 0 < deriv Real.digamma (a + 1) :=
    Real.deriv_digamma_pos fun m hm => ha_ne (m + 1) (by push_cast; linarith)
  have h2 := tricomiTailMoment_variance_le ha_neg hx
  dsimp only [phiDeriv2]
  linarith

private theorem re_tricomiIncompleteGamma_eq_mul_one_sub_exp_neg_phi {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha₁ : -2 * (n : ℝ) < a) (ha₂ : a < 1 - 2 * (n : ℝ)) {x : ℝ} (hx : 0 < x) :
    (tricomiIncompleteGamma a x).re = x ^ (-a) * (1 - Real.exp (-phi a x)) := by
  rw [tricomiIncompleteGamma_ofReal_re_eq_sub_div_Gamma (ne_neg_nat_of_even_band hn ha₁ ha₂) hx]
  have hΓ_pos : 0 < Real.Gamma a := Gamma_pos_of_even_band hn ha₁ ha₂
  have hI_pos : 0 < tricomiTailMoment 0 a x := tricomiTailMoment_zero_pos a hx
  have hexp : Real.exp (-phi a x) = tricomiTailMoment 0 a x * x ^ a / Real.Gamma a := by
    rw [phi, show -(Real.log (Real.Gamma a) - a * Real.log x -
      Real.log (tricomiTailMoment 0 a x)) =
      Real.log (tricomiTailMoment 0 a x) + a * Real.log x - Real.log (Real.Gamma a) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hI_pos, Real.exp_log hΓ_pos,
      Real.rpow_def_of_pos hx, mul_comm a (Real.log x)]
  rw [hexp, mul_sub, mul_one, ← mul_div_assoc, ← mul_assoc, mul_comm (x ^ (-a)), mul_assoc,
    ← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, mul_one]

private theorem deriv_re_tricomiIncompleteGamma_at_zero {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha₁ : -2 * (n : ℝ) < a) (ha₂ : a < 1 - 2 * (n : ℝ)) {x : ℝ} (hx : 0 < x)
    (hφ : phi a x = 0) :
    deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a = x ^ (-a) * phiDeriv a x := by
  have hev : (fun b : ℝ => (tricomiIncompleteGamma b x).re) =ᶠ[𝓝 a]
      fun b => x ^ (-b) * (1 - Real.exp (-phi b x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ha₁, ha₂⟩] with b hb
    exact re_tricomiIncompleteGamma_eq_mul_one_sub_exp_neg_phi hn hb.1 hb.2 hx
  have h1 : HasDerivAt (fun b => x ^ (-b)) (-(Real.log x) * x ^ (-a)) a := by
    simpa [mul_comm] using ((hasDerivAt_id a).neg).const_rpow hx
  have h2 : HasDerivAt (fun b => 1 - Real.exp (-phi b x))
      (Real.exp (-phi a x) * phiDeriv a x) a := by
    simpa [mul_comm] using ((hasDerivAt_phi_left hn ha₁ ha₂ hx).neg.exp).const_sub 1
  have hprod := (h1.fun_mul h2).congr_of_eventuallyEq hev
  rw [hprod.deriv, hφ, neg_zero, Real.exp_zero, sub_self, mul_zero, zero_add, one_mul]

private theorem deriv2_re_tricomiIncompleteGamma_at_double_zero {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha₁ : -2 * (n : ℝ) < a) (ha₂ : a < 1 - 2 * (n : ℝ)) {x : ℝ} (hx : 0 < x)
    (hφ : phi a x = 0) (hφ' : phiDeriv a x = 0) :
    deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a = x ^ (-a) * phiDeriv2 a x := by
  have hev_deriv : deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) =ᶠ[𝓝 a]
      fun b => -(Real.log x) * x ^ (-b) * (1 - Real.exp (-phi b x)) +
        x ^ (-b) * Real.exp (-phi b x) * phiDeriv b x := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ha₁, ha₂⟩] with b hb
    have hev_b : (fun c : ℝ => (tricomiIncompleteGamma c x).re) =ᶠ[𝓝 b]
        fun c => x ^ (-c) * (1 - Real.exp (-phi c x)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hb] with c hc
      exact re_tricomiIncompleteGamma_eq_mul_one_sub_exp_neg_phi hn hc.1 hc.2 hx
    have h1 : HasDerivAt (fun c => x ^ (-c)) (-(Real.log x) * x ^ (-b)) b := by
      simpa [mul_comm] using ((hasDerivAt_id b).neg).const_rpow hx
    have h2 : HasDerivAt (fun c => 1 - Real.exp (-phi c x))
        (Real.exp (-phi b x) * phiDeriv b x) b := by
      simpa [mul_comm] using ((hasDerivAt_phi_left hn hb.1 hb.2 hx).neg.exp).const_sub 1
    rw [((h1.fun_mul h2).congr_of_eventuallyEq hev_b).deriv]
    ring
  have hpow : HasDerivAt (fun b => x ^ (-b)) (-(Real.log x) * x ^ (-a)) a := by
    simpa [mul_comm] using ((hasDerivAt_id a).neg).const_rpow hx
  have hexp_neg : HasDerivAt (fun b => Real.exp (-phi b x))
      (-Real.exp (-phi a x) * phiDeriv a x) a := by
    simpa [mul_comm] using (hasDerivAt_phi_left hn ha₁ ha₂ hx).neg.exp
  have hterm1 : HasDerivAt (fun b => -(Real.log x) * x ^ (-b) * (1 - Real.exp (-phi b x))) 0 a := by
    convert (hpow.const_mul (-(Real.log x))).fun_mul (hexp_neg.const_sub 1) using 1
    rw [hφ, hφ', neg_zero, Real.exp_zero]; ring
  have hterm2 : HasDerivAt (fun b => x ^ (-b) * Real.exp (-phi b x) * phiDeriv b x)
      (x ^ (-a) * phiDeriv2 a x) a := by
    convert (hpow.fun_mul hexp_neg).fun_mul (hasDerivAt_phiDeriv_left hn ha₁ ha₂ hx) using 1
    rw [hφ, hφ', neg_zero, Real.exp_zero]; ring
  simpa using ((hterm1.fun_add hterm2).congr_of_eventuallyEq hev_deriv).deriv

private theorem tendsto_phi_endpoints {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a => phi a x) (𝓝[>] (-2 * (n : ℝ))) atTop ∧
      Tendsto (fun a => phi a x) (𝓝[<] (1 - 2 * (n : ℝ))) atTop := by
  have hcont_tail :
      Continuous fun a : ℝ => -(a * Real.log x + Real.log (tricomiTailMoment 0 a x)) := by
    refine ((continuous_id.mul continuous_const).add ?_).neg
    refine Continuous.log ?_ fun a => (tricomiTailMoment_zero_pos a hx).ne'
    exact continuousOn_univ.mp <|
      continuousOn_tricomiTailMoment_zero.comp (continuous_id.prodMk continuous_const).continuousOn
        fun a _ => ⟨mem_univ a, hx⟩
  have hlogΓ : ∀ c : ℝ, (∃ m : ℕ, c = -(m : ℝ)) →
      Tendsto (fun a => Real.log (Real.Gamma a))
        (𝓝[Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))] c) atTop := by
    rintro c ⟨m, rfl⟩
    have hinv0 : Tendsto (fun a => (Real.Gamma a)⁻¹)
        (𝓝[Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))] (-(m : ℝ))) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h := (Real.continuous_inv_Gamma.tendsto (-(m : ℝ))).mono_left
          (nhdsWithin_le_nhds (s := Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))))
        rwa [Real.Gamma_neg_nat_eq_zero, inv_zero] at h
      · filter_upwards [self_mem_nhdsWithin] with a ha
        exact inv_pos.mpr (Gamma_pos_of_even_band hn ha.1 ha.2)
    have hΓtop : Tendsto Real.Gamma (𝓝[Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))] (-(m : ℝ))) atTop := by
      simpa [Function.comp_def, inv_inv] using tendsto_inv_nhdsGT_zero.comp hinv0
    exact Real.tendsto_log_atTop.comp hΓtop
  have hL_nat : ∃ m : ℕ, -2 * (n : ℝ) = -(m : ℝ) := ⟨2 * n, by push_cast; ring⟩
  have hR_nat : ∃ m : ℕ, 1 - 2 * (n : ℝ) = -(m : ℝ) :=
    ⟨2 * n - 1, by rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring⟩
  constructor
  · have h1 := (hlogΓ _ hL_nat).mono_left
      (le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Ioo_mem_nhdsGT (by linarith))))
    have h2 := (hcont_tail.tendsto (-2 * (n : ℝ))).mono_left
      (nhdsWithin_le_nhds (s := Ioi (-2 * (n : ℝ))))
    exact (Filter.Tendsto.atTop_add h1 h2).congr fun a => by dsimp only [phi]; ring
  · have h1 := (hlogΓ _ hR_nat).mono_left
      (le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Ioo_mem_nhdsLT (by linarith))))
    have h2 := (hcont_tail.tendsto (1 - 2 * (n : ℝ))).mono_left
      (nhdsWithin_le_nhds (s := Iio (1 - 2 * (n : ℝ))))
    exact (Filter.Tendsto.atTop_add h1 h2).congr fun a => by dsimp only [phi]; ring

private theorem exists_phi_min {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)),
      ∀ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)), phi a₀ x ≤ phi a x := by
  let L : ℝ := -2 * (n : ℝ)
  let R : ℝ := 1 - 2 * (n : ℝ)
  let c : ℝ := (L + R) / 2
  have hc : c ∈ Ioo L R := ⟨by dsimp [L, R, c]; linarith, by dsimp [L, R, c]; linarith⟩
  obtain ⟨hL_top, hR_top⟩ := tendsto_phi_endpoints hn hx
  obtain ⟨L₁, hLL₁, hL_gt⟩ :=
    (nhdsGT_basis L).eventually_iff.mp (hL_top.eventually (eventually_gt_atTop (phi c x)))
  obtain ⟨R₁, hR₁R, hR_gt⟩ :=
    (nhdsLT_basis R).eventually_iff.mp (hR_top.eventually (eventually_gt_atTop (phi c x)))
  let L' : ℝ := min c L₁
  let R' : ℝ := max c R₁
  have hLL' : L < L' := lt_min hc.1 hLL₁
  have hR'R : R' < R := max_lt hc.2 hR₁R
  have hcont : ContinuousOn (fun a => phi a x) (Icc L' R') := fun a ha =>
    (hasDerivAt_phi_left hn (hLL'.trans_le ha.1)
      (ha.2.trans_lt hR'R) hx).continuousAt.continuousWithinAt
  obtain ⟨a₀, ha₀_mem, ha₀_min⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr ((min_le_left c L₁).trans (le_max_left c R₁)))
      hcont
  refine ⟨a₀, ⟨hLL'.trans_le ha₀_mem.1, ha₀_mem.2.trans_lt hR'R⟩, fun a ha => ?_⟩
  have ha₀_le_c : phi a₀ x ≤ phi c x := ha₀_min ⟨min_le_left c L₁, le_max_left c R₁⟩
  by_cases ha1 : a < L'
  · exact ha₀_le_c.trans (hL_gt ⟨ha.1, ha1.trans_le (min_le_right _ _)⟩).le
  · by_cases ha2 : R' < a
    · exact ha₀_le_c.trans (hR_gt ⟨(le_max_right _ _).trans_lt ha2, ha.2⟩).le
    · exact ha₀_min ⟨not_lt.mp ha1, not_lt.mp ha2⟩

private theorem phi_trichotomy {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    {a₀ : ℝ} (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)))
    (hmin : ∀ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)), phi a₀ x ≤ phi a x) :
    (phi a₀ x < 0 → ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0} = {a₁, a₂} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0) ∧
    (phi a₀ x = 0 → ∃ aStar : ℝ,
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0} = {aStar} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) aStar = 0 ∧
      deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) aStar ≠ 0) ∧
    (0 < phi a₀ x →
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0} = ∅) := by
  let L : ℝ := -2 * (n : ℝ)
  let R : ℝ := 1 - 2 * (n : ℝ)
  have hφ'_mono : StrictMonoOn (fun a => phiDeriv a x) (Ioo L R) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo L R)
      (fun a ha => (hasDerivAt_phiDeriv_left hn ha.1 ha.2 hx).continuousAt.continuousWithinAt)
      fun a ha => ?_
    rw [interior_Ioo] at ha
    rw [(hasDerivAt_phiDeriv_left hn ha.1 ha.2 hx).deriv]
    exact phiDeriv2_pos hn ha.1 ha.2 hx
  have hφ'_a₀ : phiDeriv a₀ x = 0 := by
    have hloc : IsLocalMin (fun a => phi a x) a₀ := by
      filter_upwards [isOpen_Ioo.mem_nhds ha₀] with a ha; exact hmin a ha
    rw [← (hasDerivAt_phi_left hn ha₀.1 ha₀.2 hx).deriv]
    exact hloc.deriv_eq_zero
  have hφ_anti : StrictAntiOn (fun a => phi a x) (Ioc L a₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc L a₀)
      (fun a ha => (hasDerivAt_phi_left hn ha.1
        (ha.2.trans_lt ha₀.2) hx).continuousAt.continuousWithinAt) fun a ha => ?_
    rw [interior_Ioc] at ha
    rw [(hasDerivAt_phi_left hn ha.1 (ha.2.trans ha₀.2) hx).deriv, ← hφ'_a₀]
    exact hφ'_mono ⟨ha.1, ha.2.trans ha₀.2⟩ ha₀ ha.2
  have hφ_mono : StrictMonoOn (fun a => phi a x) (Ico a₀ R) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico a₀ R)
      (fun a ha => (hasDerivAt_phi_left hn (ha₀.1.trans_le ha.1)
        ha.2 hx).continuousAt.continuousWithinAt) fun a ha => ?_
    rw [interior_Ico] at ha
    rw [(hasDerivAt_phi_left hn (ha₀.1.trans ha.1) ha.2 hx).deriv, ← hφ'_a₀]
    exact hφ'_mono ha₀ ⟨ha₀.1.trans ha.1, ha.2⟩ ha.1
  have hzero_iff : ∀ a ∈ Ioo L R, tricomiIncompleteGamma a x = 0 ↔ phi a x = 0 := fun a ha => by
    rw [tricomiIncompleteGamma_ofReal_eq_zero_iff,
      re_tricomiIncompleteGamma_eq_mul_one_sub_exp_neg_phi hn ha.1 ha.2 hx,
      mul_eq_zero, or_iff_right (Real.rpow_pos_of_pos hx (-a)).ne', sub_eq_zero, eq_comm,
      Real.exp_eq_one_iff, neg_eq_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro hneg
    obtain ⟨hL_top, hR_top⟩ := tendsto_phi_endpoints hn hx
    obtain ⟨b₁, hφb₁, hb₁⟩ :=
      ((hL_top.eventually (eventually_gt_atTop 0)).and (Ioo_mem_nhdsGT ha₀.1)).exists
    have hcont1 : ContinuousOn (fun a => phi a x) (Icc b₁ a₀) := fun a ha =>
      (hasDerivAt_phi_left hn (hb₁.1.trans_le ha.1)
        (ha.2.trans_lt ha₀.2) hx).continuousAt.continuousWithinAt
    obtain ⟨a₁, ha₁_mem, hφa₁⟩ := intermediate_value_Ioo' hb₁.2.le hcont1 ⟨hneg, hφb₁⟩
    obtain ⟨b₂, hφb₂, hb₂⟩ :=
      ((hR_top.eventually (eventually_gt_atTop 0)).and (Ioo_mem_nhdsLT ha₀.2)).exists
    have hcont2 : ContinuousOn (fun a => phi a x) (Icc a₀ b₂) := fun a ha =>
      (hasDerivAt_phi_left hn (ha₀.1.trans_le ha.1)
        (ha.2.trans_lt hb₂.2) hx).continuousAt.continuousWithinAt
    obtain ⟨a₂, ha₂_mem, hφa₂⟩ := intermediate_value_Ioo hb₂.1.le hcont2 ⟨hneg, hφb₂⟩
    have ha₁_Ioo : a₁ ∈ Ioo L R := ⟨hb₁.1.trans ha₁_mem.1, ha₁_mem.2.trans ha₀.2⟩
    have ha₂_Ioo : a₂ ∈ Ioo L R := ⟨ha₀.1.trans ha₂_mem.1, ha₂_mem.2.trans hb₂.2⟩
    refine ⟨a₁, a₂, ha₁_mem.2.trans ha₂_mem.1, ?_, ?_, ?_⟩
    · ext a
      simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨ha, hγ⟩
        have hφa : phi a x = 0 := (hzero_iff a ha).mp hγ
        rcases lt_trichotomy a a₀ with hlt | rfl | hgt
        · exact Or.inl <|
            hφ_anti.injOn ⟨ha.1, hlt.le⟩ ⟨ha₁_Ioo.1, ha₁_mem.2.le⟩ (hφa.trans hφa₁.symm)
        · linarith
        · exact Or.inr <|
            hφ_mono.injOn ⟨hgt.le, ha.2⟩ ⟨ha₂_mem.1.le, ha₂_Ioo.2⟩ (hφa.trans hφa₂.symm)
      · rintro (ha | ha)
        · rw [ha]; exact ⟨ha₁_Ioo, (hzero_iff a₁ ha₁_Ioo).mpr hφa₁⟩
        · rw [ha]; exact ⟨ha₂_Ioo, (hzero_iff a₂ ha₂_Ioo).mpr hφa₂⟩
    · rw [deriv_re_tricomiIncompleteGamma_at_zero hn ha₁_Ioo.1 ha₁_Ioo.2 hx hφa₁]
      have hlt : phiDeriv a₁ x < 0 := by rw [← hφ'_a₀]; exact hφ'_mono ha₁_Ioo ha₀ ha₁_mem.2
      exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' hlt.ne
    · rw [deriv_re_tricomiIncompleteGamma_at_zero hn ha₂_Ioo.1 ha₂_Ioo.2 hx hφa₂]
      have hgt : 0 < phiDeriv a₂ x := by rw [← hφ'_a₀]; exact hφ'_mono ha₀ ha₂_Ioo ha₂_mem.1
      exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' hgt.ne'
  · intro hzero
    refine ⟨a₀, ?_, ?_, ?_⟩
    · ext a
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨ha, hγ⟩
        have hφa : phi a x = 0 := (hzero_iff a ha).mp hγ
        rcases lt_trichotomy a a₀ with hlt | rfl | hgt
        · linarith [hφ_anti ⟨ha.1, hlt.le⟩ ⟨ha₀.1, le_rfl⟩ hlt]
        · rfl
        · linarith [hφ_mono ⟨le_rfl, ha₀.2⟩ ⟨hgt.le, ha.2⟩ hgt]
      · intro ha; rw [ha]; exact ⟨ha₀, (hzero_iff a₀ ha₀).mpr hzero⟩
    · rw [deriv_re_tricomiIncompleteGamma_at_zero hn ha₀.1 ha₀.2 hx hzero, hφ'_a₀, mul_zero]
    · rw [deriv2_re_tricomiIncompleteGamma_at_double_zero hn ha₀.1 ha₀.2 hx hzero hφ'_a₀]
      exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' (phiDeriv2_pos hn ha₀.1 ha₀.2 hx).ne'
  · intro hpos
    ext a
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro ha hγ
    linarith [hmin a ha, (hzero_iff a ha).mp hγ]

private theorem strictMonoOn_phi_right (a : ℝ) : StrictMonoOn (fun x => phi a x) (Ioi 0) := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y => phi a y)
      (Real.exp (-x) / (x * tricomiTailMoment 0 a x)) x := fun x hx => by
    have h1 : HasDerivAt (fun y => a * Real.log y) (a / x) x := by
      simpa [div_eq_mul_inv] using (Real.hasDerivAt_log hx.ne').const_mul a
    have h2 : HasDerivAt (fun y => Real.log (tricomiTailMoment 0 a y))
        (-tricomiTailMoment 0 (a + 1) x / tricomiTailMoment 0 a x) x :=
      (hasDerivAt_tricomiTailMoment_zero_right a hx).log (tricomiTailMoment_zero_pos a hx).ne'
    refine (((hasDerivAt_const x (Real.log (Real.Gamma a))).fun_sub h1).fun_sub h2).congr_deriv ?_
    have hI0_ne : tricomiTailMoment 0 a x ≠ 0 := (tricomiTailMoment_zero_pos a hx).ne'
    have hrec := tricomiTailMoment_zero_recurrence a hx
    field_simp [hx.ne', hI0_ne]
    linarith
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [(hd x hx).deriv]
  exact div_pos (Real.exp_pos (-x)) (mul_pos hx (tricomiTailMoment_zero_pos a hx))

private theorem exists_phi_lt_zero {n : ℕ} (hn : 1 ≤ n) :
    ∃ x₁ > 0, ∃ c ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)), phi c x₁ < 0 := by
  let L : ℝ := -2 * (n : ℝ)
  let R : ℝ := 1 - 2 * (n : ℝ)
  let c : ℝ := (L + R) / 2
  have hc_mem : c ∈ Ioo L R := ⟨by dsimp [L, R, c]; linarith, by dsimp [L, R, c]; linarith⟩
  have hc_neg : c < 0 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [L, R, c]; linarith
  have hΓc : 0 < Real.Gamma c := Gamma_pos_of_even_band hn hc_mem.1 hc_mem.2
  let B : ℝ := Real.Gamma c * (-c) * Real.exp 1 + 2
  have hB_gt1 : 1 < B := by
    linarith [mul_pos (mul_pos hΓc (show 0 < -c by linarith)) (Real.exp_pos 1)]
  have hB_pos : 0 < B := zero_lt_one.trans hB_gt1
  let x₁ : ℝ := B ^ c⁻¹
  have hx₁_pos : 0 < x₁ := Real.rpow_pos_of_pos hB_pos _
  have hx₁_lt1 : x₁ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hB_gt1 (inv_neg''.mpr hc_neg)
  have hx₁_pow : x₁ ^ c = B := by
    dsimp only [x₁]; rw [← Real.rpow_mul hB_pos.le, inv_mul_cancel₀ hc_neg.ne, Real.rpow_one]
  have hlog_pos : 0 < -Real.log x₁ := neg_pos.mpr (Real.log_neg hx₁_pos hx₁_lt1)
  have hint := integrableOn_tricomiTailIntegrand 0 c hx₁_pos
  have hsub : Ioc (0 : ℝ) (-Real.log x₁) ⊆ Ioi (0 : ℝ) := fun _ ht => ht.1
  have hmono1 : ∫ s in Ioc (0 : ℝ) (-Real.log x₁), Real.exp (c * s - x₁ * Real.exp s) ≤
      tricomiTailMoment 0 c x₁ := by
    simpa [tricomiTailMoment_def] using setIntegral_mono_set hint
      (Eventually.of_forall fun _ => by simp [Real.exp_nonneg]) (ae_of_all _ hsub)
  have hmono2 : ∫ s in Ioc (0 : ℝ) (-Real.log x₁), Real.exp (-1) * Real.exp (c * s) ≤
      ∫ s in Ioc (0 : ℝ) (-Real.log x₁), Real.exp (c * s - x₁ * Real.exp s) := by
    refine setIntegral_mono_on
      (Continuous.integrableOn_Ioc (f := fun s => Real.exp (-1) * Real.exp (c * s)) (by fun_prop))
      ((hint.mono_set hsub).congr_fun (fun _ _ => by simp) measurableSet_Ioc)
      measurableSet_Ioc fun s hs => ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hexp_le : x₁ * Real.exp s ≤ 1 := calc
      x₁ * Real.exp s ≤ x₁ * Real.exp (-Real.log x₁) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs.2) hx₁_pos.le
      _ = 1 := by rw [Real.exp_neg, Real.exp_log hx₁_pos, mul_inv_cancel₀ hx₁_pos.ne']
    linarith
  have hval : ∫ s in Ioc (0 : ℝ) (-Real.log x₁), Real.exp (-1) * Real.exp (c * s) =
      Real.exp (-1) * (1 - x₁ ^ (-c)) / (-c) := by
    rw [← intervalIntegral.integral_of_le hlog_pos.le, intervalIntegral.integral_const_mul]
    have hftc : ∫ s in (0 : ℝ)..(-Real.log x₁), Real.exp (c * s) =
        Real.exp (c * (-Real.log x₁)) / c - Real.exp (c * 0) / c := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.exp (c * s) / c)
        (fun s _ => ?_)
        (Continuous.intervalIntegrable (show Continuous fun s => Real.exp (c * s) by fun_prop) _ _)
      have h1 : HasDerivAt (fun s => Real.exp (c * s) / c) (c * Real.exp (c * s) / c) s :=
        (((hasDerivAt_id s).const_mul c).exp.congr_deriv (by simp [mul_comm])).div_const c
      simpa [mul_div_cancel_left₀ _ hc_neg.ne] using h1
    have hexp_c : Real.exp (c * (-Real.log x₁)) = x₁ ^ (-c) := by
      rw [Real.rpow_def_of_pos hx₁_pos]; congr 1; ring
    rw [hftc, hexp_c, mul_zero, Real.exp_zero]; field_simp [hc_neg.ne]; ring
  have hprod_gt : Real.Gamma c < x₁ ^ c * tricomiTailMoment 0 c x₁ := by
    have hmul := mul_le_mul_of_nonneg_left (hval ▸ hmono2.trans hmono1)
      (Real.rpow_pos_of_pos hx₁_pos c).le
    have hsimp : x₁ ^ c * (Real.exp (-1) * (1 - x₁ ^ (-c)) / (-c)) =
        Real.exp (-1) * (B - 1) / (-c) := by
      rw [← mul_div_assoc, mul_left_comm (x₁ ^ c), mul_sub, mul_one,
        ← Real.rpow_add hx₁_pos, add_neg_cancel, Real.rpow_zero, hx₁_pow]
    rw [hsimp] at hmul
    have hgt : Real.Gamma c < Real.exp (-1) * (B - 1) / (-c) := by
      rw [lt_div_iff₀ (show 0 < -c by linarith), Real.exp_neg, ← div_eq_inv_mul,
        lt_div_iff₀ (Real.exp_pos 1)]
      dsimp only [B]; linarith
    exact hgt.trans_le hmul
  refine ⟨x₁, hx₁_pos, c, hc_mem, ?_⟩
  have hlog := Real.log_lt_log hΓc hprod_gt
  rw [Real.log_mul (Real.rpow_pos_of_pos hx₁_pos c).ne' (tricomiTailMoment_zero_pos c hx₁_pos).ne',
    Real.log_rpow hx₁_pos] at hlog
  dsimp only [phi]; linarith

private theorem exists_phi_pos_on {n : ℕ} (hn : 1 ≤ n) :
    ∃ x₂ > 0, ∀ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)), 0 < phi a x₂ := by
  let L : ℝ := -2 * (n : ℝ)
  let R : ℝ := 1 - 2 * (n : ℝ)
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Real.continuous_inv_Gamma.continuousOn (s := Icc L R))
  let M : ℝ := max M₀ 1
  let x₂ : ℝ := max 1 (Real.log M + 1)
  have hx₂_ge1 : 1 ≤ x₂ := le_max_left _ _
  have hx₂_pos : 0 < x₂ := lt_of_lt_of_le zero_lt_one hx₂_ge1
  refine ⟨x₂, hx₂_pos, fun a ha_mem => ?_⟩
  have ha_neg : a < 0 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [ha_mem.2]
  have hΓ_pos : 0 < Real.Gamma a := Gamma_pos_of_even_band hn ha_mem.1 ha_mem.2
  have hlogΓ_ge : -Real.log M ≤ Real.log (Real.Gamma a) := by
    have hbd := hM₀ a (Ioo_subset_Icc_self ha_mem)
    rw [Real.norm_of_nonneg (inv_pos.mpr hΓ_pos).le] at hbd
    have h := Real.log_le_log (inv_pos.mpr hΓ_pos) (hbd.trans (le_max_left M₀ 1))
    rw [Real.log_inv] at h; linarith
  have halogx_nonpos : a * Real.log x₂ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg ha_neg.le (Real.log_nonneg hx₂_ge1)
  have hI_le : tricomiTailMoment 0 a x₂ ≤ Real.exp (-x₂) := by
    have hmono : tricomiTailMoment 0 a x₂ ≤
        ∫ s in Ioi (0 : ℝ), Real.exp (-x₂) * Real.exp ((-1 : ℝ) * s) := by
      rw [tricomiTailMoment_def]
      refine setIntegral_mono_on (integrableOn_tricomiTailIntegrand 0 a hx₂_pos)
        ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul _)
        measurableSet_Ioi fun s hs => ?_
      simp only [pow_zero, one_mul, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : a * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha_neg.le hs.le
      have h2 : x₂ * (s + 1) ≤ x₂ * Real.exp s :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp s) hx₂_pos.le
      nlinarith [hs.out]
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -1) (by norm_num) 0] at hmono
    simpa using hmono
  have hlogI_le : Real.log (tricomiTailMoment 0 a x₂) ≤ -x₂ := by
    simpa [Real.log_exp] using Real.log_le_log (tricomiTailMoment_zero_pos a hx₂_pos) hI_le
  have hx₂_gt : Real.log M < x₂ := by linarith [le_max_right (1 : ℝ) (Real.log M + 1)]
  dsimp only [phi]; linarith

/-- **DLMF §8.13(iii)(b)**: for every `n ≥ 1`, there is a threshold `xs > 0` such that the zeros of
`γ*(·, x)` in `(-2n, 1 - 2n)` are two simple zeros for `0 < x < xs`, one double zero for `x = xs`,
and empty for `x > xs`. -/
theorem tricomiIncompleteGamma_param_zeros {n : ℕ} (hn : 1 ≤ n) :
    ∃ xs : ℝ, 0 < xs ∧ ∀ x : ℝ, 0 < x →
      (x < xs → ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = {a₁, a₂} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0) ∧
      (x = xs → ∃ a₀ : ℝ,
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = {a₀} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ = 0 ∧
        deriv (deriv fun b : ℝ => (tricomiIncompleteGamma b x).re) a₀ ≠ 0) ∧
      (xs < x →
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma a x = 0} = ∅) := by
  let L : ℝ := -2 * (n : ℝ)
  let R : ℝ := 1 - 2 * (n : ℝ)
  let aMin : ∀ x : ℝ, 0 < x → ℝ := fun x hx => (exists_phi_min hn hx).choose
  have haMin_mem : ∀ {x : ℝ} (hx : 0 < x), aMin x hx ∈ Ioo L R :=
    fun hx => (exists_phi_min hn hx).choose_spec.1
  have haMin_le : ∀ {x : ℝ} (hx : 0 < x), ∀ a ∈ Ioo L R, phi (aMin x hx) x ≤ phi a x :=
    fun hx => (exists_phi_min hn hx).choose_spec.2
  let m : ℝ → ℝ := fun x => if hx : 0 < x then phi (aMin x hx) x else 0
  have hm_eq : ∀ {x : ℝ} (hx : 0 < x), m x = phi (aMin x hx) x := fun hx => by simp [m, hx]
  have hm_mono : StrictMonoOn m (Ioi 0) := by
    intro x₁ hx₁ x₂ hx₂ h12
    rw [hm_eq hx₁, hm_eq hx₂]
    exact (haMin_le hx₁ (aMin x₂ hx₂) (haMin_mem hx₂)).trans_lt
      (strictMonoOn_phi_right (aMin x₂ hx₂) hx₁ hx₂ h12)
  have hm_cont : ContinuousOn m (Ioi 0) := by
    intro x₀ hx₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    let K : Set (ℝ × ℝ) := Icc L R ×ˢ Icc (x₀ / 2) (x₀ + 1)
    let H : ℝ × ℝ → ℝ := fun p => p.1 * Real.log p.2 + Real.log (tricomiTailMoment 0 p.1 p.2)
    have hH_cont : ContinuousOn H K := by
      have hK_sub : K ⊆ univ ×ˢ Ioi 0 := fun p hp =>
        ⟨mem_univ p.1, lt_of_lt_of_le (half_pos hx₀) hp.2.1⟩
      refine (continuousOn_fst.mul
        (ContinuousOn.log continuousOn_snd fun p hp => (hK_sub hp).2.ne')).add ?_
      exact (continuousOn_tricomiTailMoment_zero.mono hK_sub).log fun p hp =>
        (tricomiTailMoment_zero_pos p.1 (hK_sub hp).2).ne'
    obtain ⟨δ, hδ, hδ_bound⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hH_cont) ε hε
    refine ⟨min δ (min (x₀ / 2) 1), lt_min hδ (lt_min (half_pos hx₀) zero_lt_one),
      fun x hx hdist => ?_⟩
    have hx_Icc : x ∈ Icc (x₀ / 2) (x₀ + 1) := by
      rw [Real.dist_eq, abs_lt] at hdist
      exact ⟨by linarith [min_le_right δ (min (x₀ / 2) 1), min_le_left (x₀ / 2) (1 : ℝ)],
        by linarith [min_le_right δ (min (x₀ / 2) 1), min_le_right (x₀ / 2) (1 : ℝ)]⟩
    have hx₀_Icc : x₀ ∈ Icc (x₀ / 2) (x₀ + 1) := ⟨by linarith [hx₀.out], by linarith⟩
    have hphi_close : ∀ a ∈ Ioo L R, |phi a x - phi a x₀| < ε := fun a ha => by
      have hd : dist (a, x) (a, x₀) < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact hdist.trans_le (min_le_left _ _)
      have hbd := hδ_bound (a, x) ⟨Ioo_subset_Icc_self ha, hx_Icc⟩
        (a, x₀) ⟨Ioo_subset_Icc_self ha, hx₀_Icc⟩ hd
      rw [Real.dist_eq] at hbd
      have heq : phi a x - phi a x₀ = -(H (a, x) - H (a, x₀)) := by dsimp [phi, H]; ring
      rwa [heq, abs_neg]
    rw [Real.dist_eq, hm_eq hx, hm_eq hx₀, abs_lt]
    have hup := abs_lt.mp (hphi_close (aMin x₀ hx₀) (haMin_mem hx₀))
    have hlo := abs_lt.mp (hphi_close (aMin x hx) (haMin_mem hx))
    exact ⟨by linarith [haMin_le hx₀ (aMin x hx) (haMin_mem hx)],
      by linarith [haMin_le hx (aMin x₀ hx₀) (haMin_mem hx₀)]⟩
  obtain ⟨x₁, hx₁_pos, c, hc_mem, hφc_neg⟩ := exists_phi_lt_zero hn
  obtain ⟨x₂, hx₂_pos, hφ_pos⟩ := exists_phi_pos_on hn
  have hm₁_neg : m x₁ < 0 := by
    rw [hm_eq hx₁_pos]; exact (haMin_le hx₁_pos c hc_mem).trans_lt hφc_neg
  have hm₂_pos : 0 < m x₂ := by
    rw [hm_eq hx₂_pos]; exact hφ_pos (aMin x₂ hx₂_pos) (haMin_mem hx₂_pos)
  have hx₁₂ : x₁ ≤ x₂ := by
    by_contra hlt; linarith [hm_mono hx₂_pos hx₁_pos (not_le.mp hlt)]
  obtain ⟨xs, hxs_mem, hms⟩ := intermediate_value_Icc hx₁₂
    (hm_cont.mono fun x hx => lt_of_lt_of_le hx₁_pos hx.1) ⟨hm₁_neg.le, hm₂_pos.le⟩
  have hxs_pos : 0 < xs := lt_of_lt_of_le hx₁_pos hxs_mem.1
  refine ⟨xs, hxs_pos, fun x hx => ?_⟩
  have htri := phi_trichotomy hn hx (haMin_mem hx) (haMin_le hx)
  refine ⟨fun hlt => htri.1 ?_, fun heq => htri.2.1 ?_, fun hgt => htri.2.2 ?_⟩
  · rw [← hm_eq hx, ← hms]; exact hm_mono hx hxs_pos hlt
  · rw [← hm_eq hx, heq, hms]
  · rw [← hm_eq hx, ← hms]; exact hm_mono hxs_pos hx hgt

end Complex

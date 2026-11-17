/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Parameter zeros of Tricomi's incomplete Gamma function for negative arguments

This file classifies the real zeros of `a ↦ γ*(a, x)` for fixed real `x < 0`, where `γ*` is
Tricomi's entire incomplete Gamma function (`Complex.tricomiIncompleteGamma`), establishing
DLMF §8.13(iii)(a):

* `Complex.existsUnique_tricomiIncompleteGamma_eq_zero_of_neg` — for `x < 0` and every `m : ℕ`,
  `γ*(·, x)` has a unique real zero in `(−(m + 1), −m)`.
* `Complex.deriv_tricomiIncompleteGamma_re_ne_zero_of_neg` — every such zero is simple.
* `Complex.tricomiIncompleteGamma_param_zeros_of_neg` — for `x < 0` and `n ≥ 1`, `γ*(·, x)`
  has exactly two real zeros in `(−2n, 2 − 2n)`, both simple.

## Implementation notes

Multiplying by `Γ(a)` turns `γ*(a, x)` into the positive-coefficient series
`∑ (-x)^k / (k! (a + k))`, which is differentiable term-by-term with strictly negative derivative
on every negative unit interval `(−(m + 1), −m)` and changes sign between the poles.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.13(iii)](https://dlmf.nist.gov/8.13#iii).
* F. G. Tricomi, *Sulla funzione gamma incompleta*, Ann. Mat. Pura Appl. (4) 31 (1950).
-/

public section

noncomputable section

open Complex Filter Finset Set
open scoped Nat Topology

namespace Complex

private def negParamSeries (x a : ℝ) : ℝ :=
  ∑' k : ℕ, (-x) ^ k / (k ! * (a + k))

private theorem hasSum_negParamSeries (x : ℝ) {a : ℝ} (ha : ∀ k : ℕ, a ≠ -(k : ℝ)) :
    HasSum (fun k : ℕ => (-x) ^ k / (k ! * (a + k)))
      (Real.Gamma a * (tricomiIncompleteGamma a x).re) := by
  have haC : ∀ k : ℕ, (a : ℂ) ≠ -(k : ℂ) := fun k hk => ha k (by exact_mod_cast hk)
  have hΓ : Gamma (a : ℂ) ≠ 0 := Gamma_ne_zero haC
  have hre := Complex.reCLM.hasSum
    ((hasSum_tricomiIncompleteGamma_of_ne_neg_natCast haC (x : ℂ)).mul_left (Gamma (a : ℂ)))
  have hval : (Gamma (a : ℂ) * tricomiIncompleteGamma a x).re =
      Real.Gamma a * (tricomiIncompleteGamma a x).re := by
    rw [Complex.Gamma_ofReal, Complex.re_ofReal_mul]
  rw [Complex.reCLM_apply, hval] at hre
  refine hre.congr_fun fun k => ?_
  rw [Complex.reCLM_apply, ← mul_assoc, mul_inv_cancel₀ hΓ, one_mul]
  have hreal : (-(x : ℂ)) ^ k / ((k ! : ℂ) * ((a : ℂ) + k)) =
      (((-x) ^ k / ((k ! : ℝ) * (a + k)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hreal, Complex.ofReal_re]

private theorem negParamSeries_eq_Gamma_mul (x : ℝ) {a : ℝ}
    (ha : ∀ k : ℕ, a ≠ -(k : ℝ)) :
    negParamSeries x a = Real.Gamma a * (tricomiIncompleteGamma a x).re :=
  (hasSum_negParamSeries x ha).tsum_eq

private theorem hasDerivAt_negParamSeries {x : ℝ} (hx : x < 0) {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ))) :
    HasDerivAt (negParamSeries x) (∑' k : ℕ, -((-x) ^ k / (k ! * (a + k) ^ 2))) a := by
  have hy : 0 < -x := neg_pos.mpr hx
  let δ : ℝ := min (a - -((m + 1 : ℕ) : ℝ)) (-(m : ℝ) - a) / 2
  have hδ : 0 < δ := half_pos (lt_min (by linarith [ha.1]) (by linarith [ha.2]))
  have hδ1 : δ ≤ (a - -((m + 1 : ℕ) : ℝ)) / 2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδ2 : δ ≤ (-(m : ℝ) - a) / 2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hdist : ∀ k : ℕ, ∀ b ∈ Ioo (a - δ) (a + δ), δ ≤ |b + k| := fun k b hb => by
    by_cases hk : k ≤ m
    · have hk' : (k : ℝ) ≤ m := Nat.cast_le.mpr hk
      rw [abs_of_nonpos (by linarith [hb.2, hδ2])]; linarith [hb.2, hδ2]
    · have hk' : ((m + 1 : ℕ) : ℝ) ≤ k := Nat.cast_le.mpr (by omega)
      rw [abs_of_nonneg (by linarith [hb.1, hδ1])]; linarith [hb.1, hδ1]
  have hu : Summable fun k : ℕ => (δ ^ 2)⁻¹ * ((-x) ^ k / (k ! : ℝ)) :=
    (Real.summable_pow_div_factorial (-x)).mul_left _
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun k y => (-x) ^ k / (k ! * (y + k)))
    (g' := fun k y => -((-x) ^ k / (k ! * (y + k) ^ 2)))
    (t := Ioo (a - δ) (a + δ)) (y₀ := a) (y := a) hu isOpen_Ioo
    isPreconnected_Ioo (fun k b hb => ?_) (fun k b hb => ?_) ⟨by linarith, by linarith⟩
    (hasSum_negParamSeries x (Real.ne_neg_natCast_of_mem_Ioo ha)).summable
    ⟨by linarith, by linarith⟩
  · have hbk : b + k ≠ 0 := fun h0 => by
      have := hdist k b hb; rw [h0, abs_zero] at this; linarith
    have h2 : HasDerivAt (fun y : ℝ => (y + k)⁻¹) (-((b + k) ^ 2)⁻¹) b := by
      simpa only [neg_div, one_div] using ((hasDerivAt_id' b).add_const (k : ℝ)).fun_inv hbk
    have h3 := h2.const_mul ((-x) ^ k / (k ! : ℝ))
    have hfun : (fun y : ℝ => (-x) ^ k / (k ! : ℝ) * (y + k)⁻¹) =
        fun y => (-x) ^ k / (k ! * (y + k)) := by
      ext y; rw [← div_eq_mul_inv, div_div]
    rw [hfun] at h3
    convert h3 using 1
    rw [mul_neg, ← div_eq_mul_inv, div_div]
  · have hsq : δ ^ 2 ≤ (b + k) ^ 2 := by
      rw [← sq_abs (b + k)]; exact pow_le_pow_left₀ hδ.le (hdist k b hb) 2
    have hnn : 0 ≤ (-x) ^ k / (k ! * (b + k) ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hnn]
    calc (-x) ^ k / (k ! * (b + k) ^ 2)
        = ((b + k) ^ 2)⁻¹ * ((-x) ^ k / (k ! : ℝ)) := by
            rw [div_mul_eq_div_div, div_eq_inv_mul]
      _ ≤ (δ ^ 2)⁻¹ * ((-x) ^ k / (k ! : ℝ)) := by gcongr

private theorem deriv_negParamSeries_neg {x : ℝ} (hx : x < 0) {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ))) :
    deriv (negParamSeries x) a < 0 := by
  have hy : 0 < -x := neg_pos.mpr hx
  let δ : ℝ := min (a - -((m + 1 : ℕ) : ℝ)) (-(m : ℝ) - a)
  have hδ : 0 < δ := lt_min (by linarith [ha.1]) (by linarith [ha.2])
  have hdist : ∀ k : ℕ, δ ≤ |a + k| := fun k => by
    by_cases hk : k ≤ m
    · have hk' : (k : ℝ) ≤ m := Nat.cast_le.mpr hk
      rw [abs_of_nonpos (by linarith [ha.2])]; linarith [min_le_right (a - -((m + 1 : ℕ) : ℝ))
        (-(m : ℝ) - a)]
    · have hk' : ((m + 1 : ℕ) : ℝ) ≤ k := Nat.cast_le.mpr (by omega)
      rw [abs_of_nonneg (by linarith [ha.1])]; linarith [min_le_left (a - -((m + 1 : ℕ) : ℝ))
        (-(m : ℝ) - a)]
  rw [(hasDerivAt_negParamSeries hx ha).deriv]
  have hsum : Summable fun k : ℕ => (-x) ^ k / (k ! * (a + k) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((Real.summable_pow_div_factorial (-x)).mul_left (δ ^ 2)⁻¹)
    have hsq : δ ^ 2 ≤ (a + k) ^ 2 := by
      rw [← sq_abs (a + k)]; exact pow_le_pow_left₀ hδ.le (hdist k) 2
    calc (-x) ^ k / (k ! * (a + k) ^ 2)
        = ((a + k) ^ 2)⁻¹ * ((-x) ^ k / (k ! : ℝ)) := by
            rw [div_mul_eq_div_div, div_eq_inv_mul]
      _ ≤ (δ ^ 2)⁻¹ * ((-x) ^ k / (k ! : ℝ)) := by gcongr
  rw [tsum_neg]
  have ha0 : a ≠ 0 := by simpa using Real.ne_neg_natCast_of_mem_Ioo ha 0
  have h0 : 0 < (-x) ^ 0 / ((0 : ℕ)! * (a + (0 : ℕ)) ^ 2) := by
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, add_zero, one_mul]
    positivity
  linarith [hsum.le_tsum 0 (fun k _ => by positivity)]

private theorem exists_negParamSeries_pos {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃ a ∈ Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ)), 0 < negParamSeries x a := by
  have hy : 0 < -x := neg_pos.mpr hx
  let C : ℝ := ∑ k ∈ range (m + 1), 2 * ((-x) ^ k / (k ! : ℝ))
  have hC : 0 ≤ C := sum_nonneg fun k _ => by positivity
  let ε : ℝ := min (1 / 4) (((-x) ^ (m + 1) / ((m + 1)! : ℝ)) / (C + 2))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε_le : ε ≤ 1 / 4 := min_le_left _ _
  let a : ℝ := -((m + 1 : ℕ) : ℝ) + ε
  have ha : a ∈ Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ)) := by
    dsimp only [a]; constructor <;> [linarith; (push_cast; linarith)]
  refine ⟨a, ha, ?_⟩
  have hsum := (hasSum_negParamSeries x (Real.ne_neg_natCast_of_mem_Ioo ha)).summable
  rw [negParamSeries, ← hsum.sum_add_tsum_nat_add (m + 1)]
  have hfin : -C ≤ ∑ k ∈ range (m + 1), (-x) ^ k / (k ! * (a + k)) := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun k hk => ?_
    have hkm : (k : ℝ) ≤ m := Nat.cast_le.mpr (Nat.lt_succ_iff.mp (mem_range.mp hk))
    have hak : a + k ≤ -(1 / 2 : ℝ) := by dsimp only [a]; push_cast; linarith
    have hinv : (-(a + k))⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    have hle : (-x) ^ k / (k ! * -(a + k)) ≤ 2 * ((-x) ^ k / (k ! : ℝ)) := by
      calc (-x) ^ k / (k ! * -(a + k))
          = (-(a + k))⁻¹ * ((-x) ^ k / (k ! : ℝ)) := by
              rw [div_mul_eq_div_div, div_eq_inv_mul]
        _ ≤ 2 * ((-x) ^ k / (k ! : ℝ)) := by gcongr
    have heq : (-x) ^ k / (k ! * (a + k)) = -((-x) ^ k / (k ! * -(a + k))) := by
      rw [mul_neg, div_neg, neg_neg]
    linarith
  have htail : (-x) ^ (m + 1) / ((m + 1)! * ε) ≤
      ∑' j : ℕ, (-x) ^ (j + (m + 1)) / ((j + (m + 1))! * (a + (j + (m + 1) : ℕ))) := by
    have h0 := ((summable_nat_add_iff (m + 1)).mpr hsum).le_tsum 0 fun j _ => by
      have : 0 < a + (j + (m + 1) : ℕ) := by
        dsimp only [a]; push_cast; linarith [j.cast_nonneg (α := ℝ)]
      positivity
    have ha_add : a + ((m : ℝ) + 1) = ε := by dsimp only [a]; push_cast; ring
    simpa [ha_add] using h0
  have hbig : C + 1 < (-x) ^ (m + 1) / ((m + 1)! * ε) := by
    have hle : ε ≤ ((-x) ^ (m + 1) / ((m + 1)! : ℝ)) / (C + 2) := min_le_right _ _
    rw [← div_div, lt_div_iff₀ hε]
    linarith [(le_div_iff₀ (by linarith : 0 < C + 2)).mp hle]
  linarith

private theorem exists_negParamSeries_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃ a ∈ Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ)), negParamSeries x a < 0 := by
  have hy : 0 < -x := neg_pos.mpr hx
  let C : ℝ := 2 * Real.exp (-x)
  have hC : 0 < C := by positivity
  let ε : ℝ := min (1 / 4) (((-x) ^ m / (m ! : ℝ)) / (C + 2))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε_le : ε ≤ 1 / 4 := min_le_left _ _
  let a : ℝ := -(m : ℝ) - ε
  have ha : a ∈ Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ)) := by
    dsimp only [a]; constructor <;> [(push_cast; linarith); linarith]
  refine ⟨a, ha, ?_⟩
  have hsum := (hasSum_negParamSeries x (Real.ne_neg_natCast_of_mem_Ioo ha)).summable
  rw [negParamSeries, ← hsum.sum_add_tsum_nat_add (m + 1)]
  have hfin : ∑ k ∈ range (m + 1), (-x) ^ k / (k ! * (a + k)) ≤ -((-x) ^ m / (m ! * ε)) := by
    rw [sum_range_succ]
    have hprev : ∑ k ∈ range m, (-x) ^ k / (k ! * (a + k)) ≤ 0 := sum_nonpos fun k hk => by
      have hkm : (k : ℝ) ≤ m := Nat.cast_le.mpr (le_of_lt (mem_range.mp hk))
      exact div_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [ha.2]))
    have hm : (-x) ^ m / (m ! * (a + m)) = -((-x) ^ m / (m ! * ε)) := by
      have : a + m = -ε := by dsimp only [a]; ring
      rw [this, mul_neg, div_neg]
    linarith
  have htail :
      ∑' j : ℕ, (-x) ^ (j + (m + 1)) / ((j + (m + 1))! * (a + (j + (m + 1) : ℕ))) ≤ C := by
    have hle1 := ((summable_nat_add_iff (m + 1)).mpr hsum).tsum_le_tsum (fun j => by
      have hge : (1 / 2 : ℝ) ≤ a + (j + (m + 1) : ℕ) := by
        dsimp only [a]; push_cast; linarith [j.cast_nonneg (α := ℝ)]
      have hinv : (a + (j + (m + 1) : ℕ))⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) two_pos]; linarith
      rw [div_mul_eq_div_div, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right hinv (by positivity))
      ((summable_nat_add_iff (m + 1)).mpr ((Real.summable_pow_div_factorial (-x)).mul_left 2))
    have hall := ((Real.summable_pow_div_factorial (-x)).mul_left 2).sum_add_tsum_nat_add (m + 1)
    have hnn : 0 ≤ ∑ k ∈ range (m + 1), 2 * ((-x) ^ k / (k ! : ℝ)) :=
      sum_nonneg fun k _ => by positivity
    have heq : ∑' k : ℕ, 2 * ((-x) ^ k / (k ! : ℝ)) = C := by
      dsimp only [C]; rw [tsum_mul_left, Real.exp_eq_exp_ℝ]
      exact congrArg (2 * ·) (NormedSpace.expSeries_div_hasSum_exp (-x)).tsum_eq
    linarith
  have hbig : C + 1 < (-x) ^ m / (m ! * ε) := by
    have hle : ε ≤ ((-x) ^ m / (m ! : ℝ)) / (C + 2) := min_le_right _ _
    rw [← div_div, lt_div_iff₀ hε]
    linarith [(le_div_iff₀ (by linarith : 0 < C + 2)).mp hle]
  linarith

/-- For `x < 0` and every `m : ℕ`, Tricomi's function `γ*(·, x)` has a unique real zero in
`(−(m + 1), −m)`. -/
theorem existsUnique_tricomiIncompleteGamma_eq_zero_of_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃! a : ℝ,
      a ∈ Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ)) ∧ tricomiIncompleteGamma a x = 0 := by
  let I := Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ))
  have hanti : StrictAntiOn (negParamSeries x) I :=
    strictAntiOn_of_deriv_neg (convex_Ioo _ _)
      (fun _ ha => (hasDerivAt_negParamSeries hx ha).continuousAt.continuousWithinAt)
      (fun _ ha => deriv_negParamSeries_neg hx (interior_subset ha))
  obtain ⟨a₁, ha₁, hpos⟩ := exists_negParamSeries_pos hx m
  obtain ⟨a₂, ha₂, hneg⟩ := exists_negParamSeries_neg hx m
  have hlt : a₁ < a₂ := by
    by_contra hle
    rcases eq_or_lt_of_le (not_lt.mp hle) with rfl | hgt
    · linarith
    · linarith [hanti ha₂ ha₁ hgt]
  have hcont : ContinuousOn (negParamSeries x) (Icc a₁ a₂) := fun _ hb =>
    (hasDerivAt_negParamSeries hx ⟨lt_of_lt_of_le ha₁.1 hb.1, lt_of_le_of_lt hb.2 ha₂.2⟩)
      |>.continuousAt.continuousWithinAt
  obtain ⟨a, ha_icc, ha_zero⟩ := intermediate_value_Icc' hlt.le hcont ⟨hneg.le, hpos.le⟩
  have haI : a ∈ I := ⟨lt_of_lt_of_le ha₁.1 ha_icc.1, lt_of_le_of_lt ha_icc.2 ha₂.2⟩
  have hiff : ∀ b ∈ I, tricomiIncompleteGamma b x = 0 ↔ negParamSeries x b = 0 :=
    fun b hb => by
      rw [tricomiIncompleteGamma_ofReal_eq_zero_iff,
        negParamSeries_eq_Gamma_mul x (Real.ne_neg_natCast_of_mem_Ioo hb),
        mul_eq_zero, or_iff_right (Real.Gamma_ne_zero (Real.ne_neg_natCast_of_mem_Ioo hb))]
  refine ⟨a, ⟨haI, (hiff a haI).mpr ha_zero⟩, ?_⟩
  rintro b ⟨hbI, hb0⟩
  exact hanti.injOn hbI haI (((hiff b hbI).mp hb0).trans ha_zero.symm)

/-- For `x < 0` and every `m : ℕ`, every real zero of `γ*(·, x)` in `(−(m + 1), −m)` is
simple. -/
theorem deriv_tricomiIncompleteGamma_re_ne_zero_of_neg {x : ℝ} (hx : x < 0) {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-((m + 1 : ℕ) : ℝ)) (-(m : ℝ)))
    (h0 : tricomiIncompleteGamma a x = 0) :
    deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a ≠ 0 := by
  have hre0 : (tricomiIncompleteGamma a x).re = 0 :=
    (tricomiIncompleteGamma_ofReal_eq_zero_iff a x).mp h0
  have hEq : negParamSeries x =ᶠ[𝓝 a]
      fun b : ℝ => Real.Gamma b * (tricomiIncompleteGamma b x).re := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact negParamSeries_eq_Gamma_mul x (Real.ne_neg_natCast_of_mem_Ioo hb)
  have hdiff : DifferentiableAt ℝ (fun b : ℝ => (tricomiIncompleteGamma b x).re) a := by
    have hc := (differentiable_tricomiIncompleteGamma_left (x : ℂ) a).hasDerivAt.comp_ofReal
    exact Complex.reCLM.differentiableAt.comp a hc.differentiableAt
  have hprod := (Real.differentiableAt_Gamma (Real.ne_neg_natCast_of_mem_Ioo ha)).hasDerivAt
    |>.fun_mul hdiff.hasDerivAt
  have hderiv : deriv (negParamSeries x) a =
      Real.Gamma a * deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a := by
    rw [hEq.deriv_eq, hprod.deriv, hre0, mul_zero, zero_add]
  have hneg := deriv_negParamSeries_neg hx ha
  intro hd0
  rw [hd0, mul_zero] at hderiv
  linarith

/-- DLMF §8.13(iii)(a): for `x < 0` and `n ≥ 1`, Tricomi's function `γ*(·, x)` has exactly two
real zeros in `(−2n, 2 − 2n)`, both simple. -/
theorem tricomiIncompleteGamma_param_zeros_of_neg {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x < 0) :
    ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (2 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma a x = 0} = {a₁, a₂} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₁ ≠ 0 ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma b x).re) a₂ ≠ 0 := by
  obtain ⟨a₁, ⟨ha₁I, ha₁0⟩, ha₁u⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * n - 1)
  obtain ⟨a₂, ⟨ha₂I, ha₂0⟩, ha₂u⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * n - 2)
  have hc1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hc2 : ((2 * n - 1 + 1 : ℕ) : ℝ) = 2 * (n : ℝ) := by
    rw [Nat.sub_add_cancel (by omega)]; push_cast; ring
  have hc3 : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hc4 : ((2 * n - 2 + 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    have h21 : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    rw [h21, hc1]
  refine ⟨a₁, a₂, by linarith [ha₁I.2, ha₂I.1], ?_,
    deriv_tricomiIncompleteGamma_re_ne_zero_of_neg hx ha₁I ha₁0,
    deriv_tricomiIncompleteGamma_re_ne_zero_of_neg hx ha₂I ha₂0⟩
  ext a
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨haI, ha0⟩
    rcases lt_trichotomy a (1 - 2 * (n : ℝ)) with hlt | heq | hgt
    · exact Or.inl (ha₁u a ⟨⟨by linarith [haI.1], by linarith⟩, ha0⟩)
    · exfalso
      have hcast : (a : ℂ) = -((2 * n - 1 : ℕ) : ℂ) := by
        rw [heq, Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast, tricomiIncompleteGamma_neg_natCast] at ha0
      exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hx.ne) ha0
    · exact Or.inr (ha₂u a ⟨⟨by linarith, by linarith [haI.2]⟩, ha0⟩)
  · rintro (rfl | rfl)
    · exact ⟨⟨by linarith [ha₁I.1], by linarith [ha₁I.2]⟩, ha₁0⟩
    · exact ⟨⟨by linarith [ha₂I.1], by linarith [ha₂I.2]⟩, ha₂0⟩

end Complex

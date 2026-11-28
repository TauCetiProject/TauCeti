/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Distant vertical integrals in Perron inversion

In the subtracted Perron contour for an interval `(a, b]`, the distant left edge vanishes
when both endpoints are at least one and the multiplier is at most logarithmic on the edge.
The left abscissae can approach `−∞` through a sequence avoiding poles; the bound need
not hold in the whole left half-plane. The contour method is from Koukoulopoulos,
*The Distribution of Prime Numbers*, Chapter 8, proof of Theorem 5.1.
-/

public section

open Complex Filter Set
open scoped Interval NNReal Topology

namespace TauCeti

/-- Linear growth in `‖s‖` of the multiplier cancels the divisor `s` on a vertical
segment. The bound is the length of the segment times the sum of the two endpoint
powers, scaled by the growth constant. -/
theorem norm_integral_mul_sub_perronIntegrand_le {F : ℂ → ℂ} {a b c u v : ℝ} {C : ℝ≥0}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ t ∈ uIoc u v, ‖F ((c : ℂ) + t * I)‖ ≤ C * ‖(c : ℂ) + t * I‖) :
    ‖∫ t in u..v, F ((c : ℂ) + t * I) *
        (perronIntegrand b c t - perronIntegrand a c t)‖ ≤
      C * (b ^ c + a ^ c) * |v - u| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
  let s : ℂ := (c : ℂ) + t * I
  have hs : s.re = c := by simp [s]
  have hpow (x : ℝ) (hx : 0 ≤ x) : ‖(x : ℂ) ^ s‖ ≤ x ^ c := by
    rcases hx.eq_or_lt with rfl | hx
    · by_cases h : s = 0
      · have hc : c = 0 := by simpa [h] using hs.symm
        simp [h, hc]
      · simpa [Complex.zero_cpow h] using Real.rpow_nonneg (x := 0) le_rfl c
    · rw [norm_cpow_eq_rpow_re_of_pos hx, hs]
  rw [perronIntegrand_def, perronIntegrand_def, ← sub_div, norm_mul, norm_div]
  calc
    _ ≤ ((C : ℝ) * ‖s‖) * (‖(b : ℂ) ^ s - (a : ℂ) ^ s‖ / ‖s‖) :=
      mul_le_mul_of_nonneg_right (hF t ht) (by positivity)
    _ ≤ C * ‖(b : ℂ) ^ s - (a : ℂ) ^ s‖ := by
      by_cases h : ‖s‖ = 0
      · rw [h, mul_zero, zero_mul]
        positivity
      · rw [mul_assoc, mul_div_cancel₀ _ h]
    _ ≤ C * (b ^ c + a ^ c) :=
      mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add (hpow b hb) (hpow a ha))) C.coe_nonneg

/-- Along any family of vertical segments whose abscissae tend to `−∞`, the subtracted
Perron integral tends to zero if the multiplier grows at most linearly in `‖s‖` there.
The endpoints of the counting interval must exceed one, and the ordinate interval is fixed. -/
theorem tendsto_integral_mul_sub_perronIntegrand {ι : Type*} {l : Filter ι} {c : ι → ℝ}
    {F : ℂ → ℂ} {a b u v : ℝ} {C : ℝ≥0} (ha : 1 < a) (hb : 1 < b) (hc : Tendsto c l atBot)
    (hF : ∀ᶠ j in l, ∀ t ∈ uIoc u v,
      ‖F ((c j : ℂ) + t * I)‖ ≤ C * ‖(c j : ℂ) + t * I‖) :
    Tendsto (fun j ↦ ∫ t in u..v, F ((c j : ℂ) + t * I) *
      (perronIntegrand b (c j) t - perronIntegrand a (c j) t)) l (𝓝 0) := by
  have hpow (x : ℝ) (hx : 1 < x) : Tendsto (fun j ↦ x ^ c j) l (𝓝 0) :=
    (tendsto_rpow_atBot_of_base_gt_one x hx).comp hc
  have hbound : Tendsto (fun j ↦ (C : ℝ) * (b ^ c j + a ^ c j) * |v - u|) l (𝓝 0) := by
    simpa using (((hpow b hb).add (hpow a ha)).const_mul (C : ℝ)).mul_const |v - u|
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hF] with j hj
  exact norm_integral_mul_sub_perronIntegrand_le (zero_le_one.trans ha.le)
    (zero_le_one.trans hb.le) hj

/-- The distant vertical side of the subtracted Perron contour tends to zero under the
logarithmic growth bound for a Dirichlet logarithmic derivative. The abscissae may
be restricted to negative half-integers. The divisor `s` gives decay even with a
counting endpoint equal to one. -/
theorem tendsto_integral_mul_sub_perronIntegrand_of_log_bound
    {ι : Type*} {l : Filter ι} {c : ι → ℝ} {F : ℂ → ℂ} {a b u v : ℝ} {q : ℕ} {C : ℝ≥0}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : Tendsto c l atBot)
    (hF : ∀ᶠ j in l, ∀ t ∈ uIoc u v,
      ‖F ((c j : ℂ) + t * I)‖ ≤ C * Real.log (q * (‖(c j : ℂ) + t * I‖ + 2))) :
    Tendsto (fun j ↦ ∫ t in u..v, F ((c j : ℂ) + t * I) *
      (perronIntegrand b (c j) t - perronIntegrand a (c j) t)) l (𝓝 0) := by
  let B : ℝ := 2 * C * √(3 * q)
  have hlim := (Real.tendsto_sqrt_atTop.comp (tendsto_neg_atBot_atTop.comp hc)).inv_tendsto_atTop
  have hbound : Tendsto (fun j ↦ (B / √(-c j)) * 2 * |v - u|) l (𝓝 0) := by
    simpa [div_eq_mul_inv] using (((hlim.const_mul B).mul_const 2).mul_const |v - u|)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hF, hc.eventually (eventually_le_atBot (-1 : ℝ))] with j hj hj₁
  let D : ℝ≥0 := ⟨B / √(-c j), by dsimp [B]; positivity⟩
  have hD_def : (D : ℝ) = B / √(-c j) := rfl
  have hD : ∀ t ∈ uIoc u v, ‖F ((c j : ℂ) + t * I)‖ ≤ D * ‖(c j : ℂ) + t * I‖ := by
    intro t ht
    let s : ℂ := (c j : ℂ) + t * I
    have hc_le : -c j ≤ ‖s‖ := by
      simpa [s, abs_of_nonpos (by linarith : c j ≤ 0)] using abs_re_le_norm s
    have hnorm : 1 ≤ ‖s‖ := by linarith
    have hlog : Real.log (q * (‖s‖ + 2)) ≤ 2 * √(3 * q) * √‖s‖ := calc
      _ ≤ √((q : ℝ) * (‖s‖ + 2)) / (1 / 2) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.log_le_rpow_div (by positivity) (by norm_num)
      _ ≤ √((3 * q : ℝ) * ‖s‖) / (1 / 2) := by
        refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num)
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) q) (sub_nonneg.mpr hnorm)]
      _ = _ := by rw [Real.sqrt_mul (by positivity)]; ring
    refine (hj t ht).trans ((mul_le_mul_of_nonneg_left hlog C.coe_nonneg).trans ?_)
    have hsqrt : 0 < √(-c j) := Real.sqrt_pos_of_pos (by linarith)
    have hsq := Real.sq_sqrt (norm_nonneg s)
    -- Compare the two square roots, then cancel one against the divisor bound.
    rw [hD_def, div_mul_eq_mul_div, le_div_iff₀ hsqrt]
    calc
      _ = B * (√‖s‖ * √(-c j)) := by dsimp [B]; ring
      _ ≤ B * (√‖s‖ * √‖s‖) := by gcongr
      _ = B * ‖s‖ := by rw [← sq, hsq]
  refine (norm_integral_mul_sub_perronIntegrand_le (zero_le_one.trans ha)
    (zero_le_one.trans hb) hD).trans ?_
  have hexp : c j ≤ 0 := by linarith
  have hpa := Real.rpow_le_one_of_one_le_of_nonpos ha hexp
  have hpb := Real.rpow_le_one_of_one_le_of_nonpos hb hexp
  have hsum : b ^ c j + a ^ c j ≤ 2 := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum D.coe_nonneg) (abs_nonneg _)

end TauCeti

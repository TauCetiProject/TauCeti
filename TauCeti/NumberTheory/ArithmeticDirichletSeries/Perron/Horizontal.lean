/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.ExpWeight

/-!
# Horizontal edges for the subtracted Perron kernel

Integrate the kernel `(x^s - y^s) / s` on a horizontal segment. Exponential decay in the
real coordinate compensates for linear growth of the multiplier, giving a bound independent
of how far left the contour is shifted. The half-interval specialization uses `y = x / 2`
and the Perron abscissa `1 + 1 / log x`.

For the contour argument see Koukoulopoulos, *The Distribution of Prime Numbers*, Chapter 8,
proof of Theorem 5.1; the kernel here is the difference of the two endpoint kernels.
-/

public section

open Complex (I add_re add_im ofReal_re ofReal_im mul_re mul_im norm_cpow_eq_rpow_re_of_pos)
open Real Set

namespace TauCeti

/-- Bound a horizontal integral of a subtracted Perron kernel with an arbitrary multiplier.
The multiplier may grow linearly with the distance from the right endpoint `c`. -/
theorem norm_intervalIntegral_mul_cpow_sub_div_le {f : ℂ → ℂ} {x y a c t M : ℝ}
    (hx : 1 < x) (hy : 1 < y) (hac : a ≤ c) (ht : t ≠ 0)
    (hf : ∀ σ ∈ Icc a c, ‖f (σ + t * I)‖ ≤ M * (1 + c - σ)) :
    ‖∫ σ in a..c, f (σ + t * I) * (((x : ℂ) ^ ((σ : ℂ) + t * I) -
      (y : ℂ) ^ ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I))‖ ≤
      M / |t| * (x ^ c * ((log x)⁻¹ + (log x)⁻¹ ^ 2) +
        y ^ c * ((log y)⁻¹ + (log y)⁻¹ ^ 2)) := by
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hy₀ : 0 < y := zero_lt_one.trans hy
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hf c ⟨hac, le_rfl⟩)
  let g (v σ : ℝ) := v ^ σ * (1 + c - σ)
  have hcont {v : ℝ} (hv : v ≠ 0) : Continuous (g v) := by dsimp only [g]; fun_prop
  have hix := (hcont hx₀.ne').intervalIntegrable (μ := MeasureTheory.volume) a c
  have hiy := (hcont hy₀.ne').intervalIntegrable (μ := MeasureTheory.volume) a c
  calc
    _ ≤ ∫ σ in a..c, M / |t| * (g x σ + g y σ) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hac
        (Filter.Eventually.of_forall fun σ hσ ↦ ?_)
        ((hix.add hiy).const_mul _)
      let z : ℂ := σ + t * I
      have hzRe : z.re = σ := by simp [z, mul_re]
      have hzIm : z.im = t := by simp [z, mul_im]
      have hzNorm : |t| ≤ ‖z‖ := hzIm ▸ Complex.abs_im_le_norm z
      have hK : ‖((x : ℂ) ^ z - (y : ℂ) ^ z) / z‖ ≤ (x ^ σ + y ^ σ) / |t| := by
        rw [norm_div]
        apply div_le_div₀ (by positivity) ?_ (abs_pos.mpr ht) hzNorm
        simpa only [norm_cpow_eq_rpow_re_of_pos hx₀, norm_cpow_eq_rpow_re_of_pos hy₀, hzRe]
          using norm_sub_le ((x : ℂ) ^ z) ((y : ℂ) ^ z)
      rw [norm_mul]
      calc
        _ ≤ (M * (1 + c - σ)) * ((x ^ σ + y ^ σ) / |t|) :=
          mul_le_mul (hf σ ⟨hσ.1.le, hσ.2⟩) hK (norm_nonneg _)
            (mul_nonneg hM (by linarith [hσ.2]))
        _ = _ := by dsimp only [g]; ring
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hix hiy]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (Real.intervalIntegral_rpow_mul_one_add_sub_le hx hac)
          (Real.intervalIntegral_rpow_mul_one_add_sub_le hy hac)) (by positivity)

/-- For the half-interval Perron kernel, a linear multiplier bound on the horizontal edge
at height `t` gives an error at most `12 e M x / |t|`. The estimate is the same on the top
and bottom edges and uniform in the left endpoint. -/
theorem norm_integral_subtracted_perron_horizontal_le {f : ℂ → ℂ} {x a t M : ℝ}
    (hx : 4 ≤ x) (ha : a ≤ 1 + (log x)⁻¹) (ht : t ≠ 0)
    (hf : ∀ σ ∈ Icc a (1 + (log x)⁻¹), ‖f (σ + t * I)‖ ≤ M * (2 + (log x)⁻¹ - σ)) :
    ‖∫ σ in a..(1 + (log x)⁻¹), f (σ + t * I) * (((x : ℂ) ^ ((σ : ℂ) + t * I) -
      ((x / 2 : ℝ) : ℂ) ^ ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I))‖ ≤
      12 * exp 1 * M * x / |t| := by
  let c := 1 + (log x)⁻¹
  have hx₁ : 1 < x := by linarith
  have hy₁ : 1 < x / 2 := by linarith
  have hF : ∀ σ ∈ Icc a c, ‖f (σ + t * I)‖ ≤ M * (1 + c - σ) := by
    intro σ hσ
    rw [show 1 + c - σ = 2 + (log x)⁻¹ - σ by dsimp only [c]; ring]
    exact hf σ hσ
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hF c ⟨ha, le_rfl⟩)
  have hlog (v : ℝ) (hv : 2 ≤ v) : (log v)⁻¹ + (log v)⁻¹ ^ 2 ≤ 6 := by
    have h : (1 / 2 : ℝ) ≤ log v := by
      have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      exact (by norm_num at h₂ ⊢; linarith : (1 / 2 : ℝ) ≤ log 2) |>.trans
        (Real.log_le_log (by norm_num) hv)
    have hi : (log v)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
      simpa using h
    nlinarith [sq_nonneg ((log v)⁻¹), mul_nonneg (sub_nonneg.mpr hi)
      (by positivity : (0 : ℝ) ≤ 2 + (log v)⁻¹)]
  refine (norm_intervalIntegral_mul_cpow_sub_div_le hx₁ hy₁ ha ht hF).trans ?_
  have hc : 0 ≤ c := by dsimp only [c]; positivity [Real.log_pos hx₁]
  have hyx : (x / 2) ^ c ≤ x ^ c :=
    Real.rpow_le_rpow (by positivity : 0 ≤ x / 2) (by linarith) hc
  have hxc : x ^ c ≤ x * exp 1 := by
    rw [Real.rpow_add (zero_lt_one.trans hx₁), Real.rpow_one]
    exact mul_le_mul_of_nonneg_left Real.rpow_inv_log_le_exp_one (by linarith)
  calc
    _ ≤ M / |t| * (x ^ c * 6 + (x / 2) ^ c * 6) := by
      gcongr
      · exact hlog x (by linarith)
      · exact hlog (x / 2) (by linarith)
    _ ≤ M / |t| * ((x * exp 1) * 6 + (x * exp 1) * 6) := by
      gcongr
      exact hyx.trans hxc
    _ = _ := by ring

/-- A half-interval Perron edge with a uniform near-strip bound `A` and a logarithmic
bound `B log(q (‖s‖ + 2))` to the left of `Re s = -1`. Its integral is bounded uniformly
in the left endpoint, with the logarithm evaluated at the height rather than the left edge. -/
theorem norm_integral_subtracted_perron_horizontal_le_of_log_bound
    {f : ℂ → ℂ} {x a t q A B : ℝ}
    (hx : 4 ≤ x) (ha : a ≤ 1 + (log x)⁻¹) (ht : t ≠ 0) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (hnear : ∀ σ ∈ Icc a (1 + (log x)⁻¹), -1 ≤ σ → ‖f (σ + t * I)‖ ≤ A)
    (hfar : ∀ σ ∈ Icc a (1 + (log x)⁻¹), σ < -1 →
      ‖f (σ + t * I)‖ ≤ B * log (q * (‖(σ : ℂ) + t * I‖ + 2))) :
    ‖∫ σ in a..(1 + (log x)⁻¹), f (σ + t * I) * (((x : ℂ) ^ ((σ : ℂ) + t * I) -
      ((x / 2 : ℝ) : ℂ) ^ ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I))‖ ≤
      12 * exp 1 * (A + B * (1 + log (q * (|t| + 2)))) * x / |t| := by
  let c := 1 + (log x)⁻¹
  let L := log (q * (|t| + 2))
  have hc : 0 ≤ c := by dsimp only [c]; positivity [Real.log_pos (by linarith : 1 < x)]
  have hA : 0 ≤ A := (norm_nonneg _).trans (hnear c ⟨ha, le_rfl⟩ (by linarith))
  have hT : 1 ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hL : 0 ≤ L := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq hT)
  refine norm_integral_subtracted_perron_horizontal_le hx ha ht fun σ hσ ↦ ?_
  have hr : 1 ≤ 2 + (log x)⁻¹ - σ := by linarith [hσ.2]
  rcases le_or_gt (-1) σ with hs | hs
  · exact (hnear σ hσ hs).trans <| le_mul_of_one_le_right
      (by positivity) hr |>.trans' (le_add_of_nonneg_right (by positivity))
  have hn : ‖(σ : ℂ) + t * I‖ ≤ -σ + |t| := by
    simpa [norm_mul, Complex.norm_real, abs_of_neg (by linarith : σ < 0)] using
      norm_add_le (σ : ℂ) ((t : ℂ) * I)
  -- Divide out the height scale before applying `log(1+u) ≤ u`.
  have heq : q * (-σ + |t| + 2) = q * (|t| + 2) * (1 + (-σ) / (|t| + 2)) := by
    field_simp [show 0 < |t| + 2 by positivity |>.ne']
    ring
  have hd : 0 ≤ (-σ) / (|t| + 2) := by positivity [show 0 ≤ -σ by linarith]
  have hl : log (q * (‖(σ : ℂ) + t * I‖ + 2)) ≤ L + (-σ) := by
    calc
      _ ≤ log (q * (-σ + |t| + 2)) := by
        apply Real.log_le_log (by positivity : 0 < q * (‖(σ : ℂ) + t * I‖ + 2))
        gcongr
      _ = L + log (1 + (-σ) / (|t| + 2)) := by
        rw [heq, Real.log_mul (by positivity) (by positivity)]
      _ ≤ _ := by
        have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (-σ) / (|t| + 2) by positivity)
        linarith [div_le_self (show 0 ≤ -σ by linarith) hT]
  refine (hfar σ hσ hs).trans ((mul_le_mul_of_nonneg_left hl hB).trans ?_)
  have hneg : -σ ≤ 2 + (log x)⁻¹ - σ := by dsimp only [c] at hc; linarith
  have hprod := mul_le_mul_of_nonneg_left hr hL
  have hl' : L + -σ ≤ (1 + L) * (2 + (log x)⁻¹ - σ) := by linarith only [hneg, hprod]
  exact (mul_le_mul_of_nonneg_left hl' hB).trans (by rw [← mul_assoc]; gcongr; linarith)

end TauCeti

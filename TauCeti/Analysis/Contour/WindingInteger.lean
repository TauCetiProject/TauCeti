module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Contour.WindingNumber
import Mathlib.Data.Complex.BigOperators
import TauCeti.Analysis.Contour.WindingSegmentSum
import TauCeti.Analysis.Contour.ArgumentLift

/-!
# The winding number of a closed curve is an integer

For a closed curve `γ` on `[a, b]` (with `γ a = γ b`) that avoids `w`, the generalized winding
number `windingNumber γ a b w` is an integer. The index integral is evaluated over a continuous
argument-lift partition (`exists_continuousOn_arg_lift_with_partition`): it splits into a real
logarithm-of-modulus increment plus `I` times the imaginary part of the segment logarithm sum
(`contourIntegral_inv_re_im_decomp`). For a closed curve the modulus increment telescopes to zero,
so the integral is `I` times the total argument change `θ b - θ a`; closedness makes
`exp (I * (θ b - θ a)) = 1`, whence `θ b - θ a` is an integer multiple of `2π` and the winding
number is that integer.

## Main results

* `TauCeti.Contour.contourIntegral_inv_re_im_decomp` — real/imaginary decomposition of the index
  integral over a slit-compatible monotone partition.
* `TauCeti.Contour.exists_int_windingNumber_of_closed` — the generalized winding number of a closed
  curve is an integer.

## Provenance

Adapted from `hasGeneralizedWindingNumber_integer_of_closed` in `WindingInteger.lean` of the
AINTLIB `LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on `[a, b]`.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- **Real/imaginary decomposition of the index integral.** Over a slit-compatible monotone
partition, the index integral splits into a real logarithm-of-modulus increment plus `I` times the
imaginary part of the segment logarithm sum. For a closed curve the real part vanishes. -/
theorem contourIntegral_inv_re_im_decomp {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    {N : ℕ} {s : ℕ → ℝ} (hP : P.Countable)
    (hs_zero : s 0 = a) (hs_N : s N = b) (hs_mono : Monotone s)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, DifferentiableAt ℝ γ t)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ t - w) / (γ (s j) - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t
      = ((Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ : ℝ) : ℂ)
        + Complex.I * ((∑ j ∈ Finset.range N,
            (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im : ℝ) : ℂ) := by
  rw [integral_inv_sub_mul_deriv_eq_sum_log hP hs_zero hs_N hs_mono hγ_cont hγ_diff h_slit h_int]
  have hmono_seg : ∀ j, s j ≤ s (j + 1) := fun j ↦ hs_mono (Nat.le_succ j)
  have hne : ∀ j, j < N → γ (s j) - w ≠ 0 ∧ γ (s (j + 1)) - w ≠ 0 := fun j hj ↦
    ⟨(div_ne_zero_iff.mp (slitPlane_ne_zero
        (h_slit j hj (s j) (left_mem_Icc.mpr (hmono_seg j))))).1,
      (div_ne_zero_iff.mp (slitPlane_ne_zero
        (h_slit j hj (s (j + 1)) (right_mem_Icc.mpr (hmono_seg j))))).1⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.re_sum]
    calc ∑ j ∈ Finset.range N, (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).re
        = ∑ j ∈ Finset.range N, (Real.log ‖γ (s (j + 1)) - w‖ - Real.log ‖γ (s j) - w‖) := by
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          rw [Finset.mem_range] at hj
          rw [Complex.log_re, norm_div,
            Real.log_div (norm_ne_zero_iff.mpr (hne j hj).2) (norm_ne_zero_iff.mpr (hne j hj).1)]
      _ = Real.log ‖γ (s N) - w‖ - Real.log ‖γ (s 0) - w‖ :=
          Finset.sum_range_sub (fun j ↦ Real.log ‖γ (s j) - w‖) N
      _ = Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ := by rw [hs_N, hs_zero]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, zero_add, one_mul]
    exact Complex.im_sum _ _

/-- **The winding number of a closed curve is an integer.** For a closed curve `γ` (with
`γ a = γ b`) that is continuous on `[a, b]`, differentiable off a countable set `P`, avoids `w`
throughout, and has an interval-integrable index integrand, the generalized winding number
`windingNumber γ a b w` is an integer. Along a continuous argument lift the index integral equals
`I` times the total argument change; closedness forces the modulus increment to vanish and the
argument change to be an integer multiple of `2π`. -/
theorem exists_int_windingNumber_of_closed {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hab : a ≤ b) (hclosed : γ a = γ b) (hP : P.Countable)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∃ n : ℤ, windingNumber γ a b w = n := by
  obtain ⟨N, s, _, hs_zero, hs_N, hs_mono, _, hs_avoid, h_slit, _, h_lift⟩ :=
    exists_continuousOn_arg_lift_with_partition hab hγ_cont h_avoid
  have hla := h_lift a (left_mem_Icc.mpr hab)
  have hlb := h_lift b (right_mem_Icc.mpr hab)
  have hint :=
    contourIntegral_inv_re_im_decomp hP hs_zero hs_N hs_mono hγ_cont hγ_diff h_slit h_int
  have hnorm_ne : (‖γ a - w‖ : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero, sub_eq_zero]
    exact h_avoid a (left_mem_Icc.mpr hab)
  have hsa : (∑ j ∈ Finset.range N,
      (Complex.log (segRatio γ w (s j) (s (j + 1)) a)).im) = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have ha_le : a ≤ s j := by rw [← hs_zero]; exact hs_mono (Nat.zero_le j)
    rw [segRatio_eq_one_of_le ha_le (hs_avoid j hj.le), Complex.log_one, Complex.zero_im]
  have hsb_eq : (∑ j ∈ Finset.range N,
        (Complex.log (segRatio γ w (s j) (s (j + 1)) b)).im)
      = ∑ j ∈ Finset.range N,
        (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have hb_ge : s (j + 1) ≤ b := by rw [← hs_N]; exact hs_mono hj
    rw [segRatio_eq_endpoint_div_of_le (hs_mono (Nat.le_succ j)) hb_ge]
  set Se : ℝ := ∑ j ∈ Finset.range N,
    (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im with hSe_def
  set Sa : ℝ := ∑ j ∈ Finset.range N,
    (Complex.log (segRatio γ w (s j) (s (j + 1)) a)).im with hSa_def
  set Sb : ℝ := ∑ j ∈ Finset.range N,
    (Complex.log (segRatio γ w (s j) (s (j + 1)) b)).im with hSb_def
  set Ea : ℝ := Complex.arg (γ a - w) + Sa with hEa_def
  set Eb : ℝ := Complex.arg (γ a - w) + Sb with hEb_def
  have hEab : Complex.exp (Complex.I * (Ea : ℂ)) = Complex.exp (Complex.I * (Eb : ℂ)) := by
    refine mul_left_cancel₀ hnorm_ne ?_
    calc (‖γ a - w‖ : ℂ) * Complex.exp (Complex.I * (Ea : ℂ))
        = γ a - w := hla.symm
      _ = γ b - w := by rw [hclosed]
      _ = (‖γ b - w‖ : ℂ) * Complex.exp (Complex.I * (Eb : ℂ)) := hlb
      _ = (‖γ a - w‖ : ℂ) * Complex.exp (Complex.I * (Eb : ℂ)) := by rw [← hclosed]
  have hEdiff : Eb - Ea = Se := by rw [hEb_def, hEa_def, hsb_eq, hsa]; ring
  have hexp_one : Complex.exp (Complex.I * (Se : ℂ)) = 1 := by
    have h1 : Complex.I * (Se : ℂ) = Complex.I * (Eb : ℂ) - Complex.I * (Ea : ℂ) := by
      rw [← mul_sub, ← Complex.ofReal_sub, hEdiff]
    rw [h1, Complex.exp_sub, hEab, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp_one
  have hint' : (∫ t in a..b, (γ t - w)⁻¹ * deriv γ t) = Complex.I * (Se : ℂ) := by
    rw [hint, show Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ = 0 by rw [hclosed, sub_self],
      Complex.ofReal_zero, zero_add]
  refine ⟨n, ?_⟩
  have hcont_u : ContinuousOn γ (Set.uIcc a b) := by rw [Set.uIcc_of_le hab]; exact hγ_cont
  have havoid_u : ∀ t ∈ Set.uIcc a b, γ t ≠ w := by rw [Set.uIcc_of_le hab]; exact h_avoid
  have h2πI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [windingNumber_eq_integral_of_avoidance hcont_u havoid_u h_int, hint', hn,
    mul_comm (n : ℂ) (2 * (Real.pi : ℂ) * Complex.I), ← mul_assoc,
    inv_mul_cancel₀ h2πI_ne, one_mul]

end TauCeti.Contour

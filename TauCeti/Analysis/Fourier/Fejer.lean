/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Monomial
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Fourier.AddCircle

/-!
# The normalized Fejér kernel on the circle

The Fejér kernel of order `N` on `AddCircle T` is the squared norm of the sum of the first
`N` Fourier monomials, divided by `N`. It is nonnegative and has integral one for normalized
Haar measure when `N > 0`. Its Fourier coefficients are the triangular weights
`(N - |k|) / N`, truncated to zero outside `|k| < N`.

The normalization uses `AddCircle.haarAddCircle`, of total mass one, and the Fourier
monomials of Mathlib. This is the positive kernel underlying Cesàro means of Fourier sums.

The development is motivated by the real periodic Fejér kernel and convergence formalization
in the [PrimeNumberTheoremAnd formalization][PNTFejer], by Aristotle (Harmonic) and
Dr. Gotthelf. That source uses half the usual real kernel with weight
`1 / π`;
here the kernel is normalized against probability Haar measure for every positive period.

[PNTFejer]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/dc6e36e/PrimeNumberTheoremAnd/Unused/Fejer_I_know_this_is_dirty_but_it_typechecks.lean
-/

public section

open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

namespace TauCeti

variable {T : ℝ}

/-- The Fejér kernel of order `N` on the circle. Order zero is the zero kernel. -/
noncomputable def fejerKernel (N : ℕ) (x : AddCircle T) : ℝ :=
  (N : ℝ)⁻¹ * ‖∑ j ∈ Finset.range N, fourier (j : ℤ) x‖ ^ 2

/-- The Fejér kernel is the normalized squared norm of the first `N` Fourier monomials. -/
theorem fejerKernel_def (N : ℕ) (x : AddCircle T) :
    fejerKernel N x = (N : ℝ)⁻¹ * ‖∑ j ∈ Finset.range N, fourier (j : ℤ) x‖ ^ 2 := by
  rfl

/-- The Fejér kernel is nonnegative. -/
theorem fejerKernel_nonneg (N : ℕ) (x : AddCircle T) : 0 ≤ fejerKernel N x := by
  unfold fejerKernel
  positivity

/-- Each Fejér kernel is continuous on the circle. -/
theorem continuous_fejerKernel (N : ℕ) : Continuous (fejerKernel (T := T) N) := by
  unfold fejerKernel
  fun_prop

/-- Order zero is the zero kernel. -/
@[simp]
theorem fejerKernel_zero : fejerKernel (T := T) 0 = 0 := by
  ext x
  simp [fejerKernel]

/-- Order one is the constant kernel one. -/
@[simp]
theorem fejerKernel_one : fejerKernel (T := T) 1 = 1 := by
  ext x
  simp [fejerKernel]

/-- At the identity of the circle the Fejér kernel has value `N`. -/
@[simp]
theorem fejerKernel_apply_zero (N : ℕ) : fejerKernel N (0 : AddCircle T) = N := by
  by_cases hN : N = 0
  · simp [hN]
  · simp [fejerKernel, pow_two, hN]

/-- Multiplying the Fejér kernel by `‖fourier 1 x - 1‖²` gives
`N⁻¹ * ‖fourier N x - 1‖²`, by the geometric-sum identity. -/
theorem fejerKernel_mul_norm_sq (N : ℕ) (x : AddCircle T) :
    fejerKernel N x * ‖fourier 1 x - 1‖ ^ 2 =
      (N : ℝ)⁻¹ * ‖fourier (N : ℤ) x - 1‖ ^ 2 := by
  have hg := congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) (geom_sum_mul (fourier 1 x) N)
  simp only [norm_mul, mul_pow] at hg
  simp only [fejerKernel_def, ← fourier_one_pow_apply]
  rw [mul_assoc, hg]

/-- Away from zeros of `sin (π * t / T)`, `(M : ℝ) * fejerKernel M (t : AddCircle T)` equals
`(sin (π * M * t / T) / sin (π * t / T)) ^ 2`. -/
theorem natCast_mul_fejerKernel_coe (M : ℕ) {t : ℝ} (ht : Real.sin (Real.pi * t / T) ≠ 0) :
    (M : ℝ) * fejerKernel M (t : AddCircle T) =
      (Real.sin (Real.pi * (M : ℝ) * t / T) / Real.sin (Real.pi * t / T)) ^ 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hnorm (m : ℤ) :
      ‖fourier (T := T) m (t : AddCircle T) - 1‖ =
        2 * |Real.sin (Real.pi * (m : ℝ) * t / T)| := by
    have hexp : fourier (T := T) m (t : AddCircle T) =
        Complex.exp (Complex.I * ((2 * (Real.pi * (m : ℝ) * t / T) : ℝ) : ℂ)) := by
      rw [fourier_coe_apply]
      congr 1; push_cast; ring
    rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
      mul_div_cancel_left₀ _ two_ne_zero, abs_mul, abs_two]
  have hmul := fejerKernel_mul_norm_sq (T := T) M (t : AddCircle T)
  have h1 := hnorm 1
  have hMnorm := hnorm M
  simp only [Int.cast_one, mul_one, Int.cast_natCast] at h1 hMnorm
  rw [h1, hMnorm, mul_pow, mul_pow, sq_abs, sq_abs] at hmul
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hmul' : (M : ℝ) * fejerKernel M (t : AddCircle T) * (4 * Real.sin (Real.pi * t / T) ^ 2) =
      4 * Real.sin (Real.pi * (M : ℝ) * t / T) ^ 2 := by
    calc
      (M : ℝ) * fejerKernel M (t : AddCircle T) * (4 * Real.sin (Real.pi * t / T) ^ 2)
          = (M : ℝ) *
              (fejerKernel M (t : AddCircle T) * (2 ^ 2 * Real.sin (Real.pi * t / T) ^ 2)) := by
            ring
      _ = (M : ℝ) * ((M : ℝ)⁻¹ * (2 ^ 2 * Real.sin (Real.pi * (M : ℝ) * t / T) ^ 2)) := by
            rw [hmul]
      _ = 4 * Real.sin (Real.pi * (M : ℝ) * t / T) ^ 2 := by
            rw [← mul_assoc, mul_inv_cancel₀ hMne]; ring
  rw [div_pow, eq_div_iff (sq_pos_of_ne_zero ht).ne']
  linarith

/-- Away from the identity, the Fejér kernels satisfy a bound of order `1 / N`. -/
theorem fejerKernel_le (N : ℕ) (x : AddCircle T) (hx : fourier 1 x ≠ 1) :
    fejerKernel N x ≤ (4 / N : ℝ) / ‖fourier 1 x - 1‖ ^ 2 := by
  have hd : 0 < ‖fourier 1 x - 1‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr hx))
  have hb : ‖fourier (N : ℤ) x - 1‖ ≤ 2 := by
    simpa only [norm_fourier_apply, norm_one, one_add_one_eq_two] using
      norm_sub_le (fourier (N : ℤ) x) (1 : ℂ)
  rw [le_div_iff₀ hd, fejerKernel_mul_norm_sq]
  have hsq : ‖fourier (N : ℤ) x - 1‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (fourier (N : ℤ) x - 1)]
  calc
    _ ≤ (N : ℝ)⁻¹ * 4 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

/-- Expanding the square gives a finite Fourier polynomial for the Fejér kernel. -/
theorem ofReal_fejerKernel (N : ℕ) (x : AddCircle T) :
    (fejerKernel N x : ℂ) =
      (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        fourier ((i : ℤ) - j) x := by
  simp only [fejerKernel, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_pow]
  rw [← Complex.mul_conj']
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, ← fourier_neg, sub_eq_add_neg,
    ← fourier_add]
  rw [Finset.sum_comm]

/-- For `M ≤ K`, the triangular Fourier polynomial over `[-K, K]` equals `M` times the
Fejér kernel `fejerKernel M x`. -/
theorem sum_Icc_max_sub_abs_mul_fourier {M K : ℕ} (hMK : M ≤ K) (x : AddCircle T) :
    ∑ n ∈ Finset.Icc (-(K : ℤ)) K,
        ((max (0 : ℝ) ((M : ℝ) - |(n : ℝ)|) : ℝ) : ℂ) * fourier n x =
      (M : ℂ) * (fejerKernel M x : ℂ) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [fejerKernel_zero]
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hexp :
      (M : ℂ) * (fejerKernel M x : ℂ) =
        ∑ p ∈ Finset.range M ×ˢ Finset.range M, fourier ((p.1 : ℤ) - p.2) x := by
    rw [ofReal_fejerKernel, ← mul_assoc, mul_inv_cancel₀ hMne, one_mul, Finset.sum_product]
  have hmem : ∀ p ∈ Finset.range M ×ˢ Finset.range M,
      ((p.1 : ℤ) - p.2) ∈ Finset.Icc (-(K : ℤ)) K := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hi, hj⟩
    rw [Finset.mem_range] at hi hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [hexp, ← sum_card_filter_nsmul_eq_sum_comp (t := Finset.Icc (-(K : ℤ)) K) hmem
      (fun n ↦ fourier n x)]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have hcount :
      ((Finset.range M ×ˢ Finset.range M).filter fun p ↦ (p.1 : ℤ) - p.2 = n).card =
        M - n.natAbs := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_range_sum_range_ite_int_sub_eq_nsmul,
      smul_eq_mul, mul_one]
  rw [hcount, nsmul_eq_mul]
  congr 1
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hcast : ((M - n.natAbs : ℕ) : ℝ) = max (0 : ℝ) ((M : ℝ) - |(n : ℝ)|) := by
    rw [← habs]
    by_cases hn : n.natAbs ≤ M
    · rw [Nat.cast_sub hn, max_eq_right (sub_nonneg.mpr (Nat.cast_le.mpr hn))]
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hn), Nat.cast_zero,
        max_eq_left (sub_nonpos.mpr (Nat.cast_le.mpr (le_of_not_ge hn)))]
  exact_mod_cast hcast.symm

variable [Fact (0 < T)]

/-- The Fourier coefficients of the Fejér kernel are the triangular weights. Natural
subtraction makes the coefficient zero when the frequency has magnitude at least `N`. -/
theorem fourierCoeff_fejerKernel (N : ℕ) (k : ℤ) :
    fourierCoeff (fun x : AddCircle T ↦ (fejerKernel N x : ℂ)) k =
      ((N - k.natAbs : ℕ) : ℂ) / N := by
  have hpoly : (fun x : AddCircle T ↦ (fejerKernel N x : ℂ)) = fun x ↦
      (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        fourier ((i : ℤ) - j) x := funext (ofReal_fejerKernel N)
  rw [hpoly, fourierCoeff.const_mul]
  have hint (m : ℤ) : Integrable (fourier (T := T) m) haarAddCircle :=
    (fourier m).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcalc : fourierCoeff (fun x : AddCircle T ↦
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, fourier ((i : ℤ) - j) x) k =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        if (i : ℤ) - j = k then (1 : ℂ) else 0 := by
    have hs : (fun x : AddCircle T ↦
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, fourier ((i : ℤ) - j) x) =
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (fourier ((i : ℤ) - j) : AddCircle T → ℂ) := by
      ext x
      simp only [Finset.sum_apply]
    rw [hs, fourierCoeff.sum _ _ (fun i _ ↦
      integrable_finsetSum' _ (fun j _ ↦ hint _))]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [fourierCoeff.sum _ _ (fun j _ ↦ hint _)]
    simp only [Finset.sum_apply, fourierCoeff_fourier, Pi.single_apply, eq_comm]
  rw [hcalc, Finset.sum_range_sum_range_ite_int_sub_eq_nsmul, nsmul_eq_mul, mul_one]
  ring

/-- A positive-order Fejér kernel has mass one for normalized Haar measure. -/
theorem integral_fejerKernel (N : ℕ) (hN : 0 < N) :
    ∫ x : AddCircle T, fejerKernel N x ∂haarAddCircle = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_one, ← integral_complex_ofReal]
  have h := fourierCoeff_fejerKernel (T := T) N 0
  rw [fourierCoeff_zero_eq_integral] at h
  simpa [Nat.ne_of_gt hN] using h

end TauCeti

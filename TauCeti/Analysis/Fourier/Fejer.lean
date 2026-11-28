/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Monomial
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Fourier.AddCircle

/-!
# The normalized Fejér kernel on the circle

The Fejér kernel of order `N` on `AddCircle T` is the squared norm of the sum of the first
`N` Fourier monomials, divided by `N`. It is nonnegative and has integral one for normalized
Haar measure when `N > 0`. Its Fourier coefficients are the triangular weights
`(N - |k|) / N`, truncated to zero outside `|k| < N`.

For finite samples, `half_natCast_le_fejerKernel_of_mul_norm_le` bounds the kernel below near
zero on the unit circle, and `Finset.sum_fejerKernel_le_card_add` bounds its sum by the zero mode
and the norms of the positive modes of Mathlib's Fourier monomials.

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

/-- For positive order `N`, the Fejér kernel is at least half its peak within distance
`1 / (4 * N)` of zero on the unit circle. At order zero both sides vanish. -/
theorem half_natCast_le_fejerKernel_of_mul_norm_le {N : ℕ} {x : UnitAddCircle}
    (hx : (N : ℝ) * ‖x‖ ≤ 1 / 4) : (N : ℝ) / 2 ≤ fejerKernel N x := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : 0 < (N : ℝ) := Nat.cast_pos'.mpr hN
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  let t : ℝ := y - round y
  have ht : (t : UnitAddCircle) = (y : UnitAddCircle) := by
    have hround : ((round y : ℝ) : UnitAddCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨round y, by simp⟩
    rw [AddCircle.coe_sub, hround, sub_zero]
  have htN : (N : ℝ) * |t| ≤ 1 / 4 := by simpa only [UnitAddCircle.norm_eq] using hx
  by_cases ht0 : t = 0
  · rw [← ht, ht0, AddCircle.coe_zero, fejerKernel_apply_zero]
    linarith
  let u := |Real.pi * t|
  let v := |Real.pi * (N : ℝ) * t|
  have hu : 0 < u := abs_pos.mpr (mul_ne_zero Real.pi_pos.ne' ht0)
  have hv_formula : v = (N : ℝ) * u := by grind
  have hvπ : v ≤ Real.pi / 4 := by
    rw [hv_formula]
    dsimp only [u]
    rw [abs_mul, abs_of_pos Real.pi_pos, mul_left_comm]
    linarith [mul_le_mul_of_nonneg_left htN Real.pi_pos.le]
  have huπ : u ≤ Real.pi / 4 :=
    (le_mul_of_one_le_left hu.le (by exact_mod_cast hN : (1 : ℝ) ≤ N)).trans
      (hv_formula ▸ hvπ)
  have hv1 : v ≤ 1 := hvπ.trans (by linarith [Real.pi_lt_four])
  have hden : |Real.sin (Real.pi * t)| = Real.sin u :=
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (huπ.trans (by linarith [Real.pi_pos]))
  have hnum : |Real.sin (Real.pi * N * t)| = Real.sin v :=
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (hvπ.trans (by linarith [Real.pi_pos]))
  have hsin : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos])
  have hv3 : v ^ 3 ≤ v :=
    (pow_le_pow_of_le_one (abs_nonneg _) hv1 (by decide : 1 ≤ 3)).trans_eq (pow_one v)
  have hratio : 5 / 6 * (N : ℝ) ≤ |Real.sin (Real.pi * N * t) / Real.sin (Real.pi * t)| := by
    rw [abs_div, hnum, hden, le_div_iff₀ hsin]
    calc
      _ ≤ 5 / 6 * v := by
        rw [hv_formula, mul_assoc]
        gcongr
        exact Real.sin_le hu.le
      _ ≤ _ := by linarith [Real.sin_ge_sub_cube (abs_nonneg (Real.pi * (N : ℝ) * t))]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 5 / 6 * (N : ℝ)) hratio 2
  rw [sq_abs] at hsq
  have hkernel := natCast_mul_fejerKernel_coe (T := 1) N (t := t)
    (by simpa only [div_one, ← abs_pos, hden] using hsin)
  simp only [div_one] at hkernel
  rw [← ht, ← mul_le_mul_iff_of_pos_left hN', hkernel]
  nlinarith [sq_nonneg (N : ℝ)]

/-- The sum of the Fejér kernel over a finite sample is bounded by its zero-frequency mass
plus twice the sum of the norms of its positive-frequency exponential sums. -/
theorem _root_.Finset.sum_fejerKernel_le_card_add {ι : Type*} (s : Finset ι)
    (x : ι → AddCircle T) (N : ℕ) :
    ∑ i ∈ s, fejerKernel N (x i) ≤
      (s.card : ℝ) + 2 * ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖∑ i ∈ s, fourier k (x i)‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  let F : ℤ → ℂ := fun k ↦ ∑ i ∈ s, fourier k (x i)
  let w : ℤ → ℝ := fun k ↦ max 0 ((N : ℝ) - |(k : ℝ)|)
  let J := Finset.Icc (-(N : ℤ)) N
  have hN' : 0 < (N : ℝ) := Nat.cast_pos'.mpr hN
  have hexp : (∑ k ∈ J, (w k : ℂ) * F k) = ((N : ℝ) * ∑ i ∈ s, fejerKernel N (x i) : ℝ) := by
    push_cast
    simp only [F, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ sum_Icc_max_sub_abs_mul_fourier le_rfl (x i)
  have htriangle : (N : ℝ) * ∑ i ∈ s, fejerKernel N (x i) ≤ (N : ℝ) * ∑ k ∈ J, ‖F k‖ := by
    calc
      _ = ‖∑ k ∈ J, (w k : ℂ) * F k‖ := by
        rw [hexp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg hN'.le (Finset.sum_nonneg fun i _ ↦ fejerKernel_nonneg N (x i))
      _ ≤ ∑ k ∈ J, ‖(w k : ℂ) * F k‖ := norm_sum_le _ _
      _ ≤ _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have hw0 : 0 ≤ w k := le_max_left _ _
        have hwN : w k ≤ N := max_le hN'.le (sub_le_self _ (abs_nonneg _))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
        gcongr
  have heven : Function.Even (fun k ↦ ‖F k‖) := by
    intro k
    simp only [F, fourier_neg, ← map_sum, Complex.norm_conj]
  have hzero : ‖F 0‖ = (s.card : ℝ) := by
    simp only [F, fourier_zero, Finset.sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  have hsplit : ∑ k ∈ J, ‖F k‖ = (s.card : ℝ) + 2 * ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖F k‖ := by
    have hpos : ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖F k‖ =
        ∑ k ∈ Finset.range N, ‖F (1 + (k : ℤ))‖ := by
      rw [← Finset.Ico_add_one_right_eq_Icc, add_comm (N : ℤ),
        Finset.sum_Ico_int_add_eq_sum_range]
    rw [hpos, Finset.sum_Icc_of_even_eq_range heven, Finset.sum_range_succ', two_nsmul]
    simp only [Nat.cast_zero, Nat.cast_succ, add_comm (1 : ℤ), hzero]
    ring
  rw [← hsplit]
  exact (mul_le_mul_iff_of_pos_left hN').mp htriangle

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

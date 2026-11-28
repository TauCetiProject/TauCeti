/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.AddCircle
public import TauCeti.Analysis.Fourier.Fejer
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.InnerProductSpace.Gram.RowSum
import TauCeti.Analysis.Normed.Group.AddCircle.Basic
import TauCeti.Analysis.Normed.Group.AddCircle.Cosecant
import TauCeti.Analysis.Normed.Group.AddCircle.Trigonometric
import TauCeti.Analysis.SpecialFunctions.Complex.Circle.FourierChar

/-!
# Bombieri's additive large sieve inequality

This file proves Bombieri's additive large sieve inequality for trigonometric polynomials evaluated
at points well-spaced in the circle `UnitAddCircle = ℝ / ℤ`, following Bombieri's 1971 Hilbert-space
proof via Selberg's weighted Gram inequality
(`TauCeti.sum_norm_inner_sq_le_of_norm_sq_le_of_sum_erase_le`) and tapered Fourier vectors.

## Main definitions

* `TauCeti.taperWeight`: the trapezoidal weight `w(n) = (max 0 (N + L - |n|) - max 0 (N - |n|)) / L`
  on `ℤ`, equal to `1` on the flat core `|n| ≤ N` for `0 < L` (identically `0` when `L = 0`),
  decaying linearly over `N ≤ |n| ≤ N + L`, and vanishing outside `|n| < N + L`.
* `TauCeti.taperedFourierVec`: the vector in `EuclideanSpace ℂ (Fin (2 * (N + L) + 1))` with
  frequency `n = k - (N + L)` carrying entry `√(taperWeight N L n) * Real.fourierChar (-n * x)`.
* `TauCeti.intervalVector`: zero-padding of an integer-interval sequence on `[M, M + H)` into
  `EuclideanSpace ℂ (Fin (2 * (N + L) + 1))`.

## Main results

* `TauCeti.inner_taperedFourierVec_eq_sum_taperWeight`, `TauCeti.inner_taperedFourierVec`,
  `TauCeti.norm_taperedFourierVec_sq`, and `TauCeti.norm_inner_taperedFourierVec_le`: Gram entries
  of `taperedFourierVec`.
* `TauCeti.intervalVector_apply`, `TauCeti.intervalVector_eq_zero_of_lt_abs`,
  `TauCeti.norm_intervalVector_sq`, `TauCeti.fourierChar_mul_sum_intervalVector`, and
  `TauCeti.norm_sum_intervalVector_fourierChar`: coordinate, core-support, norm-preservation, and
  phase-translation laws for `intervalVector`.
* `TauCeti.natFloor_inv_add_pi_sq_div_le`: explicit taper-width estimate
  `⌊1 / δ⌋₊ + (π ^ 2 / (12 * δ ^ 2)) / ⌊1 / δ⌋₊ ≤ 2 / δ` for `0 < δ ≤ 1 / 2`.
* `Finset.sum_norm_sum_fourierChar_sq_le_of_sum_inv_sin_sq_le` and
  `Finset.sum_norm_sum_fourierChar_sq_le_of_core_support`: the cosecant-row and centered-core
  large sieves for core-supported vectors.
* `Finset.sum_norm_sum_Ico_fourierChar_sq_le` and `Finset.sum_norm_sum_fourierChar_sq_le`:
  **Bombieri's additive large sieve inequality** with constant `H + 2 / δ` for arbitrary `H : ℕ`,
  `M : ℤ`, `0 < δ`, and `δ`-separated points in `UnitAddCircle`.

## References

* E. Bombieri, *A note on the large sieve*, Acta Arithmetica **18** (1971), 401–404,
  Proposition 1 and Theorem 2.
-/

public section

open scoped InnerProductSpace ComplexConjugate

namespace TauCeti

/-! ### Bombieri's tapered Fourier vectors -/

/-- Bombieri's trapezoidal Fourier taper weight on `ℤ`: equal to `1` on `|n| ≤ N`, decaying
linearly across `N ≤ |n| ≤ N + L`, and vanishing for `|n| ≥ N + L` (and identically `0` when
`L = 0`). -/
noncomputable def taperWeight (N L : ℕ) (n : ℤ) : ℝ :=
  (max (0 : ℝ) (((N + L : ℕ) : ℝ) - |(n : ℝ)|) - max (0 : ℝ) ((N : ℝ) - |(n : ℝ)|)) / (L : ℝ)

/-- Definitional formula for `taperWeight`. -/
theorem taperWeight_def (N L : ℕ) (n : ℤ) :
    taperWeight N L n =
      (max (0 : ℝ) (((N + L : ℕ) : ℝ) - |(n : ℝ)|) - max (0 : ℝ) ((N : ℝ) - |(n : ℝ)|)) /
        (L : ℝ) :=
  (rfl)

/-- For taper width `L = 0`, `taperWeight` vanishes identically. -/
@[simp]
theorem taperWeight_zero (N : ℕ) (n : ℤ) : taperWeight N 0 n = 0 := by
  simp [taperWeight_def]

/-- `taperWeight` is an even function of the frequency `n : ℤ`. -/
@[simp]
theorem taperWeight_neg (N L : ℕ) (n : ℤ) : taperWeight N L (-n) = taperWeight N L n := by
  simp [taperWeight_def]

/-- `taperWeight` is nonnegative. -/
theorem taperWeight_nonneg (N L : ℕ) (n : ℤ) : 0 ≤ taperWeight N L n := by
  rw [taperWeight_def]
  refine div_nonneg (sub_nonneg.mpr ?_) (Nat.cast_nonneg L)
  exact max_le_max_left 0 (sub_le_sub_right (Nat.cast_le.mpr (Nat.le_add_right N L)) _)

/-- `taperWeight` is at most `1`. -/
theorem taperWeight_le_one (N L : ℕ) (n : ℤ) : taperWeight N L n ≤ 1 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [taperWeight_def, div_le_one (Nat.cast_pos.mpr hL), sub_le_iff_le_add]
  refine max_le ?_ ?_
  · linarith [le_max_left (0 : ℝ) ((N : ℝ) - |(n : ℝ)|), Nat.cast_nonneg (α := ℝ) L]
  · push_cast
    linarith [le_max_right (0 : ℝ) ((N : ℝ) - |(n : ℝ)|)]

/-- On the flat core `|n| ≤ N` with positive taper width `0 < L`, `taperWeight N L n = 1`. -/
@[simp]
theorem taperWeight_eq_one {N L : ℕ} {n : ℤ} (hL : 0 < L) (hn : |n| ≤ (N : ℤ)) :
    taperWeight N L n = 1 := by
  have hn' : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hn
  have h1 : max (0 : ℝ) (((N + L : ℕ) : ℝ) - |(n : ℝ)|) = (N : ℝ) + (L : ℝ) - |(n : ℝ)| := by
    push_cast
    exact max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) L])
  have h2 : max (0 : ℝ) ((N : ℝ) - |(n : ℝ)|) = (N : ℝ) - |(n : ℝ)| :=
    max_eq_right (by linarith)
  rw [taperWeight_def, h1, h2]
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  field_simp [hLne]
  ring

/-- In the transition region `N ≤ |n| ≤ N + L`, `taperWeight N L n = (N + L - |n|) / L`. -/
theorem taperWeight_eq_div {N L : ℕ} {n : ℤ} (h1 : (N : ℤ) ≤ |n|)
    (h2 : |n| ≤ ((N + L : ℕ) : ℤ)) :
    taperWeight N L n = (((N + L : ℕ) : ℝ) - |(n : ℝ)|) / (L : ℝ) := by
  have h1' : (N : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h1
  have h2' : |(n : ℝ)| ≤ ((N + L : ℕ) : ℝ) := by exact_mod_cast h2
  rw [taperWeight_def, max_eq_right (sub_nonneg.mpr h2'), max_eq_left (sub_nonpos.mpr h1'),
    sub_zero]

/-- Outside the open interval `|n| < N + L`, `taperWeight N L n = 0`. -/
@[simp]
theorem taperWeight_eq_zero {N L : ℕ} {n : ℤ} (hn : (N : ℤ) + (L : ℤ) ≤ |n|) :
    taperWeight N L n = 0 := by
  have hn' : ((N + L : ℕ) : ℝ) ≤ |(n : ℝ)| := by push_cast; exact_mod_cast hn
  have hN' : (N : ℝ) ≤ |(n : ℝ)| :=
    le_trans (Nat.cast_le.mpr (Nat.le_add_right N L)) hn'
  rw [taperWeight_def, max_eq_left (sub_nonpos.mpr hn'), max_eq_left (sub_nonpos.mpr hN'),
    sub_self, zero_div]

/-- Bombieri's tapered Fourier vector in `EuclideanSpace ℂ (Fin (2 * (N + L) + 1))`, with coordinate
`k` indexing the centered integer frequency `n = k - (N + L)` and carrying weight
`√(taperWeight N L n)` times the conjugated character `Real.fourierChar (-n * x)`. -/
noncomputable def taperedFourierVec (N L : ℕ) (x : ℝ) :
    EuclideanSpace ℂ (Fin (2 * (N + L) + 1)) :=
  WithLp.toLp 2 fun k : Fin (2 * (N + L) + 1) ↦
    (Real.sqrt (taperWeight N L ((k : ℤ) - ((N + L : ℕ) : ℤ))) : ℂ) *
      (Real.fourierChar (-((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x)) : ℂ)

/-- Coordinate formula for `taperedFourierVec`. -/
@[simp]
theorem taperedFourierVec_apply (N L : ℕ) (x : ℝ) (k : Fin (2 * (N + L) + 1)) :
    taperedFourierVec N L x k =
      (Real.sqrt (taperWeight N L ((k : ℤ) - ((N + L : ℕ) : ℤ))) : ℂ) *
        (Real.fourierChar (-((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x)) : ℂ) := by
  rw [taperedFourierVec, PiLp.toLp_apply]

/-- For taper width `L = 0`, `taperedFourierVec` is the zero vector. -/
@[simp]
theorem taperedFourierVec_zero (N : ℕ) (x : ℝ) : taperedFourierVec N 0 x = 0 := by
  ext k
  simp [taperedFourierVec_apply]

/-- On the flat core `|k - (N + L)| ≤ N` with `0 < L`, `taperedFourierVec N L x k` has unit
weight. -/
theorem taperedFourierVec_apply_of_abs_le {N L : ℕ} (hL : 0 < L) (x : ℝ)
    {k : Fin (2 * (N + L) + 1)} (hk : |(k : ℤ) - ((N + L : ℕ) : ℤ)| ≤ (N : ℤ)) :
    taperedFourierVec N L x k =
      (Real.fourierChar (-((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x)) : ℂ) := by
  rw [taperedFourierVec_apply, taperWeight_eq_one hL hk, Real.sqrt_one, Complex.ofReal_one, one_mul]

/-- Coordinatewise weighted character-sum formula for
`⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ`. -/
theorem inner_taperedFourierVec_eq_sum_taperWeight (N L : ℕ) (x y : ℝ) :
    ⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ =
      ∑ k : Fin (2 * (N + L) + 1),
        (taperWeight N L ((k : ℤ) - ((N + L : ℕ) : ℤ)) : ℂ) *
          (Real.fourierChar (((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * (x - y))) : ℂ) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [RCLike.inner_apply, taperedFourierVec_apply, map_mul, Complex.conj_ofReal,
    Circle.starRingEnd_addChar, neg_neg]
  set n : ℤ := (k : ℤ) - ((N + L : ℕ) : ℤ)
  calc
    (Real.sqrt (taperWeight N L n) : ℂ) * (Real.fourierChar (-((n : ℝ) * y)) : ℂ) *
        ((Real.sqrt (taperWeight N L n) : ℂ) * (Real.fourierChar ((n : ℝ) * x) : ℂ))
        = ((Real.sqrt (taperWeight N L n) * Real.sqrt (taperWeight N L n) : ℝ) : ℂ) *
            ((Real.fourierChar (-((n : ℝ) * y)) : ℂ) * (Real.fourierChar ((n : ℝ) * x) : ℂ)) := by
          rw [Complex.ofReal_mul]; ring
    _ = (taperWeight N L n : ℂ) * (Real.fourierChar ((n : ℝ) * (x - y)) : ℂ) := by
          rw [Real.mul_self_sqrt (taperWeight_nonneg N L n), ← Circle.coe_mul,
            ← AddChar.map_add_eq_mul]
          congr 3
          ring

/-- Exact Gram inner product of two tapered Fourier vectors as a difference of two normalized
Fejér kernels on `UnitAddCircle`. -/
theorem inner_taperedFourierVec (N L : ℕ) (x y : ℝ) :
    ⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ =
      (((((N + L : ℕ) : ℝ) * fejerKernel (N + L) ((x - y : ℝ) : UnitAddCircle) -
          (N : ℝ) * fejerKernel N ((x - y : ℝ) : UnitAddCircle)) /
          (L : ℝ) : ℝ) : ℂ) := by
  have hchar : ∀ n : ℤ, (Real.fourierChar ((n : ℝ) * (x - y)) : ℂ) =
      fourier (T := (1 : ℝ)) n ((x - y : ℝ) : UnitAddCircle) := by
    intro n
    rw [Real.fourierChar_apply, fourier_coe_apply]
    congr 1; push_cast; ring
  rw [inner_taperedFourierVec_eq_sum_taperWeight,
    ← Finset.sum_Icc_neg_eq_sum_fin (N + L) fun n ↦
      (taperWeight N L n : ℂ) * (Real.fourierChar ((n : ℝ) * (x - y)) : ℂ)]
  simp_rw [hchar]
  calc
    ∑ n ∈ Finset.Icc (-((N + L : ℕ) : ℤ)) (N + L : ℕ),
        (taperWeight N L n : ℂ) * fourier (T := (1 : ℝ)) n ((x - y : ℝ) : UnitAddCircle)
        = (∑ n ∈ Finset.Icc (-((N + L : ℕ) : ℤ)) (N + L : ℕ),
            (((max (0 : ℝ) (((N + L : ℕ) : ℝ) - |(n : ℝ)|) : ℝ) : ℂ) *
              fourier (T := (1 : ℝ)) n ((x - y : ℝ) : UnitAddCircle) -
            ((max (0 : ℝ) ((N : ℝ) - |(n : ℝ)|) : ℝ) : ℂ) *
              fourier (T := (1 : ℝ)) n ((x - y : ℝ) : UnitAddCircle))) / (L : ℂ) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          simp only [taperWeight_def, Complex.ofReal_div, Complex.ofReal_sub,
            Complex.ofReal_natCast]
          ring
    _ = (((((N + L : ℕ) : ℝ) * fejerKernel (N + L) ((x - y : ℝ) : UnitAddCircle) -
            (N : ℝ) * fejerKernel N ((x - y : ℝ) : UnitAddCircle)) /
            (L : ℝ) : ℝ) : ℂ) := by
          rw [Finset.sum_sub_distrib,
            sum_Icc_max_sub_abs_mul_fourier (T := (1 : ℝ)) le_rfl ((x - y : ℝ) : UnitAddCircle),
            sum_Icc_max_sub_abs_mul_fourier (T := (1 : ℝ)) (Nat.le_add_right N L)
              ((x - y : ℝ) : UnitAddCircle)]
          simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
            Complex.ofReal_natCast]

/-- For positive taper width `0 < L`, `‖taperedFourierVec N L x‖ ^ 2 = 2 * N + L`. -/
theorem norm_taperedFourierVec_sq {N L : ℕ} (hL : 0 < L) (x : ℝ) :
    ‖taperedFourierVec N L x‖ ^ 2 = 2 * (N : ℝ) + (L : ℝ) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_taperedFourierVec]
  simp only [RCLike.re_to_complex, Complex.ofReal_re, sub_self, AddCircle.coe_zero,
    fejerKernel_apply_zero]
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  push_cast
  field_simp [hLne]
  ring

/-- Off-diagonal Gram bound for tapered Fourier vectors: whenever `sin (π * (x - y)) ≠ 0`,
`‖⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ‖ ≤ (L * sin (π * (x - y)) ^ 2)⁻¹`. -/
theorem norm_inner_taperedFourierVec_le (N L : ℕ) {x y : ℝ}
    (hxy : Real.sin (Real.pi * (x - y)) ≠ 0) :
    ‖⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ‖ ≤
      ((L : ℝ) * Real.sin (Real.pi * (x - y)) ^ 2)⁻¹ := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  have hsin_pos : 0 < Real.sin (Real.pi * (x - y)) ^ 2 := sq_pos_of_ne_zero hxy
  have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  have hnorm : ∀ m : ℤ,
      ‖fourier (T := (1 : ℝ)) m ((x - y : ℝ) : UnitAddCircle) - 1‖ =
        2 * |Real.sin (Real.pi * (m : ℝ) * (x - y))| := by
    intro m
    have hexp : fourier (T := (1 : ℝ)) m ((x - y : ℝ) : UnitAddCircle) =
        Complex.exp (Complex.I * ((2 * (Real.pi * (m : ℝ) * (x - y)) : ℝ) : ℂ)) := by
      rw [fourier_coe_apply]
      congr 1; push_cast; ring
    rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
      mul_div_cancel_left₀ _ two_ne_zero, abs_mul, abs_two]
  have hfejer : ∀ M : ℕ,
      (M : ℝ) * fejerKernel M ((x - y : ℝ) : UnitAddCircle) =
        (Real.sin (Real.pi * (M : ℝ) * (x - y)) / Real.sin (Real.pi * (x - y))) ^ 2 := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    have hmul := fejerKernel_mul_norm_sq (T := (1 : ℝ)) M ((x - y : ℝ) : UnitAddCircle)
    have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
    have h1 := hnorm 1
    have hMnorm := hnorm M
    simp only [Int.cast_one, mul_one, Int.cast_natCast] at h1 hMnorm
    rw [h1, hMnorm, mul_pow, mul_pow, sq_abs, sq_abs] at hmul
    have hmul' : (M : ℝ) * fejerKernel M ((x - y : ℝ) : UnitAddCircle) *
        (4 * Real.sin (Real.pi * (x - y)) ^ 2) =
        4 * Real.sin (Real.pi * (M : ℝ) * (x - y)) ^ 2 := by
      calc
        (M : ℝ) * fejerKernel M ((x - y : ℝ) : UnitAddCircle) *
            (4 * Real.sin (Real.pi * (x - y)) ^ 2)
            = (M : ℝ) * (fejerKernel M ((x - y : ℝ) : UnitAddCircle) *
                (2 ^ 2 * Real.sin (Real.pi * (x - y)) ^ 2)) := by ring
        _ = (M : ℝ) * ((M : ℝ)⁻¹ * (2 ^ 2 * Real.sin (Real.pi * (M : ℝ) * (x - y)) ^ 2)) := by
              rw [hmul]
        _ = 4 * Real.sin (Real.pi * (M : ℝ) * (x - y)) ^ 2 := by
              rw [← mul_assoc, mul_inv_cancel₀ hMne]; ring
    rw [div_pow, eq_div_iff hsin_pos.ne']
    linarith
  rw [inner_taperedFourierVec, Complex.norm_real, Real.norm_eq_abs, hfejer (N + L), hfejer N]
  have hrew :
      ((Real.sin (Real.pi * ((N + L : ℕ) : ℝ) * (x - y)) / Real.sin (Real.pi * (x - y))) ^ 2 -
        (Real.sin (Real.pi * (N : ℝ) * (x - y)) / Real.sin (Real.pi * (x - y))) ^ 2) / (L : ℝ) =
        (Real.sin (Real.pi * ((N + L : ℕ) : ℝ) * (x - y)) ^ 2 -
          Real.sin (Real.pi * (N : ℝ) * (x - y)) ^ 2) /
          ((L : ℝ) * Real.sin (Real.pi * (x - y)) ^ 2) := by
    field_simp [hxy, hL_pos.ne']
  rw [hrew, abs_div, abs_of_pos (mul_pos hL_pos hsin_pos), ← one_div]
  refine div_le_div_of_nonneg_right ?_ (mul_pos hL_pos hsin_pos).le
  have h1 := Real.sin_sq_le_one (Real.pi * ((N + L : ℕ) : ℝ) * (x - y))
  have h2 := Real.sin_sq_le_one (Real.pi * (N : ℝ) * (x - y))
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (Real.sin (Real.pi * ((N + L : ℕ) : ℝ) * (x - y)))],
    by nlinarith [sq_nonneg (Real.sin (Real.pi * (N : ℝ) * (x - y)))]⟩

/-- Pairing `taperedFourierVec N L x` with a vector supported on the flat core `|k - (N + L)| ≤ N`
recovers its exact untapered Fourier sum. -/
theorem inner_taperedFourierVec_eq_sum {N L : ℕ} (hL : 0 < L) (x : ℝ)
    (f : EuclideanSpace ℂ (Fin (2 * (N + L) + 1)))
    (hf : ∀ k : Fin (2 * (N + L) + 1), (N : ℤ) < |(k : ℤ) - ((N + L : ℕ) : ℤ)| → f k = 0) :
    ⟪taperedFourierVec N L x, f⟫_ℂ =
      ∑ k : Fin (2 * (N + L) + 1),
        f k * (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x) : ℂ) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : |(k : ℤ) - ((N + L : ℕ) : ℤ)| ≤ (N : ℤ)
  · simp only [RCLike.inner_apply, taperedFourierVec_apply_of_abs_le hL x hk,
      Circle.starRingEnd_addChar, neg_neg, mul_comm]
  · rw [hf k (lt_of_not_ge hk), inner_zero_right, zero_mul]

/-! ### Interval-to-core zero-padding construction -/

/-- Zero-padding an integer-interval sequence `a` on `[M, M + H)` into coordinates `L ≤ k < L + H`
of `EuclideanSpace ℂ (Fin (2 * (N + L) + 1))` (which lies in the flat core `|k - (N + L)| ≤ N` when
`H ≤ 2 * N + 1`, and truncates entries when `L + H > 2 * (N + L) + 1`). -/
noncomputable def intervalVector (M : ℤ) (H N L : ℕ) (a : ℤ → ℂ) :
    EuclideanSpace ℂ (Fin (2 * (N + L) + 1)) :=
  WithLp.toLp 2 fun k ↦
    if L ≤ k.val ∧ k.val - L < H then a (M + ((k.val - L : ℕ) : ℤ)) else 0

/-- Coordinate formula for `intervalVector`. -/
@[simp]
theorem intervalVector_apply (M : ℤ) (H N L : ℕ) (a : ℤ → ℂ)
    (k : Fin (2 * (N + L) + 1)) :
    intervalVector M H N L a k =
      if L ≤ k.val ∧ k.val - L < H then a (M + ((k.val - L : ℕ) : ℤ)) else 0 :=
  PiLp.toLp_apply 2 _ _ k

/-- When `H ≤ 2 * N + 1`, `intervalVector M H N L a` vanishes outside the flat core
`|k - (N + L)| ≤ N` for every taper width `L`. -/
theorem intervalVector_eq_zero_of_lt_abs {M : ℤ} {H N : ℕ} (hHN : H ≤ 2 * N + 1) (L : ℕ)
    (a : ℤ → ℂ) {k : Fin (2 * (N + L) + 1)}
    (hk : (N : ℤ) < |(k : ℤ) - ((N + L : ℕ) : ℤ)|) :
    intervalVector M H N L a k = 0 := by
  have hnot : ¬ (L ≤ k.val ∧ k.val - L < H) := by
    rcases abs_cases ((k : ℤ) - ((N + L : ℕ) : ℤ)) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  rw [intervalVector_apply, ite_eq_right hnot]

/-- When `L + H ≤ 2 * (N + L) + 1`, the squared norm of `intervalVector M H N L a` equals the
squared `ℓ²` norm of `a` on `Finset.Ico M (M + H)`. -/
theorem norm_intervalVector_sq {M : ℤ} {H N L : ℕ} (hLH : L + H ≤ 2 * (N + L) + 1)
    (a : ℤ → ℂ) :
    ‖intervalVector M H N L a‖ ^ 2 = ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_Ico_int_add_eq_sum_range M H (fun n ↦ ‖a n‖ ^ 2),
    ← Finset.sum_fin_ite_sub_eq_sum_range (D := 2 * (N + L) + 1) (L := L) hLH
      (fun j ↦ ‖a (M + (j : ℤ))‖ ^ 2)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [intervalVector_apply]
  by_cases hk : L ≤ k.val ∧ k.val - L < H <;> simp [hk]

/-- When `L + H ≤ 2 * (N + L) + 1`, shifting the centered Fourier sum of `intervalVector M H N L a`
by the unimodular phase `Real.fourierChar ((M + N) * t)` recovers the Fourier sum of `a` on
`Finset.Ico M (M + H)`. -/
theorem fourierChar_mul_sum_intervalVector {M : ℤ} {H N L : ℕ}
    (hLH : L + H ≤ 2 * (N + L) + 1) (a : ℤ → ℂ) (t : ℝ) :
    (Real.fourierChar (((M + (N : ℤ) : ℤ) : ℝ) * t) : ℂ) *
        ∑ k : Fin (2 * (N + L) + 1),
          intervalVector M H N L a k *
            (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * t) : ℂ) =
      ∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * t) : ℂ) := by
  rw [Finset.mul_sum, Finset.sum_Ico_int_add_eq_sum_range M H
    (fun n ↦ a n * (Real.fourierChar ((n : ℝ) * t) : ℂ)),
    ← Finset.sum_fin_ite_sub_eq_sum_range (D := 2 * (N + L) + 1) (L := L) hLH (fun j ↦
      a (M + (j : ℤ)) * (Real.fourierChar (((M + (j : ℤ) : ℤ) : ℝ) * t) : ℂ))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [intervalVector_apply]
  by_cases hk : L ≤ k.val ∧ k.val - L < H
  · simp only [hk]
    calc
      (Real.fourierChar (((M + (N : ℤ) : ℤ) : ℝ) * t) : ℂ) *
          (a (M + ((k.val - L : ℕ) : ℤ)) *
            (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * t) : ℂ))
          = a (M + ((k.val - L : ℕ) : ℤ)) *
              ((Real.fourierChar (((M + (N : ℤ) : ℤ) : ℝ) * t) : ℂ) *
                (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * t) : ℂ)) := by
            ring
      _ = a (M + ((k.val - L : ℕ) : ℤ)) *
            (Real.fourierChar (((M + ((k.val - L : ℕ) : ℤ) : ℤ) : ℝ) * t) : ℂ) := by
          rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
          congr 3
          have heq : M + ((k.val - L : ℕ) : ℤ) =
              (M + (N : ℤ)) + ((k : ℤ) - ((N + L : ℕ) : ℤ)) := by omega
          rw [heq]; push_cast; ring
  · simp [hk]

/-- When `L + H ≤ 2 * (N + L) + 1`, the centered Fourier sum of `intervalVector M H N L a` has the
same norm as the Fourier sum of `a` on `Finset.Ico M (M + H)`. -/
theorem norm_sum_intervalVector_fourierChar {M : ℤ} {H N L : ℕ}
    (hLH : L + H ≤ 2 * (N + L) + 1) (a : ℤ → ℂ) (t : ℝ) :
    ‖∑ k : Fin (2 * (N + L) + 1),
        intervalVector M H N L a k *
          (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * t) : ℂ)‖ =
      ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * t) : ℂ)‖ := by
  rw [← fourierChar_mul_sum_intervalVector hLH a t, norm_mul, Circle.norm_coe, one_mul]

/-- Taper-width estimate for `L = ⌊1 / δ⌋₊` when `0 < δ ≤ 1 / 2` (with `0 < L` by
`TauCeti.natFloor_one_div_pos`): `L + (π ^ 2 / (12 * δ ^ 2)) / L ≤ 2 / δ`. -/
theorem natFloor_inv_add_pi_sq_div_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (⌊1 / δ⌋₊ : ℝ) + (Real.pi ^ 2 / (12 * δ ^ 2)) / (⌊1 / δ⌋₊ : ℝ) ≤ 2 / δ := by
  have hpi : Real.pi ^ 2 / 12 ≤ 8 / 9 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  simpa only [div_div] using natFloor_one_div_add_div_le hδ hδ' hpi

end TauCeti

/-! ### Bombieri's additive large sieve -/

namespace Finset

open TauCeti

/-- Cosecant-row large sieve for vectors supported on the flat core `|k - (N + L)| ≤ N`: if the
off-diagonal cosecant row sums are bounded by `S ≥ 0`, then the sum of squared Fourier polynomial
norms is at most `(2 * N + L + S / L) * ‖f‖ ^ 2`. -/
theorem sum_norm_sum_fourierChar_sq_le_of_sum_inv_sin_sq_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) {N L : ℕ} (hL : 0 < L)
    (f : EuclideanSpace ℂ (Fin (2 * (N + L) + 1)))
    (hf : ∀ k : Fin (2 * (N + L) + 1), (N : ℤ) < |(k : ℤ) - ((N + L : ℕ) : ℤ)| → f k = 0)
    {S : ℝ} (hS : 0 ≤ S)
    (hsin : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Real.sin (Real.pi * (x i - x j)) ≠ 0)
    (hrow : ∀ i ∈ s, ∑ j ∈ s.erase i, (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹ ≤ S) :
    ∑ i ∈ s,
        ‖∑ k : Fin (2 * (N + L) + 1),
            f k * (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x i) : ℂ)‖ ^ 2 ≤
      (2 * (N : ℝ) + (L : ℝ) + S / (L : ℝ)) * ‖f‖ ^ 2 := by
  have hinner :
      (∑ i ∈ s,
          ‖∑ k : Fin (2 * (N + L) + 1),
              f k * (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x i) : ℂ)‖ ^ 2) =
        ∑ i ∈ s, ‖⟪f, taperedFourierVec N L (x i)⟫_ℂ‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_inner_symm, inner_taperedFourierVec_eq_sum hL (x i) f hf]
  rw [hinner, ← Finset.sum_coe_sort s]
  refine TauCeti.sum_norm_inner_sq_le_of_norm_sq_le_of_sum_erase_le
    (fun i : s ↦ taperedFourierVec N L (x i.val)) f
    (by positivity) (fun i ↦ (norm_taperedFourierVec_sq hL (x i.val)).le) fun i ↦ ?_
  have hmap : (Finset.univ.erase i).map (Function.Embedding.subtype _) = s.erase i.val := by
    ext j
    simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, Function.Embedding.coe_subtype,
      Subtype.exists, and_true]
    exact ⟨fun ⟨a, ha, hne, heq⟩ ↦ heq ▸ ⟨fun h ↦ hne (Subtype.ext h), ha⟩,
      fun ⟨hne, hj⟩ ↦ ⟨j, hj, fun h ↦ hne (congrArg Subtype.val h), rfl⟩⟩
  calc
    ∑ j ∈ Finset.univ.erase i,
        ‖⟪taperedFourierVec N L (x i.val), taperedFourierVec N L (x j.val)⟫_ℂ‖
        = ∑ j ∈ s.erase i.val,
            ‖⟪taperedFourierVec N L (x i.val), taperedFourierVec N L (x j)⟫_ℂ‖ := by
          rw [← hmap, Finset.sum_map]
          rfl
    _ ≤ ∑ j ∈ s.erase i.val, ((L : ℝ) * Real.sin (Real.pi * (x i.val - x j)) ^ 2)⁻¹ :=
      Finset.sum_le_sum fun j hj ↦
        norm_inner_taperedFourierVec_le N L
          (hsin i.val i.property j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm)
    _ = (L : ℝ)⁻¹ * ∑ j ∈ s.erase i.val, (Real.sin (Real.pi * (x i.val - x j)) ^ 2)⁻¹ := by
      simp_rw [mul_inv, Finset.mul_sum]
    _ ≤ (L : ℝ)⁻¹ * S := mul_le_mul_of_nonneg_left (hrow i.val i.property) (by positivity)
    _ = S / (L : ℝ) := by ring

/-- Centered core additive large sieve for `0 < δ ≤ 1 / 2`: taking taper width `L = ⌊1 / δ⌋₊`
yields the explicit constant `2 * N + 2 / δ`. -/
theorem sum_norm_sum_fourierChar_sq_le_of_core_support {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖)
    (N : ℕ) (f : EuclideanSpace ℂ (Fin (2 * (N + ⌊1 / δ⌋₊) + 1)))
    (hf : ∀ k : Fin (2 * (N + ⌊1 / δ⌋₊) + 1),
      (N : ℤ) < |(k : ℤ) - ((N + ⌊1 / δ⌋₊ : ℕ) : ℤ)| → f k = 0) :
    ∑ i ∈ s,
        ‖∑ k : Fin (2 * (N + ⌊1 / δ⌋₊) + 1),
            f k *
              (Real.fourierChar ((((k : ℤ) - ((N + ⌊1 / δ⌋₊ : ℕ) : ℤ) : ℤ) : ℝ) * x i) : ℂ)‖ ^ 2 ≤
      (2 * (N : ℝ) + 2 / δ) * ‖f‖ ^ 2 := by
  classical
  let L : ℕ := ⌊1 / δ⌋₊
  have hL_pos : 0 < L := natFloor_one_div_pos hδ (hδ'.trans (by norm_num))
  have hwidth := natFloor_inv_add_pi_sq_div_le hδ hδ'
  have hsin : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Real.sin (Real.pi * (x i - x j)) ≠ 0 := by
    intro i hi j hj hne hzero
    have hlb := (x i - x j).two_mul_norm_unitAddCircle_le_abs_sin
    rw [hzero, abs_zero] at hlb
    linarith [hsep i hi j hj hne]
  have hmain := s.sum_norm_sum_fourierChar_sq_le_of_sum_inv_sin_sq_le x hL_pos f hf
    (by positivity) hsin (fun i hi ↦ sum_erase_inv_sin_sq_le hδ hsep hi)
  exact le_trans hmain (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

/-- Small-spacing branch (`δ ≤ 1 / 2`) of Bombieri's additive large sieve on `Finset.Ico M (M + H)`,
obtained by applying the centered core sieve to `intervalVector M H (H / 2) ⌊1 / δ⌋₊ a`. -/
private theorem sum_norm_sum_Ico_fourierChar_sq_le_of_le_half {ι : Type*}
    (s : Finset ι) (M : ℤ) (H : ℕ) (a : ℤ → ℂ) (x : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖) :
    ∑ i ∈ s, ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ^ 2 ≤
      ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
  let N : ℕ := H / 2
  have hHN : H ≤ 2 * N + 1 := by omega
  have hLH : ⌊1 / δ⌋₊ + H ≤ 2 * (N + ⌊1 / δ⌋₊) + 1 := by omega
  let f := intervalVector M H N ⌊1 / δ⌋₊ a
  have h2N : 2 * (N : ℝ) ≤ (H : ℝ) := by exact_mod_cast (by omega : 2 * (H / 2) ≤ H)
  simp_rw [← norm_sum_intervalVector_fourierChar hLH a]
  calc
    ∑ i ∈ s,
        ‖∑ k : Fin (2 * (N + ⌊1 / δ⌋₊) + 1),
            f k *
              (Real.fourierChar ((((k : ℤ) - ((N + ⌊1 / δ⌋₊ : ℕ) : ℤ) : ℤ) : ℝ) * x i) : ℂ)‖ ^ 2
        ≤ (2 * (N : ℝ) + 2 / δ) * ‖f‖ ^ 2 :=
      s.sum_norm_sum_fourierChar_sq_le_of_core_support x hδ hδ' hsep N f
        (fun k hk ↦ intervalVector_eq_zero_of_lt_abs hHN ⌊1 / δ⌋₊ a hk)
    _ = (2 * (N : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
      rw [norm_intervalVector_sq hLH]
    _ ≤ ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- **Bombieri's additive large sieve inequality** (Bombieri 1971, Theorem 2) on an integer interval
`Finset.Ico M (M + H)`: for any finite family of `δ`-separated real frequencies (`0 < δ`) in
`UnitAddCircle`, `∑ i ∈ s, ‖∑ n ∈ Ico M (M + H), a n * e(n * x i)‖ ^ 2 ≤`
`(H + 2 / δ) * ∑ n ∈ Ico M (M + H), ‖a n‖ ^ 2`.
Handles all `H : ℕ` (including `H = 0`) and all `δ > 0` (including `δ > 1 / 2`). -/
theorem sum_norm_sum_Ico_fourierChar_sq_le {ι : Type*} (s : Finset ι) (M : ℤ) (H : ℕ)
    (a : ℤ → ℂ) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖) :
    ∑ i ∈ s, ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ^ 2 ≤
      ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
  by_cases hδ' : δ ≤ 1 / 2
  · exact s.sum_norm_sum_Ico_fourierChar_sq_le_of_le_half M H a x hδ hδ' hsep
  have hcard : s.card ≤ 1 :=
    card_le_one_of_half_lt_of_unitAddCircle_separated (lt_of_not_ge hδ') hsep
  have hsingle : ∀ i ∈ s,
      ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ^ 2 ≤
        ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
    intro i _
    have hcs := Finset.norm_sum_fourierChar_sq_le_card_mul_sum (Finset.Ico M (M + H)) a (x i)
    rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] at hcs
    exact hcs.trans
      (mul_le_mul_of_nonneg_right (by linarith [div_pos (two_pos : (0 : ℝ) < 2) hδ])
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  refine (Finset.sum_le_card_nsmul _ _ _ hsingle).trans ?_
  rw [nsmul_eq_mul]
  exact mul_le_of_le_one_left
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    (by exact_mod_cast hcard)

/-- **Bombieri's additive large sieve inequality** (Bombieri 1971, Theorem 2) indexed by `Fin H`:
for any finite family of `δ`-separated real frequencies (`0 < δ`) in `UnitAddCircle` and any
starting frequency `M : ℤ`,
`∑ i ∈ s, ‖∑ j : Fin H, a j * e((M + j) * x i)‖ ^ 2 ≤ (H + 2 / δ) * ∑ j : Fin H, ‖a j‖ ^ 2`. -/
theorem sum_norm_sum_fourierChar_sq_le {ι : Type*} (s : Finset ι) (M : ℤ) (H : ℕ)
    (a : Fin H → ℂ) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖) :
    ∑ i ∈ s, ‖∑ j : Fin H, a j * (Real.fourierChar (((M : ℝ) + (j : ℕ)) * x i) : ℂ)‖ ^ 2 ≤
      ((H : ℝ) + 2 / δ) * ∑ j : Fin H, ‖a j‖ ^ 2 := by
  let b : ℤ → ℂ := fun n ↦
    if h : 0 ≤ n - M ∧ (n - M).toNat < H then a ⟨(n - M).toNat, h.2⟩ else 0
  have hb : ∀ j : Fin H, b (M + (j : ℤ)) = a j := by
    intro j
    have h1 : 0 ≤ M + (j : ℤ) - M := by omega
    have h2 : (M + (j : ℤ) - M).toNat < H := by omega
    simp only [b, h1, h2, and_self, ↓reduceDIte]
    congr 1; ext; dsimp; omega
  have hsum_norm_sq : (∑ n ∈ Finset.Ico M (M + H), ‖b n‖ ^ 2) = ∑ j : Fin H, ‖a j‖ ^ 2 := by
    rw [Finset.sum_Ico_int_add_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ ‖b (M + (j : ℤ))‖ ^ 2)]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hb j]
  have hsum_fourier : ∀ t : ℝ,
      (∑ n ∈ Finset.Ico M (M + H), b n * (Real.fourierChar ((n : ℝ) * t) : ℂ)) =
        ∑ j : Fin H, a j * (Real.fourierChar (((M : ℝ) + (j : ℕ)) * t) : ℂ) := by
    intro t
    rw [Finset.sum_Ico_int_add_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range
        (fun j : ℕ ↦ b (M + (j : ℤ)) * (Real.fourierChar (((M + (j : ℤ) : ℤ) : ℝ) * t) : ℂ))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [hb j]
  simpa only [hsum_fourier, hsum_norm_sq] using
    s.sum_norm_sum_Ico_fourierChar_sq_le M H b x hδ hsep

end Finset

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.FiniteDifference
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Lipschitz
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.Chebyshev.WeightMethod

/-!
# Lipschitz and size bounds for the Riesz remainder

For coefficients `c : ℕ → ℂ` with `‖c(n)‖ ≤ Λ(n)` and a constant `D ∈ ℂ` put
`G(y) = ∑_{1 ≤ n ≤ y} c(n) (y / n - 1) + y D = TauCeti.rieszSum c y + y D`;
for `c(n) = χ(n) Λ(n)` and `D = (L′/L)(1, χ)` this is the *Riesz remainder* `G_χ` of a Dirichlet
character (see `TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder`). For the
trivial character the Riesz remainder is `G_1(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y +
(1 + γ) y`, with the real sum written as `∑ n ∈ Ioc 0 ⌊y⌋₊, …`, the index set of `Chebyshev.psi`.
The Lipschitz bounds for Riesz sums (`TauCeti.norm_rieszSum_sub_rieszSum_le`,
`TauCeti.norm_mul_rieszSum_div_sub_mul_rieszSum_div_le`), Chebyshev's bound `ψ(y) ≤ 3 y`
(`Chebyshev.psi_le_three_mul_self`) and the bounds from Mertens' first theorem
(`Chebyshev.sum_vonMangoldt_div_le`, `Chebyshev.abs_sum_vonMangoldt_div_sub_log_le`)
give, for `a ≥ 0`, `w, w' > 0` and `y, z ≥ 1`,
* `|w G(a / w) - w' G(a / w')| ≤ 3 (a / min w w') |w - w'|`, also for `G_1`;
* `|G(y) - G(z)| ≤ |y - z| (log (max y z) + log 4 + ‖D‖)` and
  `|G_1(y) - G_1(z)| ≤ (log 4 + 4 + γ) |y - z|`;
* `|G(y)| ≤ y (log y + log 4 + ‖D‖)` and `|G_1(y)| ≤ (log 4 + 6 + γ) y`.

All constants above are at most `2 + γ + (log 4 + 4)`, so this one absolute constant serves in the
bounds for `G_χ` and `G_1`.

A bound on an increment `G(y) - G(z)` over `(z, y]` also controls the sharp truncation
`D + ∑_{1 ≤ n ≤ z} c(n) / n`: the forward difference of `TauCeti.rieszSum c` differs from
`(y - z) ∑_{1 ≤ n ≤ z} c(n) / n` only by the terms with `z < n ≤ y`.

## Main results

* `Chebyshev.norm_mul_rieszSum_div_add_mul_sub_le`, `Chebyshev.norm_rieszSum_add_mul_sub_le`,
  `Chebyshev.norm_rieszSum_add_mul_le`: the three bounds for `G` with `‖c(n)‖ ≤ Λ(n)`.
* `Chebyshev.norm_add_sum_div_le_of_norm_rieszSum_sub_add_le`,
  `Chebyshev.norm_add_sum_div_le_at_rpow`: a bound on an increment `G(y) - G(z)` controls the
  sharp truncation `D + ∑_{1 ≤ n ≤ z} c(n) / n`, in general and at `z = x^(1/δ₀)`,
  `y = z (1 + x⁻²)`.
* `Chebyshev.abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le`,
  `Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le`,
  `Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_le`: the three bounds for `G_1`.

## References

* The Riesz remainder and these bounds, in the form with an absolute constant, are those of the
  formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  https://github.com/leanprover-community/riemann-hypothesis.
-/

public section

open Finset ArithmeticFunction
open scoped Chebyshev
open Real (eulerMascheroniConstant)

namespace Chebyshev

open TauCeti

/-! ### The Riesz remainder of coefficients bounded by `Λ` -/

/-- `ψ` bounds the partial sums of coefficients dominated by `Λ`, over the index set
`Icc 1 ⌊y⌋₊` of `TauCeti.rieszSum`: `∑_{1 ≤ n ≤ y} ‖c(n)‖ ≤ ψ(y) ≤ 3 y` for `y ≥ 0`. -/
private theorem sum_Icc_norm_le_three_mul {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) {y : ℝ}
    (hy : 0 ≤ y) : ∑ n ∈ Icc 1 ⌊y⌋₊, ‖c n‖ ≤ 3 * y := by
  have h := psi_le_three_mul_self hy
  rw [psi, ← Icc_add_one_left_eq_Ioc, zero_add] at h
  exact (sum_le_sum fun n _ ↦ hc n).trans h

/-- Ordered case of `Chebyshev.norm_mul_rieszSum_div_add_mul_sub_le`. -/
private theorem norm_mul_rieszSum_div_add_mul_sub_le_of_le {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ) {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hww' : w ≤ w') :
    ‖(w : ℂ) * (rieszSum c (a / w) + ((a / w : ℝ) : ℂ) * D) -
        (w' : ℂ) * (rieszSum c (a / w') + ((a / w' : ℝ) : ℂ) * D)‖ ≤
      3 * (a / w) * (w' - w) := by
  have hD (v : ℝ) (hv : 0 < v) : (v : ℂ) * (((a / v : ℝ) : ℂ) * D) = a * D := by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hv.ne']
  rw [mul_add, mul_add, hD w hw, hD w' (hw.trans_le hww'), add_sub_add_right_eq_sub]
  exact (norm_mul_rieszSum_div_sub_mul_rieszSum_div_le c hw hww').trans
    (mul_le_mul_of_nonneg_right (sum_Icc_norm_le_three_mul hc (by positivity))
      (sub_nonneg.2 hww'))

/-- **Lipschitz bound in the weight for the Riesz remainder.** Let
`‖c(n)‖ ≤ Λ(n)` for all `n`, let `D ∈ ℂ` and `G(y) = TauCeti.rieszSum c y + y D`. For
`a ≥ 0` and `w, w' > 0`, `‖w G(a / w) - w' G(a / w')‖ ≤ 3 (a / min w w') |w - w'|`. -/
theorem norm_mul_rieszSum_div_add_mul_sub_le {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ)
    {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hw' : 0 < w') :
    ‖(w : ℂ) * (rieszSum c (a / w) + ((a / w : ℝ) : ℂ) * D) -
        (w' : ℂ) * (rieszSum c (a / w') + ((a / w' : ℝ) : ℂ) * D)‖ ≤
      3 * (a / min w w') * |w - w'| := by
  rcases le_total w w' with h | h
  · rw [min_eq_left h, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact norm_mul_rieszSum_div_add_mul_sub_le_of_le hc D ha hw h
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h), norm_sub_rev]
    exact norm_mul_rieszSum_div_add_mul_sub_le_of_le hc D ha hw' h

/-- **Lipschitz bound for the Riesz remainder.** Let `‖c(n)‖ ≤ Λ(n)` for all
`n`, let `D ∈ ℂ` and `G(y) = TauCeti.rieszSum c y + y D`. If `max y z ≥ 1`, then
`‖G(y) - G(z)‖ ≤ |y - z| (log (max y z) + log 4 + ‖D‖)`. -/
theorem norm_rieszSum_add_mul_sub_le {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ) {y z : ℝ}
    (h : 1 ≤ max y z) :
    ‖(rieszSum c y + y * D) - (rieszSum c z + z * D)‖ ≤
      |y - z| * (Real.log (max y z) + Real.log 4 + ‖D‖) := by
  wlog hzy : z ≤ y generalizing y z
  · rw [norm_sub_rev, abs_sub_comm, max_comm]
    exact this (by rwa [max_comm]) (not_le.1 hzy).le
  rw [max_eq_left hzy] at h ⊢
  have hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, ‖c n‖ / n ≤ Real.log y + Real.log 4 := by
    have hΛ := sum_vonMangoldt_div_le h
    rw [← Icc_add_one_left_eq_Ioc, zero_add] at hΛ
    exact (sum_le_sum fun n _ ↦ div_le_div_of_nonneg_right (hc n) n.cast_nonneg).trans hΛ
  rw [abs_of_nonneg (sub_nonneg.2 hzy), add_sub_add_comm, ← sub_mul, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_rieszSum_sub_rieszSum_le c hzy).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.2 hzy)
  · simp only [← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.2 hzy), le_refl]

/-- **Size bound for the Riesz remainder.** Let `‖c(n)‖ ≤ Λ(n)` for all `n` and
`D ∈ ℂ`. For `y ≥ 1`, `‖TauCeti.rieszSum c y + y D‖ ≤ y (log y + log 4 + ‖D‖)`. -/
theorem norm_rieszSum_add_mul_le {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ) {y : ℝ}
    (hy : 1 ≤ y) :
    ‖rieszSum c y + y * D‖ ≤ y * (Real.log y + Real.log 4 + ‖D‖) := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  simpa [abs_of_nonneg hy0, max_eq_left hy0] using
    norm_rieszSum_add_mul_sub_le hc D (z := 0) (le_max_of_le_left hy)

/-! ### Sharp truncations from Riesz increments -/

/-- **Sharp truncation from a Riesz increment.** Let `‖c(n)‖ ≤ Λ(n)` for all `n`, let `D ∈ ℂ`
and `G(y) = TauCeti.rieszSum c y + y D`. A bound `B` on the increment `G(y) - G(z)` over `(z, y]`
bounds the error in truncating `D + ∑_{1 ≤ n ≤ z} c(n) / n` at `z`, up to an additional error
due to the integers in `(z, y]`. -/
theorem norm_add_sum_div_le_of_norm_rieszSum_sub_add_le {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n)
    (D : ℂ) {z y B : ℝ} (hz : 0 < z) (hzy : z < y) (hy : 1 ≤ y)
    (hinc : ‖rieszSum c y - rieszSum c z + ((y - z : ℝ) : ℂ) * D‖ ≤ B) :
    ‖D + ∑ n ∈ Icc 1 ⌊z⌋₊, c n / (n : ℂ)‖ ≤ B / (y - z) + (y - z + 1) * (Real.log y / z) := by
  have hs : 0 < y - z := sub_pos.mpr hzy
  have hs₀ : ((y - z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hshort := norm_rieszSum_sub_div_sub_sum_div_le c hz hzy (M := Real.log y) (fun n hn ↦ by
    have hnz := (mem_Ioc.mp hn).1
    have hn₀ : 0 < n := by omega
    have hny := (Nat.le_floor_iff' hn₀.ne').mp (mem_Ioc.mp hn).2
    exact (hc n).trans (vonMangoldt_le_log.trans (Real.log_le_log (Nat.cast_pos.mpr hn₀) hny)))
  have hcard : ((Ioc ⌊z⌋₊ ⌊y⌋₊).card : ℝ) ≤ y - z + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_le_floor hzy.le)]
    linarith [Nat.floor_le (hz.trans hzy).le, Nat.lt_floor_add_one z]
  set R := rieszSum c y - rieszSum c z
  set S := ∑ n ∈ Icc 1 ⌊z⌋₊, c n / (n : ℂ)
  have hsplit : D + S = (R + ((y - z : ℝ) : ℂ) * D) / ((y - z : ℝ) : ℂ) -
      (R / ((y - z : ℝ) : ℂ) - S) := by
    rw [add_div, mul_div_cancel_left₀ _ hs₀]
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact div_le_div_of_nonneg_right hinc hs.le
  · exact hshort.trans
      (mul_le_mul_of_nonneg_right hcard (div_nonneg (Real.log_nonneg hy) hz.le))

section rpow

open Real

/-- The contour part of the error at `z = x ^ r` with relative width `η = x⁻²`. -/
private theorem rpow_box_error_div_le {x Q r σ K z η : ℝ} (hx : 1 ≤ x) (hz_eq : z = x ^ r)
    (hη_eq : η = x ^ (-2 : ℝ)) (hQ : z * x ^ (3 : ℝ) ≤ Q) (hlogQ : 1 ≤ log Q) (hK : 0 ≤ K)
    (hσ : -1 ≤ r * (σ - 1)) :
    K * log Q * (η * z ^ σ * log Q + z ^ 2 / Q) / (z * η) ≤
      2 * K * x ^ (r * (σ - 1)) * log Q ^ 2 := by
  have hx₀ := zero_lt_one.trans_le hx
  have hz : 0 < z := by rw [hz_eq]; exact rpow_pos_of_pos hx₀ _
  have hη : 0 < η := by rw [hη_eq]; exact rpow_pos_of_pos hx₀ _
  have hQ₀ : 0 < Q := (mul_pos hz (rpow_pos_of_pos hx₀ _)).trans_le hQ
  have hpow : z ^ σ / z = x ^ (r * (σ - 1)) := by
    rw [hz_eq, ← rpow_mul hx₀.le, mul_sub, mul_one, rpow_sub hx₀, rpow_mul hx₀.le]
  have htail : (z ^ 2 / Q) / (z * η) ≤ x ^ (-1 : ℝ) := calc
    _ ≤ (z ^ 2 / (z * x ^ (3 : ℝ))) / (z * η) := by gcongr
    _ = 1 / (x ^ (3 : ℝ) * η) := by
      field_simp [hz.ne', hη.ne', (rpow_pos_of_pos hx₀ 3).ne']
    _ = x ^ (-1 : ℝ) := by
      apply (div_eq_iff (mul_ne_zero (rpow_pos_of_pos hx₀ 3).ne' hη.ne')).mpr
      rw [hη_eq, mul_comm, ← rpow_add hx₀, ← rpow_add hx₀]
      norm_num
  have htail' : (z ^ 2 / Q) / (z * η) ≤ x ^ (r * (σ - 1)) * log Q :=
    htail.trans ((rpow_le_rpow_of_exponent_le hx hσ).trans
      (le_mul_of_one_le_right (by positivity) hlogQ))
  calc
    _ = K * log Q * (z ^ σ / z * log Q + (z ^ 2 / Q) / (z * η)) := by
      field_simp [hz.ne', hη.ne', hQ₀.ne']
    _ ≤ _ := by
      rw [hpow]
      calc
        _ ≤ K * log Q * (x ^ (r * (σ - 1)) * log Q + x ^ (r * (σ - 1)) * log Q) := by
          gcongr
        _ = _ := by ring

/-- The smoothing part of the error at `z = x ^ r` with relative width `η = x⁻²`. -/
private theorem rpow_smoothing_error_le {x Q r e z η : ℝ} (hx : 2 ≤ x) (hr : 1 ≤ r)
    (he : -1 ≤ e) (hz_eq : z = x ^ r) (hη_eq : η = x ^ (-2 : ℝ)) (hQ : z * x ^ (3 : ℝ) ≤ Q)
    (hlogQ : 1 ≤ log Q) :
    (z * η + 1) * (log (z * (1 + η)) / z) ≤ 2 * x ^ e * log Q ^ 2 := by
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hz : 0 < z := by rw [hz_eq]; exact rpow_pos_of_pos hx₀ _
  have hη : 0 < η := by rw [hη_eq]; exact rpow_pos_of_pos hx₀ _
  have hη₁ : η ≤ 1 := by
    rw [hη_eq]; exact rpow_le_one_of_one_le_of_nonpos hx₁ (by norm_num)
  have hlog : log (z * (1 + η)) ≤ log Q := by
    apply log_le_log (by positivity)
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hz.le) hQ
    calc
      1 + η ≤ 2 := by linarith
      _ ≤ x ^ (3 : ℝ) := by
        refine hx.trans ?_
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hx₁ (by norm_num : (1 : ℝ) ≤ 3)
  have hηe : η ≤ x ^ e := by
    rw [hη_eq]; exact rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  have hze : 1 / z ≤ x ^ e := by
    rw [hz_eq, one_div, ← rpow_neg hx₀.le]
    exact rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  calc
    _ = (η + 1 / z) * log (z * (1 + η)) := by field_simp [hz.ne']
    _ ≤ (2 * x ^ e) * log Q := by
      refine (mul_le_mul_of_nonneg_left hlog (add_nonneg hη.le (one_div_nonneg.mpr hz.le))).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith

/-- **Sharp truncation at a power cutoff.** Let `‖c(n)‖ ≤ Λ(n)` for all `n` and `D ∈ ℂ`. With
`z = x^(1/δ₀)` and relative width `η = x⁻²`, a bound
`K log Q (η z^(1 - δ₀ + δ) log Q + z² / Q)` for the increment of `TauCeti.rieszSum c y + y D`
over `(z, z (1 + η)]` gives the truncation error
`‖D + ∑_{1 ≤ n ≤ z} c(n) / n‖ ≤ (2K + 2) x^(-1 + δ/δ₀) (log Q)²`. -/
theorem norm_add_sum_div_le_at_rpow {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ)
    {x Q δ₀ δ K : ℝ} (hx : 2 ≤ x) (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ ≤ 1) (hδ : 0 ≤ δ)
    (hQ : x ^ (1 / δ₀ + 3) ≤ Q)
    (hinc : ‖rieszSum c (x ^ (1 / δ₀) * (1 + x ^ (-2 : ℝ))) - rieszSum c (x ^ (1 / δ₀)) +
        ((x ^ (1 / δ₀) * x ^ (-2 : ℝ) : ℝ) : ℂ) * D‖ ≤
      K * log Q * (x ^ (-2 : ℝ) * (x ^ (1 / δ₀)) ^ (1 - δ₀ + δ) * log Q +
        (x ^ (1 / δ₀)) ^ 2 / Q)) :
    ‖D + ∑ n ∈ Icc 1 ⌊x ^ (1 / δ₀)⌋₊, c n / (n : ℂ)‖ ≤
      (2 * K + 2) * x ^ (-1 + δ / δ₀) * log Q ^ 2 := by
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  set z := x ^ (1 / δ₀) with hz_eq
  set η := x ^ (-2 : ℝ) with hη_eq
  have hr : 1 ≤ 1 / δ₀ := (le_div_iff₀ hδ₀).mpr (by simpa using hδ₀')
  have hz : 1 ≤ z := by rw [hz_eq]; exact one_le_rpow hx₁ (by positivity)
  have hη : 0 < η := by rw [hη_eq]; exact rpow_pos_of_pos hx₀ _
  have hQ' : z * x ^ (3 : ℝ) ≤ Q := by rwa [hz_eq, ← rpow_add hx₀]
  have hlogQ : 1 ≤ log Q := by
    have hh : (2 : ℝ) ^ (3 : ℝ) ≤ z * x ^ (3 : ℝ) := by
      calc
        _ ≤ x ^ (3 : ℝ) := rpow_le_rpow (by norm_num) hx (by norm_num)
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hz
    have := log_le_log (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) (hh.trans hQ')
    rw [log_rpow (by norm_num : (0 : ℝ) < 2)] at this
    linarith [log_two_gt_d9]
  have hy : z < z * (1 + η) := by nlinarith
  have hstep : z * (1 + η) - z = z * η := by ring
  have h := norm_add_sum_div_le_of_norm_rieszSum_sub_add_le hc D
    (B := K * log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q))
    (zero_lt_one.trans_le hz) hy (hz.trans hy.le) (by rw [hstep]; exact hinc)
  rw [hstep] at h
  refine h.trans ?_
  have hK : 0 ≤ K := by
    have hQ₀ : 0 < Q :=
      (mul_pos (zero_lt_one.trans_le hz) (rpow_pos_of_pos hx₀ _)).trans_le hQ'
    have hpos : 0 < log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q) := by positivity
    have hn : 0 ≤ K * (log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q)) := by
      rw [← mul_assoc]
      exact (norm_nonneg _).trans hinc
    exact nonneg_of_mul_nonneg_left hn hpos
  have hexp : (1 / δ₀) * ((1 - δ₀ + δ) - 1) = -1 + δ / δ₀ := by
    field_simp [hδ₀.ne']
    ring
  have he : -1 ≤ -1 + δ / δ₀ := by linarith [div_nonneg hδ hδ₀.le]
  have hbox := rpow_box_error_div_le (σ := 1 - δ₀ + δ) hx₁ hz_eq hη_eq hQ' hlogQ hK
    (by rw [hexp]; exact he)
  rw [hexp] at hbox
  calc
    _ ≤ 2 * K * x ^ (-1 + δ / δ₀) * log Q ^ 2 + 2 * x ^ (-1 + δ / δ₀) * log Q ^ 2 :=
      add_le_add hbox (rpow_smoothing_error_le hx hr he hz_eq hη_eq hQ' hlogQ)
    _ = _ := by ring

end rpow

/-! ### The Riesz remainder of the trivial character -/

/-- Ordered case of `Chebyshev.abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le`. -/
private theorem abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le_of_le {a w w' : ℝ} (ha : 0 ≤ a)
    (hw : 0 < w) (hww' : w ≤ w') :
    |w * (∑ n ∈ Ioc 0 ⌊a / w⌋₊, Λ n * (a / w / n - 1) - a / w * Real.log (a / w) +
          (1 + eulerMascheroniConstant) * (a / w)) -
        w' * (∑ n ∈ Ioc 0 ⌊a / w'⌋₊, Λ n * (a / w' / n - 1) - a / w' * Real.log (a / w') +
          (1 + eulerMascheroniConstant) * (a / w'))| ≤ 3 * (a / w) * (w' - w) := by
  have hw' := hw.trans_le hww'
  have hX := mul_sum_Ioc_floor_div_le_mul_sum (c := ⇑Λ) (fun n ↦ vonMangoldt_nonneg) (a := a) hw
    hww'
  have hY := (norm_mul_rieszSum_div_sub_mul_rieszSum_div_le (fun n ↦ (Λ n : ℂ)) (a := a) hw
    hww').trans (mul_le_mul_of_nonneg_right (sum_Icc_norm_le_three_mul
      (fun n ↦ (Complex.norm_real _).trans_le (Real.norm_of_nonneg vonMangoldt_nonneg).le)
      (by positivity)) (sub_nonneg.2 hww'))
  rw [← ofReal_sum_Ioc_floor_mul_div_sub_one, ← ofReal_sum_Ioc_floor_mul_div_sub_one] at hY
  norm_cast at hY
  rw [Real.norm_eq_abs] at hY
  have hL : a * Real.log (a / w) - a * Real.log (a / w') = a * (Real.log w' - Real.log w) := by
    rcases ha.eq_or_lt with rfl | ha'
    · simp
    · rw [Real.log_div ha'.ne' hw.ne', Real.log_div ha'.ne' hw'.ne']
      ring
  have hlog : Real.log w' - Real.log w ≤ (w' - w) / w := by
    have h := Real.log_le_sub_one_of_pos (div_pos hw' hw)
    have hq : w' / w - 1 = (w' - w) / w := by field_simp
    rwa [Real.log_div hw'.ne' hw.ne', hq] at h
  have h1 : a * (Real.log w' - Real.log w) ≤ a / w * (w' - w) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlog ha
  have h2 : 0 ≤ a * (Real.log w' - Real.log w) :=
    mul_nonneg ha (sub_nonneg.2 (Real.log_le_log hw hww'))
  have e (v : ℝ) (hv : 0 < v) (S : ℝ) :
      v * (S - a / v * Real.log (a / v) + (1 + eulerMascheroniConstant) * (a / v)) =
        v * S - a * Real.log (a / v) + (1 + eulerMascheroniConstant) * a := by
    field_simp
  rw [e w hw, e w' hw', abs_le]
  constructor <;> linarith [abs_le.1 hY]

/-- **Lipschitz bound in the weight for the trivial Riesz remainder.** Let
`G₁(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y + (1 + γ) y`. For `a ≥ 0` and `w, w' > 0`,
`|w G₁(a / w) - w' G₁(a / w')| ≤ 3 (a / min w w') |w - w'|`. -/
theorem abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w)
    (hw' : 0 < w') :
    |w * (∑ n ∈ Ioc 0 ⌊a / w⌋₊, Λ n * (a / w / n - 1) - a / w * Real.log (a / w) +
          (1 + eulerMascheroniConstant) * (a / w)) -
        w' * (∑ n ∈ Ioc 0 ⌊a / w'⌋₊, Λ n * (a / w' / n - 1) - a / w' * Real.log (a / w') +
          (1 + eulerMascheroniConstant) * (a / w'))| ≤ 3 * (a / min w w') * |w - w'| := by
  rcases le_total w w' with h | h
  · rw [min_eq_left h, abs_sub_comm w, abs_of_nonneg (sub_nonneg.2 h)]
    exact abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le_of_le ha hw h
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm]
    exact abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le_of_le ha hw' h

/-- Ordered case of `Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le`. -/
private theorem abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le_of_le {y z : ℝ}
    (hz : 1 ≤ z) (hzy : z ≤ y) :
    |(∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) - y * Real.log y + (1 + eulerMascheroniConstant) * y) -
        (∑ n ∈ Ioc 0 ⌊z⌋₊, Λ n * (z / n - 1) - z * Real.log z +
          (1 + eulerMascheroniConstant) * z)| ≤
      (Real.log 4 + 4 + eulerMascheroniConstant) * (y - z) := by
  have hf : ContinuousOn (fun t ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n * (t / n - 1) - t * Real.log t +
      (1 + eulerMascheroniConstant) * t) (Set.Icc z y) :=
    (((continuous_sum_Ioc_floor_mul_div_sub_one _).continuousOn).sub
      Real.continuous_mul_log.continuousOn).add (by fun_prop)
  have hd : ∀ x ∈ Set.Ico z y, HasDerivWithinAt (fun t ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n * (t / n - 1) -
      t * Real.log t + (1 + eulerMascheroniConstant) * t) (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (1 / n) -
        (Real.log x + 1) + (1 + eulerMascheroniConstant) * 1) (Set.Ici x) x := fun x hx ↦
    ((hasDerivWithinAt_sum_Ioc_floor_mul_div_sub_one _ x).sub
      (Real.hasDerivAt_mul_log (by linarith [hx.1])).hasDerivWithinAt).add
      ((hasDerivAt_id' x).const_mul _).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico z y, ‖∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (1 / n) - (Real.log x + 1) +
      (1 + eulerMascheroniConstant) * 1‖ ≤ Real.log 4 + 4 + eulerMascheroniConstant := by
    intro x hx
    have h := abs_le.1 (abs_sum_vonMangoldt_div_sub_log_le (hz.trans hx.1))
    simp only [mul_one_div] at h ⊢
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant]
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment hf hd hb y ⟨hzy, le_rfl⟩
  rwa [Real.norm_eq_abs] at key

/-- **Lipschitz bound for the trivial Riesz remainder.** Let
`G₁(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y + (1 + γ) y`. For `y, z ≥ 1`,
`|G₁(y) - G₁(z)| ≤ (log 4 + 4 + γ) |y - z|`. -/
theorem abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le {y z : ℝ} (hy : 1 ≤ y)
    (hz : 1 ≤ z) :
    |(∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) - y * Real.log y + (1 + eulerMascheroniConstant) * y) -
        (∑ n ∈ Ioc 0 ⌊z⌋₊, Λ n * (z / n - 1) - z * Real.log z +
          (1 + eulerMascheroniConstant) * z)| ≤
      (Real.log 4 + 4 + eulerMascheroniConstant) * |y - z| := by
  rcases le_total z y with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le_of_le hz h
  · rw [abs_sub_comm y z, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm]
    exact abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le_of_le hy h

/-- **Size bound for the trivial Riesz remainder.** For `y ≥ 1`,
`|∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y + (1 + γ) y| ≤ (log 4 + 6 + γ) y`. -/
theorem abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_le {y : ℝ} (hy : 1 ≤ y) :
    |∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) - y * Real.log y + (1 + eulerMascheroniConstant) * y| ≤
      (Real.log 4 + 6 + eulerMascheroniConstant) * y := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hS : ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) = y * ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n / n - ψ y := by
    rw [psi, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ ↦ by ring
  have hE := abs_le.1 (abs_sum_vonMangoldt_div_sub_log_le hy)
  have h1 := mul_le_mul_of_nonneg_left hE.2 hy0
  have h2 := mul_le_mul_of_nonneg_left hE.1 hy0
  have hγ : 0 ≤ eulerMascheroniConstant * y :=
    mul_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant]) hy0
  rw [hS, abs_le]
  constructor <;> linarith [psi_le_three_mul_self hy0, psi_nonneg y]

end Chebyshev

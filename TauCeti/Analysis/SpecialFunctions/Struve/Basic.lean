/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# The Struve functions `𝐇_ν` and `𝐋_ν`

The Struve function and the modified Struve function are (DLMF 11.2.1–11.2.2)

`𝐇_ν(z) = (z/2)^{ν+1} 𝐅₁₂(3/2, ν + 3/2; −z²/4)`, `𝐋_ν(z) = (z/2)^{ν+1} 𝐅₁₂(3/2, ν + 3/2; z²/4)`,

where `𝐅₁₂(b₁, b₂; x) = Complex.regularizedHGFun {1} {b₁, b₂} x = ∑ₖ xᵏ / (Γ(b₁ + k) Γ(b₂ + k))`
is Mathlib's regularized `₁F₂` series and the power is principal. Since `1 / Γ` vanishes at the
poles of `Γ`, the definitions and the statements below need no condition on the order `ν`. The
functions are holomorphic on the slit plane, and the cores `𝐅₁₂(3/2, ν + 3/2; ∓z²/4)` are entire
and even in `z`. At `z = 0` the products take the value of Mathlib's `0 ^ (ν + 1)`, which is not
the limit of the function in general, so the series are stated for `z ≠ 0`, except at order zero,
where the power is `z/2`.

## Main definitions

* `Complex.struveH` — the Struve function `𝐇_ν(z)`.
* `Complex.struveL` — the modified Struve function `𝐋_ν(z)`.

## Main results

* `Complex.hasSum_struveH`, `Complex.hasSum_struveL` — the series
  `𝐇_ν(z) = ∑ₖ (−1)ᵏ (z/2)^{2k+ν+1} / (Γ(k + 3/2) Γ(k + ν + 3/2))` and its analogue without
  `(−1)ᵏ` for `𝐋_ν`, for `z ≠ 0` (DLMF 11.2.1–11.2.2).
* `Complex.hasSum_struveH_zero`, `Complex.hasSum_struveL_zero` — the order-zero series
  `𝐇₀(z) = (2/π) ∑ₖ (−1)ᵏ z^{2k+1} / ((2k + 1)!!)²`, and the same without `(−1)ᵏ` for `𝐋₀`, for
  every `z` (DLMF 11.2.3–11.2.4).
* `Complex.differentiableAt_struveH`, `Complex.differentiableOn_struveH`,
  `Complex.analyticOnNhd_struveH` and their `struveL` versions — holomorphy on the slit plane.
* `Complex.differentiable_struveH_intCast`, `Complex.differentiable_struveL_intCast` — for an
  integer order `n ≥ -1`, `𝐇_n` and `𝐋_n` are entire.
* `Complex.cpow_neg_mul_struveH`, `Complex.cpow_neg_mul_struveL` — for `z ≠ 0`,
  `(z/2)^{−ν−1} 𝐇_ν(z)` and `(z/2)^{−ν−1} 𝐋_ν(z)` are the entire cores. Their value
  `(Γ(3/2) Γ(ν + 3/2))⁻¹` at `z = 0` is `Complex.regularizedHGFun_zero` with
  `Complex.regularizedHGFunCoeff_one_pair`.
* `Complex.struveL_eq_struveH_I_mul` — `𝐋_ν(z) = −i e^{−iνπ/2} 𝐇_ν(iz)` when
  `ph(iz) = ph z + π/2`.
* `Complex.struveH_ofReal_im`, `Complex.struveL_ofReal_im` — `𝐇_ν(x)` and `𝐋_ν(x)` are real for
  real `ν` and `x ≥ 0`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 7 §15.1.
* *NIST Digital Library of Mathematical Functions*, [§11.2](https://dlmf.nist.gov/11.2).

The definitions and the series, holomorphy and order-zero results are adapted from lean-DLMF
(`DLMF/Struve/Basic/Functions.lean`: `struveH`, `struveL`; `DLMF/Struve/SeriesAndEquations.lean`:
`hasSum_struveHCore`, `hasSum_struveLCore`, `struve_analytic`, `struveH_nat_entire`,
`struveL_nat_entire`, `struveH_zero_order_series`, `struveL_zero_order_series`), with the
cores written as Mathlib's `₁F₂` series rather than as separate definitions.
-/

public section

noncomputable section

open Set
open scoped Nat Real

namespace Complex

/-- The **Struve function** `𝐇_ν(z) = (z/2)^{ν+1} 𝐅₁₂(3/2, ν + 3/2; −z²/4)` (DLMF 11.2.1), with
the principal power and Mathlib's regularized `₁F₂` series
`𝐅₁₂(b₁, b₂; x) = regularizedHGFun {1} {b₁, b₂} x = ∑ₖ xᵏ / (Γ(b₁ + k) Γ(b₂ + k))`. -/
def struveH (ν z : ℂ) : ℂ :=
  (z / 2) ^ (ν + 1) * regularizedHGFun {1} {3 / 2, ν + 3 / 2} (-(z ^ 2) / 4)

/-- The **modified Struve function** `𝐋_ν(z) = (z/2)^{ν+1} 𝐅₁₂(3/2, ν + 3/2; z²/4)`
(DLMF 11.2.2), with the principal power and Mathlib's regularized `₁F₂` series. -/
def struveL (ν z : ℂ) : ℂ :=
  (z / 2) ^ (ν + 1) * regularizedHGFun {1} {3 / 2, ν + 3 / 2} (z ^ 2 / 4)

/-- The defining formula of `struveH`. -/
theorem struveH_def (ν z : ℂ) :
    struveH ν z = (z / 2) ^ (ν + 1) * regularizedHGFun {1} {3 / 2, ν + 3 / 2} (-(z ^ 2) / 4) :=
  (rfl)

/-- The defining formula of `struveL`. -/
theorem struveL_def (ν z : ℂ) :
    struveL ν z = (z / 2) ^ (ν + 1) * regularizedHGFun {1} {3 / 2, ν + 3 / 2} (z ^ 2 / 4) :=
  (rfl)

/-! ### The series -/

/-- The common series of `𝐇_ν` (`c = -1`) and `𝐋_ν` (`c = 1`). -/
private theorem hasSum_cpow_mul_regularizedHGFun (ν c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => c ^ k * (z / 2) ^ (2 * k + ν + 1) /
        (Gamma (k + 3 / 2) * Gamma (k + ν + 3 / 2)))
      ((z / 2) ^ (ν + 1) * regularizedHGFun {1} {3 / 2, ν + 3 / 2} (c * z ^ 2 / 4)) := by
  have h2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  refine ((hasSum_regularizedHGFun (by simp) _).mul_left ((z / 2) ^ (ν + 1))).congr_fun
    fun k => ?_
  -- `cpow_add` splits the power only once the exponent is written as a natural number plus
  -- `ν + 1`; the natural part then becomes an ordinary power.
  have he : 2 * (k : ℂ) + ν + 1 = ((2 * k : ℕ) : ℂ) + (ν + 1) := by push_cast; ring
  rw [Multiset.insert_eq_cons, regularizedHGFunCoeff_one_pair, he, cpow_add _ _ h2, cpow_natCast,
    pow_mul]
  ring_nf

/-- **The Struve series** (DLMF 11.2.1): for `z ≠ 0`,
`𝐇_ν(z) = ∑ₖ (−1)ᵏ (z/2)^{2k+ν+1} / (Γ(k + 3/2) Γ(k + ν + 3/2))`, for every order `ν`. -/
theorem hasSum_struveH (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-1) ^ k * (z / 2) ^ (2 * k + ν + 1) /
      (Gamma (k + 3 / 2) * Gamma (k + ν + 3 / 2))) (struveH ν z) := by
  simpa [struveH_def, neg_div] using hasSum_cpow_mul_regularizedHGFun ν (-1) hz

/-- **The modified Struve series** (DLMF 11.2.2): for `z ≠ 0`,
`𝐋_ν(z) = ∑ₖ (z/2)^{2k+ν+1} / (Γ(k + 3/2) Γ(k + ν + 3/2))`, for every order `ν`. -/
theorem hasSum_struveL (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (z / 2) ^ (2 * k + ν + 1) /
      (Gamma (k + 3 / 2) * Gamma (k + ν + 3 / 2))) (struveL ν z) := by
  simpa [struveL_def] using hasSum_cpow_mul_regularizedHGFun ν 1 hz

/-- The common series of `𝐇₀` (`c = -1`) and `𝐋₀` (`c = 1`). -/
private theorem hasSum_mul_regularizedHGFun_three_halves (c z : ℂ) :
    HasSum (fun k : ℕ => 2 / π * (c ^ k * z ^ (2 * k + 1) / ((2 * k + 1)‼ : ℂ) ^ 2))
      (z / 2 * regularizedHGFun {1} {3 / 2, 3 / 2} (c * z ^ 2 / 4)) := by
  refine ((hasSum_regularizedHGFun (by simp) _).mul_left (z / 2)).congr_fun fun k => ?_
  have hπ : ((√π : ℝ) : ℂ) ^ 2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hd : ((2 * k + 1)‼ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.doubleFactorial_pos _).ne'
  -- Mathlib's real `Γ(k + 1 + 1/2) = (2k + 1)!! √π / 2^{k+1}`, cast to `ℂ`: the complex argument
  -- is first written as the cast of that real argument, so that `Gamma_ofReal` applies.
  have hk : 3 / 2 + (k : ℂ) = ((k + 1 + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hΓ : Gamma (3 / 2 + k) = ((2 * k + 1)‼ : ℂ) * (√π : ℝ) / 2 ^ (k + 1) := by
    rw [hk, Gamma_ofReal, Real.Gamma_nat_add_one_add_half]
    push_cast
    ring
  have hx : c * z ^ 2 / 4 = c * (z / 2) ^ 2 := by ring
  rw [Multiset.insert_eq_cons, regularizedHGFunCoeff_one_pair, hΓ, hx]
  rw [mul_pow, div_pow, div_pow, ← pow_mul, ← pow_mul]
  field_simp
  rw [hπ]
  ring

/-- DLMF 11.2.3: `𝐇₀(z) = (2/π) ∑ₖ (−1)ᵏ z^{2k+1} / ((2k + 1)!!)²`, for every `z`. -/
theorem hasSum_struveH_zero (z : ℂ) :
    HasSum (fun k : ℕ => 2 / π * ((-1) ^ k * z ^ (2 * k + 1) / ((2 * k + 1)‼ : ℂ) ^ 2))
      (struveH 0 z) := by
  simpa [struveH_def, neg_div] using hasSum_mul_regularizedHGFun_three_halves (-1) z

/-- DLMF 11.2.4: `𝐋₀(z) = (2/π) ∑ₖ z^{2k+1} / ((2k + 1)!!)²`, for every `z`. -/
theorem hasSum_struveL_zero (z : ℂ) :
    HasSum (fun k : ℕ => 2 / π * (z ^ (2 * k + 1) / ((2 * k + 1)‼ : ℂ) ^ 2)) (struveL 0 z) := by
  simpa [struveL_def] using hasSum_mul_regularizedHGFun_three_halves 1 z

/-! ### Holomorphy in the argument -/

/-- The common factorization of `𝐇_ν` (`c = -1`) and `𝐋_ν` (`c = 1`) is holomorphic on the slit
plane. -/
private theorem differentiableAt_cpow_mul_regularizedHGFun (ν c : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ
      (fun w => (w / 2) ^ (ν + 1) * regularizedHGFun {1} {3 / 2, ν + 3 / 2} (c * w ^ 2 / 4)) z := by
  have h2 : z / 2 ∈ slitPlane := by simpa using TauCeti.div_ofReal_mem_slitPlane hz two_pos
  have hF := differentiable_regularizedHGFun_of_card_le (a := {1}) (b := {3 / 2, ν + 3 / 2})
    (by simp)
  fun_prop (disch := assumption)

/-- At an integer order `n ≥ -1`, the common factorization of `𝐇_n` (`c = -1`) and `𝐋_n`
(`c = 1`) is entire, because `(w/2)^{n+1}` is a natural power. -/
private theorem differentiable_cpow_mul_regularizedHGFun {n : ℤ} (hn : -1 ≤ n) (c : ℂ) :
    Differentiable ℂ (fun w => (w / 2) ^ ((n : ℂ) + 1) *
      regularizedHGFun {1} {3 / 2, (n : ℂ) + 3 / 2} (c * w ^ 2 / 4)) := by
  have he : ((n : ℂ) + 1) = ((n + 1).toNat : ℕ) := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ n + 1)).symm
  have hF := differentiable_regularizedHGFun_of_card_le (a := {1})
    (b := {3 / 2, (n : ℂ) + 3 / 2}) (by simp)
  simp only [he, cpow_natCast]
  fun_prop

/-- `𝐇_ν` is holomorphic at each point of the slit plane. -/
theorem differentiableAt_struveH (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ (struveH ν) z := by
  simpa [funext (struveH_def ν), neg_div] using
    differentiableAt_cpow_mul_regularizedHGFun ν (-1) hz

/-- `𝐋_ν` is holomorphic at each point of the slit plane. -/
theorem differentiableAt_struveL (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ (struveL ν) z := by
  simpa [funext (struveL_def ν)] using differentiableAt_cpow_mul_regularizedHGFun ν 1 hz

/-- `𝐇_ν` is holomorphic on the slit plane. -/
theorem differentiableOn_struveH (ν : ℂ) : DifferentiableOn ℂ (struveH ν) slitPlane :=
  fun _ hz => (differentiableAt_struveH ν hz).differentiableWithinAt

/-- `𝐋_ν` is holomorphic on the slit plane. -/
theorem differentiableOn_struveL (ν : ℂ) : DifferentiableOn ℂ (struveL ν) slitPlane :=
  fun _ hz => (differentiableAt_struveL ν hz).differentiableWithinAt

/-- `𝐇_ν` is analytic on the slit plane. -/
theorem analyticOnNhd_struveH (ν : ℂ) : AnalyticOnNhd ℂ (struveH ν) slitPlane :=
  (differentiableOn_struveH ν).analyticOnNhd isOpen_slitPlane

/-- `𝐋_ν` is analytic on the slit plane. -/
theorem analyticOnNhd_struveL (ν : ℂ) : AnalyticOnNhd ℂ (struveL ν) slitPlane :=
  (differentiableOn_struveL ν).analyticOnNhd isOpen_slitPlane

/-- For an integer order `n ≥ -1`, `𝐇_n` is entire. -/
theorem differentiable_struveH_intCast {n : ℤ} (hn : -1 ≤ n) :
    Differentiable ℂ (struveH n) := by
  simpa [funext (struveH_def n), neg_div] using differentiable_cpow_mul_regularizedHGFun hn (-1)

/-- For an integer order `n ≥ -1`, `𝐋_n` is entire. -/
theorem differentiable_struveL_intCast {n : ℤ} (hn : -1 ≤ n) :
    Differentiable ℂ (struveL n) := by
  simpa [funext (struveL_def n)] using differentiable_cpow_mul_regularizedHGFun hn 1

/-! ### The entire cores -/

/-- For `z ≠ 0`, `(z/2)^{−ν−1} 𝐇_ν(z) = 𝐅₁₂(3/2, ν + 3/2; −z²/4)`, the core of `𝐇_ν`, which is
an entire even function of `z`. -/
theorem cpow_neg_mul_struveH (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    (z / 2) ^ (-(ν + 1)) * struveH ν z =
      regularizedHGFun {1} {3 / 2, ν + 3 / 2} (-(z ^ 2) / 4) := by
  rw [struveH_def, ← mul_assoc, ← cpow_add _ _ (div_ne_zero hz two_ne_zero), neg_add_cancel,
    cpow_zero, one_mul]

/-- For `z ≠ 0`, `(z/2)^{−ν−1} 𝐋_ν(z) = 𝐅₁₂(3/2, ν + 3/2; z²/4)`, the core of `𝐋_ν`, which is
an entire even function of `z`. -/
theorem cpow_neg_mul_struveL (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    (z / 2) ^ (-(ν + 1)) * struveL ν z = regularizedHGFun {1} {3 / 2, ν + 3 / 2} (z ^ 2 / 4) := by
  rw [struveL_def, ← mul_assoc, ← cpow_add _ _ (div_ne_zero hz two_ne_zero), neg_add_cancel,
    cpow_zero, one_mul]

/-! ### The relation between `𝐋_ν` and `𝐇_ν`, and reality -/

/-- `𝐋_ν(z) = −i e^{−iνπ/2} 𝐇_ν(iz)` (DLMF 11.2.2), for `z` with `ph(iz) = ph z + π/2`; these are
the `z ≠ 0` with `ph z ≤ π/2`. -/
theorem struveL_eq_struveH_I_mul (ν : ℂ) {z : ℂ} (h : arg (I * z) = arg z + π / 2) :
    struveL ν z = -I * exp (-I * ν * π / 2) * struveH ν (I * z) := by
  have hz : z ≠ 0 := by
    rintro rfl
    simp only [mul_zero, arg_zero, zero_add] at h
    linarith [Real.pi_pos]
  have hmem : arg I + arg (z / 2) ∈ Ioc (-π) π := by
    rw [arg_div_ofNat]
    exact (arg_mul_eq_add_arg_iff I_ne_zero hz).1 (by rw [h, arg_I, add_comm])
  have hpow : (I * z / 2) ^ (ν + 1) = exp (π / 2 * I * (ν + 1)) * (z / 2) ^ (ν + 1) := by
    rw [mul_div_assoc, mul_cpow hmem, cpow_def_of_ne_zero I_ne_zero, log_I]
  have hsq : -((I * z) ^ 2) / 4 = z ^ 2 / 4 := by rw [mul_pow, I_sq]; ring
  rw [struveH_def, struveL_def, hpow, hsq]
  -- the phase factors cancel: their exponents add up to `π/2 * I`, and `-I * e^{iπ/2} = 1`
  have hphase : -I * ν * π / 2 + π / 2 * I * (ν + 1) = π / 2 * I := by ring
  have he : -I * exp (-I * ν * π / 2) * exp (π / 2 * I * (ν + 1)) = 1 := by
    rw [mul_assoc, ← exp_add, hphase, exp_pi_div_two_mul_I, neg_mul, I_mul_I, neg_neg]
  linear_combination (-(z / 2) ^ (ν + 1) * regularizedHGFun {1} {3 / 2, ν + 3 / 2} (z ^ 2 / 4)) * he

/-- The factor `(x/2)^{ν+1}` and the core of `𝐇_ν`, `𝐋_ν` at real order and argument. -/
private theorem struve_ofReal_im (ν x c : ℝ) (hx : 0 ≤ x) :
    (((x : ℂ) / 2) ^ ((ν : ℂ) + 1) *
      regularizedHGFun {1} {3 / 2, (ν : ℂ) + 3 / 2} (c * (x : ℂ) ^ 2 / 4)).im = 0 := by
  have h1 : ((x : ℂ) / 2) ^ ((ν : ℂ) + 1) = (((x / 2) ^ (ν + 1) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by positivity)]
    norm_num
  have h2 := regularizedHGFun_map_ofReal_im {1} {3 / 2, ν + 3 / 2} (c * x ^ 2 / 4)
  simp only [Multiset.map_singleton, Multiset.insert_eq_cons, Multiset.map_cons] at h2
  push_cast at h2
  rw [← Multiset.insert_eq_cons] at h2
  rw [h1, im_ofReal_mul, h2, mul_zero]

/-- `𝐇_ν(x)` is real for real `ν` and `x ≥ 0`. -/
@[simp]
theorem struveH_ofReal_im (ν : ℝ) {x : ℝ} (hx : 0 ≤ x) : (struveH ν x).im = 0 := by
  simpa [struveH_def, neg_div] using struve_ofReal_im ν x (-1) hx

/-- `𝐋_ν(x)` is real for real `ν` and `x ≥ 0`. -/
@[simp]
theorem struveL_ofReal_im (ν : ℝ) {x : ℝ} (hx : 0 ≤ x) : (struveL ν x).im = 0 := by
  simpa [struveL_def] using struve_ofReal_im ν x 1 hx

end Complex

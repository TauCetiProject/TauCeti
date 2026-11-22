/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import TauCeti.Analysis.SpecialFunctions.BarnesG.Basic
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Ordinary.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The arithmetic and Barnes factors of the zeta moment conjecture

For real `k`, the Keating–Snaith conjecture predicts
`∫₀ᵀ |ζ(1/2 + it)|^(2k) dt ∼ a(k) g(k) T (log T)^(k²)`, with an arithmetic factor `a(k)` and a
random-matrix factor `g(k)`. This file defines both constants and proves the facts about them
that hold unconditionally: `a(k)` is positive for every real `k` and `g(k)` is positive for
`k > -1/2`, and they take the predicted values in the cases `k = 1, 2` where the moments are known.

Write `c_k(j) = (k)_j / j!` for the coefficients of `(1 - x)⁻ᵏ = ∑ c_k(j) xʲ`; this is Mathlib's
`Ring.multichoose k j`. The local series `∑ c_k(j)² xʲ` is the Gauss hypergeometric function
`₂F₁(k, k; 1; x)` (`TauCeti.hasSum_multichoose_sq_mul_pow`), and the arithmetic
factor is the Euler product
`a(k) = ∏_p (1 - 1/p)^(k²) ₂F₁(k, k; 1; 1/p)`.
Since `₂F₁(k, k; 1; x) = 1 + k² x + O(x²)`, the first-order terms cancel in each local factor,
so the logarithms of the local factors are `O(p⁻²)`. The product therefore converges
unconditionally, for every real `k`, to a positive number. The random-matrix factor is the
Barnes quotient `g(k) = G(k + 1)² / G(2k + 1)`, a real number because `G` is real on the real
axis, and positive for `k > -1/2`.

## Main definitions

* `TauCeti.zetaMomentLocalFactor k x = (1 - x)^(k²) ₂F₁(k, k; 1; x)`: the local factor, evaluated
  at `x = 1/p`.
* `TauCeti.zetaMomentArithmeticFactor k`: the arithmetic factor `a(k)`, an unordered product over
  the primes.
* `TauCeti.zetaMomentBarnesFactor k`: the Barnes factor `g(k)`, the real part of
  `G(k + 1)² / G(2k + 1)`.

## Main results

* `TauCeti.zetaMomentLocalFactor_def`: the local factor is `(1 - x)^(k²) ₂F₁(k, k; 1; x)`.
* `TauCeti.hasProd_zetaMomentArithmeticFactor`, `TauCeti.zetaMomentArithmeticFactor_pos`: the
  Euler product converges unconditionally and `a(k) > 0`, for every real `k`.
* `TauCeti.zetaMomentArithmeticFactor_one`, `TauCeti.zetaMomentArithmeticFactor_two`:
  `a(1) = 1` and `a(2) = 1/ζ(2) = 6/π²`.
* `TauCeti.ofReal_zetaMomentBarnesFactor`, `TauCeti.zetaMomentBarnesFactor_pos`: the Barnes
  quotient is real, and positive for `k > -1/2`.
* `TauCeti.zetaMomentBarnesFactor_natCast`: `g(n) = ∏_{j < n} j! / (j + n)!` for `n : ℕ`, so
  `g(1) = 1`, `g(2) = 1/12` and `g(3) = 1/8640`.
* `TauCeti.zetaMomentArithmeticFactor_two_mul_zetaMomentBarnesFactor_two`:
  `a(2) g(2) = 1/(2π²)`, the leading coefficient of the fourth moment.

## References

* J. P. Keating and N. C. Snaith, *Random matrix theory and `ζ(1/2 + it)`*, Comm. Math. Phys.
  **214** (2000), 57–89, equations (4)–(6) and (15)–(19).
-/

public section

open Real
open scoped Nat

namespace TauCeti

/-! ### The local factors -/

/-- The local factor `(1 - x)^(k²) ₂F₁(k, k; 1; x)` of the arithmetic factor of the zeta moment
conjecture. At `x = 1/p` it is `(1 - 1/p)^(k²) ∑_j c_k(j)² p⁻ʲ`, where `c_k(j) = (k)_j / j!`. -/
noncomputable def zetaMomentLocalFactor (k x : ℝ) : ℝ :=
  (1 - x) ^ (k ^ 2) * ₂F₁ k k 1 x

/-- The defining formula of the local factor, `(1 - x)^(k²) ₂F₁(k, k; 1; x)`. Combined with
`TauCeti.hasSum_multichoose_sq_mul_pow`, this identifies the local factor at `x = 1/p` with
`(1 - 1/p)^(k²) ∑_j c_k(j)² p⁻ʲ`. -/
theorem zetaMomentLocalFactor_def (k x : ℝ) :
    zetaMomentLocalFactor k x = (1 - x) ^ (k ^ 2) * ₂F₁ k k 1 x :=
  (rfl)

/-- The local factor is positive for `0 ≤ x < 1`. -/
theorem zetaMomentLocalFactor_pos (k : ℝ) {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    0 < zetaMomentLocalFactor k x :=
  mul_pos (rpow_pos_of_pos (by linarith) _)
    (by nlinarith [one_add_sq_mul_le_ordinaryHypergeometric k hx₀ hx₁, sq_nonneg k])

/-- The first-order terms cancel in the local factor: `log ((1 - x)^(k²) ₂F₁(k, k; 1; x))` is
`O(x²)` on `[0, 1/2]`. -/
private theorem exists_abs_log_zetaMomentLocalFactor_le (k : ℝ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → |log (zetaMomentLocalFactor k x)| ≤ C * x ^ 2 := by
  obtain ⟨C, hC, hup⟩ :=
    exists_ordinaryHypergeometric_le k (r := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨2 * k ^ 2 + C + (k ^ 2 + C) ^ 2, fun x hx₀ hx₁ ↦ ?_⟩
  set S := ₂F₁ k k 1 x
  have hlow : 1 + k ^ 2 * x ≤ S := one_add_sq_mul_le_ordinaryHypergeometric k hx₀ (by linarith)
  have hup : S ≤ 1 + k ^ 2 * x + C * x ^ 2 := hup x hx₀ hx₁
  have hk : 0 ≤ k ^ 2 := sq_nonneg k
  have hS : 0 < S := by nlinarith
  -- `log (1 - x) = -x + O(x²)`.
  have hlog₁ : |x + log (1 - x)| ≤ 2 * x ^ 2 := by
    have h := abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx₀]; linarith) 1
    rw [abs_of_nonneg hx₀] at h
    norm_num at h
    exact h.trans <| (div_le_iff₀ (by linarith)).2 (by nlinarith)
  -- `log S = k² x + O(x²)`, from `1 - S⁻¹ ≤ log S ≤ S - 1`.
  have hlogS_le : log S ≤ k ^ 2 * x + C * x ^ 2 := by linarith [log_le_sub_one_of_pos hS]
  have hlogS_ge : k ^ 2 * x - (k ^ 2 + C) ^ 2 * x ^ 2 ≤ log S := by
    set u := S - 1
    have hu₀ : k ^ 2 * x ≤ u := by linarith
    have hu : 0 ≤ u := le_trans (by positivity) hu₀
    have hu₁ : u ≤ (k ^ 2 + C) * x := by nlinarith
    have hinv : S⁻¹ ≤ 1 - u + u ^ 2 := by
      rw [inv_le_iff_one_le_mul₀' hS]
      nlinarith [pow_nonneg hu 3]
    have hsq : u ^ 2 ≤ ((k ^ 2 + C) * x) ^ 2 := pow_le_pow_left₀ hu hu₁ 2
    nlinarith [one_sub_inv_le_log_of_pos hS]
  rw [zetaMomentLocalFactor, log_mul (rpow_pos_of_pos (by linarith) _).ne' hS.ne',
    log_rpow (by linarith)]
  rw [abs_le] at hlog₁ ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlog₁.1 hk,
    mul_le_mul_of_nonneg_left hlog₁.2 hk, sq_nonneg x, sq_nonneg (k ^ 2 + C)]

/-- The logarithms of the local factors at the primes are summable. -/
private theorem summable_log_zetaMomentLocalFactor (k : ℝ) :
    Summable fun p : Nat.Primes ↦ log (zetaMomentLocalFactor k (p : ℝ)⁻¹) := by
  obtain ⟨C, hC⟩ := exists_abs_log_zetaMomentLocalFactor_le k
  have hsum : Summable fun p : Nat.Primes ↦ C * ((p : ℝ)⁻¹) ^ 2 := by
    refine (Nat.Primes.summable_rpow.2 (by norm_num : (-2 : ℝ) < -1)).mul_left C |>.congr
      fun p ↦ ?_
    rw [rpow_neg (Nat.cast_nonneg _), inv_pow, rpow_two]
  refine hsum.of_norm_bounded fun p ↦ ?_
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  rw [Real.norm_eq_abs]
  exact hC _ (by positivity) (by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith)

/-! ### The arithmetic factor -/

/-- The reciprocal of a prime lies strictly inside the unit interval. -/
private theorem abs_inv_prime_lt_one (p : Nat.Primes) : |(p : ℝ)⁻¹| < 1 := by
  rw [abs_inv, Nat.abs_cast]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.property.one_lt)

/-- The arithmetic factor `a(k) = ∏_p (1 - 1/p)^(k²) ∑_j c_k(j)² p⁻ʲ` of the zeta moment
conjecture, with `c_k(j) = (k)_j / j!`, as an unordered product over the primes. The product
converges unconditionally for every real `k` (`TauCeti.hasProd_zetaMomentArithmeticFactor`). -/
noncomputable def zetaMomentArithmeticFactor (k : ℝ) : ℝ :=
  ∏' p : Nat.Primes, zetaMomentLocalFactor k (p : ℝ)⁻¹

private theorem hasProd_rexp_zetaMomentArithmeticFactor (k : ℝ) :
    HasProd (fun p : Nat.Primes ↦ zetaMomentLocalFactor k (p : ℝ)⁻¹)
      (rexp (∑' p : Nat.Primes, log (zetaMomentLocalFactor k (p : ℝ)⁻¹))) :=
  hasProd_of_hasSum_log
    (fun p ↦ zetaMomentLocalFactor_pos k (by positivity)
      (lt_of_abs_lt (abs_inv_prime_lt_one p)))
    (summable_log_zetaMomentLocalFactor k).hasSum

/-- The Euler product defining the arithmetic factor converges unconditionally, for every real
`k`. -/
theorem hasProd_zetaMomentArithmeticFactor (k : ℝ) :
    HasProd (fun p : Nat.Primes ↦ zetaMomentLocalFactor k (p : ℝ)⁻¹)
      (zetaMomentArithmeticFactor k) :=
  (hasProd_rexp_zetaMomentArithmeticFactor k).multipliable.hasProd

/-- The arithmetic factor `a(k)` is positive, for every real `k`. -/
theorem zetaMomentArithmeticFactor_pos (k : ℝ) : 0 < zetaMomentArithmeticFactor k := by
  rw [zetaMomentArithmeticFactor, (hasProd_rexp_zetaMomentArithmeticFactor k).tprod_eq]
  exact exp_pos _

/-! ### The cases `k = 1` and `k = 2` -/

/-- At `k = 1` every local factor is `1`: `c_1(j) = 1` and `₂F₁(1, 1; 1; x) = 1/(1 - x)`. -/
theorem zetaMomentLocalFactor_one {x : ℝ} (hx : |x| < 1) : zetaMomentLocalFactor 1 x = 1 := by
  have h := hasSum_multichoose_sq_mul_pow (1 : ℝ) (x := x) (by rwa [Real.norm_eq_abs])
  simp only [Ring.multichoose_one, one_pow, one_mul] at h
  have hx₁ : 1 - x ≠ 0 := by linarith [le_abs_self x]
  rw [zetaMomentLocalFactor, h.unique (hasSum_geometric_of_abs_lt_one hx), one_pow, rpow_one,
    mul_inv_cancel₀ hx₁]

/-- `a(1) = 1`. -/
@[simp]
theorem zetaMomentArithmeticFactor_one : zetaMomentArithmeticFactor 1 = 1 := by
  simp [zetaMomentArithmeticFactor, zetaMomentLocalFactor_one (abs_inv_prime_lt_one _)]

/-- At `k = 2` the local factor is `1 - x²`: `c_2(j) = j + 1`, and
`∑_j (j + 1)² xʲ = (1 + x)/(1 - x)³`. At `x = 1/2` this is the local factor `3/4` at `p = 2`. -/
theorem zetaMomentLocalFactor_two {x : ℝ} (hx : |x| < 1) :
    zetaMomentLocalFactor 2 x = 1 - x ^ 2 := by
  have hx' : ‖x‖ < 1 := by rwa [Real.norm_eq_abs]
  -- `(j + 1)² = 2 (j + 2).choose 2 - (j + 1).choose 1`.
  have h := ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hx').mul_left 2).sub
    (hasSum_choose_mul_geometric_of_norm_lt_one 1 hx')
  have hS : ₂F₁ (2 : ℝ) 2 1 x = 2 * (1 / (1 - x) ^ 3) - 1 / (1 - x) ^ 2 := by
    refine (hasSum_multichoose_sq_mul_pow (2 : ℝ) hx').unique (h.congr_fun fun j ↦ ?_)
    rw [Ring.multichoose_two, Nat.cast_choose_two, Nat.choose_one_right]
    push_cast
    ring
  have hx₁ : 1 - x ≠ 0 := by linarith [le_abs_self x]
  rw [zetaMomentLocalFactor, hS, show (2 : ℝ) ^ 2 = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]
  field_simp [hx₁]
  ring

/-- `a(2) = 1/ζ(2) = 6/π²`, by the Euler product of the Riemann zeta function. -/
theorem zetaMomentArithmeticFactor_two : zetaMomentArithmeticFactor 2 = 6 / π ^ 2 := by
  -- The real product `∏_p (1 - p⁻²)`, read in `ℂ`, is the inverse of the Euler product of `ζ(2)`.
  have hreal := (hasProd_zetaMomentArithmeticFactor 2).map Complex.ofRealHom
    Complex.continuous_ofReal
  have heuler := (riemannZeta_eulerProduct_hasProd (s := 2) (by norm_num)).inv₀
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  simp only [inv_inv] at heuler
  have hfun : (Complex.ofRealHom ∘ fun p : Nat.Primes ↦
      zetaMomentLocalFactor 2 (p : ℝ)⁻¹) = fun p : Nat.Primes ↦ 1 - (p : ℂ) ^ (-(2 : ℂ)) := by
    ext p
    simp only [Function.comp_apply, zetaMomentLocalFactor_two (abs_inv_prime_lt_one p),
      Complex.cpow_neg, Complex.cpow_ofNat, Complex.ofRealHom_eq_coe]
    push_cast
    rw [inv_pow]
  rw [hfun] at hreal
  have h := hreal.unique heuler
  simp only [Complex.ofRealHom_eq_coe, riemannZeta_two] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  field_simp

/-! ### The Barnes factor -/

/-- The Barnes factor `g(k)` of the zeta moment conjecture: the real part of
`G(k + 1)² / G(2k + 1)`, which is itself real (`TauCeti.ofReal_zetaMomentBarnesFactor`). -/
noncomputable def zetaMomentBarnesFactor (k : ℝ) : ℝ :=
  (barnesG ((k : ℂ) + 1) ^ 2 / barnesG (2 * (k : ℂ) + 1)).re

/-- The Barnes quotient `G(k + 1)² / G(2k + 1)` is real for real `k`, with value `g(k)`. -/
theorem ofReal_zetaMomentBarnesFactor (k : ℝ) :
    (zetaMomentBarnesFactor k : ℂ) = barnesG ((k : ℂ) + 1) ^ 2 / barnesG (2 * (k : ℂ) + 1) := by
  rw [zetaMomentBarnesFactor, ← Complex.conj_eq_iff_re, map_div₀, map_pow, ← barnesG_conj,
    ← barnesG_conj]
  simp [Complex.conj_ofReal, map_ofNat]

/-- The Barnes factor `g(k)` is positive for `k > -1/2`. -/
theorem zetaMomentBarnesFactor_pos {k : ℝ} (hk : -1 / 2 < k) : 0 < zetaMomentBarnesFactor k := by
  have h₁ : barnesG ((k : ℂ) + 1) = ((barnesG ((k + 1 : ℝ) : ℂ)).re : ℂ) := by
    simpa using barnesG_ofReal_eq_re (k + 1)
  have h₂ : barnesG (2 * (k : ℂ) + 1) = ((barnesG ((2 * k + 1 : ℝ) : ℂ)).re : ℂ) := by
    simpa using barnesG_ofReal_eq_re (2 * k + 1)
  rw [zetaMomentBarnesFactor, h₁, h₂, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    Complex.ofReal_re]
  exact div_pos (pow_pos (barnesG_ofReal_re_pos (by linarith)) 2)
    (barnesG_ofReal_re_pos (by linarith))

/-- At a natural number `n`, `g(n) = ∏_{j < n} j! / (j + n)!`. -/
theorem zetaMomentBarnesFactor_natCast (n : ℕ) :
    zetaMomentBarnesFactor n = ∏ j ∈ Finset.range n, (j ! : ℝ) / (j + n)! := by
  -- `G(n + 1) = ∏_{j < n} j!` and `G(2n + 1) = ∏_{j < n} j! * ∏_{j < n} (n + j)!`.
  have hnum := barnesG_natCast_add_one n
  have hden : barnesG (2 * (n : ℂ) + 1) =
      (∏ j ∈ Finset.range n, (j ! : ℂ)) * ∏ j ∈ Finset.range n, ((n + j)! : ℂ) := by
    rw [show 2 * (n : ℂ) = ((n + n : ℕ) : ℂ) by push_cast; ring, barnesG_natCast_add_one,
      Finset.prod_range_add]
  have hP : (∏ j ∈ Finset.range n, (j ! : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ ↦ by exact_mod_cast j.factorial_ne_zero
  apply Complex.ofReal_injective
  rw [ofReal_zetaMomentBarnesFactor, Complex.ofReal_natCast, hnum, hden, Complex.ofReal_prod]
  push_cast
  rw [Finset.prod_div_distrib]
  field_simp
  simp_rw [Nat.add_comm n]

/-- `g(1) = 1`. -/
@[simp]
theorem zetaMomentBarnesFactor_one : zetaMomentBarnesFactor 1 = 1 := by
  simpa using zetaMomentBarnesFactor_natCast 1

/-- `g(2) = 1/12`. -/
theorem zetaMomentBarnesFactor_two : zetaMomentBarnesFactor 2 = 1 / 12 := by
  have h := zetaMomentBarnesFactor_natCast 2
  simp only [Nat.cast_ofNat, Finset.prod_range_succ, Finset.prod_range_zero] at h
  rw [h]
  norm_num [Nat.factorial]

/-- `g(3) = 1/8640 = 42/9!`. -/
theorem zetaMomentBarnesFactor_three : zetaMomentBarnesFactor 3 = 1 / 8640 := by
  have h := zetaMomentBarnesFactor_natCast 3
  simp only [Nat.cast_ofNat, Finset.prod_range_succ, Finset.prod_range_zero] at h
  rw [h]
  norm_num [Nat.factorial]

/-- `a(2) g(2) = 1/(2π²)`, the predicted leading coefficient of the fourth moment of `ζ` on the
critical line. -/
theorem zetaMomentArithmeticFactor_two_mul_zetaMomentBarnesFactor_two :
    zetaMomentArithmeticFactor 2 * zetaMomentBarnesFactor 2 = 1 / (2 * π ^ 2) := by
  rw [zetaMomentArithmeticFactor_two, zetaMomentBarnesFactor_two]
  field_simp
  norm_num

end TauCeti

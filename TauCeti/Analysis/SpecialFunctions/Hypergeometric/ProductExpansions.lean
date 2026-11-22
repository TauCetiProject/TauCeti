/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.Analytic.TaylorSeries
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Polynomial.Pochhammer
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Data.Nat.Choose.Cast
import TauCeti.Data.Nat.Factorial.Basic
import TauCeti.Data.Nat.Factorial.NatCast
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Product expansions of the Gauss hypergeometric function

This file proves the Cayley–Orr one-variable product expansion (DLMF 15.16.1–15.16.2) and the
Burchnall–Chaundy two-variable product expansion (DLMF 15.16.3) of the Gauss hypergeometric
function on their open convergence regions.

## Cayley–Orr and Burchnall–Chaundy product identities

For `a`, `b`, `c` in a field `𝕂`, `TauCeti.cayleyOrrCoeff a b c s` is the finite sum
$$A_s = \sum_{k=0}^s \frac{(c - a - b)_{s - k}}{(s - k)!} \frac{(2a)_k (2b)_k}{k! \, (2c - 1)_k},$$
where vanishing factorial or Pochhammer denominators evaluate to `0` via `0⁻¹ = 0` when
`CharZero 𝕂` fails or `2c - 1 ∈ -ℕ` (matching the classical Cauchy convolution coefficient when
`CharZero 𝕂` and `2c - 1 ∉ -ℕ`). Over `ℂ`, `cayleyOrrCoeff a b c` gives the power-series and Taylor
coefficients of `(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` on `‖z‖ < 1` (classical DLMF
15.16.2 when `2c - 1 ∉ -ℕ`, and matching termwise `0⁻¹ = 0` truncation when `2c - 1 ∈ -ℕ`). Over
any characteristic-zero field with `2c - 1 ∉ -ℕ`, creative telescoping (Zeilberger) with explicit
rational certificates shows both the Cauchy product of `₂F₁(a, b; c - 1/2; z)` with
`₂F₁(c - a, c - b; c + 1/2; z)` and `((c)_s / (c + 1/2)_s) A_s` satisfy the same second-order
recurrence and initial values, giving DLMF 15.16.1 on `‖z‖ < 1` over `RCLike` Banach algebras.

For `‖z‖ < 1`, `‖ζ‖ < 1`, and `‖z + ζ - z * ζ‖ < 1`, combining
`Complex.regularizedGaussHGFun_eq_sum_choose_mul_regularizedGaussHGFun` and
`Complex.hasSum_regularizedGaussHGFun_add` via absolute double summation near `0` and analytic
continuation across `{z | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1}` yields DLMF 15.16.3 for **all**
`a, b, c : ℂ` (including `c ∈ -ℕ`), and multiplying by `Γ(c)²` gives the `₂F₁` form when `c ∉ -ℕ`:
$$\mathbf{F}(a, b; c; z) \, \mathbf{F}(a, b; c; \zeta)
  = \sum_{s=0}^\infty \frac{(a)_s (b)_s (c - a)_s (c - b)_s}{s! \, \Gamma(c + s)} (z \zeta)^s \,
    \mathbf{F}(a + s, b + s; c + 2s; z + \zeta - z\zeta).$$

## Main definitions and results

* `TauCeti.cayleyOrrCoeff`: the Cayley–Orr coefficient sequence `A_s` over any field, together with
  `TauCeti.map_cayleyOrrCoeff`, initial/degenerate `@[simp]` lemmas, and
  `TauCeti.cayleyOrrCoeff_recurrence`.
* `TauCeti.sum_ordinaryHypergeometricCoefficient_mul_eq_div_mul_cayleyOrrCoeff`: the algebraic
  Cayley–Orr convolution identity over any characteristic-zero field.
* `TauCeti.hasFPowerSeriesOnBall_ordinaryHypergeometric_mul_ordinaryHypergeometric_sub`,
  `TauCeti.hasSum_ordinaryHypergeometric_mul_ordinaryHypergeometric_sub`: DLMF 15.16.1 Cayley–Orr
  product expansion on the unit ball over `RCLike` scalars.
* `Complex.hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric`,
  `Complex.hasSum_cayleyOrrCoeff_mul_pow`,
  `Complex.coeff_taylorSeries_one_sub_cpow_mul_ordinaryHypergeometric`,
  `Complex.eq_cayleyOrrCoeff_of_eventually_hasSum`: DLMF 15.16.2 generating-function expansion and
  coefficient characterizations.
* `Complex.hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun`,
  `Complex.hasSum_ordinaryHypergeometric_mul_ordinaryHypergeometric`: DLMF 15.16.3
  Burchnall–Chaundy two-variable product expansion in regularized and ordinary forms.

## References

* NIST Digital Library of Mathematical Functions, §15.16, equations 15.16.1–15.16.3.
* A. Cayley, *On a theorem relating to hypergeometric series*, Philos. Mag. (4) **16** (1858),
  356–357.
* W. McF. Orr, *Theorems relating to the product of two hypergeometric series*, Trans. Cambridge
  Philos. Soc. **17** (1899), 1–15.
* W. N. Bailey, *Generalized Hypergeometric Series*, Cambridge Univ. Press, 1935, §10.1.
* J. L. Burchnall and T. W. Chaundy, *Expansions of Appell's double hypergeometric functions*,
  Quart. J. Math. Oxford Ser. **11** (1940), 249–270.
* D. Zeilberger, *The method of creative telescoping*, J. Symbolic Comput. **11** (1991), 195–204.
-/

public section

open Filter Finset Polynomial
open scoped Nat Topology BigOperators

namespace TauCeti

/-! ### Algebraic Cayley–Orr coefficients and recurrence -/

/-- The `s`-th Cayley–Orr coefficient `A_s(a, b, c)` over a field `𝕂`. When `CharZero 𝕂` and
`2 * c - 1 ∉ -ℕ`, this is the classical `s`-th Cauchy product coefficient of the binomial series
for `(1 - z) ^ (a + b - c)` with `₂F₁(2a, 2b; 2c - 1; z)` (DLMF 15.16.2); for general `[Field 𝕂]`
or when `2 * c - 1 ∈ -ℕ`, summands with vanishing factorial or Pochhammer denominators evaluate
their inverses as `0` via `0⁻¹ = 0`. -/
noncomputable def cayleyOrrCoeff {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (s : ℕ) : 𝕂 :=
  ∑ k ∈ range (s + 1),
    ((s - k)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 (s - k)).eval (c - a - b) *
      ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) k

/-- Unfolding lemma for `cayleyOrrCoeff`. -/
theorem cayleyOrrCoeff_def {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (s : ℕ) :
    cayleyOrrCoeff a b c s =
      ∑ k ∈ range (s + 1),
        ((s - k)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 (s - k)).eval (c - a - b) *
          ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) k :=
  (rfl)

/-- Field homomorphisms commute with `cayleyOrrCoeff`. -/
@[simp]
theorem map_cayleyOrrCoeff {𝕂 L F : Type*} [Field 𝕂] [Field L] [FunLike F 𝕂 L]
    [RingHomClass F 𝕂 L] (f : F) (a b c : 𝕂) (s : ℕ) :
    f (cayleyOrrCoeff a b c s) = cayleyOrrCoeff (f a) (f b) (f c) s := by
  have hp (m : ℕ) (x : 𝕂) :
      f ((ascPochhammer 𝕂 m).eval x) = (ascPochhammer L m).eval (f x) := by
    simpa using (Polynomial.eval_map_apply (f := (f : 𝕂 →+* L)) (p := ascPochhammer 𝕂 m) x).symm
  simp [cayleyOrrCoeff_def, ordinaryHypergeometricCoefficient, hp, map_ofNat]

/-- The zeroth Cayley–Orr coefficient is `1`. -/
@[simp]
theorem cayleyOrrCoeff_zero {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) :
    cayleyOrrCoeff a b c 0 = 1 := by
  simp [cayleyOrrCoeff, ordinaryHypergeometricCoefficient]

/-- The first Cayley–Orr coefficient is `(c - a - b) + 4ab / (2c - 1)` (with `/ 0 = 0` when
`2c = 1`). -/
@[simp]
theorem cayleyOrrCoeff_one {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) :
    cayleyOrrCoeff a b c 1 = c - a - b + 4 * a * b / (2 * c - 1) := by
  rw [cayleyOrrCoeff_def, sum_range_succ, sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    inv_one, ascPochhammer_zero, Polynomial.eval_one, ascPochhammer_one, Polynomial.eval_X,
    ordinaryHypergeometricCoefficient, div_eq_mul_inv]
  ring

/-- The Cayley–Orr coefficients are symmetric in `a` and `b`. -/
theorem cayleyOrrCoeff_comm {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (s : ℕ) :
    cayleyOrrCoeff a b c s = cayleyOrrCoeff b a c s := by
  rw [cayleyOrrCoeff_def, cayleyOrrCoeff_def]
  refine sum_congr rfl fun k _ ↦ ?_
  have hsub : c - b - a = c - a - b := by ring
  simp only [ordinaryHypergeometricCoefficient, hsub]
  ring

/-- When `a = 0`, only the `k = 0` term of `cayleyOrrCoeff` survives, leaving
`(s!)⁻¹ * (c - b)_s`. -/
@[simp]
theorem cayleyOrrCoeff_zero_left {𝕂 : Type*} [Field 𝕂] (b c : 𝕂) (s : ℕ) :
    cayleyOrrCoeff 0 b c s = (s ! : 𝕂)⁻¹ * (ascPochhammer 𝕂 s).eval (c - b) := by
  rw [cayleyOrrCoeff_def, sum_eq_single 0]
  · simp [ordinaryHypergeometricCoefficient]
  · intro k _ hk
    simp [ordinaryHypergeometricCoefficient, ascPochhammer_ne_zero_eval_zero 𝕂 hk]
  · simp

/-- When `b = 0`, only the `k = 0` term of `cayleyOrrCoeff` survives, leaving
`(s!)⁻¹ * (c - a)_s`. -/
@[simp]
theorem cayleyOrrCoeff_zero_right {𝕂 : Type*} [Field 𝕂] (a c : 𝕂) (s : ℕ) :
    cayleyOrrCoeff a 0 c s = (s ! : 𝕂)⁻¹ * (ascPochhammer 𝕂 s).eval (c - a) := by
  rw [cayleyOrrCoeff_comm, cayleyOrrCoeff_zero_left]

/-- When `c = a + b`, the binomial factor reduces to `1` and `cayleyOrrCoeff a b (a + b) s` reduces
to the single hypergeometric coefficient
`ordinaryHypergeometricCoefficient (2a) (2b) (2(a + b) - 1) s`. -/
@[simp]
theorem cayleyOrrCoeff_add_self {𝕂 : Type*} [Field 𝕂] (a b : 𝕂) (s : ℕ) :
    cayleyOrrCoeff a b (a + b) s =
      ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * (a + b) - 1) s := by
  rw [cayleyOrrCoeff_def, sum_eq_single s]
  · simp
  · intro k hk hne
    have hpos : s - k ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (mem_range_succ_iff.mp hk) hne)
    have hsub : a + b - a - b = 0 := by ring
    rw [hsub, ascPochhammer_ne_zero_eval_zero 𝕂 hpos, mul_zero, zero_mul]
  · simp

section CayleyOrrRecurrence

private theorem sum_range_recurrence_of_cert {𝕂 : Type*} [CommRing 𝕂] {r₂ r₁ r₀ : 𝕂}
    {F : ℕ → ℕ → 𝕂} {C : ℕ → 𝕂} {n : ℕ} (hC0 : C 0 = 0)
    (hstep : ∀ k ≤ n, r₂ * F (n + 2) k + r₁ * F (n + 1) k + r₀ * F n k = C (k + 1) - C k)
    (hbd : C (n + 1) + r₂ * (F (n + 2) (n + 1) + F (n + 2) (n + 2)) +
      r₁ * F (n + 1) (n + 1) = 0) :
    r₂ * (∑ k ∈ range (n + 3), F (n + 2) k) + r₁ * (∑ k ∈ range (n + 2), F (n + 1) k) +
      r₀ * (∑ k ∈ range (n + 1), F n k) = 0 := by
  rw [sum_range_succ _ (n + 2), sum_range_succ _ (n + 1), sum_range_succ _ (n + 1)]
  have hsum : r₂ * (∑ k ∈ range (n + 1), F (n + 2) k) + r₁ * (∑ k ∈ range (n + 1), F (n + 1) k) +
      r₀ * (∑ k ∈ range (n + 1), F n k) = C (n + 1) := by
    simp only [mul_sum, ← sum_add_distrib]
    rw [sum_congr rfl fun k hk ↦ hstep k (mem_range_succ_iff.mp hk), sum_range_sub, hC0, sub_zero]
  linear_combination hsum + hbd

variable {𝕂 : Type*} [Field 𝕂]

private theorem two_mul_sub_one_add_ne_zero {c : 𝕂} (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m)
    (m : ℕ) : 2 * c - 1 + (m : 𝕂) ≠ 0 :=
  fun h ↦ hc m (by linear_combination h)

private theorem sub_half_add_ne_zero [CharZero 𝕂] {c : 𝕂} (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m)
    (m : ℕ) : c - 1 / 2 + (m : 𝕂) ≠ 0 :=
  fun h ↦ hc (2 * m) (by push_cast; linear_combination 2 * h)

private theorem add_half_add_ne_zero [CharZero 𝕂] {c : 𝕂} (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m)
    (m : ℕ) : c + 1 / 2 + (m : 𝕂) ≠ 0 :=
  fun h ↦ hc (2 * (m + 1)) (by push_cast; linear_combination 2 * h)

private theorem inv_factorial_eq_mul_inv_factorial_add_two [CharZero 𝕂] (n : ℕ) :
    (n ! : 𝕂)⁻¹ = ((n : 𝕂) + 1) * ((n : 𝕂) + 2) * ((n + 2)! : 𝕂)⁻¹ := by
  rw [Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ n,
    Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ (n + 1)]
  push_cast; ring

private theorem inv_ascPochhammer_eq_mul_inv_ascPochhammer_add_two {z : 𝕂} {n : ℕ}
    (hz0 : z + (n : 𝕂) ≠ 0) (hz1 : z + ((n + 1 : ℕ) : 𝕂) ≠ 0) :
    ((ascPochhammer 𝕂 n).eval z)⁻¹ =
      (z + n) * (z + n + 1) * ((ascPochhammer 𝕂 (n + 2)).eval z)⁻¹ := by
  rw [inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval hz0,
    inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval hz1]
  push_cast; ring

private theorem inv_factorial_mul_ascPochhammer_eq_add_two [CharZero 𝕂] (d : 𝕂) (l : ℕ) :
    (l ! : 𝕂)⁻¹ * (ascPochhammer 𝕂 l).eval d =
      ((l : 𝕂) + 1) * ((l : 𝕂) + 2) * (((l + 2)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 l).eval d) := by
  rw [inv_factorial_eq_mul_inv_factorial_add_two l]; ring

private theorem inv_factorial_mul_ascPochhammer_add_one_eq_add_two [CharZero 𝕂] (d : 𝕂) (l : ℕ) :
    ((l + 1)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 (l + 1)).eval d =
      ((l : 𝕂) + 2) * (d + l) * (((l + 2)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 l).eval d) := by
  rw [Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ (l + 1), ascPochhammer_succ_eval]
  push_cast; ring

private theorem inv_factorial_mul_ascPochhammer_add_two (d : 𝕂) (l : ℕ) :
    ((l + 2)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 (l + 2)).eval d =
      (d + l) * (d + l + 1) * (((l + 2)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 l).eval d) := by
  rw [ascPochhammer_succ_eval (l + 1) d, ascPochhammer_succ_eval l d]
  push_cast; ring

private theorem ordinaryHypergeometricCoefficient_eq_add_two [CharZero 𝕂] (x y : 𝕂) {z : 𝕂}
    {l : ℕ} (hz0 : z + (l : 𝕂) ≠ 0) (hz1 : z + ((l + 1 : ℕ) : 𝕂) ≠ 0) :
    ordinaryHypergeometricCoefficient x y z l =
      ((l : 𝕂) + 1) * ((l : 𝕂) + 2) * (z + l) * (z + l + 1) *
        ((ascPochhammer 𝕂 l).eval x * (ascPochhammer 𝕂 l).eval y *
          ((l + 2)! : 𝕂)⁻¹ * ((ascPochhammer 𝕂 (l + 2)).eval z)⁻¹) := by
  simp only [ordinaryHypergeometricCoefficient]
  rw [inv_factorial_eq_mul_inv_factorial_add_two l,
    inv_ascPochhammer_eq_mul_inv_ascPochhammer_add_two hz0 hz1]
  ring

private theorem ordinaryHypergeometricCoefficient_add_one_eq_add_two [CharZero 𝕂] (x y : 𝕂)
    {z : 𝕂} {l : ℕ} (hz1 : z + ((l + 1 : ℕ) : 𝕂) ≠ 0) :
    ordinaryHypergeometricCoefficient x y z (l + 1) =
      ((l : 𝕂) + 2) * (x + l) * (y + l) * (z + l + 1) *
        ((ascPochhammer 𝕂 l).eval x * (ascPochhammer 𝕂 l).eval y *
          ((l + 2)! : 𝕂)⁻¹ * ((ascPochhammer 𝕂 (l + 2)).eval z)⁻¹) := by
  simp only [ordinaryHypergeometricCoefficient]
  rw [Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ (l + 1),
    inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval hz1,
    ascPochhammer_succ_eval l x, ascPochhammer_succ_eval l y]
  push_cast; ring

private theorem ordinaryHypergeometricCoefficient_add_two_eq_add_two (x y z : 𝕂) (l : ℕ) :
    ordinaryHypergeometricCoefficient x y z (l + 2) =
      (x + l) * (x + l + 1) * (y + l) * (y + l + 1) *
        ((ascPochhammer 𝕂 l).eval x * (ascPochhammer 𝕂 l).eval y *
          ((l + 2)! : 𝕂)⁻¹ * ((ascPochhammer 𝕂 (l + 2)).eval z)⁻¹) := by
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval]
  push_cast; ring

private theorem ascPochhammer_div_eq_add_two (x : 𝕂) {y : 𝕂} {n : ℕ}
    (hy0 : y + (n : 𝕂) ≠ 0) (hy1 : y + ((n + 1 : ℕ) : 𝕂) ≠ 0) :
    (ascPochhammer 𝕂 n).eval x / (ascPochhammer 𝕂 n).eval y =
      (y + n) * (y + n + 1) *
        ((ascPochhammer 𝕂 n).eval x * ((ascPochhammer 𝕂 (n + 2)).eval y)⁻¹) := by
  simp only [div_eq_mul_inv]
  rw [inv_ascPochhammer_eq_mul_inv_ascPochhammer_add_two hy0 hy1]
  ring

private theorem ascPochhammer_div_add_one_eq_add_two (x : 𝕂) {y : 𝕂} {n : ℕ}
    (hy1 : y + ((n + 1 : ℕ) : 𝕂) ≠ 0) :
    (ascPochhammer 𝕂 (n + 1)).eval x / (ascPochhammer 𝕂 (n + 1)).eval y =
      (x + n) * (y + n + 1) *
        ((ascPochhammer 𝕂 n).eval x * ((ascPochhammer 𝕂 (n + 2)).eval y)⁻¹) := by
  simp only [div_eq_mul_inv]
  rw [inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval hy1, ascPochhammer_succ_eval n x]
  push_cast; ring

private theorem ascPochhammer_div_add_two_eq_add_two (x y : 𝕂) (n : ℕ) :
    (ascPochhammer 𝕂 (n + 2)).eval x / (ascPochhammer 𝕂 (n + 2)).eval y =
      (x + n) * (x + n + 1) *
        ((ascPochhammer 𝕂 n).eval x * ((ascPochhammer 𝕂 (n + 2)).eval y)⁻¹) := by
  simp only [div_eq_mul_inv, ascPochhammer_succ_eval]
  push_cast; ring

private def cayleyRecR2 (c : 𝕂) (n : ℕ) : 𝕂 := (n + 2) * (n + 2 * c)

private def cayleyRecR1 (a b c : 𝕂) (n : ℕ) : 𝕂 :=
  -2 * (n + 1) * n - 4 * c * (n + 1) + (a + b - c) * (2 * c - 1) - 4 * a * b

private def cayleyRecR0 (a b c : 𝕂) (n : ℕ) : 𝕂 := (n + c + a - b) * (n + c - a + b)

private noncomputable def cayleySummand (a b c : 𝕂) (s k : ℕ) : 𝕂 :=
  ((s - k)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 (s - k)).eval (c - a - b) *
    ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) k

private noncomputable def cayleyCertH (a b c : 𝕂) (n : ℕ) : ℕ → 𝕂
  | 0 => 0
  | j + 1 =>
      (a + b - c + 1) * (ascPochhammer 𝕂 (n - j)).eval (c - a - b) *
        (ascPochhammer 𝕂 (j + 1)).eval (2 * a) * (ascPochhammer 𝕂 (j + 1)).eval (2 * b) *
        (j ! : 𝕂)⁻¹ * ((n + 1 - j)! : 𝕂)⁻¹ * ((ascPochhammer 𝕂 j).eval (2 * c - 1))⁻¹

private theorem succ_add_sub_succ (j l : ℕ) : j + 1 + l - (j + 1) = l :=
  Nat.add_sub_cancel_left (j + 1) l

private theorem succ_add_add_sub_succ (j l m : ℕ) : j + 1 + l + m - (j + 1) = l + m := by
  omega

private theorem succ_add_sub_self (j l : ℕ) : j + 1 + l - j = l + 1 := by
  omega

private theorem succ_add_one_sub_self (j l : ℕ) : j + 1 + l + 1 - j = l + 2 := by
  omega

private theorem add_two_sub_add_one (n : ℕ) : n + 2 - (n + 1) = 1 := by
  omega

private theorem add_one_sub_self (n : ℕ) : n + 1 - n = 1 :=
  Nat.add_sub_cancel_left n 1

private theorem cayleyOrrCoeff_eq_sum_cayleySummand (a b c : 𝕂) (s : ℕ) :
    cayleyOrrCoeff a b c s = ∑ k ∈ range (s + 1), cayleySummand a b c s k := by
  simp only [cayleyOrrCoeff_def, cayleySummand]

private theorem cayleySummand_step [CharZero 𝕂] (a b : 𝕂) {c : 𝕂} (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m)
    {n k : ℕ} (hk : k ≤ n) :
    cayleyRecR2 c n * cayleySummand a b c (n + 2) k +
      cayleyRecR1 a b c n * cayleySummand a b c (n + 1) k +
      cayleyRecR0 a b c n * cayleySummand a b c n k =
      cayleyCertH a b c n (k + 1) - cayleyCertH a b c n k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero =>
    rw [zero_add]
    simp only [cayleySummand, cayleyCertH, Nat.sub_zero, zero_add,
      ordinaryHypergeometricCoefficient]
    rw [inv_factorial_mul_ascPochhammer_eq_add_two (c - a - b) l,
      inv_factorial_mul_ascPochhammer_add_one_eq_add_two (c - a - b) l,
      inv_factorial_mul_ascPochhammer_add_two (c - a - b) l,
      Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ (l + 1),
      ascPochhammer_succ_eval 0 (2 * a), ascPochhammer_succ_eval 0 (2 * b)]
    simp only [ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.cast_add,
      Nat.cast_one, Nat.cast_zero, inv_one]
    dsimp only [cayleyRecR2, cayleyRecR1, cayleyRecR0]
    ring
  | succ j =>
    simp only [cayleySummand, cayleyCertH, succ_add_sub_succ, succ_add_add_sub_succ,
      succ_add_sub_self, succ_add_one_sub_self]
    rw [inv_factorial_mul_ascPochhammer_eq_add_two (c - a - b) l,
      inv_factorial_mul_ascPochhammer_add_one_eq_add_two (c - a - b) l,
      inv_factorial_mul_ascPochhammer_add_two (c - a - b) l,
      Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ j,
      Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ (l + 1),
      inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval
        (two_mul_sub_one_add_ne_zero hc j),
      ascPochhammer_succ_eval l (c - a - b),
      ascPochhammer_succ_eval (j + 1) (2 * a), ascPochhammer_succ_eval (j + 1) (2 * b)]
    dsimp only [cayleyRecR2, cayleyRecR1, cayleyRecR0, ordinaryHypergeometricCoefficient]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem cayleyOrrCoeff_recurrence_aux [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) (n : ℕ) :
    cayleyRecR2 c n * cayleyOrrCoeff a b c (n + 2) +
      cayleyRecR1 a b c n * cayleyOrrCoeff a b c (n + 1) +
      cayleyRecR0 a b c n * cayleyOrrCoeff a b c n = 0 := by
  simp only [cayleyOrrCoeff_eq_sum_cayleySummand]
  refine sum_range_recurrence_of_cert (F := cayleySummand a b c) (C := cayleyCertH a b c n)
    (by simp [cayleyCertH]) (fun k hk ↦ cayleySummand_step a b hc hk) ?_
  simp only [cayleyCertH, cayleySummand, Nat.sub_self, add_two_sub_add_one, add_one_sub_self]
  rw [ordinaryHypergeometricCoefficient_add_one_eq_add_two (2 * a) (2 * b)
      (two_mul_sub_one_add_ne_zero hc (n + 1)),
    ordinaryHypergeometricCoefficient_add_two_eq_add_two,
    inv_factorial_eq_mul_inv_factorial_add_two n,
    inv_ascPochhammer_eq_mul_inv_ascPochhammer_add_two
      (two_mul_sub_one_add_ne_zero hc n) (two_mul_sub_one_add_ne_zero hc (n + 1)),
    ascPochhammer_succ_eval n (2 * a), ascPochhammer_succ_eval n (2 * b),
    ascPochhammer_succ_eval 0 (c - a - b)]
  simp only [ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, Nat.cast_zero, inv_one]
  dsimp only [cayleyRecR2, cayleyRecR1]
  ring

/-- **Three-term recurrence for the Cayley–Orr coefficients.** Over any characteristic-zero field
`𝕂`, when `2 * c - 1` avoids the nonpositive integers, `cayleyOrrCoeff a b c` satisfies the
second-order polynomial recurrence
`(n + 2)(n + 2c) A_{n + 2} + (-2(n + 1)n - 4c(n + 1) + (a + b - c)(2c - 1) - 4ab) A_{n + 1} +
(n + c + a - b)(n + c - a + b) A_n = 0`. -/
theorem cayleyOrrCoeff_recurrence [CharZero 𝕂] (a b : 𝕂) {c : 𝕂} (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m)
    (n : ℕ) :
    ((n : 𝕂) + 2) * (n + 2 * c) * cayleyOrrCoeff a b c (n + 2) +
      (-2 * (n + 1) * n - 4 * c * (n + 1) + (a + b - c) * (2 * c - 1) - 4 * a * b) *
        cayleyOrrCoeff a b c (n + 1) +
      (n + c + a - b) * (n + c - a + b) * cayleyOrrCoeff a b c n = 0 := by
  simpa only [cayleyRecR2, cayleyRecR1, cayleyRecR0] using cayleyOrrCoeff_recurrence_aux a b hc n

private def cayleyRecQ2 (c : 𝕂) (n : ℕ) : 𝕂 := cayleyRecR2 c n * (c + n + 1 / 2) * (c + n + 3 / 2)

private def cayleyRecQ1 (a b c : 𝕂) (n : ℕ) : 𝕂 :=
  cayleyRecR1 a b c n * (c + n + 1 / 2) * (c + n + 1)

private def cayleyRecQ0 (a b c : 𝕂) (n : ℕ) : 𝕂 := cayleyRecR0 a b c n * (c + n) * (c + n + 1)

private def cayleyCertPolyAux (s₁ s₂ d m kp : 𝕂) : 𝕂 :=
  ((m + 1 + 2 * d * (s₁ + m - d)) * kp ^ 2 +
    (s₁ * (m + 1 - d) - d * (2 * m + 1) * (3 * d + 1) + 6 * d ^ 2 * (d - s₁) + 4 * s₂ * d) * kp +
    (s₂ * ((m + 1) * (1 - 2 * d) - 2 * d * (2 * d + 1)) -
      2 * s₁ * d * (m + 1 - d - 2 * d ^ 2) +
      d * ((2 * d - 1) * (m + 1) + 2 * d ^ 2 * (2 * m + 1 - 2 * d)))) / 2

private def cayleyCertPoly (a b c : 𝕂) (n j : ℕ) : 𝕂 :=
  cayleyCertPolyAux (a + b) (a * b) (c + (n + 1)) (n + 1) (j + 1)

private noncomputable def cayleyConvTerm (a b c : 𝕂) (s k : ℕ) : 𝕂 :=
  ordinaryHypergeometricCoefficient a b (c - 1 / 2) k *
    ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2) (s - k)

private noncomputable def cayleyConvSum (a b c : 𝕂) (s : ℕ) : 𝕂 :=
  ∑ k ∈ range (s + 1), cayleyConvTerm a b c s k

private noncomputable def cayleyRhs (a b c : 𝕂) (s : ℕ) : 𝕂 :=
  (ascPochhammer 𝕂 s).eval c / (ascPochhammer 𝕂 s).eval (c + 1 / 2) * cayleyOrrCoeff a b c s

private noncomputable def cayleyCertG (a b c : 𝕂) (n : ℕ) : ℕ → 𝕂
  | 0 => 0
  | j + 1 =>
      cayleyCertPoly a b c n j * (ascPochhammer 𝕂 (j + 1)).eval a *
        (ascPochhammer 𝕂 (j + 1)).eval b * (ascPochhammer 𝕂 (n - j)).eval (c - a) *
        (ascPochhammer 𝕂 (n - j)).eval (c - b) *
        (j ! : 𝕂)⁻¹ * ((n + 1 - j)! : 𝕂)⁻¹ * ((ascPochhammer 𝕂 j).eval (c - 1 / 2))⁻¹ *
        ((ascPochhammer 𝕂 (n + 1 - j)).eval (c + 1 / 2))⁻¹

private theorem cayleyConvTerm_step [CharZero 𝕂] (a b : 𝕂) {c : 𝕂} (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m)
    {n k : ℕ} (hk : k ≤ n) :
    cayleyRecQ2 c n * cayleyConvTerm a b c (n + 2) k +
      cayleyRecQ1 a b c n * cayleyConvTerm a b c (n + 1) k +
      cayleyRecQ0 a b c n * cayleyConvTerm a b c n k =
      cayleyCertG a b c n (k + 1) - cayleyCertG a b c n k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hadd1 := add_half_add_ne_zero hc l
  have hadd2 := add_half_add_ne_zero hc (l + 1)
  cases k with
  | zero =>
    rw [zero_add]
    simp only [cayleyConvTerm, cayleyCertG, Nat.sub_zero, zero_add]
    rw [ordinaryHypergeometricCoefficient_eq_add_two (c - a) (c - b) hadd1 hadd2,
      ordinaryHypergeometricCoefficient_add_one_eq_add_two (c - a) (c - b) hadd2,
      ordinaryHypergeometricCoefficient_add_two_eq_add_two,
      Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ (l + 1),
      inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval hadd2,
      ascPochhammer_succ_eval 0 a, ascPochhammer_succ_eval 0 b]
    simp only [ordinaryHypergeometricCoefficient, ascPochhammer_zero, Polynomial.eval_one,
      Nat.factorial_zero, inv_one, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    dsimp only [cayleyRecQ2, cayleyRecQ1, cayleyRecQ0, cayleyRecR2, cayleyRecR1, cayleyRecR0,
      cayleyCertPoly, cayleyCertPolyAux]
    ring
  | succ j =>
    simp only [cayleyConvTerm, cayleyCertG, succ_add_sub_succ, succ_add_add_sub_succ,
      succ_add_sub_self, succ_add_one_sub_self]
    rw [ordinaryHypergeometricCoefficient_eq_add_two (c - a) (c - b) hadd1 hadd2,
      ordinaryHypergeometricCoefficient_add_one_eq_add_two (c - a) (c - b) hadd2,
      ordinaryHypergeometricCoefficient_add_two_eq_add_two,
      Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ j,
      Nat.inv_factorial_eq_add_one_mul_inv_factorial_succ (l + 1),
      inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval (sub_half_add_ne_zero hc j),
      inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval hadd2,
      ascPochhammer_succ_eval l (c - a), ascPochhammer_succ_eval l (c - b),
      ascPochhammer_succ_eval (j + 1) a, ascPochhammer_succ_eval (j + 1) b]
    dsimp only [cayleyRecQ2, cayleyRecQ1, cayleyRecQ0, cayleyRecR2, cayleyRecR1, cayleyRecR0,
      cayleyCertPoly, cayleyCertPolyAux, ordinaryHypergeometricCoefficient]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem cayleyConvSum_recurrence [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) (n : ℕ) :
    cayleyRecQ2 c n * cayleyConvSum a b c (n + 2) +
      cayleyRecQ1 a b c n * cayleyConvSum a b c (n + 1) +
      cayleyRecQ0 a b c n * cayleyConvSum a b c n = 0 := by
  simp only [cayleyConvSum]
  refine sum_range_recurrence_of_cert (F := cayleyConvTerm a b c) (C := cayleyCertG a b c n)
    (by simp [cayleyCertG]) (fun k hk ↦ cayleyConvTerm_step a b hc hk) ?_
  simp only [cayleyCertG, cayleyConvTerm, Nat.sub_self, add_two_sub_add_one, add_one_sub_self]
  rw [ordinaryHypergeometricCoefficient_add_one_eq_add_two a b (sub_half_add_ne_zero hc (n + 1)),
    ordinaryHypergeometricCoefficient_add_two_eq_add_two,
    inv_factorial_eq_mul_inv_factorial_add_two n,
    inv_ascPochhammer_eq_mul_inv_ascPochhammer_add_two
      (sub_half_add_ne_zero hc n) (sub_half_add_ne_zero hc (n + 1))]
  dsimp only [ordinaryHypergeometricCoefficient]
  rw [inv_ascPochhammer_eval_eq_mul_inv_ascPochhammer_succ_eval (add_half_add_ne_zero hc 0),
    ascPochhammer_succ_eval n a, ascPochhammer_succ_eval n b,
    ascPochhammer_succ_eval 0 (c - a), ascPochhammer_succ_eval 0 (c - b)]
  simp only [ascPochhammer_zero, Polynomial.eval_one, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, Nat.cast_zero, inv_one]
  dsimp only [cayleyRecQ2, cayleyRecQ1, cayleyRecR2, cayleyRecR1, cayleyCertPoly,
    cayleyCertPolyAux]
  ring

private theorem cayleyRhs_recurrence [CharZero 𝕂] (a b : 𝕂) {c : 𝕂} (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m)
    (n : ℕ) :
    cayleyRecQ2 c n * cayleyRhs a b c (n + 2) + cayleyRecQ1 a b c n * cayleyRhs a b c (n + 1) +
      cayleyRecQ0 a b c n * cayleyRhs a b c n = 0 := by
  have hrec := cayleyOrrCoeff_recurrence a b hc n
  dsimp only [cayleyRhs]
  rw [ascPochhammer_div_eq_add_two c (add_half_add_ne_zero hc n) (add_half_add_ne_zero hc (n + 1)),
    ascPochhammer_div_add_one_eq_add_two c (add_half_add_ne_zero hc (n + 1)),
    ascPochhammer_div_add_two_eq_add_two]
  dsimp only [cayleyRecQ2, cayleyRecQ1, cayleyRecQ0, cayleyRecR2, cayleyRecR1, cayleyRecR0]
  calc
    _ = (ascPochhammer 𝕂 n).eval c * (c + n) * (c + n + 1) *
          (c + 1 / 2 + n) * (c + n + 3 / 2) * ((ascPochhammer 𝕂 (n + 2)).eval (c + 1 / 2))⁻¹ *
          (((n : 𝕂) + 2) * (n + 2 * c) * cayleyOrrCoeff a b c (n + 2) +
            (-2 * (n + 1) * n - 4 * c * (n + 1) + (a + b - c) * (2 * c - 1) - 4 * a * b) *
              cayleyOrrCoeff a b c (n + 1) +
            (n + c + a - b) * (n + c - a + b) * cayleyOrrCoeff a b c n) := by ring
    _ = 0 := by rw [hrec, mul_zero]

private theorem cayleyConvSum_one [CharZero 𝕂] (a b : 𝕂) {c : 𝕂} (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) :
    cayleyConvSum a b c 1 = cayleyRhs a b c 1 := by
  have hw : 2 * c - 1 ≠ 0 := by simpa using two_mul_sub_one_add_ne_zero hc 0
  have hv : c - 1 / 2 ≠ 0 := by simpa using sub_half_add_ne_zero hc 0
  have hu : c + 1 / 2 ≠ 0 := by simpa using add_half_add_ne_zero hc 0
  rw [cayleyConvSum, cayleyRhs, sum_range_succ, sum_range_one, cayleyOrrCoeff_one]
  simp only [cayleyConvTerm, ordinaryHypergeometricCoefficient, ascPochhammer_zero,
    Polynomial.eval_one, ascPochhammer_one, Polynomial.eval_X, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, Nat.sub_zero, Nat.sub_self]
  generalize hu_eq : c + 1 / 2 = u at hu ⊢
  generalize hv_eq : c - 1 / 2 = v at hv ⊢
  generalize hw_eq : 2 * c - 1 = w at hw ⊢
  field_simp
  subst hu_eq hv_eq hw_eq; ring

private theorem cayleyConvSum_eq_cayleyRhs [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ n : ℕ, 2 * c - 1 ≠ -n) (s : ℕ) :
    cayleyConvSum a b c s = cayleyRhs a b c s := by
  suffices ∀ m : ℕ,
      cayleyConvSum a b c m = cayleyRhs a b c m ∧
        cayleyConvSum a b c (m + 1) = cayleyRhs a b c (m + 1) from (this s).1
  intro m
  induction m with
  | zero =>
    refine ⟨?_, cayleyConvSum_one a b hc⟩
    simp [cayleyConvSum, cayleyRhs, cayleyConvTerm, ordinaryHypergeometricCoefficient]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hS := cayleyConvSum_recurrence a b hc n
    have hB := cayleyRhs_recurrence a b hc n
    have hn2 : (n : 𝕂) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    have h2c : (n : 𝕂) + 2 * c ≠ 0 := fun h ↦
      two_mul_sub_one_add_ne_zero hc (n + 1) (by push_cast; linear_combination h)
    have hq2 : cayleyRecQ2 c n ≠ 0 := by
      simp only [cayleyRecQ2, cayleyRecR2]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero hn2 h2c) ?_) ?_
      · simpa only [add_right_comm] using add_half_add_ne_zero hc n
      · exact fun h ↦ add_half_add_ne_zero hc (n + 1) (by push_cast; linear_combination h)
    have hdiff : cayleyRecQ2 c n * (cayleyConvSum a b c (n + 2) - cayleyRhs a b c (n + 2)) = 0 := by
      rw [ih.1, ih.2] at hS
      linear_combination hS - hB
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hq2)

end CayleyOrrRecurrence

/-- **Algebraic Cayley–Orr coefficient identity (DLMF 15.16.1–15.16.2).** Over any field `𝕂` of
characteristic zero, if `2 * c - 1` avoids the nonpositive integers, the Cauchy product of the
hypergeometric coefficients of `₂F₁(a, b; c - 1/2; z)` and `₂F₁(c - a, c - b; c + 1/2; z)` equals
`((c)_s / (c + 1/2)_s) * cayleyOrrCoeff a b c s`. -/
theorem sum_ordinaryHypergeometricCoefficient_mul_eq_div_mul_cayleyOrrCoeff {𝕂 : Type*} [Field 𝕂]
    [CharZero 𝕂] (a b : 𝕂) {c : 𝕂} (hc : ∀ n : ℕ, 2 * c - 1 ≠ -n) (s : ℕ) :
    ∑ k ∈ range (s + 1),
      ordinaryHypergeometricCoefficient a b (c - 1 / 2) k *
        ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2) (s - k) =
      (ascPochhammer 𝕂 s).eval c / (ascPochhammer 𝕂 s).eval (c + 1 / 2) *
        cayleyOrrCoeff a b c s := by
  simpa only [cayleyConvSum, cayleyConvTerm, cayleyRhs] using cayleyConvSum_eq_cayleyRhs a b hc s

/-! ### Analytic Cayley–Orr product expansion over `RCLike` scalars (DLMF 15.16.1) -/

/-- **Cayley–Orr product expansion on the unit ball (DLMF 15.16.1, `HasFPowerSeriesOnBall` form).**
In any Banach division algebra `𝔸` over an `RCLike` scalar field `𝕂`, when `2 * c - 1` avoids the
nonpositive integers, `₂F₁(a, b; c - 1/2; z) * ₂F₁(c - a, c - b; c + 1/2; z)` is represented on the
open unit ball around `0` by the scalar power series with coefficients
`((c)_s / (c + 1/2)_s) * cayleyOrrCoeff a b c s`. -/
theorem hasFPowerSeriesOnBall_ordinaryHypergeometric_mul_ordinaryHypergeometric_sub
    {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    [CompleteSpace 𝔸] (a b : 𝕂) {c : 𝕂} (hc : ∀ n : ℕ, 2 * c - 1 ≠ -n) :
    HasFPowerSeriesOnBall
      (fun z : 𝔸 ↦ ₂F₁ a b (c - 1 / 2) z * ₂F₁ (c - a) (c - b) (c + 1 / 2) z)
      (FormalMultilinearSeries.ofScalars 𝔸 fun s : ℕ ↦
        (ascPochhammer 𝕂 s).eval c / (ascPochhammer 𝕂 s).eval (c + 1 / 2) *
          cayleyOrrCoeff a b c s) 0 1 := by
  simpa only [sum_ordinaryHypergeometricCoefficient_mul_eq_div_mul_cayleyOrrCoeff a b hc] using
    (hasFPowerSeriesOnBall_ordinaryHypergeometric 𝔸 a b (c - 1 / 2)).mul_ofScalars
      (hasFPowerSeriesOnBall_ordinaryHypergeometric 𝔸 (c - a) (c - b) (c + 1 / 2))

/-- **Cayley–Orr product expansion (DLMF 15.16.1, `HasSum` form).** Over any `RCLike` field `𝕂`
(such as `ℝ` or `ℂ`), for `‖z‖ < 1` and `2 * c - 1 ∉ -ℕ`,
`₂F₁(a, b; c - 1/2; z) * ₂F₁(c - a, c - b; c + 1/2; z)` expands as
`∑ s, ((c)_s / (c + 1/2)_s) * cayleyOrrCoeff a b c s * z ^ s`. -/
theorem hasSum_ordinaryHypergeometric_mul_ordinaryHypergeometric_sub {𝕂 : Type*} [RCLike 𝕂]
    (a b : 𝕂) {c z : 𝕂} (hc : ∀ n : ℕ, 2 * c - 1 ≠ -n) (hz : ‖z‖ < 1) :
    HasSum
      (fun s : ℕ ↦ (ascPochhammer 𝕂 s).eval c / (ascPochhammer 𝕂 s).eval (c + 1 / 2) *
        cayleyOrrCoeff a b c s * z ^ s)
      (₂F₁ a b (c - 1 / 2) z * ₂F₁ (c - a) (c - b) (c + 1 / 2) z) := by
  have hz' : z ∈ Metric.eball (0 : 𝕂) 1 := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using hz
  have hs := (hasFPowerSeriesOnBall_ordinaryHypergeometric_mul_ordinaryHypergeometric_sub 𝕂
    a b hc).hasSum hz'
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hs

end TauCeti

namespace Complex

/-! ### Generating function of the Cayley–Orr coefficients (DLMF 15.16.2) -/

/-- **Generating function of the Cayley–Orr coefficients (DLMF 15.16.2).** On the open unit disk,
`(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` is represented by the scalar power series with
coefficients `TauCeti.cayleyOrrCoeff a b c`. Classical DLMF 15.16.2 requires `2 * c - 1 ∉ -ℕ`
(outside terminating cases); at `2 * c - 1 ∈ -ℕ` both `₂F₁(2a, 2b; 2c - 1; z)` and
`TauCeti.cayleyOrrCoeff` zero out summands with `(2 * c - 1)_k = 0` via `0⁻¹ = 0`. -/
theorem hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric (a b c : ℂ) :
    HasFPowerSeriesOnBall
      (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)
      (FormalMultilinearSeries.ofScalars ℂ (TauCeti.cayleyOrrCoeff a b c)) 0 1 := by
  have h1 := one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (c - a - b)
  have h2 := TauCeti.hasFPowerSeriesOnBall_ordinaryHypergeometric ℂ (2 * a) (2 * b) (2 * c - 1)
  have hmul := h1.mul_ofScalars h2
  have hchoose (j : ℕ) :
      Ring.choose (c - a - b + j - 1) j = (j ! : ℂ)⁻¹ * (ascPochhammer ℂ j).eval (c - a - b) := by
    have hsub : c - a - b + j - 1 - j + 1 = c - a - b := by ring
    rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer, hsub,
      Polynomial.ascPochhammer_smeval_eq_eval, smul_eq_mul]
  have hser :
      (FormalMultilinearSeries.ofScalars ℂ fun s ↦
        ∑ k ∈ range (s + 1), Ring.choose (c - a - b + k - 1) k *
          ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) (s - k)) =
      FormalMultilinearSeries.ofScalars ℂ (TauCeti.cayleyOrrCoeff a b c) := by
    congr 1; ext s; rw [TauCeti.cayleyOrrCoeff_def, ← sum_range_reflect]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [Nat.add_succ_sub_one, add_zero, Nat.sub_sub_self (mem_range_succ_iff.mp hk), hchoose]
  rw [hser] at hmul
  refine hmul.congr fun z _ ↦ ?_
  dsimp only
  have hneg : -(c - a - b) = a + b - c := by ring
  rw [one_div, ← cpow_neg, hneg]

/-- **DLMF 15.16.2 (`HasSum` form).** For `‖z‖ < 1`, the power series
`∑ s, cayleyOrrCoeff a b c s * z ^ s` converges to
`(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)`. Classical DLMF 15.16.2 requires `2 * c - 1 ∉ -ℕ`
(outside terminating cases); at `2 * c - 1 ∈ -ℕ` both sides zero out summands with
`(2 * c - 1)_k = 0` via `0⁻¹ = 0`. -/
theorem hasSum_cayleyOrrCoeff_mul_pow (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun s : ℕ ↦ TauCeti.cayleyOrrCoeff a b c s * z ^ s)
      ((1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z) := by
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using hz
  have hs := (hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric a b c).hasSum hz'
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hs

/-- The Taylor coefficients at `0` of `(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` are
`TauCeti.cayleyOrrCoeff a b c` (DLMF 15.16.2; classical when `2 * c - 1 ∉ -ℕ`, and reflecting
`0⁻¹ = 0` truncation of summands with `(2 * c - 1)_k = 0` when `2 * c - 1 ∈ -ℕ`). -/
theorem coeff_taylorSeries_one_sub_cpow_mul_ordinaryHypergeometric (a b c : ℂ) (s : ℕ) :
    PowerSeries.coeff s
      (TauCeti.taylorSeries
        (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z) 0) =
      TauCeti.cayleyOrrCoeff a b c s := by
  rw [(hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric
    a b c).hasFPowerSeriesAt.coeff_taylorSeries, FormalMultilinearSeries.coeff_ofScalars]

/-- Uniqueness of the generating-function coefficients in DLMF 15.16.2: any sequence `A : ℕ → ℂ`
whose power series represents `(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` in a neighborhood of
`0` equals `TauCeti.cayleyOrrCoeff a b c` (classical when `2 * c - 1 ∉ -ℕ`, and matching the
`0⁻¹ = 0` truncation of `(2 * c - 1)_k = 0` summands when `2 * c - 1 ∈ -ℕ`). -/
theorem eq_cayleyOrrCoeff_of_eventually_hasSum (a b c : ℂ) {A : ℕ → ℂ}
    (hA : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun s : ℕ ↦ A s * z ^ s)
      ((1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)) :
    A = TauCeti.cayleyOrrCoeff a b c := by
  have hpA : HasFPowerSeriesAt
      (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)
      (FormalMultilinearSeries.ofScalars ℂ A) 0 :=
    hasFPowerSeriesAt_iff.mpr (hA.mono fun z hz ↦ by simpa [mul_comm] using hz)
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (hpA.eq_formalMultilinearSeries
      (hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric a b c).hasFPowerSeriesAt)

/-! ### Burchnall–Chaundy two-variable product expansion (DLMF 15.16.3) -/

section BurchnallChaundyBounds

private noncomputable def bcPref (a b c : ℂ) (s : ℕ) (u : ℂ) : ℂ :=
  (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
      (s ! * Gamma (c + s)) * u ^ s

private noncomputable def bcTerm (a b c : ℂ) (s : ℕ) (z ζ : ℂ) : ℂ :=
  bcPref a b c s (z * ζ) *
    regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ)

private noncomputable def bcGenCoeff (a b c : ℂ) (s j k : ℕ) : ℂ :=
  (ascPochhammer ℂ (s + j + k)).eval a * (ascPochhammer ℂ (s + j + k)).eval b *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
    (s ! * Gamma (c + s) * j ! * k ! * Gamma (c + (2 * s + j + k : ℕ)))

private noncomputable def bcGenPref (a b c u v : ℂ) (s j : ℕ) : ℂ :=
  bcPref a b c s u *
    ((ascPochhammer ℂ j).eval (a + s) * (ascPochhammer ℂ j).eval (b + s) / j ! * v ^ j)

private theorem bcGenPref_zero (a b c u v : ℂ) (s : ℕ) :
    bcGenPref a b c u v s 0 = bcPref a b c s u := by
  simp [bcGenPref]

private noncomputable def bcDoubleTerm (a b c z ζ : ℂ) (p : ℕ × ℕ) : ℂ :=
  bcGenPref a b c (z * ζ) (ζ * (1 - z)) p.1 p.2 *
    regularizedGaussHGFun (a + p.1 + p.2) (b + p.1 + p.2) (c + 2 * p.1 + p.2) z

private theorem bc_factorial_ratio_le (s j k : ℕ) :
    (((s + (j + k))! : ℝ) * (s + (j + k))! * s ! * s !) /
      ((s ! : ℝ) * s ! * j ! * k ! * (2 * s + (j + k))!) ≤ ((j + k).choose j : ℝ) := by
  set m := j + k
  rw [div_le_iff₀ (by positivity)]
  have hsq : ((s + m)! : ℝ) * (s + m)! ≤ m ! * (2 * s + m)! := by
    rw [← sq, add_comm s m, add_comm (2 * s) m]
    exact_mod_cast Nat.factorial_add_sq_le_factorial_mul_factorial_add_two_mul m s
  have hch : (m ! : ℝ) = (m.choose j : ℝ) * j ! * k ! := by
    exact_mod_cast (by simpa [m, add_tsub_cancel_left] using
      (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j k)).symm)
  calc ((s + m)! : ℝ) * (s + m)! * s ! * s !
      ≤ (m ! * (2 * s + m)!) * s ! * s ! := by gcongr
    _ = (m.choose j : ℝ) * ((s ! : ℝ) * s ! * j ! * k ! * (2 * s + m)!) := by rw [hch]; ring

private theorem exists_bc_coeff_bound (a b c : ℂ) :
    ∃ K : ℝ, ∃ P Q : ℕ, 0 ≤ K ∧ ∀ s j k : ℕ,
      ‖bcGenCoeff a b c s j k‖ ≤
        K * ((s : ℝ) + 1) ^ P * ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) := by
  let N : ℕ := max (max ⌈‖a‖⌉₊ ⌈‖b‖⌉₊) (max ⌈‖c - a‖⌉₊ ⌈‖c - b‖⌉₊) + 1
  have hN (w : ℂ) (hw : ⌈‖w‖⌉₊ ≤ N - 1) : ‖w‖ ≤ N :=
    (Nat.le_ceil ‖w‖).trans (by exact_mod_cast hw.trans (Nat.sub_le N 1))
  have haN : ‖a‖ ≤ N := hN a ((le_max_left _ _).trans (le_max_left _ _))
  have hbN : ‖b‖ ≤ N := hN b ((le_max_right _ _).trans (le_max_left _ _))
  have hcaN : ‖c - a‖ ≤ N := hN (c - a) ((le_max_left _ _).trans (le_max_right _ _))
  have hcbN : ‖c - b‖ ≤ N := hN (c - b) ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨CΓ, M, hCΓ, hΓ⟩ := exists_norm_inv_Gamma_add_natCast_le c
  refine ⟨CΓ ^ 2 * ((N : ℝ) + 1) ^ (4 * N) * 2 ^ M, 4 * N + 2 * M, 2 * N + M,
    by positivity, fun s j k ↦ ?_⟩
  set m := j + k
  have h1 := TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial haN (s + m)
  have h2 := TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial hbN (s + m)
  have h3 := TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial hcaN s
  have h4 := TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial hcbN s
  have h5 := hΓ s; have h6 := hΓ (2 * s + m); have hfac := bc_factorial_ratio_le s j k
  have hp1 : ((s + m + N : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
    have : (s : ℝ) + m + 1 ≤ ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
      nlinarith [s.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]
    push_cast; nlinarith [N.cast_nonneg (α := ℝ), s.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]
  have hp2 : ((s + N : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * ((s : ℝ) + 1) := by
    push_cast; nlinarith [N.cast_nonneg (α := ℝ), s.cast_nonneg (α := ℝ)]
  have hp3 : ((2 * s + m : ℕ) : ℝ) + 1 ≤ 2 * ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
    push_cast; nlinarith [s.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]
  have hsjk : s + j + k = s + m := add_assoc s j k
  have h2sjk : 2 * s + j + k = 2 * s + m := add_assoc (2 * s) j k
  rw [bcGenCoeff, hsjk, h2sjk, div_eq_mul_inv]
  simp only [mul_inv, norm_mul, norm_inv, norm_natCast]
  rw [← norm_inv (Gamma _), ← norm_inv (Gamma _)]
  calc ‖(ascPochhammer ℂ (s + m)).eval a‖ * ‖(ascPochhammer ℂ (s + m)).eval b‖ *
        ‖(ascPochhammer ℂ s).eval (c - a)‖ * ‖(ascPochhammer ℂ s).eval (c - b)‖ *
        ((s ! : ℝ)⁻¹ * ‖(Gamma (c + s))⁻¹‖ * (j ! : ℝ)⁻¹ * (k ! : ℝ)⁻¹ *
          ‖(Gamma (c + (2 * s + m : ℕ)))⁻¹‖)
      ≤ ((((s + m : ℕ) + (N : ℝ)) ^ N * (s + m)!) * (((s + m : ℕ) + (N : ℝ)) ^ N * (s + m)!) *
          ((s + N : ℝ) ^ N * s !) * ((s + N : ℝ) ^ N * s !)) *
        ((s ! : ℝ)⁻¹ * (CΓ * ((s : ℝ) + 1) ^ M / s !) * (j ! : ℝ)⁻¹ * (k ! : ℝ)⁻¹ *
          (CΓ * (((2 * s + m : ℕ) : ℝ) + 1) ^ M / (2 * s + m)!)) := by gcongr
    _ = CΓ ^ 2 * ((s + m + N : ℕ) : ℝ) ^ (2 * N) * ((s + N : ℕ) : ℝ) ^ (2 * N) *
          ((s : ℝ) + 1) ^ M * (((2 * s + m : ℕ) : ℝ) + 1) ^ M *
          ((((s + m)! : ℝ) * (s + m)! * s ! * s !) /
            ((s ! : ℝ) * s ! * j ! * k ! * (2 * s + m)!)) := by push_cast; ring
    _ ≤ CΓ ^ 2 * (((N : ℝ) + 1) * ((s : ℝ) + 1) * ((m : ℝ) + 1)) ^ (2 * N) *
          (((N : ℝ) + 1) * ((s : ℝ) + 1)) ^ (2 * N) * ((s : ℝ) + 1) ^ M *
          (2 * ((s : ℝ) + 1) * ((m : ℝ) + 1)) ^ M * (m.choose j : ℝ) := by gcongr
    _ = CΓ ^ 2 * ((N : ℝ) + 1) ^ (4 * N) * 2 ^ M * ((s : ℝ) + 1) ^ (4 * N + 2 * M) *
          ((j + k : ℝ) + 1) ^ (2 * N + M) * ((j + k).choose j : ℝ) := by
        simp only [m, Nat.cast_add, mul_pow]; ring_nf

private theorem norm_bcGenTerm_coeff_eq (a b c u v y : ℂ) (s j k : ℕ) :
    ‖bcGenPref a b c u v s j *
        ((regularizedGaussHGFunSeries (a + s + j) (b + s + j) (c + 2 * s + j)).coeff k *
          y ^ k)‖ =
      ‖bcGenCoeff a b c s j k‖ * ‖u‖ ^ s * ‖v‖ ^ j * ‖y‖ ^ k := by
  have hp1 : (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ j).eval (a + s) *
      (ascPochhammer ℂ k).eval (a + s + j) = (ascPochhammer ℂ (s + j + k)).eval a := by
    rw [TauCeti.ascPochhammer_add_eval a (s + j) k, TauCeti.ascPochhammer_add_eval a s j]
    push_cast; ring_nf
  have hp2 : (ascPochhammer ℂ s).eval b * (ascPochhammer ℂ j).eval (b + s) *
      (ascPochhammer ℂ k).eval (b + s + j) = (ascPochhammer ℂ (s + j + k)).eval b := by
    rw [TauCeti.ascPochhammer_add_eval b (s + j) k, TauCeti.ascPochhammer_add_eval b s j]
    push_cast; ring_nf
  have hc_eq : c + 2 * (s : ℂ) + j + k = c + (2 * s + j + k : ℕ) := by push_cast; ring
  simp only [bcGenPref, bcPref, bcGenCoeff, coeff_regularizedGaussHGFunSeries, hc_eq]
  rw [← norm_pow u s, ← norm_pow v j, ← norm_pow y k, ← norm_mul, ← norm_mul, ← norm_mul]
  refine congrArg norm ?_
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
      (s ! : ℂ)⁻¹ * (Gamma (c + s))⁻¹ * (j ! : ℂ)⁻¹ * (k ! : ℂ)⁻¹ *
      (Gamma (c + (2 * s + j + k : ℕ)))⁻¹ * u ^ s * v ^ j * y ^ k *
      ((ascPochhammer ℂ (s + j + k)).eval b * hp1 +
        (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ j).eval (a + s) *
          (ascPochhammer ℂ k).eval (a + s + j) * hp2)

private theorem norm_bcGenTerm_le {a b c u v y : ℂ} {K : ℝ} {P Q : ℕ} (hy : ‖y‖ < 1)
    (hbound : ∀ s j k : ℕ,
      ‖bcGenCoeff a b c s j k‖ ≤
        K * ((s : ℝ) + 1) ^ P * ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ))
    (s j : ℕ)
    (hrow : Summable fun k : ℕ ↦
      ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) :
    ‖bcGenPref a b c u v s j *
        regularizedGaussHGFun (a + s + j) (b + s + j) (c + 2 * s + j) y‖ ≤
      K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s *
        (∑' k : ℕ, ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) := by
  have hsy := (hasSum_regularizedGaussHGFun (a + s + j) (b + s + j)
    (c + 2 * s + j) hy).mul_left (bcGenPref a b c u v s j)
  have hterm_le (k : ℕ) :
      ‖bcGenPref a b c u v s j *
          ((regularizedGaussHGFunSeries (a + s + j) (b + s + j) (c + 2 * s + j)).coeff k *
            y ^ k)‖ ≤
        K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s *
          (((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) := by
    rw [norm_bcGenTerm_coeff_eq a b c u v y s j k]
    calc _ ≤ (K * ((s : ℝ) + 1) ^ P * ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ)) *
            ‖u‖ ^ s * ‖v‖ ^ j * ‖y‖ ^ k := by gcongr; exact hbound s j k
      _ = K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s *
            (((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) := by ring
  have hmaj := hrow.mul_left (K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s)
  have hsum_norm := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le hmaj
  rw [← hsy.tsum_eq]
  exact (norm_tsum_le_tsum_norm hsum_norm).trans
    ((Summable.tsum_le_tsum hterm_le hsum_norm hmaj).trans_eq (hrow.tsum_mul_left _))

private theorem exists_summable_norm_bcTerm_le (a b c : ℂ) {ζ : ℂ} {r : ℝ}
    (hζ : ‖ζ‖ < 1) (hr1 : r < 1) :
    ∃ g : ℕ → ℝ, Summable g ∧ ∀ s : ℕ, ∀ z : ℂ, ‖z‖ ≤ r → ‖z + ζ - z * ζ‖ ≤ r →
      ‖bcTerm a b c s z ζ‖ ≤ g s := by
  by_cases hr0 : 0 ≤ r
  · obtain ⟨K, P, Q, hK0, hbound⟩ := exists_bc_coeff_bound a b c
    have hrow_r : Summable fun k : ℕ ↦ ((k : ℝ) + 1) ^ Q * r ^ k :=
      TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 Q (by rwa [Real.norm_of_nonneg hr0])
    refine ⟨fun s ↦ K * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) * (((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s),
      (TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 P (r := r * ‖ζ‖)
        (by rw [Real.norm_of_nonneg (by positivity)]; nlinarith [norm_nonneg ζ])).mul_left _,
      fun s z hz hw ↦ ?_⟩
    set w := z + ζ - z * ζ
    have hw1 : ‖w‖ < 1 := hw.trans_lt hr1
    have hrow_w0 := TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 Q
      (r := ‖w‖) (by simpa using hw1)
    have hbc : ‖bcTerm a b c s z ζ‖ ≤
        K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k) := by
      have h0 := norm_bcGenTerm_le (u := z * ζ) (v := 1) hw1 hbound s 0
        (hrow_w0.congr fun k ↦ by simp)
      rw [bcGenPref_zero] at h0
      simp only [Nat.cast_zero, add_zero, zero_add, Nat.choose_zero_right, Nat.cast_one,
        norm_one, one_pow, mul_one] at h0
      exact h0
    have htsum : (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k) ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k :=
      Summable.tsum_le_tsum (fun k ↦ by gcongr) hrow_w0 hrow_r
    have huz : ‖z * ζ‖ ^ s ≤ (r * ‖ζ‖) ^ s := by
      rw [norm_mul]; exact pow_le_pow_left₀ (by positivity) (by gcongr) s
    calc ‖bcTerm a b c s z ζ‖
        ≤ K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k) := hbc
      _ ≤ K * ((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) := by
          gcongr
      _ = K * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) * (((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s) := by
          ring
  · exact ⟨0, summable_zero, fun _ z hz _ ↦ absurd ((norm_nonneg z).trans hz) hr0⟩

private theorem isOpen_bcBall (ζ : ℂ) (r : ℝ) :
    IsOpen {z : ℂ | ‖z‖ < r ∧ ‖z + ζ - z * ζ‖ < r} :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt (by fun_prop : Continuous fun z : ℂ ↦ ‖z + ζ - z * ζ‖) continuous_const)

private theorem differentiableOn_tsum_bcTerm (a b c : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z ζ)
      {z : ℂ | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1} := by
  intro z₀ hz₀
  set r : ℝ := (max ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖ + 1) / 2
  have hr_lt : r < 1 := by simp only [r]; linarith [max_lt hz₀.1 hz₀.2]
  let V : Set ℂ := {z : ℂ | ‖z‖ < r ∧ ‖z + ζ - z * ζ‖ < r}
  have hV_open : IsOpen V := isOpen_bcBall ζ r
  have hz₀V : z₀ ∈ V :=
    ⟨by simp only [r]; linarith [le_max_left ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖, hz₀.1, hz₀.2],
      by simp only [r]; linarith [le_max_right ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖, hz₀.1, hz₀.2]⟩
  obtain ⟨g, hg, hbound⟩ := exists_summable_norm_bcTerm_le a b c hζ hr_lt
  have hdiffV : DifferentiableOn ℂ (fun z : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z ζ) V := by
    refine differentiableOn_tsum_of_summable_norm hg (fun s z hzV ↦ ?_) hV_open fun s z hzV ↦
      hbound s z hzV.1.le hzV.2.le
    have hcomp : DifferentiableAt ℂ
        (fun z : ℂ ↦ regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ)) z :=
      (analyticAt_regularizedGaussHGFun _ _ _ (hzV.2.trans hr_lt)).differentiableAt.comp z
        (by fun_prop)
    exact (((differentiableAt_const _).mul ((differentiableAt_id.mul
      (differentiableAt_const ζ)).pow s)).mul hcomp).differentiableWithinAt
  exact ((hdiffV z₀ hz₀V).differentiableAt (hV_open.mem_nhds hz₀V)).differentiableWithinAt

private theorem norm_snd_lt_one_of_add_norm_mul_sub_lt_one {z ζ : ℂ}
    (hzv : ‖z‖ + ‖ζ * (1 - z)‖ < 1) : ‖ζ‖ < 1 := by
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg (ζ * (1 - z))]
  have h1z : 1 - ‖z‖ ≤ ‖1 - z‖ := by simpa using norm_sub_norm_le 1 z
  have hmul : ‖ζ‖ * (1 - ‖z‖) ≤ ‖ζ * (1 - z)‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left h1z (norm_nonneg ζ)
  by_contra! hζ
  nlinarith

private theorem summable_norm_bcDoubleTerm (a b c : ℂ) {z ζ : ℂ}
    (hzv : ‖z‖ + ‖ζ * (1 - z)‖ < 1) :
    Summable fun p : ℕ × ℕ ↦ ‖bcDoubleTerm a b c z ζ p‖ := by
  obtain ⟨K, P, Q, _, hbound⟩ := exists_bc_coeff_bound a b c
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg (ζ * (1 - z))]
  have hζ : ‖ζ‖ < 1 := norm_snd_lt_one_of_add_norm_mul_sub_lt_one hzv
  have hzζ1 : ‖z * ζ‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg ζ]
  set r₁ := ‖z‖
  set r₂ := ‖ζ * (1 - z)‖
  have hjk_sum : Summable fun q : ℕ × ℕ ↦
      ((q.1 + q.2 : ℝ) + 1) ^ Q * ((q.1 + q.2).choose q.1 : ℝ) * r₂ ^ q.1 * r₁ ^ q.2 := by
    have hdiag : Summable fun m : ℕ ↦ ((m : ℝ) + 1) ^ Q * (r₂ + r₁) ^ m :=
      TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 Q (r := r₂ + r₁)
        (by rw [Real.norm_of_nonneg (by positivity)]; linarith)
    have hsigma : Summable fun x : Σ m : ℕ, antidiagonal m ↦
        ((x.2.val.1 + x.2.val.2 : ℝ) + 1) ^ Q * ((x.2.val.1 + x.2.val.2).choose x.2.val.1 : ℝ) *
          r₂ ^ x.2.val.1 * r₁ ^ x.2.val.2 := by
      rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
      refine ⟨fun _ ↦ Summable.of_finite, hdiag.congr fun m ↦ ?_⟩
      rw [tsum_fintype]
      dsimp only
      rw [sum_coe_sort (antidiagonal m) (fun q : ℕ × ℕ ↦
        ((q.1 + q.2 : ℝ) + 1) ^ Q * ((q.1 + q.2).choose q.1 : ℝ) * r₂ ^ q.1 * r₁ ^ q.2),
        (Commute.all r₂ r₁).add_pow', mul_sum]
      refine sum_congr rfl fun q hq ↦ ?_
      rw [← Nat.cast_add, mem_antidiagonal.mp hq, nsmul_eq_mul]; ring
    exact HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hsigma
  obtain ⟨hk_row, hj_col⟩ := (summable_prod_of_nonneg (fun _ ↦ by positivity)).mp hjk_sum
  have hs_sum : Summable fun s : ℕ ↦ K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s :=
    ((TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 P (r := ‖z * ζ‖)
      (by simpa using hzζ1)).mul_left K).congr fun _ ↦ by ring
  have hprod := Summable.mul_of_nonneg hs_sum hj_col (fun _ ↦ by positivity)
    (fun j ↦ tsum_nonneg fun _ ↦ by positivity)
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun ⟨s, j⟩ ↦ ?_) hprod
  simpa [bcDoubleTerm, r₁, r₂] using
    norm_bcGenTerm_le (u := z * ζ) (v := ζ * (1 - z)) hz1 hbound s j (hk_row j)

private theorem bcDoubleTerm_antidiag_eq (a b c z ζ : ℂ) {n s : ℕ} (hsn : s ≤ n) :
    bcDoubleTerm a b c z ζ (s, n - s) =
      (n.choose s : ℂ) * (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
        (ascPochhammer ℂ (n - s)).eval (c + s) * z ^ s * (1 - z) ^ (n - s) *
        regularizedGaussHGFun (a + n) (b + n) (c + n + s) z *
        ((regularizedGaussHGFunSeries a b c).coeff n * ζ ^ n) := by
  have hadd_n : s + (n - s) = n := Nat.add_sub_of_le hsn
  have hch : (n.choose s : ℂ) * (n ! : ℂ)⁻¹ = (s ! : ℂ)⁻¹ * ((n - s)! : ℂ)⁻¹ := by
    rw [mul_comm, Nat.inv_factorial_mul_choose (K := ℂ) n s (n - s) hadd_n]
  have hshift (x : ℂ) : x + (s : ℂ) + (n - s : ℕ) = x + n := by
    rw [add_assoc, ← Nat.cast_add, hadd_n]
  have hΓ := (inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (c + s) (n - s)).symm
  rw [hshift c] at hΓ
  have hp (x : ℂ) : (ascPochhammer ℂ s).eval x * (ascPochhammer ℂ (n - s)).eval (x + s) =
      (ascPochhammer ℂ n).eval x := by
    simpa [hadd_n] using (TauCeti.ascPochhammer_add_eval x s (n - s)).symm
  have hζn : ζ ^ s * ζ ^ (n - s) = ζ ^ n := by rw [← pow_add, hadd_n]
  have hc2_shift : c + 2 * (s : ℂ) + (n - s : ℕ) = c + n + s := by
    have htwo : c + 2 * (s : ℂ) = c + s + s := by ring
    rw [htwo, hshift (c + s), add_right_comm]
  simp only [bcDoubleTerm, bcGenPref, bcPref, coeff_regularizedGaussHGFunSeries, hshift a, hshift b,
    hc2_shift, div_eq_mul_inv, mul_inv, mul_pow]
  rw [← hΓ, ← hp a, ← hp b, ← hζn]
  linear_combination (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ (n - s)).eval (a + s) *
    (ascPochhammer ℂ s).eval b * (ascPochhammer ℂ (n - s)).eval (b + s) *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
    (ascPochhammer ℂ (n - s)).eval (c + s) * (Gamma (c + n))⁻¹ *
    z ^ s * ζ ^ s * ζ ^ (n - s) * (1 - z) ^ (n - s) *
    regularizedGaussHGFun (a + n) (b + n) (c + n + s) z * hch.symm

private theorem hasSum_bcTerm_of_add_norm_lt (a b c : ℂ) {z ζ : ℂ}
    (hzv : ‖z‖ + ‖ζ * (1 - z)‖ < 1) :
    HasSum (fun s : ℕ ↦ bcTerm a b c s z ζ)
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) := by
  let D := bcDoubleTerm a b c z ζ
  have hD : Summable D := (summable_norm_bcDoubleTerm a b c hzv).of_norm
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg (ζ * (1 - z))]
  have hζ : ‖ζ‖ < 1 := norm_snd_lt_one_of_add_norm_mul_sub_lt_one hzv
  have hrow : HasSum (fun s : ℕ ↦ bcTerm a b c s z ζ) (∑' p, D p) := by
    refine hD.hasSum.prod_fiberwise fun s ↦ ?_
    have hadd := (hasSum_regularizedGaussHGFun_add (a + s) (b + s) (c + 2 * s) hzv).mul_left
      (bcPref a b c s (z * ζ))
    have hw : z + ζ * (1 - z) = z + ζ - z * ζ := by ring
    rw [hw] at hadd
    simpa only [D, bcDoubleTerm, bcGenPref, bcTerm, mul_assoc] using hadd
  have hdiag : HasSum
      (fun n : ℕ ↦ regularizedGaussHGFun a b c z *
        ((regularizedGaussHGFunSeries a b c).coeff n * ζ ^ n)) (∑' p, D p) := by
    have h := (HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hD.hasSum).sigma
      fun n ↦ hasSum_fintype _
    simp only [Function.comp_apply, HasAntidiagonal.sigmaAntidiagonalEquivProd_apply,
      sum_coe_sort (antidiagonal _) D] at h
    refine h.congr_fun fun n ↦ ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun s j ↦ D (s, j)) n,
      regularizedGaussHGFun_eq_sum_choose_mul_regularizedGaussHGFun a b c hz1 n, sum_mul]
    exact sum_congr rfl fun s hs ↦
      (bcDoubleTerm_antidiag_eq a b c z ζ (mem_range_succ_iff.mp hs)).symm
  have hprod := (hasSum_regularizedGaussHGFun a b c hζ).mul_left (regularizedGaussHGFun a b c z)
  rwa [← hprod.unique hdiag] at hrow

private theorem convex_bcDomain (ζ : ℂ) :
    Convex ℝ {z : ℂ | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1} := by
  have hset : {z : ℂ | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1} =
      Metric.ball (0 : ℂ) 1 ∩
        (LinearMap.mulLeft ℝ (1 - ζ) ⁻¹' ((· + ζ) ⁻¹' Metric.ball (0 : ℂ) 1)) := by
    ext z
    have hmul : (1 - ζ) * z + ζ = z + ζ - z * ζ := by ring
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_ball,
      dist_zero_right, LinearMap.mulLeft_apply, hmul]
  rw [hset]
  exact (convex_ball (0 : ℂ) 1).inter
    (((convex_ball (0 : ℂ) 1).translate_preimage_left ζ).linear_preimage
      (LinearMap.mulLeft ℝ (1 - ζ)))

end BurchnallChaundyBounds

/-- **Burchnall–Chaundy two-variable product expansion for `regularizedGaussHGFun` (DLMF 15.16.3).**
Whenever `‖z‖ < 1`, `‖ζ‖ < 1`, and `‖z + ζ - z * ζ‖ < 1`, the product
`𝐅(a, b; c; z) * 𝐅(a, b; c; ζ)` expands as a series in
`(z * ζ) ^ s * 𝐅(a + s, b + s; c + 2s; z + ζ - z * ζ)`, for all complex parameters `a`, `b`, `c`
(including nonpositive integer poles of `Γ(c)`). -/
theorem hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun (a b c : ℂ) {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hw : ‖z + ζ - z * ζ‖ < 1) :
    HasSum
      (fun s : ℕ ↦ (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * Gamma (c + s)) * (z * ζ) ^ s *
        regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) := by
  let U : Set ℂ := {z' : ℂ | ‖z'‖ < 1 ∧ ‖z' + ζ - z' * ζ‖ < 1}
  have hf_an : AnalyticOnNhd ℂ (fun z' : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z' ζ) U :=
    (differentiableOn_tsum_bcTerm a b c hζ).analyticOnNhd (isOpen_bcBall ζ 1)
  have hg_an : AnalyticOnNhd ℂ
      (fun z' : ℂ ↦ regularizedGaussHGFun a b c z' * regularizedGaussHGFun a b c ζ) U :=
    fun _ hz' ↦ (analyticAt_regularizedGaussHGFun a b c hz'.1).mul analyticAt_const
  have heq0 : (fun z' : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z' ζ) =ᶠ[𝓝 (0 : ℂ)]
      fun z' : ℂ ↦ regularizedGaussHGFun a b c z' * regularizedGaussHGFun a b c ζ := by
    have hrad : 0 < (1 - ‖ζ‖) / 4 := by linarith
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hrad] with z' hz'
    rw [Metric.mem_ball, dist_zero_right] at hz'
    have hzv : ‖z'‖ + ‖ζ * (1 - z')‖ < 1 := by
      calc ‖z'‖ + ‖ζ * (1 - z')‖ = ‖z'‖ + ‖ζ‖ * ‖1 - z'‖ := by rw [norm_mul]
        _ ≤ ‖z'‖ + ‖ζ‖ * (1 + ‖z'‖) := by gcongr; exact (norm_sub_le 1 z').trans_eq (by simp)
        _ < 1 := by nlinarith [norm_nonneg ζ, norm_nonneg z']
    exact (hasSum_bcTerm_of_add_norm_lt a b c hzv).tsum_eq
  have heqU := hf_an.eqOn_of_preconnected_of_eventuallyEq hg_an
    (convex_bcDomain ζ).isPreconnected ⟨by simp, by simpa using hζ⟩ heq0
  obtain ⟨g, hg, hbound⟩ := exists_summable_norm_bcTerm_le a b c hζ (max_lt hz hw)
  have hsum_z : Summable fun s : ℕ ↦ bcTerm a b c s z ζ :=
    .of_norm_bounded hg fun s ↦ hbound s z (le_max_left _ _) (le_max_right _ _)
  simpa only [bcTerm, bcPref, ← heqU ⟨hz, hw⟩] using hsum_z.hasSum

/-- **Burchnall–Chaundy two-variable product expansion for `₂F₁` (DLMF 15.16.3, ordinary form).**
When `c` avoids the nonpositive integers and `‖z‖ < 1`, `‖ζ‖ < 1`, `‖z + ζ - z * ζ‖ < 1`,
`₂F₁(a, b; c; z) * ₂F₁(a, b; c; ζ)` expands as a series in
`((a)_s (b)_s (c - a)_s (c - b)_s / (s! (c)_s (c)_{2s})) (z * ζ) ^ s ₂F₁(a + s, b + s; c + 2s; w)`
with `w = z + ζ - z * ζ`. -/
theorem hasSum_ordinaryHypergeometric_mul_ordinaryHypergeometric (a b : ℂ) {c z ζ : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hw : ‖z + ζ - z * ζ‖ < 1) :
    HasSum
      (fun s : ℕ ↦ (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * (ascPochhammer ℂ s).eval c * (ascPochhammer ℂ (2 * s)).eval c) * (z * ζ) ^ s *
        ₂F₁ (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (₂F₁ a b c z * ₂F₁ a b c ζ) := by
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hmul := (hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun a b c hz hζ hw).mul_left
    (Gamma c * Gamma c)
  have hprod : Gamma c * Gamma c *
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) =
      ₂F₁ a b c z * ₂F₁ a b c ζ := by
    rw [← ordinaryHypergeometric_div_Gamma_eq hc, ← ordinaryHypergeometric_div_Gamma_eq hc]
    field_simp
  rw [hprod] at hmul
  refine hmul.congr_fun fun s ↦ ?_
  have hc2s : ∀ k : ℕ, c + 2 * (s : ℂ) ≠ -k := fun k h ↦
    hc (2 * s + k) (by push_cast; linear_combination h)
  have hΓm (m : ℕ) : Gamma (c + m) = (ascPochhammer ℂ m).eval c * Gamma c := by
    rw [← Gamma_add_nat_div_Gamma_eq c hc, div_mul_cancel₀ _ hΓc]
  have hΓc2s : Gamma (c + 2 * (s : ℂ)) = (ascPochhammer ℂ (2 * s)).eval c * Gamma c := by
    simpa [Nat.cast_mul] using hΓm (2 * s)
  have hp (m : ℕ) : (ascPochhammer ℂ m).eval c ≠ 0 := by
    rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩; exact hc k (by linear_combination hk)
  have hps := hp s
  have hp2s := hp (2 * s)
  have hfs : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
  rw [← ordinaryHypergeometric_div_Gamma_eq hc2s, hΓm s, hΓc2s]
  field_simp

end Complex

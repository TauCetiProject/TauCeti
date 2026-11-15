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
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.Basic
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Product expansions of the Gauss hypergeometric function

This file proves the Cayley–Orr one-variable product expansion (DLMF 15.16.1–15.16.2) and the
Burchnall–Chaundy two-variable product expansion (DLMF 15.16.3) of the Gauss hypergeometric
function on their open convergence regions.

## Cayley–Orr product identity (DLMF 15.16.1–15.16.2)

For parameters `a`, `b`, `c` in a field `𝕂`, `TauCeti.cayleyOrrCoeff a b c s` is the `s`-th Cauchy
convolution coefficient of `(1 - z) ^ (a + b - c)` with `₂F₁(2a, 2b; 2c - 1; z)`:
$$A_s = \sum_{k=0}^s \frac{(c - a - b)_{s - k}}{(s - k)!}
  \frac{(2a)_k (2b)_k}{k! \, (2c - 1)_k}.$$
Over `ℂ`, these are the power-series and Taylor coefficients of the generating function
`(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` on the open unit disk (DLMF 15.16.2), for all
complex parameters `a`, `b`, `c`.

Over any field `𝕂` of characteristic zero with `2c - 1 ∉ -ℕ`, both the Cauchy product of
`₂F₁(a, b; c - 1/2; z)` with `₂F₁(c - a, c - b; c + 1/2; z)` and `((c)_s / (c + 1/2)_s) A_s`
satisfy the same polynomial recurrence with identical initial values at `s = 0, 1`, yielding the
coefficient identity
$$\sum_{k=0}^s \frac{(a)_k (b)_k}{k! \, (c - \tfrac{1}{2})_k}
  \frac{(c - a)_{s - k} (c - b)_{s - k}}{(s - k)! \, (c + \tfrac{1}{2})_{s - k}}
  = \frac{(c)_s}{(c + \tfrac{1}{2})_s} A_s$$
and the analytic Cayley–Orr expansion on `‖z‖ < 1` (DLMF 15.16.1).

## Burchnall–Chaundy two-variable product identity (DLMF 15.16.3)

For `‖z‖ < 1`, `‖ζ‖ < 1`, and `‖z + ζ - z * ζ‖ < 1`, the regularized Gauss function satisfies
$$\mathbf{F}(a, b; c; z) \, \mathbf{F}(a, b; c; \zeta)
  = \sum_{s=0}^\infty \frac{(a)_s (b)_s (c - a)_s (c - b)_s}{s! \, \Gamma(c + s)} (z \zeta)^s \,
    \mathbf{F}(a + s, b + s; c + 2s; z + \zeta - z\zeta)$$
for **all** complex parameters `a`, `b`, `c`. Writing `1 / Γ(c + s)` in place of
`1 / (Γ(c) (c)_s)` resolves the removable singularity at nonpositive integer values of `c`. When
`c ∉ -ℕ`, multiplying by `Γ(c)²` gives the corresponding expansion for `₂F₁`.

The proof establishes Burchnall and Chaundy's finite expansion of `𝐅(a, b; c; z)` in powers of `z`
and `1 - z` together with the Taylor addition series of `𝐅(a, b; c; z + w)` for `‖z‖ + ‖w‖ < 1`,
deduces the identity on a small ball in `z` about `0` by absolute rearrangement, and continues in
`z` across the convex domain `{z | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1}` by the identity theorem.

## Main definitions and results

* `TauCeti.cayleyOrrCoeff`: the Cayley–Orr coefficient sequence `A_s` over any field.
* `TauCeti.sum_ordinaryHypergeometricCoefficient_mul_eq_cayleyOrrCoeff`: the algebraic Cayley–Orr
  convolution identity over any characteristic-zero field.
* `Complex.hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric`,
  `Complex.hasSum_cayleyOrrCoeff_mul_pow`,
  `Complex.coeff_taylorSeries_one_sub_cpow_mul_ordinaryHypergeometric`,
  `Complex.eq_cayleyOrrCoeff_of_eventually_hasSum`: DLMF 15.16.2 generating-function expansion and
  coefficient characterizations.
* `Complex.hasFPowerSeriesOnBall_ordinaryHypergeometric_mul_cayleyOrr`,
  `Complex.hasSum_ordinaryHypergeometric_mul_cayleyOrr`: DLMF 15.16.1 Cayley–Orr product
  expansion on `‖z‖ < 1`.
* `Complex.regularizedGaussHGFun_eq_sum_choose`: finite Burchnall–Chaundy expansion of
  `𝐅(a, b; c; z)` in powers of `z` and `1 - z` on `‖z‖ < 1`.
* `Complex.hasSum_regularizedGaussHGFun_add`: addition series for `𝐅(a, b; c; z + w)` when
  `‖z‖ + ‖w‖ < 1`.
* `Complex.hasSum_regularizedGaussHGFun_mul`, `Complex.hasSum_ordinaryHypergeometric_mul`:
  DLMF 15.16.3 Burchnall–Chaundy two-variable product expansion in regularized and ordinary forms.

## References

* NIST Digital Library of Mathematical Functions, §15.16, equations 15.16.1–15.16.3.
* A. Cayley, *A memoir on the transformation of elliptic functions*, Philos. Trans. Roy. Soc.
  London **148** (1858), 47–56.
* W. McF. Orr, *Theorems relating to the product of two hypergeometric series*, Trans. Cambridge
  Philos. Soc. **17** (1899), 1–15.
* W. N. Bailey, *Generalized Hypergeometric Series*, Cambridge Univ. Press, 1935, §10.1.
* J. L. Burchnall and T. W. Chaundy, *Expansions of Appell's double hypergeometric functions*,
  Quart. J. Math. Oxford Ser. **11** (1940), 249–270.
-/

public section

open Filter Finset Polynomial
open scoped Nat NNReal Topology BigOperators ENNReal

namespace TauCeti

/-! ### Algebraic Cayley–Orr coefficients and recurrence -/

/-- The `s`-th Cayley–Orr coefficient `A_s(a, b, c)` over a field `𝕂`: the `s`-th Cauchy product
coefficient of the binomial series for `(1 - z) ^ (a + b - c)` with the hypergeometric series
`₂F₁(2a, 2b; 2c - 1; z)` (DLMF 15.16.2). -/
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

/-- The zeroth Cayley–Orr coefficient is `1`. -/
@[simp]
theorem cayleyOrrCoeff_zero {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) :
    cayleyOrrCoeff a b c 0 = 1 := by
  simp [cayleyOrrCoeff, ordinaryHypergeometricCoefficient]

/-- The Cayley–Orr coefficients are symmetric in `a` and `b`. -/
theorem cayleyOrrCoeff_comm {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (s : ℕ) :
    cayleyOrrCoeff a b c s = cayleyOrrCoeff b a c s := by
  refine sum_congr rfl fun k _ ↦ ?_
  have hsub : c - b - a = c - a - b := by ring
  simp only [ordinaryHypergeometricCoefficient, hsub]
  ring

private theorem ascPochhammer_add_eval {S : Type*} [CommSemiring S] (x : S) (m n : ℕ) :
    (ascPochhammer S (m + n)).eval x =
      (ascPochhammer S m).eval x * (ascPochhammer S n).eval (x + m) := by
  simpa [Polynomial.eval_mul, Polynomial.eval_comp] using
    (congrArg (Polynomial.eval x) (ascPochhammer_mul (S := S) m n)).symm

section CayleyOrrRecurrence

private theorem inv_factorial_eq {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (m : ℕ) :
    (m ! : 𝕂)⁻¹ = ((m : 𝕂) + 1) * ((m + 1)! : 𝕂)⁻¹ := by
  have hs : (m : 𝕂) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hs, one_mul]

private theorem inv_ascPochhammer_eq {𝕂 : Type*} [Field 𝕂] {x : 𝕂} {m : ℕ}
    (hx : x + m ≠ 0) :
    ((ascPochhammer 𝕂 m).eval x)⁻¹ =
      (x + m) * ((ascPochhammer 𝕂 (m + 1)).eval x)⁻¹ := by
  rw [ascPochhammer_succ_eval, mul_inv, mul_left_comm (x + m), mul_inv_cancel₀ hx, mul_one]

private def cayleyRecR2 {𝕂 : Type*} [Field 𝕂] (c : 𝕂) (n : ℕ) : 𝕂 :=
  (n + 2) * (n + 2 * c)

private def cayleyRecR1 {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (n : ℕ) : 𝕂 :=
  -2 * (n + 1) * n - 4 * c * (n + 1) + (a + b - c) * (2 * c - 1) - 4 * a * b

private def cayleyRecR0 {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (n : ℕ) : 𝕂 :=
  (n + c + a - b) * (n + c - a + b)

private noncomputable def cayleySummand {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (s k : ℕ) : 𝕂 :=
  ((s - k)! : 𝕂)⁻¹ * (ascPochhammer 𝕂 (s - k)).eval (c - a - b) *
    ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) k

private noncomputable def cayleyCertH {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (n : ℕ) : ℕ → 𝕂
  | 0 => 0
  | j + 1 =>
      (a + b - c + 1) * (ascPochhammer 𝕂 (n - j)).eval (c - a - b) *
        (ascPochhammer 𝕂 (j + 1)).eval (2 * a) * (ascPochhammer 𝕂 (j + 1)).eval (2 * b) *
        (j ! : 𝕂)⁻¹ * ((n + 1 - j)! : 𝕂)⁻¹ * ((ascPochhammer 𝕂 j).eval (2 * c - 1))⁻¹

private theorem cayleySummand_step {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) {n k : ℕ} (hk : k ≤ n) :
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
    rw [inv_factorial_eq l, inv_factorial_eq (l + 1),
      ascPochhammer_succ_eval (l + 1) (c - a - b), ascPochhammer_succ_eval l (c - a - b),
      ascPochhammer_succ_eval 0 (2 * a), ascPochhammer_succ_eval 0 (2 * b)]
    simp only [ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.cast_add,
      Nat.cast_one, Nat.cast_zero, inv_one]
    dsimp only [cayleyRecR2, cayleyRecR1, cayleyRecR0]
    ring
  | succ j =>
    have hs0 : j + 1 + l - (j + 1) = l := by omega
    have hs1 : j + 1 + l + 1 - (j + 1) = l + 1 := by omega
    have hs2 : j + 1 + l + 2 - (j + 1) = l + 2 := by omega
    have hs3 : j + 1 + l - j = l + 1 := by omega
    have hs4 : j + 1 + l + 1 - j = l + 2 := by omega
    have hden1 : 2 * c - 1 + (j : 𝕂) ≠ 0 := fun h ↦ hc j (by linear_combination h)
    simp only [cayleySummand, cayleyCertH, hs0, hs1, hs2, hs3, hs4,
      ordinaryHypergeometricCoefficient]
    rw [inv_factorial_eq j, inv_factorial_eq l, inv_factorial_eq (l + 1),
      inv_ascPochhammer_eq hden1, ascPochhammer_succ_eval (l + 1) (c - a - b),
      ascPochhammer_succ_eval l (c - a - b), ascPochhammer_succ_eval (j + 1) (2 * a),
      ascPochhammer_succ_eval (j + 1) (2 * b)]
    generalize (ascPochhammer 𝕂 (j + 1)).eval (2 * a) = pa,
      (ascPochhammer 𝕂 (j + 1)).eval (2 * b) = pb,
      (ascPochhammer 𝕂 l).eval (c - a - b) = pcab,
      ((j + 1)! : 𝕂)⁻¹ = fj, ((l + 2)! : 𝕂)⁻¹ = fl,
      ((ascPochhammer 𝕂 (j + 1)).eval (2 * c - 1))⁻¹ = pc
    dsimp only [cayleyRecR2, cayleyRecR1, cayleyRecR0]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem cayleyOrrCoeff_recurrence {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) (n : ℕ) :
    cayleyRecR2 c n * cayleyOrrCoeff a b c (n + 2) +
      cayleyRecR1 a b c n * cayleyOrrCoeff a b c (n + 1) +
      cayleyRecR0 a b c n * cayleyOrrCoeff a b c n = 0 := by
  have hdef (s : ℕ) : cayleyOrrCoeff a b c s = ∑ k ∈ range (s + 1), cayleySummand a b c s k := rfl
  rw [hdef (n + 2), hdef (n + 1), hdef n, sum_range_succ _ (n + 2), sum_range_succ _ (n + 1),
    sum_range_succ _ (n + 1)]
  have hsum :
      cayleyRecR2 c n * (∑ k ∈ range (n + 1), cayleySummand a b c (n + 2) k) +
        cayleyRecR1 a b c n * (∑ k ∈ range (n + 1), cayleySummand a b c (n + 1) k) +
        cayleyRecR0 a b c n * (∑ k ∈ range (n + 1), cayleySummand a b c n k) =
      cayleyCertH a b c n (n + 1) := by
    simp only [mul_sum, ← sum_add_distrib]
    rw [sum_congr rfl fun k hk ↦ cayleySummand_step a b hc (mem_range_succ_iff.mp hk),
      sum_range_sub]
    simp [cayleyCertH]
  have hs1 : n + 2 - (n + 1) = 1 := by omega
  have hs2 : n + 1 - n = 1 := by omega
  have hden1 : 2 * c - 1 + (n : 𝕂) ≠ 0 := fun h ↦ hc n (by linear_combination h)
  have hden2 : 2 * c - 1 + ((n + 1 : ℕ) : 𝕂) ≠ 0 := fun h ↦
    hc (n + 1) (by push_cast at h ⊢; linear_combination h)
  have hbd :
      cayleyCertH a b c n (n + 1) +
        cayleyRecR2 c n * (cayleySummand a b c (n + 2) (n + 1) +
          cayleySummand a b c (n + 2) (n + 2)) +
        cayleyRecR1 a b c n * cayleySummand a b c (n + 1) (n + 1) = 0 := by
    simp only [cayleyCertH, cayleySummand, hs1, hs2, Nat.sub_self,
      ordinaryHypergeometricCoefficient]
    rw [inv_factorial_eq n, inv_factorial_eq (n + 1), inv_ascPochhammer_eq hden1,
      inv_ascPochhammer_eq hden2, ascPochhammer_succ_eval (n + 1) (2 * a),
      ascPochhammer_succ_eval (n + 1) (2 * b), ascPochhammer_succ_eval 0 (c - a - b)]
    simp only [ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, inv_one]
    dsimp only [cayleyRecR2, cayleyRecR1]
    ring
  linear_combination hsum + hbd

private def cayleyRecQ2 {𝕂 : Type*} [Field 𝕂] (c : 𝕂) (n : ℕ) : 𝕂 :=
  cayleyRecR2 c n * (c + n + 1 / 2) * (c + n + 3 / 2)

private def cayleyRecQ1 {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (n : ℕ) : 𝕂 :=
  cayleyRecR1 a b c n * (c + n + 1 / 2) * (c + n + 1)

private def cayleyRecQ0 {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (n : ℕ) : 𝕂 :=
  cayleyRecR0 a b c n * (c + n) * (c + n + 1)

private def cayleyCertPolyAux {𝕂 : Type*} [Field 𝕂] (s₁ s₂ d m kp : 𝕂) : 𝕂 :=
  ((m + 1 + 2 * d * (s₁ + m - d)) * kp ^ 2 +
    (s₁ * (m + 1 - d) - d * (2 * m + 1) * (3 * d + 1) + 6 * d ^ 2 * (d - s₁) + 4 * s₂ * d) * kp +
    (s₂ * ((m + 1) * (1 - 2 * d) - 2 * d * (2 * d + 1)) -
      2 * s₁ * d * (m + 1 - d - 2 * d ^ 2) +
      d * ((2 * d - 1) * (m + 1) + 2 * d ^ 2 * (2 * m + 1 - 2 * d)))) / 2

private def cayleyCertPoly {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (n j : ℕ) : 𝕂 :=
  cayleyCertPolyAux (a + b) (a * b) (c + (n + 1)) (n + 1) (j + 1)

private noncomputable def cayleyConvTerm {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (s k : ℕ) : 𝕂 :=
  ordinaryHypergeometricCoefficient a b (c - 1 / 2) k *
    ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2) (s - k)

private noncomputable def cayleyCertG {𝕂 : Type*} [Field 𝕂] (a b c : 𝕂) (n : ℕ) : ℕ → 𝕂
  | 0 => 0
  | j + 1 =>
      cayleyCertPoly a b c n j * (ascPochhammer 𝕂 (j + 1)).eval a *
        (ascPochhammer 𝕂 (j + 1)).eval b * (ascPochhammer 𝕂 (n - j)).eval (c - a) *
        (ascPochhammer 𝕂 (n - j)).eval (c - b) *
        (j ! : 𝕂)⁻¹ * ((n + 1 - j)! : 𝕂)⁻¹ * ((ascPochhammer 𝕂 j).eval (c - 1 / 2))⁻¹ *
        ((ascPochhammer 𝕂 (n + 1 - j)).eval (c + 1 / 2))⁻¹

private theorem cayleyConvTerm_step {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) {n k : ℕ} (hk : k ≤ n) :
    cayleyRecQ2 c n * cayleyConvTerm a b c (n + 2) k +
      cayleyRecQ1 a b c n * cayleyConvTerm a b c (n + 1) k +
      cayleyRecQ0 a b c n * cayleyConvTerm a b c n k =
      cayleyCertG a b c n (k + 1) - cayleyCertG a b c n k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hadd1 : c + 1 / 2 + (l : 𝕂) ≠ 0 := fun h ↦
    hc (2 * (l + 1)) (by push_cast at h ⊢; linear_combination 2 * h)
  have hadd2 : c + 1 / 2 + ((l + 1 : ℕ) : 𝕂) ≠ 0 := fun h ↦
    hc (2 * (l + 2)) (by push_cast at h ⊢; linear_combination 2 * h)
  cases k with
  | zero =>
    rw [zero_add]
    simp only [cayleyConvTerm, cayleyCertG, Nat.sub_zero, zero_add,
      ordinaryHypergeometricCoefficient]
    rw [inv_factorial_eq l, inv_factorial_eq (l + 1), inv_ascPochhammer_eq hadd1,
      inv_ascPochhammer_eq hadd2, ascPochhammer_succ_eval (l + 1) (c - a),
      ascPochhammer_succ_eval (l + 1) (c - b), ascPochhammer_succ_eval l (c - a),
      ascPochhammer_succ_eval l (c - b), ascPochhammer_succ_eval 0 a, ascPochhammer_succ_eval 0 b]
    simp only [ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, inv_one]
    generalize (ascPochhammer 𝕂 l).eval (c - a) = pca,
      (ascPochhammer 𝕂 l).eval (c - b) = pcb,
      ((l + 2)! : 𝕂)⁻¹ = fl,
      ((ascPochhammer 𝕂 (l + 2)).eval (c + 1 / 2))⁻¹ = pc2
    dsimp only [cayleyRecQ2, cayleyRecQ1, cayleyRecQ0, cayleyRecR2, cayleyRecR1, cayleyRecR0,
      cayleyCertPoly, cayleyCertPolyAux]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    ring
  | succ j =>
    have hs0 : j + 1 + l - (j + 1) = l := by omega
    have hs1 : j + 1 + l + 1 - (j + 1) = l + 1 := by omega
    have hs2 : j + 1 + l + 2 - (j + 1) = l + 2 := by omega
    have hs3 : j + 1 + l - j = l + 1 := by omega
    have hs4 : j + 1 + l + 1 - j = l + 2 := by omega
    have hsub1 : c - 1 / 2 + (j : 𝕂) ≠ 0 := fun h ↦
      hc (2 * j) (by push_cast at h ⊢; linear_combination 2 * h)
    simp only [cayleyConvTerm, cayleyCertG, hs0, hs1, hs2, hs3, hs4,
      ordinaryHypergeometricCoefficient]
    rw [inv_factorial_eq j, inv_factorial_eq l, inv_factorial_eq (l + 1),
      inv_ascPochhammer_eq hsub1, inv_ascPochhammer_eq hadd1, inv_ascPochhammer_eq hadd2,
      ascPochhammer_succ_eval (l + 1) (c - a), ascPochhammer_succ_eval (l + 1) (c - b),
      ascPochhammer_succ_eval l (c - a), ascPochhammer_succ_eval l (c - b),
      ascPochhammer_succ_eval (j + 1) a, ascPochhammer_succ_eval (j + 1) b]
    generalize (ascPochhammer 𝕂 (j + 1)).eval a = pa,
      (ascPochhammer 𝕂 (j + 1)).eval b = pb,
      (ascPochhammer 𝕂 l).eval (c - a) = pca,
      (ascPochhammer 𝕂 l).eval (c - b) = pcb,
      ((j + 1)! : 𝕂)⁻¹ = fj, ((l + 2)! : 𝕂)⁻¹ = fl,
      ((ascPochhammer 𝕂 (j + 1)).eval (c - 1 / 2))⁻¹ = pc1,
      ((ascPochhammer 𝕂 (l + 2)).eval (c + 1 / 2))⁻¹ = pc2
    dsimp only [cayleyRecQ2, cayleyRecQ1, cayleyRecQ0, cayleyRecR2, cayleyRecR1, cayleyRecR0,
      cayleyCertPoly, cayleyCertPolyAux]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem cayleyConvSum_recurrence {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) (n : ℕ) :
    let S := fun s ↦ ∑ k ∈ range (s + 1), cayleyConvTerm a b c s k
    cayleyRecQ2 c n * S (n + 2) + cayleyRecQ1 a b c n * S (n + 1) +
      cayleyRecQ0 a b c n * S n = 0 := by
  intro S
  simp only [S]
  rw [sum_range_succ _ (n + 2), sum_range_succ _ (n + 1), sum_range_succ _ (n + 1)]
  have hsum :
      cayleyRecQ2 c n * (∑ k ∈ range (n + 1), cayleyConvTerm a b c (n + 2) k) +
        cayleyRecQ1 a b c n * (∑ k ∈ range (n + 1), cayleyConvTerm a b c (n + 1) k) +
        cayleyRecQ0 a b c n * (∑ k ∈ range (n + 1), cayleyConvTerm a b c n k) =
      cayleyCertG a b c n (n + 1) := by
    simp only [mul_sum, ← sum_add_distrib]
    rw [sum_congr rfl fun k hk ↦ cayleyConvTerm_step a b hc (mem_range_succ_iff.mp hk),
      sum_range_sub]
    simp [cayleyCertG]
  have hs1 : n + 2 - (n + 1) = 1 := by omega
  have hs2 : n + 1 - n = 1 := by omega
  have hsub1 : c - 1 / 2 + (n : 𝕂) ≠ 0 := fun h ↦
    hc (2 * n) (by push_cast at h ⊢; linear_combination 2 * h)
  have hsub2 : c - 1 / 2 + ((n + 1 : ℕ) : 𝕂) ≠ 0 := fun h ↦
    hc (2 * (n + 1)) (by push_cast at h ⊢; linear_combination 2 * h)
  have hadd0 : c + 1 / 2 + ((0 : ℕ) : 𝕂) ≠ 0 := fun h ↦
    hc 2 (by push_cast at h ⊢; linear_combination 2 * h)
  have hbd :
      cayleyCertG a b c n (n + 1) +
        cayleyRecQ2 c n * (cayleyConvTerm a b c (n + 2) (n + 1) +
          cayleyConvTerm a b c (n + 2) (n + 2)) +
        cayleyRecQ1 a b c n * cayleyConvTerm a b c (n + 1) (n + 1) = 0 := by
    simp only [cayleyCertG, cayleyConvTerm, hs1, hs2, Nat.sub_self,
      ordinaryHypergeometricCoefficient]
    rw [inv_factorial_eq n, inv_factorial_eq (n + 1), inv_ascPochhammer_eq hsub1,
      inv_ascPochhammer_eq hsub2, inv_ascPochhammer_eq hadd0, ascPochhammer_succ_eval (n + 1) a,
      ascPochhammer_succ_eval (n + 1) b, ascPochhammer_succ_eval 0 (c - a),
      ascPochhammer_succ_eval 0 (c - b)]
    simp only [ascPochhammer_zero, Polynomial.eval_one, zero_add, Nat.factorial_zero,
      Nat.factorial_one]
    generalize (ascPochhammer 𝕂 (n + 1)).eval a = pa,
      (ascPochhammer 𝕂 (n + 1)).eval b = pb,
      ((n + 2)! : 𝕂)⁻¹ = fn,
      ((ascPochhammer 𝕂 (n + 2)).eval (c - 1 / 2))⁻¹ = pc1,
      ((ascPochhammer 𝕂 1).eval (c + 1 / 2))⁻¹ = pc2
    dsimp only [cayleyRecQ2, cayleyRecQ1, cayleyRecR2, cayleyRecR1, cayleyCertPoly,
      cayleyCertPolyAux]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    ring
  linear_combination hsum + hbd

private theorem cayleyRhs_recurrence {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) (n : ℕ) :
    let B := fun s ↦
      (ascPochhammer 𝕂 s).eval c / (ascPochhammer 𝕂 s).eval (c + 1 / 2) * cayleyOrrCoeff a b c s
    cayleyRecQ2 c n * B (n + 2) + cayleyRecQ1 a b c n * B (n + 1) +
      cayleyRecQ0 a b c n * B n = 0 := by
  intro B
  have hrec := cayleyOrrCoeff_recurrence a b hc n
  have hadd1 : c + 1 / 2 + (n : 𝕂) ≠ 0 := fun h ↦
    hc (2 * (n + 1)) (by push_cast at h ⊢; linear_combination 2 * h)
  have hadd2 : c + 1 / 2 + ((n + 1 : ℕ) : 𝕂) ≠ 0 := fun h ↦
    hc (2 * (n + 2)) (by push_cast at h ⊢; linear_combination 2 * h)
  have heq :
      cayleyRecQ2 c n * B (n + 2) + cayleyRecQ1 a b c n * B (n + 1) +
        cayleyRecQ0 a b c n * B n =
      (ascPochhammer 𝕂 n).eval c * (c + n) * (c + n + 1) *
        (c + 1 / 2 + n) * (c + 1 / 2 + ((n + 1 : ℕ) : 𝕂)) *
        ((ascPochhammer 𝕂 (n + 2)).eval (c + 1 / 2))⁻¹ *
        (cayleyRecR2 c n * cayleyOrrCoeff a b c (n + 2) +
          cayleyRecR1 a b c n * cayleyOrrCoeff a b c (n + 1) +
          cayleyRecR0 a b c n * cayleyOrrCoeff a b c n) := by
    simp only [B]
    rw [div_eq_mul_inv ((ascPochhammer 𝕂 (n + 2)).eval c),
      div_eq_mul_inv ((ascPochhammer 𝕂 (n + 1)).eval c),
      div_eq_mul_inv ((ascPochhammer 𝕂 n).eval c), inv_ascPochhammer_eq hadd1,
      inv_ascPochhammer_eq hadd2, ascPochhammer_succ_eval (n + 1) c, ascPochhammer_succ_eval n c]
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp only [cayleyRecQ2, cayleyRecQ1, cayleyRecQ0]
    ring
  rw [heq, hrec, mul_zero]

private theorem cayleyConvSum_one {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂) {c : 𝕂}
    (hc : ∀ m : ℕ, 2 * c - 1 ≠ -m) :
    (∑ k ∈ range 2, cayleyConvTerm a b c 1 k) =
      (ascPochhammer 𝕂 1).eval c / (ascPochhammer 𝕂 1).eval (c + 1 / 2) *
        cayleyOrrCoeff a b c 1 := by
  have hc0 : 2 * c - 1 ≠ 0 := by simpa using hc 0
  have hc1 : c - 1 / 2 ≠ 0 := fun h ↦ hc 0 (by push_cast; linear_combination 2 * h)
  have hc2 : c + 1 / 2 ≠ 0 := fun h ↦ hc 2 (by push_cast; linear_combination 2 * h)
  have hi0 := mul_inv_cancel₀ hc0
  have hi1 := mul_inv_cancel₀ hc1
  have hi2 := mul_inv_cancel₀ hc2
  have hid : (c + 1 / 2)⁻¹ + (c - 1 / 2)⁻¹ =
      4 * c * (c + 1 / 2)⁻¹ * (2 * c - 1)⁻¹ := by
    refine mul_left_cancel₀ (mul_ne_zero hc2 (mul_ne_zero hc1 hc0)) ?_
    linear_combination
      ((c - 1 / 2) * (2 * c - 1) - 4 * c * (c - 1 / 2) * (2 * c - 1)⁻¹ * (2 * c - 1)) * hi2 +
        (c + 1 / 2) * (2 * c - 1) * hi1 - 4 * c * (c - 1 / 2) * hi0
  rw [sum_range_succ, sum_range_one, cayleyOrrCoeff_def, sum_range_succ, sum_range_one]
  simp only [cayleyConvTerm, ordinaryHypergeometricCoefficient, ascPochhammer_zero,
    Polynomial.eval_one, ascPochhammer_one, Polynomial.eval_X, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, Nat.sub_zero, Nat.sub_self, div_eq_mul_inv]
  linear_combination a * b * hid

end CayleyOrrRecurrence

/-- **Algebraic Cayley–Orr coefficient identity (DLMF 15.16.1–15.16.2).** Over any field `𝕂` of
characteristic zero, if `2 * c - 1` avoids the nonpositive integers, the Cauchy product of the
hypergeometric coefficients of `₂F₁(a, b; c - 1/2; z)` and `₂F₁(c - a, c - b; c + 1/2; z)` equals
`((c)_s / (c + 1/2)_s) * cayleyOrrCoeff a b c s`. -/
theorem sum_ordinaryHypergeometricCoefficient_mul_eq_cayleyOrrCoeff {𝕂 : Type*} [Field 𝕂]
    [CharZero 𝕂] (a b : 𝕂) {c : 𝕂} (hc : ∀ n : ℕ, 2 * c - 1 ≠ -n) (s : ℕ) :
    ∑ k ∈ range (s + 1),
      ordinaryHypergeometricCoefficient a b (c - 1 / 2) k *
        ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2) (s - k) =
      (ascPochhammer 𝕂 s).eval c / (ascPochhammer 𝕂 s).eval (c + 1 / 2) *
        cayleyOrrCoeff a b c s := by
  let S := fun m ↦ ∑ k ∈ range (m + 1), cayleyConvTerm a b c m k
  let B := fun m ↦
    (ascPochhammer 𝕂 m).eval c / (ascPochhammer 𝕂 m).eval (c + 1 / 2) * cayleyOrrCoeff a b c m
  suffices ∀ m : ℕ, S m = B m ∧ S (m + 1) = B (m + 1) from (this s).1
  intro m
  induction m with
  | zero =>
    refine ⟨?_, cayleyConvSum_one a b hc⟩
    simp [S, B, cayleyConvTerm, ordinaryHypergeometricCoefficient]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hS := cayleyConvSum_recurrence a b hc n
    have hB := cayleyRhs_recurrence a b hc n
    have hn2 : (n : 𝕂) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    have hq2 : cayleyRecQ2 c n ≠ 0 := by
      simp only [cayleyRecQ2, cayleyRecR2]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero hn2 ?_) ?_) ?_
      · exact fun h ↦ hc (n + 1) (by push_cast; linear_combination h)
      · exact fun h ↦ hc (2 * n + 2) (by push_cast; linear_combination 2 * h)
      · exact fun h ↦ hc (2 * n + 4) (by push_cast; linear_combination 2 * h)
    have hdiff : cayleyRecQ2 c n * (S (n + 2) - B (n + 2)) = 0 := by
      have : cayleyRecQ2 c n * S (n + 2) + cayleyRecQ1 a b c n * S (n + 1) +
          cayleyRecQ0 a b c n * S n -
          (cayleyRecQ2 c n * B (n + 2) + cayleyRecQ1 a b c n * B (n + 1) +
            cayleyRecQ0 a b c n * B n) = 0 := by
        rw [hS, hB, sub_self]
      rw [ih.1, ih.2] at this
      linear_combination this
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hq2)

end TauCeti

namespace Complex

/-! ### Analytic Cayley–Orr product expansion (DLMF 15.16.1–15.16.2) -/

/-- **Generating function of the Cayley–Orr coefficients (DLMF 15.16.2).** On the open unit disk,
`(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` is represented by the scalar power series with
coefficients `TauCeti.cayleyOrrCoeff a b c`, for all complex parameters `a`, `b`, `c`. -/
theorem hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric (a b c : ℂ) :
    HasFPowerSeriesOnBall
      (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)
      (FormalMultilinearSeries.ofScalars ℂ (TauCeti.cayleyOrrCoeff a b c)) 0 1 := by
  have h1 := one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (c - a - b)
  have hrad := TauCeti.one_le_radius_ordinaryHypergeometricSeries ℂ (2 * a) (2 * b) (2 * c - 1)
  have h2 : HasFPowerSeriesOnBall (₂F₁ (2 * a) (2 * b) (2 * c - 1) : ℂ → ℂ)
      (FormalMultilinearSeries.ofScalars ℂ
        (ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1))) 0 1 :=
    ((ordinaryHypergeometricSeries ℂ (2 * a) (2 * b) (2 * c - 1)).hasFPowerSeriesOnBall
      (zero_lt_one.trans_le hrad)).mono zero_lt_one hrad
  have hmul := h1.mul_ofScalars h2
  have hchoose (j : ℕ) :
      Ring.choose (c - a - b + j - 1) j =
        (j ! : ℂ)⁻¹ * (ascPochhammer ℂ j).eval (c - a - b) := by
    have hshift : c - a - b + j - 1 - j + 1 = c - a - b := by ring
    rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer, hshift,
      Polynomial.ascPochhammer_smeval_eq_eval, smul_eq_mul]
  have hser :
      (FormalMultilinearSeries.ofScalars ℂ fun s ↦
        ∑ k ∈ range (s + 1), Ring.choose (c - a - b + k - 1) k *
          ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) (s - k)) =
      FormalMultilinearSeries.ofScalars ℂ (TauCeti.cayleyOrrCoeff a b c) := by
    congr 1; ext s
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk ↦ ?_
    have hsk : s + 1 - 1 - k = s - k := rfl
    rw [hsk, Nat.sub_sub_self (mem_range_succ_iff.mp hk), hchoose]
  rw [hser] at hmul
  refine hmul.congr fun z _ ↦ ?_
  dsimp only
  have hexp : -(c - a - b) = a + b - c := by ring
  rw [one_div, ← cpow_neg, hexp]

/-- **DLMF 15.16.2 (`HasSum` form).** For `‖z‖ < 1` and arbitrary `a, b, c : ℂ`, the power series
`∑ s, cayleyOrrCoeff a b c s * z ^ s` converges to
`(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)`. -/
theorem hasSum_cayleyOrrCoeff_mul_pow (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun s : ℕ ↦ TauCeti.cayleyOrrCoeff a b c s * z ^ s)
      ((1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z) := by
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using hz
  have hs := (hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric a b c).hasSum hz'
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hs

/-- The Taylor coefficients at `0` of `(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` are
`TauCeti.cayleyOrrCoeff a b c` (DLMF 15.16.2). -/
theorem coeff_taylorSeries_one_sub_cpow_mul_ordinaryHypergeometric (a b c : ℂ) (s : ℕ) :
    PowerSeries.coeff s
      (TauCeti.taylorSeries
        (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z) 0) =
      TauCeti.cayleyOrrCoeff a b c s := by
  rw [(hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric
    a b c).hasFPowerSeriesAt.coeff_taylorSeries, FormalMultilinearSeries.coeff_ofScalars]

/-- Uniqueness of the generating-function coefficients in DLMF 15.16.2: any sequence `A : ℕ → ℂ`
whose power series represents `(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` in a neighborhood of
`0` equals `TauCeti.cayleyOrrCoeff a b c`. -/
theorem eq_cayleyOrrCoeff_of_eventually_hasSum (a b c : ℂ) {A : ℕ → ℂ}
    (hA : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun s : ℕ ↦ A s * z ^ s)
      ((1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)) :
    A = TauCeti.cayleyOrrCoeff a b c := by
  obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.mp hA
  have hρ_pos : 0 < min (r / 2) (1 / 2) := lt_min (half_pos hr0) (by norm_num)
  let ρ : ℝ≥0 := ⟨min (r / 2) (1 / 2), hρ_pos.le⟩
  have hρ : 0 < (ρ : ℝ) := hρ_pos
  have hmem : ((ρ : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_of_nonneg hρ.le]
    exact (min_le_left _ _).trans_lt (half_lt_self hr0)
  have hrad : (ρ : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ A).radius := by
    refine FormalMultilinearSeries.le_radius_of_tendsto _ (r := ρ) (l := 0) ?_
    have ht := (hball ((ρ : ℝ) : ℂ) hmem).summable.tendsto_atTop_zero.norm
    simpa [Real.norm_of_nonneg hρ.le] using ht
  have hpA : HasFPowerSeriesOnBall
      (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)
      (FormalMultilinearSeries.ofScalars ℂ A) 0 (ρ : ℝ≥0∞) := by
    refine ⟨hrad, ENNReal.coe_pos.mpr hρ_pos, fun {y} hy ↦ ?_⟩
    have hyr : y ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right, ← ENNReal.ofReal_coe_nnreal] at hy
      rw [Metric.mem_ball, dist_zero_right]
      exact ((ENNReal.ofReal_lt_ofReal_iff hρ).mp hy).trans
        ((min_le_left _ _).trans_lt (half_lt_self hr0))
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hball y hyr
  have heq := hpA.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric a b c).hasFPowerSeriesAt
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ heq

/-- **Cayley–Orr product expansion on the unit disk (DLMF 15.16.1, `HasFPowerSeriesOnBall` form).**
When `2 * c - 1` avoids the nonpositive integers,
`₂F₁(a, b; c - 1/2; z) * ₂F₁(c - a, c - b; c + 1/2; z)` is represented on the open unit disk by the
scalar power series with coefficients `((c)_s / (c + 1/2)_s) * TauCeti.cayleyOrrCoeff a b c s`. -/
theorem hasFPowerSeriesOnBall_ordinaryHypergeometric_mul_cayleyOrr (a b : ℂ) {c : ℂ}
    (hc : ∀ n : ℕ, 2 * c - 1 ≠ -n) :
    HasFPowerSeriesOnBall
      (fun z : ℂ ↦ ₂F₁ a b (c - 1 / 2) z * ₂F₁ (c - a) (c - b) (c + 1 / 2) z)
      (FormalMultilinearSeries.ofScalars ℂ fun s : ℕ ↦
        (ascPochhammer ℂ s).eval c / (ascPochhammer ℂ s).eval (c + 1 / 2) *
          TauCeti.cayleyOrrCoeff a b c s) 0 1 := by
  have hr₁ := TauCeti.one_le_radius_ordinaryHypergeometricSeries ℂ a b (c - 1 / 2)
  have hr₂ := TauCeti.one_le_radius_ordinaryHypergeometricSeries ℂ (c - a) (c - b) (c + 1 / 2)
  have hp₁ : HasFPowerSeriesOnBall (₂F₁ a b (c - 1 / 2) : ℂ → ℂ)
      (FormalMultilinearSeries.ofScalars ℂ
        (ordinaryHypergeometricCoefficient a b (c - 1 / 2))) 0 1 :=
    ((ordinaryHypergeometricSeries ℂ a b (c - 1 / 2)).hasFPowerSeriesOnBall
      (zero_lt_one.trans_le hr₁)).mono zero_lt_one hr₁
  have hp₂ : HasFPowerSeriesOnBall (₂F₁ (c - a) (c - b) (c + 1 / 2) : ℂ → ℂ)
      (FormalMultilinearSeries.ofScalars ℂ
        (ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2))) 0 1 :=
    ((ordinaryHypergeometricSeries ℂ (c - a) (c - b) (c + 1 / 2)).hasFPowerSeriesOnBall
      (zero_lt_one.trans_le hr₂)).mono zero_lt_one hr₂
  simpa only [TauCeti.sum_ordinaryHypergeometricCoefficient_mul_eq_cayleyOrrCoeff a b hc] using
    hp₁.mul_ofScalars hp₂

/-- **Cayley–Orr product expansion (DLMF 15.16.1, `HasSum` form).** For `‖z‖ < 1` and
`2 * c - 1 ∉ -ℕ`, `₂F₁(a, b; c - 1/2; z) * ₂F₁(c - a, c - b; c + 1/2; z)` expands as
`∑ s, ((c)_s / (c + 1/2)_s) * cayleyOrrCoeff a b c s * z ^ s`. -/
theorem hasSum_ordinaryHypergeometric_mul_cayleyOrr (a b : ℂ) {c z : ℂ}
    (hc : ∀ n : ℕ, 2 * c - 1 ≠ -n) (hz : ‖z‖ < 1) :
    HasSum
      (fun s : ℕ ↦ (ascPochhammer ℂ s).eval c / (ascPochhammer ℂ s).eval (c + 1 / 2) *
        TauCeti.cayleyOrrCoeff a b c s * z ^ s)
      (₂F₁ a b (c - 1 / 2) z * ₂F₁ (c - a) (c - b) (c + 1 / 2) z) := by
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using hz
  have hs := (hasFPowerSeriesOnBall_ordinaryHypergeometric_mul_cayleyOrr a b hc).hasSum hz'
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hs

/-! ### Burchnall–Chaundy two-variable product expansion (DLMF 15.16.3) -/

private theorem hasSum_coeff_regularizedGaussHGFunSeries (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ (regularizedGaussHGFunSeries a b c).coeff k * z ^ k)
      (regularizedGaussHGFun a b c z) := by
  have hmem : z ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
    Metric.eball_subset_eball (radius_regularizedGaussHGFunSeries_ge_one a b c)
      (by simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
        ENNReal.ofReal_lt_one] using hz)
  have hs := (regularizedGaussHGFunSeries a b c).hasSum hmem
  simpa [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hs

private theorem regularizedGaussHGFun_step_one (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      c * (1 - z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z +
        (c - a) * (c - b) * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z := by
  have hs₀ := (hasSum_nat_add_iff' 1).mpr (hasSum_coeff_regularizedGaussHGFunSeries a b c hz)
  have hs₁ := (hasSum_nat_add_iff' 1).mpr
    ((hasSum_coeff_regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1) hz).mul_left c)
  have hs₂ := (hasSum_coeff_regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1) hz).mul_left
    (c * z)
  have hs₃ := (hasSum_coeff_regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 2) hz).mul_left
    ((c - a) * (c - b) * z)
  have hcomb := (hs₁.sub hs₂).add hs₃
  have hzero : (regularizedGaussHGFunSeries a b c).coeff 0 * z ^ 0 =
      c * ((regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).coeff 0 * z ^ 0) := by
    simp [coeff_regularizedGaussHGFunSeries, ← one_div_Gamma_eq_self_mul_one_div_Gamma_add_one c]
  have hterm : _ := hs₀.unique (hcomb.congr_fun fun k ↦ ?_)
  · simp only [range_one, sum_singleton, hzero] at hterm
    linear_combination hterm
  · have hap (x : ℂ) : (ascPochhammer ℂ (k + 1)).eval x = x * (ascPochhammer ℂ k).eval (x + 1) := by
      simpa [Polynomial.eval_mul, Polynomial.eval_comp] using
        congrArg (Polynomial.eval x) (ascPochhammer_succ_left (S := ℂ) k)
    have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + 1 + k)
    have hc1 : c + (k + 1 : ℕ) = c + 1 + k := by push_cast; ring
    have hc2 : c + 1 + (k + 1 : ℕ) = c + 1 + k + 1 := by push_cast; ring
    have hc3 : c + 2 + (k : ℂ) = c + 1 + k + 1 := by ring
    have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hfk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    simp only [coeff_regularizedGaussHGFunSeries, hc1, hc2, hc3, div_eq_mul_inv, mul_inv,
      Nat.factorial_succ, Nat.cast_mul, pow_succ, hap a, hap b, ascPochhammer_succ_eval]
    rw [hΓ]
    field_simp; push_cast; ring

private theorem burchnallChaundy_step_mid (a b c z : ℂ) {n k : ℕ} (hkn : k + 1 ≤ n) :
    c * (1 - z) * ((n.choose (k + 1) : ℂ) *
        (ascPochhammer ℂ (k + 1)).eval (c + 1 - (a + 1)) *
        (ascPochhammer ℂ (k + 1)).eval (c + 1 - (b + 1)) *
        (ascPochhammer ℂ (n - (k + 1))).eval (c + 1 + (k + 1 : ℕ)) * z ^ (k + 1) *
        (1 - z) ^ (n - (k + 1)) *
        regularizedGaussHGFun (a + 1 + n) (b + 1 + n) (c + 1 + n + (k + 1 : ℕ)) z) +
      (c - a) * (c - b) * z * ((n.choose k : ℂ) *
        (ascPochhammer ℂ k).eval (c + 2 - (a + 1)) *
        (ascPochhammer ℂ k).eval (c + 2 - (b + 1)) *
        (ascPochhammer ℂ (n - k)).eval (c + 2 + k) * z ^ k * (1 - z) ^ (n - k) *
        regularizedGaussHGFun (a + 1 + n) (b + 1 + n) (c + 2 + n + k) z) =
    ((n + 1).choose (k + 1) : ℂ) * (ascPochhammer ℂ (k + 1)).eval (c - a) *
      (ascPochhammer ℂ (k + 1)).eval (c - b) *
      (ascPochhammer ℂ (n + 1 - (k + 1))).eval (c + (k + 1 : ℕ)) * z ^ (k + 1) *
      (1 - z) ^ (n + 1 - (k + 1)) *
      regularizedGaussHGFun (a + (n + 1 : ℕ)) (b + (n + 1 : ℕ))
        (c + (n + 1 : ℕ) + (k + 1 : ℕ)) z := by
  have hpoch_left (x : ℂ) (m : ℕ) :
      x * (ascPochhammer ℂ m).eval (x + 1) = (ascPochhammer ℂ (m + 1)).eval x := by
    simpa [Polynomial.eval_mul, Polynomial.eval_comp] using
      (congrArg (Polynomial.eval x) (ascPochhammer_succ_left (S := ℂ) m)).symm
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hkn
  have hs1 : n - (k + 1) = l := by omega
  have hs2 : n - k = l + 1 := by omega
  have hs3 : n + 1 - (k + 1) = l + 1 := by omega
  have hp1 := hpoch_left (c + (k + 1 : ℕ)) l
  have hp2 := hpoch_left (c - a) k
  have hp3 := hpoch_left (c - b) k
  have hp4 : (ascPochhammer ℂ (l + 1)).eval (c + (k + 1 : ℕ) + 1) =
      (ascPochhammer ℂ l).eval (c + (k + 1 : ℕ) + 1) * (c + (k + 1 : ℕ) + (l + 1 : ℕ)) := by
    rw [ascPochhammer_succ_eval]; push_cast; ring
  have hchoose_id :
      c * (n.choose (k + 1) : ℂ) * (ascPochhammer ℂ l).eval (c + (k + 1 : ℕ) + 1) +
        (n.choose k : ℂ) * (ascPochhammer ℂ (l + 1)).eval (c + (k + 1 : ℕ) + 1) =
      ((n + 1).choose (k + 1) : ℂ) * (ascPochhammer ℂ (l + 1)).eval (c + (k + 1 : ℕ)) := by
    have hstep : (n.choose (k + 1) : ℂ) * (k + 1 : ℕ) = (n.choose k : ℂ) * (l + 1 : ℕ) := by
      have h := Nat.choose_succ_right_eq n k
      rw [hs2] at h
      exact_mod_cast h
    have hpas : ((n + 1).choose (k + 1) : ℂ) = (n.choose k : ℂ) + (n.choose (k + 1) : ℂ) := by
      exact_mod_cast Nat.choose_succ_succ n k
    rw [hp4, ← hp1, hpas]
    linear_combination -(ascPochhammer ℂ l).eval (c + (k + 1 : ℕ) + 1) * hstep
  have he1 : c + 1 - (a + 1) = c - a := by ring
  have he2 : c + 1 - (b + 1) = c - b := by ring
  have he3 : c + 2 - (a + 1) = c - a + 1 := by ring
  have he4 : c + 2 - (b + 1) = c - b + 1 := by ring
  have he5 : c + 1 + (k + 1 : ℕ) = c + (k + 1 : ℕ) + 1 := by ring
  have he6 : c + 2 + (k : ℂ) = c + (k + 1 : ℕ) + 1 := by push_cast; ring
  have he7 : a + 1 + (n : ℂ) = a + (n + 1 : ℕ) := by push_cast; ring
  have he8 : b + 1 + (n : ℂ) = b + (n + 1 : ℕ) := by push_cast; ring
  have he9 : c + 1 + (n : ℂ) + (k + 1 : ℕ) = c + (n + 1 : ℕ) + (k + 1 : ℕ) := by push_cast; ring
  have he10 : c + 2 + (n : ℂ) + k = c + (n + 1 : ℕ) + (k + 1 : ℕ) := by push_cast; ring
  simp only [hs1, hs2, hs3, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, pow_succ]
  rw [← hp2, ← hp3]
  linear_combination
    (c - a) * (ascPochhammer ℂ k).eval (c - a + 1) *
      (c - b) * (ascPochhammer ℂ k).eval (c - b + 1) *
      (z ^ k * z) * ((1 - z) ^ l * (1 - z)) *
      regularizedGaussHGFun (a + (n + 1 : ℕ)) (b + (n + 1 : ℕ))
        (c + (n + 1 : ℕ) + (k + 1 : ℕ)) z * hchoose_id

private theorem burchnallChaundy_step_bd (a b c z : ℂ) (n : ℕ) :
    c * (1 - z) * ((n.choose 0 : ℂ) * (ascPochhammer ℂ 0).eval (c + 1 - (a + 1)) *
        (ascPochhammer ℂ 0).eval (c + 1 - (b + 1)) *
        (ascPochhammer ℂ (n - 0)).eval (c + 1 + (0 : ℕ)) * z ^ 0 * (1 - z) ^ (n - 0) *
        regularizedGaussHGFun (a + 1 + n) (b + 1 + n) (c + 1 + n + (0 : ℕ)) z) +
      (c - a) * (c - b) * z * ((n.choose n : ℂ) * (ascPochhammer ℂ n).eval (c + 2 - (a + 1)) *
        (ascPochhammer ℂ n).eval (c + 2 - (b + 1)) *
        (ascPochhammer ℂ (n - n)).eval (c + 2 + n) * z ^ n * (1 - z) ^ (n - n) *
        regularizedGaussHGFun (a + 1 + n) (b + 1 + n) (c + 2 + n + n) z) =
    ((n + 1).choose 0 : ℂ) * (ascPochhammer ℂ 0).eval (c - a) *
        (ascPochhammer ℂ 0).eval (c - b) *
        (ascPochhammer ℂ (n + 1 - 0)).eval (c + (0 : ℕ)) * z ^ 0 * (1 - z) ^ (n + 1 - 0) *
        regularizedGaussHGFun (a + (n + 1 : ℕ)) (b + (n + 1 : ℕ))
          (c + (n + 1 : ℕ) + (0 : ℕ)) z +
      ((n + 1).choose (n + 1) : ℂ) * (ascPochhammer ℂ (n + 1)).eval (c - a) *
        (ascPochhammer ℂ (n + 1)).eval (c - b) *
        (ascPochhammer ℂ (n + 1 - (n + 1))).eval (c + (n + 1 : ℕ)) * z ^ (n + 1) *
        (1 - z) ^ (n + 1 - (n + 1)) *
        regularizedGaussHGFun (a + (n + 1 : ℕ)) (b + (n + 1 : ℕ))
          (c + (n + 1 : ℕ) + (n + 1 : ℕ)) z := by
  have hpoch_left (x : ℂ) :
      x * (ascPochhammer ℂ n).eval (x + 1) = (ascPochhammer ℂ (n + 1)).eval x := by
    simpa [Polynomial.eval_mul, Polynomial.eval_comp] using
      (congrArg (Polynomial.eval x) (ascPochhammer_succ_left (S := ℂ) n)).symm
  have hpa := hpoch_left c
  have hpca := hpoch_left (c - a)
  have hpcb := hpoch_left (c - b)
  have ha1 : a + 1 + (n : ℂ) = a + (n + 1 : ℕ) := by push_cast; ring
  have hb1 : b + 1 + (n : ℂ) = b + (n + 1 : ℕ) := by push_cast; ring
  have hc1 : c + 1 + (n : ℂ) = c + (n + 1 : ℕ) := by push_cast; ring
  have hc2 : c + 2 + (n : ℂ) + n = c + (n + 1 : ℕ) + (n + 1 : ℕ) := by push_cast; ring
  have hca2 : c + 2 - (a + 1) = c - a + 1 := by ring
  have hcb2 : c + 2 - (b + 1) = c - b + 1 := by ring
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, ascPochhammer_zero,
    Polynomial.eval_one, Nat.sub_zero, Nat.sub_self, Nat.cast_zero, add_zero, pow_zero,
    one_mul, mul_one, pow_succ, ha1, hb1, hc1, hc2, hca2, hcb2]
  rw [← hpa, ← hpca, ← hpcb]
  ring

/-- **Finite Burchnall–Chaundy expansion on the open unit disk.** For every `n : ℕ`, `‖z‖ < 1`,
and arbitrary complex parameters `a`, `b`, `c`, `𝐅(a, b; c; z)` expands as a finite binomial sum
in `z ^ s * (1 - z) ^ (n - s) * 𝐅(a + n, b + n; c + n + s; z)`. -/
theorem regularizedGaussHGFun_eq_sum_choose (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    regularizedGaussHGFun a b c z =
      ∑ s ∈ range (n + 1),
        (n.choose s : ℂ) * (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
          (ascPochhammer ℂ (n - s)).eval (c + s) * z ^ s * (1 - z) ^ (n - s) *
            regularizedGaussHGFun (a + n) (b + n) (c + n + s) z := by
  induction n generalizing a b c with
  | zero => simp
  | succ n ih =>
    have h₁ := congrArg (c * (1 - z) * ·) (ih (a + 1) (b + 1) (c + 1))
    rw [mul_sum, sum_range_succ'] at h₁
    have h₂ := congrArg ((c - a) * (c - b) * z * ·) (ih (a + 1) (b + 1) (c + 2))
    rw [mul_sum, sum_range_succ] at h₂
    rw [regularizedGaussHGFun_step_one a b c hz, h₁, h₂]
    conv_rhs => rw [sum_range_succ, sum_range_succ']
    have hmid := sum_congr (s₁ := range n) rfl fun k hk ↦
      burchnallChaundy_step_mid a b c z (mem_range.mp hk)
    rw [sum_add_distrib] at hmid
    have hbd := burchnallChaundy_step_bd a b c z n
    linear_combination hmid + hbd

private theorem summable_norm_regularizedGaussHGFun_add_double (a b c : ℂ) {z w : ℂ}
    (hzw : ‖z‖ + ‖w‖ < 1) :
    Summable fun p : ℕ × ℕ ↦
      ‖((p.1 + p.2).choose p.1 : ℂ) * (regularizedGaussHGFunSeries a b c).coeff (p.1 + p.2) *
        w ^ p.1 * z ^ p.2‖ := by
  set R : ℝ := ‖z‖ + ‖w‖
  have hR0 : 0 ≤ R := by positivity
  have hmem : (R : ℂ) ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
    Metric.eball_subset_eball (radius_regularizedGaussHGFunSeries_ge_one a b c)
      (by simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one,
        norm_real, Real.norm_of_nonneg hR0] using hzw)
  have hsumR := (regularizedGaussHGFunSeries a b c).summable_norm_apply hmem
  have hdiag : Summable fun m : ℕ ↦
      ∑ p ∈ antidiagonal m,
        ‖(m.choose p.1 : ℂ) * (regularizedGaussHGFunSeries a b c).coeff m *
          w ^ p.1 * z ^ p.2‖ := by
    refine hsumR.congr fun m ↦ ?_
    have hpow : R ^ m = ∑ p ∈ antidiagonal m, (m.choose p.1 : ℝ) * ‖w‖ ^ p.1 * ‖z‖ ^ p.2 := by
      simpa [R, add_comm ‖z‖ ‖w‖, mul_comm, mul_left_comm, mul_assoc] using
        (Commute.all ‖w‖ ‖z‖).add_pow' m
    simp only [regularizedGaussHGFunSeries, regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hR0, norm_natCast]
    rw [hpow, mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  have hsigma : Summable fun q : Σ m : ℕ, antidiagonal m ↦
      ‖((q.2.1.1 + q.2.1.2).choose q.2.1.1 : ℂ) *
        (regularizedGaussHGFunSeries a b c).coeff (q.2.1.1 + q.2.1.2) *
        w ^ q.2.1.1 * z ^ q.2.1.2‖ := by
    rw [summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)]
    refine ⟨fun _ ↦ Summable.of_finite, hdiag.congr fun m ↦ ?_⟩
    rw [tsum_fintype]
    dsimp only
    rw [sum_coe_sort (antidiagonal m) (fun p : ℕ × ℕ ↦
      ‖((p.1 + p.2).choose p.1 : ℂ) *
        (regularizedGaussHGFunSeries a b c).coeff (p.1 + p.2) * w ^ p.1 * z ^ p.2‖)]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [mem_antidiagonal.mp hp]
  exact HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hsigma

/-- **Taylor addition series for `regularizedGaussHGFun`.** Whenever `‖z‖ + ‖w‖ < 1` and
`a, b, c : ℂ` are arbitrary, `𝐅(a, b; c; z + w)` expands in powers of `w` with coefficients
`((a)_n (b)_n / n!) 𝐅(a + n, b + n; c + n; z)`. -/
theorem hasSum_regularizedGaussHGFun_add (a b c : ℂ) {z w : ℂ} (hzw : ‖z‖ + ‖w‖ < 1) :
    HasSum
      (fun n : ℕ ↦ (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / n ! * w ^ n *
        regularizedGaussHGFun (a + n) (b + n) (c + n) z)
      (regularizedGaussHGFun a b c (z + w)) := by
  let F : ℕ × ℕ → ℂ := fun p ↦
    ((p.1 + p.2).choose p.1 : ℂ) * (regularizedGaussHGFunSeries a b c).coeff (p.1 + p.2) *
      w ^ p.1 * z ^ p.2
  have hF : Summable F := (summable_norm_regularizedGaussHGFun_add_double a b c hzw).of_norm
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg w]
  have hzw' : ‖z + w‖ < 1 := (norm_add_le z w).trans_lt hzw
  have h₁ : HasSum
      (fun n : ℕ ↦ (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / n ! * w ^ n *
        regularizedGaussHGFun (a + n) (b + n) (c + n) z) (∑' p, F p) := by
    refine hF.hasSum.prod_fiberwise fun n ↦ ?_
    refine ((hasSum_coeff_regularizedGaussHGFunSeries (a + n) (b + n) (c + n) hz).mul_left
      ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b / n ! * w ^ n)).congr_fun
      fun k ↦ ?_
    have hch : ((n + k).choose n : ℂ) * ((n + k)! : ℂ)⁻¹ = (n ! : ℂ)⁻¹ * (k ! : ℂ)⁻¹ := by
      have hcast : ((n + k).choose n : ℂ) * n ! * k ! = ((n + k)! : ℂ) := by
        exact_mod_cast (by simpa [add_tsub_cancel_left] using
          Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right n k))
      have hfn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hfk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hfnk : ((n + k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      refine mul_left_cancel₀ (mul_ne_zero hfn (mul_ne_zero hfk hfnk)) ?_
      rw [show (n ! : ℂ) * (k ! * (n + k)!) * (((n + k).choose n : ℂ) * ((n + k)! : ℂ)⁻¹) =
          (((n + k).choose n : ℂ) * n ! * k !) * ((n + k)! * ((n + k)! : ℂ)⁻¹) by ring,
        show (n ! : ℂ) * (k ! * (n + k)!) * ((n ! : ℂ)⁻¹ * (k ! : ℂ)⁻¹) =
          (n ! * (n ! : ℂ)⁻¹) * (k ! * (k ! : ℂ)⁻¹) * ((n + k)! : ℂ) by ring,
        mul_inv_cancel₀ hfnk, mul_inv_cancel₀ hfn, mul_inv_cancel₀ hfk, hcast]
      ring
    have hc_eq : c + ((n + k : ℕ) : ℂ) = c + n + k := by push_cast; ring
    simp only [F, coeff_regularizedGaussHGFunSeries, TauCeti.ascPochhammer_add_eval a n k,
      TauCeti.ascPochhammer_add_eval b n k, hc_eq, div_eq_mul_inv, mul_inv]
    linear_combination
      (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ k).eval (a + n) *
        (ascPochhammer ℂ n).eval b * (ascPochhammer ℂ k).eval (b + n) *
        (Gamma (c + n + k))⁻¹ * w ^ n * z ^ k * hch
  have h₂ : HasSum (fun m : ℕ ↦ (regularizedGaussHGFunSeries a b c).coeff m * (z + w) ^ m)
      (∑' p, F p) := by
    have h := (HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hF.hasSum).sigma
      fun m ↦ hasSum_fintype _
    simp only [Function.comp_apply, HasAntidiagonal.sigmaAntidiagonalEquivProd_apply,
      sum_coe_sort (antidiagonal _) F] at h
    refine h.congr_fun fun m ↦ ?_
    rw [add_comm z w, (Commute.all w z).add_pow', mul_sum]
    refine sum_congr rfl fun p hp ↦ ?_
    dsimp only [F]
    rw [nsmul_eq_mul, mem_antidiagonal.mp hp]
    ring
  rwa [← (hasSum_coeff_regularizedGaussHGFunSeries a b c hzw').unique h₂] at h₁

section BurchnallChaundyBounds

private theorem factorial_add_sq_le (m s : ℕ) :
    (m + s)! * (m + s)! ≤ m ! * (m + 2 * s)! := by
  have h1 : (m + s)! = m ! * (m + 1).ascFactorial s := (Nat.factorial_mul_ascFactorial m s).symm
  have h2 : (m + 2 * s)! = (m + s)! * (m + s + 1).ascFactorial s := by
    simpa [Nat.two_mul, add_assoc] using (Nat.factorial_mul_ascFactorial (m + s) s).symm
  rw [h2, ← mul_assoc]
  nth_rw 1 [h1]
  rw [mul_right_comm]
  exact Nat.mul_le_mul_left _ (Nat.ascFactorial_le s (by omega))

private theorem norm_ascPochhammer_le_pow_mul_factorial {x : ℂ} {N : ℕ} (hx : ‖x‖ ≤ N) (m : ℕ) :
    ‖(ascPochhammer ℂ m).eval x‖ ≤ ((m + N : ℝ) ^ N) * m ! := by
  have hfac : ‖(ascPochhammer ℂ m).eval x‖ ≤ ((m + N)! : ℝ) := by
    induction m with
    | zero =>
      simp only [ascPochhammer_zero, Polynomial.eval_one, norm_one, zero_add]
      exact_mod_cast Nat.factorial_pos N
    | succ m ih =>
      have hsucc : m + 1 + N = (m + N) + 1 := by omega
      rw [ascPochhammer_succ_eval, norm_mul, hsucc, Nat.factorial_succ, Nat.mul_comm, Nat.cast_mul]
      have hxm : ‖x + (m : ℂ)‖ ≤ ((m + N + 1 : ℕ) : ℝ) := by
        calc ‖x + (m : ℂ)‖ ≤ ‖x‖ + ‖(m : ℂ)‖ := norm_add_le _ _
          _ = ‖x‖ + m := by rw [norm_natCast]
          _ ≤ N + m := by linarith
          _ ≤ ((m + N + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact mul_le_mul ih hxm (norm_nonneg _) (by positivity)
  refine hfac.trans ?_
  have hpow : (m + N)! ≤ (m + N) ^ N * m ! := by
    rw [← Nat.factorial_mul_ascFactorial m N, mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.ascFactorial_le_pow_add m N)
  exact_mod_cast hpow

private noncomputable def bcTerm (a b c : ℂ) (s : ℕ) (z ζ : ℂ) : ℂ :=
  (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
      (s ! * Gamma (c + s)) * (z * ζ) ^ s *
    regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ)

private noncomputable def bcDoubleTerm (a b c z ζ : ℂ) (p : ℕ × ℕ) : ℂ :=
  let s := p.1
  let j := p.2
  (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
      (s ! * Gamma (c + s)) * (z * ζ) ^ s *
    ((ascPochhammer ℂ j).eval (a + s) * (ascPochhammer ℂ j).eval (b + s) / j ! *
      (ζ * (1 - z)) ^ j *
      regularizedGaussHGFun (a + s + j) (b + s + j) (c + 2 * s + j) z)

private theorem bc_factorial_ratio_le (s j k : ℕ) :
    (((s + (j + k))! : ℝ) * (s + (j + k))! * s ! * s !) /
      ((s ! : ℝ) * s ! * j ! * k ! * (2 * s + (j + k))!) ≤ ((j + k).choose j : ℝ) := by
  set m := j + k
  rw [div_le_iff₀ (by positivity)]
  have hsq : ((s + m)! : ℝ) * (s + m)! ≤ m ! * (2 * s + m)! := by
    simpa [add_comm] using (Nat.cast_le (α := ℝ)).mpr (factorial_add_sq_le m s)
  have hch : (m ! : ℝ) = (m.choose j : ℝ) * j ! * k ! := by
    exact_mod_cast (by simpa [m, add_tsub_cancel_left] using
      (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j k)).symm)
  calc ((s + m)! : ℝ) * (s + m)! * s ! * s !
      ≤ (m ! * (2 * s + m)!) * s ! * s ! := by gcongr
    _ = (m.choose j : ℝ) * ((s ! : ℝ) * s ! * j ! * k ! * (2 * s + m)!) := by rw [hch]; ring

private theorem exists_bc_coeff_bound (a b c : ℂ) :
    ∃ K : ℝ, ∃ P Q : ℕ, 0 ≤ K ∧ ∀ s j k : ℕ,
      ‖(ascPochhammer ℂ (s + j + k)).eval a * (ascPochhammer ℂ (s + j + k)).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
        (s ! * Gamma (c + s) * j ! * k ! * Gamma (c + (2 * s + j + k : ℕ)))‖ ≤
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
  have h1 := norm_ascPochhammer_le_pow_mul_factorial haN (s + m)
  have h2 := norm_ascPochhammer_le_pow_mul_factorial hbN (s + m)
  have h3 := norm_ascPochhammer_le_pow_mul_factorial hcaN s
  have h4 := norm_ascPochhammer_le_pow_mul_factorial hcbN s
  have h5 := hΓ s; have h6 := hΓ (2 * s + m); have hfac := bc_factorial_ratio_le s j k
  have hsm_ge : (s : ℝ) + m + 1 ≤ ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
    nlinarith [s.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]
  have hp1 : ((s + m + N : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
    push_cast; nlinarith [N.cast_nonneg (α := ℝ), s.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ),
      hsm_ge]
  have hp2 : ((s + N : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * ((s : ℝ) + 1) := by
    push_cast; nlinarith [N.cast_nonneg (α := ℝ), s.cast_nonneg (α := ℝ)]
  have hp3 : ((2 * s + m : ℕ) : ℝ) + 1 ≤ 2 * ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
    push_cast; nlinarith [s.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]
  rw [show s + j + k = s + m by omega, show 2 * s + j + k = 2 * s + m by omega, div_eq_mul_inv]
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

private theorem summable_pow_add_one_mul_geometric {Q : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun m : ℕ ↦ ((m : ℝ) + 1) ^ Q * r ^ m := by
  have h := summable_pow_mul_geometric_of_norm_lt_one Q (r := r)
    (by rwa [Real.norm_of_nonneg hr0])
  by_cases hr : r = 0
  · refine summable_of_ne_finset_zero (s := {0}) fun m hm ↦ ?_
    simp [hr, zero_pow (Finset.mem_singleton.not.mp hm)]
  · refine (((summable_nat_add_iff 1).mpr h).mul_left r⁻¹).congr fun m ↦ ?_
    push_cast
    field_simp
    ring

private theorem norm_bcGenTerm_coeff_eq (a b c u v y : ℂ) (s j k : ℕ) :
    ‖((ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
        (s ! * Gamma (c + s)) * u ^ s *
        ((ascPochhammer ℂ j).eval (a + s) * (ascPochhammer ℂ j).eval (b + s) / j ! * v ^ j)) *
        ((regularizedGaussHGFunSeries (a + s + j) (b + s + j) (c + 2 * s + j)).coeff k *
          y ^ k)‖ =
      ‖(ascPochhammer ℂ (s + j + k)).eval a * (ascPochhammer ℂ (s + j + k)).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
        (s ! * Gamma (c + s) * j ! * k ! * Gamma (c + (2 * s + j + k : ℕ)))‖ *
        ‖u‖ ^ s * ‖v‖ ^ j * ‖y‖ ^ k := by
  have hp1 : (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ j).eval (a + s) *
      (ascPochhammer ℂ k).eval (a + s + j) = (ascPochhammer ℂ (s + j + k)).eval a := by
    rw [TauCeti.ascPochhammer_add_eval a (s + j) k, TauCeti.ascPochhammer_add_eval a s j]
    push_cast; ring_nf
  have hp2 : (ascPochhammer ℂ s).eval b * (ascPochhammer ℂ j).eval (b + s) *
      (ascPochhammer ℂ k).eval (b + s + j) = (ascPochhammer ℂ (s + j + k)).eval b := by
    rw [TauCeti.ascPochhammer_add_eval b (s + j) k, TauCeti.ascPochhammer_add_eval b s j]
    push_cast; ring_nf
  have hc_eq : c + 2 * (s : ℂ) + j + k = c + (2 * s + j + k : ℕ) := by push_cast; ring
  simp only [coeff_regularizedGaussHGFunSeries, hc_eq]
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
      ‖(ascPochhammer ℂ (s + j + k)).eval a * (ascPochhammer ℂ (s + j + k)).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
        (s ! * Gamma (c + s) * j ! * k ! * Gamma (c + (2 * s + j + k : ℕ)))‖ ≤
        K * ((s : ℝ) + 1) ^ P * ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ))
    (s j : ℕ)
    (hrow : Summable fun k : ℕ ↦
      ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) :
    ‖(ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
        (s ! * Gamma (c + s)) * u ^ s *
        ((ascPochhammer ℂ j).eval (a + s) * (ascPochhammer ℂ j).eval (b + s) / j ! * v ^ j *
          regularizedGaussHGFun (a + s + j) (b + s + j) (c + 2 * s + j) y)‖ ≤
      K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s *
        (∑' k : ℕ, ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) := by
  set pref := (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
    (s ! * Gamma (c + s)) * u ^ s *
    ((ascPochhammer ℂ j).eval (a + s) * (ascPochhammer ℂ j).eval (b + s) / j ! * v ^ j)
  have hsy := (hasSum_coeff_regularizedGaussHGFunSeries (a + s + j) (b + s + j)
    (c + 2 * s + j) hy).mul_left pref
  have hterm_le (k : ℕ) :
      ‖pref * ((regularizedGaussHGFunSeries (a + s + j) (b + s + j) (c + 2 * s + j)).coeff k *
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
  have hlhs :
      (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
          (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * Gamma (c + s)) * u ^ s *
          ((ascPochhammer ℂ j).eval (a + s) * (ascPochhammer ℂ j).eval (b + s) / j ! * v ^ j *
            regularizedGaussHGFun (a + s + j) (b + s + j) (c + 2 * s + j) y) =
        pref * regularizedGaussHGFun (a + s + j) (b + s + j) (c + 2 * s + j) y := by
    simp only [pref, mul_assoc]
  rw [hlhs, ← hsy.tsum_eq]
  exact (norm_tsum_le_tsum_norm hsum_norm).trans
    ((Summable.tsum_le_tsum hterm_le hsum_norm hmaj).trans_eq (hrow.tsum_mul_left _))

private theorem norm_bcTerm_le {a b c z ζ : ℂ} {K r : ℝ} {P Q : ℕ}
    (hz : ‖z‖ ≤ r) (hw : ‖z + ζ - z * ζ‖ ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1) (_ : 0 ≤ K)
    (hbound : ∀ s j k : ℕ,
      ‖(ascPochhammer ℂ (s + j + k)).eval a * (ascPochhammer ℂ (s + j + k)).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
        (s ! * Gamma (c + s) * j ! * k ! * Gamma (c + (2 * s + j + k : ℕ)))‖ ≤
        K * ((s : ℝ) + 1) ^ P * ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ))
    (s : ℕ) :
    ‖bcTerm a b c s z ζ‖ ≤
      K * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) * (((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s) := by
  set w := z + ζ - z * ζ
  have hw1 : ‖w‖ < 1 := hw.trans_lt hr1
  have hrow_w0 := summable_pow_add_one_mul_geometric (Q := Q) (norm_nonneg w) hw1
  have hrow_w : Summable fun k : ℕ ↦
      (((0 : ℕ) + (k : ℝ)) + 1) ^ Q * ((0 + k).choose 0 : ℝ) * ‖(1 : ℂ)‖ ^ 0 * ‖w‖ ^ k :=
    hrow_w0.congr fun k ↦ by simp
  have hrow_r : Summable fun k : ℕ ↦ ((k : ℝ) + 1) ^ Q * r ^ k :=
    summable_pow_add_one_mul_geometric hr0 hr1
  have h0 := norm_bcGenTerm_le (u := z * ζ) (v := 1) hw1 hbound s 0 hrow_w
  have hbc : ‖bcTerm a b c s z ζ‖ ≤
      K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k) := by
    simpa [bcTerm, w] using h0
  have htsum : (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k) ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k :=
    Summable.tsum_le_tsum (fun k ↦ by gcongr) hrow_w0 hrow_r
  have huz : ‖z * ζ‖ ^ s ≤ (r * ‖ζ‖) ^ s := by
    rw [norm_mul]
    exact pow_le_pow_left₀ (by positivity) (by gcongr) s
  refine hbc.trans ?_
  calc K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k)
      ≤ K * ((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) := by
        gcongr
    _ = K * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) * (((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s) := by
        ring

private theorem differentiableOn_tsum_bcTerm (a b c : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z ζ)
      {z : ℂ | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1} := by
  intro z₀ hz₀
  set r : ℝ := (max ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖ + 1) / 2
  have hmax : max ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖ < 1 := max_lt hz₀.1 hz₀.2
  have hr_lt : r < 1 := by simp only [r]; linarith
  have hr0 : 0 ≤ r := by positivity
  let V : Set ℂ := {z : ℂ | ‖z‖ < r ∧ ‖z + ζ - z * ζ‖ < r}
  have hcont : Continuous fun z : ℂ ↦ ‖z + ζ - z * ζ‖ := by fun_prop
  have hV_open : IsOpen V :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt hcont continuous_const)
  have hz₀V : z₀ ∈ V :=
    ⟨by simp only [r]; linarith [le_max_left ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖, hz₀.1, hz₀.2],
      by simp only [r]; linarith [le_max_right ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖, hz₀.1, hz₀.2]⟩
  obtain ⟨K, P, Q, hK0, hbound⟩ := exists_bc_coeff_bound a b c
  have hrζ_lt : r * ‖ζ‖ < 1 := by nlinarith [norm_nonneg ζ]
  have hg₁ : Summable fun s : ℕ ↦
      K * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) * (((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s) :=
    (summable_pow_add_one_mul_geometric (by positivity) hrζ_lt).mul_left _
  have hdiffV : DifferentiableOn ℂ (fun z : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z ζ) V := by
    refine differentiableOn_tsum_of_summable_norm hg₁ (fun s z hzV ↦ ?_) hV_open fun s z hzV ↦
      norm_bcTerm_le hzV.1.le hzV.2.le hr0 hr_lt hK0 hbound s
    have hw : z + ζ - z * ζ ∈
        Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries (a + s) (b + s) (c + 2 * s)).radius :=
      Metric.eball_subset_eball
        (radius_regularizedGaussHGFunSeries_ge_one (a + s) (b + s) (c + 2 * s))
        (by simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
          ENNReal.ofReal_lt_one] using hzV.2.trans hr_lt)
    have han := ((regularizedGaussHGFunSeries (a + s) (b + s) (c + 2 * s)).hasFPowerSeriesOnBall
      (zero_lt_one.trans_le
        (radius_regularizedGaussHGFunSeries_ge_one (a + s) (b + s) (c + 2 * s)))).analyticAt_of_mem
      hw
    have hcomp : DifferentiableAt ℂ
        (fun z : ℂ ↦ regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ)) z :=
      han.differentiableAt.comp z (by fun_prop)
    exact (((differentiableAt_const _).mul ((differentiableAt_id.mul
      (differentiableAt_const ζ)).pow s)).mul hcomp).differentiableWithinAt
  exact ((hdiffV z₀ hz₀V).differentiableAt (hV_open.mem_nhds hz₀V)).differentiableWithinAt

private theorem summable_norm_bcDoubleTerm (a b c : ℂ) {z ζ : ℂ} (hζ : ‖ζ‖ < 1)
    (hzv : ‖z‖ + ‖ζ * (1 - z)‖ < 1) :
    Summable fun p : ℕ × ℕ ↦ ‖bcDoubleTerm a b c z ζ p‖ := by
  obtain ⟨K, P, Q, _, hbound⟩ := exists_bc_coeff_bound a b c
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg (ζ * (1 - z))]
  have hzζ1 : ‖z * ζ‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg ζ]
  set r₁ := ‖z‖
  set r₂ := ‖ζ * (1 - z)‖
  have hjk_sum : Summable fun q : ℕ × ℕ ↦
      ((q.1 + q.2 : ℝ) + 1) ^ Q * ((q.1 + q.2).choose q.1 : ℝ) * r₂ ^ q.1 * r₁ ^ q.2 := by
    have hdiag : Summable fun m : ℕ ↦ ((m : ℝ) + 1) ^ Q * (r₂ + r₁) ^ m :=
      summable_pow_add_one_mul_geometric (by positivity) (by linarith)
    have hsigma : Summable fun x : Σ m : ℕ, antidiagonal m ↦
        ((x.2.1.1 + x.2.1.2 : ℝ) + 1) ^ Q * ((x.2.1.1 + x.2.1.2).choose x.2.1.1 : ℝ) *
          r₂ ^ x.2.1.1 * r₁ ^ x.2.1.2 := by
      rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
      refine ⟨fun _ ↦ Summable.of_finite, hdiag.congr fun m ↦ ?_⟩
      rw [tsum_fintype]
      dsimp only
      rw [sum_coe_sort (antidiagonal m) (fun q : ℕ × ℕ ↦
        ((q.1 + q.2 : ℝ) + 1) ^ Q * ((q.1 + q.2).choose q.1 : ℝ) * r₂ ^ q.1 * r₁ ^ q.2),
        (Commute.all r₂ r₁).add_pow', mul_sum]
      refine sum_congr rfl fun q hq ↦ ?_
      rw [← Nat.cast_add, mem_antidiagonal.mp hq, nsmul_eq_mul]
      ring
    exact HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hsigma
  obtain ⟨hk_row, hj_col⟩ := (summable_prod_of_nonneg (fun _ ↦ by positivity)).mp hjk_sum
  have hs_sum : Summable fun s : ℕ ↦ K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s :=
    ((summable_pow_add_one_mul_geometric (norm_nonneg _) hzζ1).mul_left K).congr fun _ ↦ by ring
  have hprod := Summable.mul_of_nonneg hs_sum hj_col (fun _ ↦ by positivity)
    (fun j ↦ tsum_nonneg fun _ ↦ by positivity)
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun ⟨s, j⟩ ↦ ?_) hprod
  simpa [bcDoubleTerm, r₁, r₂] using
    norm_bcGenTerm_le (u := z * ζ) (v := ζ * (1 - z)) hz1 hbound s j (hk_row j)

private theorem choose_mul_inv_factorial_eq {n s : ℕ} (hsn : s ≤ n) :
    (n.choose s : ℂ) * (n ! : ℂ)⁻¹ = (s ! : ℂ)⁻¹ * ((n - s)! : ℂ)⁻¹ := by
  have hcast : (n.choose s : ℂ) * s ! * (n - s)! = (n ! : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hsn
  have hfs : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfns : ((n - s)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine mul_left_cancel₀ (mul_ne_zero hfs (mul_ne_zero hfns hfn)) ?_
  rw [show (s ! : ℂ) * ((n - s)! * n !) * ((n.choose s : ℂ) * (n ! : ℂ)⁻¹) =
      ((n.choose s : ℂ) * s ! * (n - s)!) * (n ! * (n ! : ℂ)⁻¹) by ring,
    show (s ! : ℂ) * ((n - s)! * n !) * ((s ! : ℂ)⁻¹ * ((n - s)! : ℂ)⁻¹) =
      (s ! * (s ! : ℂ)⁻¹) * ((n - s)! * ((n - s)! : ℂ)⁻¹) * (n ! : ℂ) by ring,
    mul_inv_cancel₀ hfn, mul_inv_cancel₀ hfs, mul_inv_cancel₀ hfns, hcast]
  ring

private theorem bcDoubleTerm_antidiag_eq (a b c z ζ : ℂ) {n s : ℕ} (hsn : s ≤ n) :
    bcDoubleTerm a b c z ζ (s, n - s) =
      (n.choose s : ℂ) * (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
        (ascPochhammer ℂ (n - s)).eval (c + s) * z ^ s * (1 - z) ^ (n - s) *
        regularizedGaussHGFun (a + n) (b + n) (c + n + s) z *
        ((regularizedGaussHGFunSeries a b c).coeff n * ζ ^ n) := by
  have hadd_n : s + (n - s) = n := Nat.add_sub_of_le hsn
  have hch := choose_mul_inv_factorial_eq hsn
  have hΓ := ascPochhammer_eval_mul_inv_Gamma_add (c + s) (n - s)
  have hc_shift : c + (s : ℂ) + (n - s : ℕ) = c + n := by
    rw [add_assoc, ← Nat.cast_add, hadd_n]
  rw [hc_shift] at hΓ
  have hpa : (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ (n - s)).eval (a + s) =
      (ascPochhammer ℂ n).eval a := by
    simpa [hadd_n] using (TauCeti.ascPochhammer_add_eval a s (n - s)).symm
  have hpb : (ascPochhammer ℂ s).eval b * (ascPochhammer ℂ (n - s)).eval (b + s) =
      (ascPochhammer ℂ n).eval b := by
    simpa [hadd_n] using (TauCeti.ascPochhammer_add_eval b s (n - s)).symm
  have hpow : (z * ζ) ^ s * (ζ * (1 - z)) ^ (n - s) = ζ ^ n * z ^ s * (1 - z) ^ (n - s) := by
    rw [mul_pow, mul_pow, show z ^ s * ζ ^ s * (ζ ^ (n - s) * (1 - z) ^ (n - s)) =
      (ζ ^ s * ζ ^ (n - s)) * z ^ s * (1 - z) ^ (n - s) by ring, ← pow_add, hadd_n]
  have ha_shift : a + (s : ℂ) + (n - s : ℕ) = a + n := by rw [add_assoc, ← Nat.cast_add, hadd_n]
  have hb_shift : b + (s : ℂ) + (n - s : ℕ) = b + n := by rw [add_assoc, ← Nat.cast_add, hadd_n]
  have hc2_shift : c + 2 * (s : ℂ) + (n - s : ℕ) = c + n + s := by
    have : (n : ℂ) = s + (n - s : ℕ) := by exact_mod_cast hadd_n.symm
    rw [this]; ring
  simp only [bcDoubleTerm, coeff_regularizedGaussHGFunSeries, ha_shift, hb_shift, hc2_shift,
    div_eq_mul_inv, mul_inv]
  calc (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
        ((s ! : ℂ)⁻¹ * (Gamma (c + s))⁻¹) * (z * ζ) ^ s *
        ((ascPochhammer ℂ (n - s)).eval (a + s) * (ascPochhammer ℂ (n - s)).eval (b + s) *
          ((n - s)! : ℂ)⁻¹ * (ζ * (1 - z)) ^ (n - s) *
          regularizedGaussHGFun (a + n) (b + n) (c + n + s) z)
      = ((s ! : ℂ)⁻¹ * ((n - s)! : ℂ)⁻¹) *
          (((ascPochhammer ℂ s).eval a * (ascPochhammer ℂ (n - s)).eval (a + s)) *
            ((ascPochhammer ℂ s).eval b * (ascPochhammer ℂ (n - s)).eval (b + s)) *
            (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
            (Gamma (c + s))⁻¹ * ((z * ζ) ^ s * (ζ * (1 - z)) ^ (n - s)) *
            regularizedGaussHGFun (a + n) (b + n) (c + n + s) z) := by ring
    _ = ((n.choose s : ℂ) * (n ! : ℂ)⁻¹) *
          ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
            (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
            ((ascPochhammer ℂ (n - s)).eval (c + s) * (Gamma (c + n))⁻¹) *
            (ζ ^ n * z ^ s * (1 - z) ^ (n - s)) *
            regularizedGaussHGFun (a + n) (b + n) (c + n + s) z) := by
        rw [← hch, hpa, hpb, hΓ, hpow]
    _ = _ := by ring

private theorem hasSum_bcTerm_of_add_norm_lt (a b c : ℂ) {z ζ : ℂ} (hζ : ‖ζ‖ < 1)
    (hzv : ‖z‖ + ‖ζ * (1 - z)‖ < 1) :
    HasSum (fun s : ℕ ↦ bcTerm a b c s z ζ)
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) := by
  let D := bcDoubleTerm a b c z ζ
  have hD : Summable D := (summable_norm_bcDoubleTerm a b c hζ hzv).of_norm
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg (ζ * (1 - z))]
  have hrow : HasSum (fun s : ℕ ↦ bcTerm a b c s z ζ) (∑' p, D p) := by
    refine hD.hasSum.prod_fiberwise fun s ↦ ?_
    have hadd := (hasSum_regularizedGaussHGFun_add (a + s) (b + s) (c + 2 * s) hzv).mul_left
      ((ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * Gamma (c + s)) * (z * ζ) ^ s)
    have hzw_eq : z + ζ * (1 - z) = z + ζ - z * ζ := by ring
    simpa only [D, bcDoubleTerm, bcTerm, hzw_eq] using hadd
  have hdiag : HasSum
      (fun n : ℕ ↦ regularizedGaussHGFun a b c z *
        ((regularizedGaussHGFunSeries a b c).coeff n * ζ ^ n)) (∑' p, D p) := by
    have h := (HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hD.hasSum).sigma
      fun n ↦ hasSum_fintype _
    simp only [Function.comp_apply, HasAntidiagonal.sigmaAntidiagonalEquivProd_apply,
      sum_coe_sort (antidiagonal _) D] at h
    refine h.congr_fun fun n ↦ ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun s j ↦ D (s, j)) n,
      regularizedGaussHGFun_eq_sum_choose a b c hz1 n, sum_mul]
    exact sum_congr rfl fun s hs ↦
      (bcDoubleTerm_antidiag_eq a b c z ζ (mem_range_succ_iff.mp hs)).symm
  have hprod := (hasSum_coeff_regularizedGaussHGFunSeries a b c hζ).mul_left
    (regularizedGaussHGFun a b c z)
  rwa [← hprod.unique hdiag] at hrow

private theorem convex_bcDomain (ζ : ℂ) :
    Convex ℝ {z : ℂ | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1} := by
  intro z₁ hz₁ z₂ hz₂ t₁ t₂ ht₁ ht₂ ht
  have ht' : (t₁ : ℂ) + t₂ = 1 := by exact_mod_cast ht
  refine ⟨?_, ?_⟩
  · calc ‖t₁ • z₁ + t₂ • z₂‖ ≤ ‖t₁ • z₁‖ + ‖t₂ • z₂‖ := norm_add_le _ _
      _ = t₁ * ‖z₁‖ + t₂ * ‖z₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht₁, Real.norm_of_nonneg ht₂]
      _ < t₁ * 1 + t₂ * 1 := by
          rcases ht₁.eq_or_lt with rfl | ht₁'
          · have : t₂ = 1 := by linarith
            simp [this, hz₂.1]
          · nlinarith [hz₁.1, hz₂.1]
      _ = 1 := by linarith
  · have haff : t₁ • z₁ + t₂ • z₂ + ζ - (t₁ • z₁ + t₂ • z₂) * ζ =
        t₁ • (z₁ + ζ - z₁ * ζ) + t₂ • (z₂ + ζ - z₂ * ζ) := by
      simp only [Complex.real_smul]
      linear_combination -ζ * ht'
    rw [haff]
    calc ‖t₁ • (z₁ + ζ - z₁ * ζ) + t₂ • (z₂ + ζ - z₂ * ζ)‖
        ≤ t₁ * ‖z₁ + ζ - z₁ * ζ‖ + t₂ * ‖z₂ + ζ - z₂ * ζ‖ := by
          refine (norm_add_le _ _).trans_eq ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht₁, Real.norm_of_nonneg ht₂]
      _ < t₁ * 1 + t₂ * 1 := by
          rcases ht₁.eq_or_lt with rfl | ht₁'
          · have : t₂ = 1 := by linarith
            simp [this, hz₂.2]
          · nlinarith [hz₁.2, hz₂.2]
      _ = 1 := by linarith

end BurchnallChaundyBounds

/-- **Burchnall–Chaundy two-variable product expansion for `regularizedGaussHGFun` (DLMF 15.16.3).**
Whenever `‖z‖ < 1`, `‖ζ‖ < 1`, and `‖z + ζ - z * ζ‖ < 1`, the product
`𝐅(a, b; c; z) * 𝐅(a, b; c; ζ)` expands as a series in
`(z * ζ) ^ s * 𝐅(a + s, b + s; c + 2s; z + ζ - z * ζ)`, for all complex parameters `a`, `b`, `c`
(including nonpositive integer poles of `Γ(c)`). -/
theorem hasSum_regularizedGaussHGFun_mul (a b c : ℂ) {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hw : ‖z + ζ - z * ζ‖ < 1) :
    HasSum
      (fun s : ℕ ↦ (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * Gamma (c + s)) * (z * ζ) ^ s *
        regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) := by
  let U : Set ℂ := {z' : ℂ | ‖z'‖ < 1 ∧ ‖z' + ζ - z' * ζ‖ < 1}
  have hcont : Continuous fun z' : ℂ ↦ ‖z' + ζ - z' * ζ‖ := by fun_prop
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt hcont continuous_const)
  have hf_an : AnalyticOnNhd ℂ (fun z' : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z' ζ) U :=
    (differentiableOn_tsum_bcTerm a b c hζ).analyticOnNhd hU_open
  have hg_an : AnalyticOnNhd ℂ
      (fun z' : ℂ ↦ regularizedGaussHGFun a b c z' * regularizedGaussHGFun a b c ζ) U := by
    intro z' hz'
    have hmem : z' ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
      Metric.eball_subset_eball (radius_regularizedGaussHGFunSeries_ge_one a b c)
        (by simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
          ENNReal.ofReal_lt_one] using hz'.1)
    exact (((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall
      (zero_lt_one.trans_le
        (radius_regularizedGaussHGFunSeries_ge_one a b c))).analyticAt_of_mem hmem).mul
      analyticAt_const
  have heq0 : (fun z' : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z' ζ) =ᶠ[𝓝 (0 : ℂ)]
      fun z' : ℂ ↦ regularizedGaussHGFun a b c z' * regularizedGaussHGFun a b c ζ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show 0 < (1 - ‖ζ‖) / 4 by linarith)]
      with z' hz'
    rw [Metric.mem_ball, dist_zero_right] at hz'
    have hzv : ‖z'‖ + ‖ζ * (1 - z')‖ < 1 := by
      have h1z : ‖1 - z'‖ ≤ 1 + ‖z'‖ := (norm_sub_le 1 z').trans_eq (by simp)
      calc ‖z'‖ + ‖ζ * (1 - z')‖ = ‖z'‖ + ‖ζ‖ * ‖1 - z'‖ := by rw [norm_mul]
        _ ≤ ‖z'‖ + ‖ζ‖ * (1 + ‖z'‖) := by gcongr
        _ < 1 := by nlinarith [norm_nonneg ζ, norm_nonneg z']
    exact (hasSum_bcTerm_of_add_norm_lt a b c hζ hzv).tsum_eq
  have h0U : (0 : ℂ) ∈ U := ⟨by simp, by simpa using hζ⟩
  have heqU := hf_an.eqOn_of_preconnected_of_eventuallyEq hg_an
    (convex_bcDomain ζ).isPreconnected h0U heq0
  obtain ⟨K, P, Q, hK0, hbound⟩ := exists_bc_coeff_bound a b c
  set r : ℝ := max ‖z‖ ‖z + ζ - z * ζ‖
  have hr1 : r < 1 := max_lt hz hw
  have hsum_z : Summable fun s : ℕ ↦ bcTerm a b c s z ζ := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun s ↦ norm_bcTerm_le (le_max_left _ _) (le_max_right _ _) (by positivity) hr1 hK0
        hbound s)
      ((summable_pow_add_one_mul_geometric (by positivity)
        (by nlinarith [norm_nonneg ζ])).mul_left _))
  simpa only [bcTerm, ← heqU ⟨hz, hw⟩] using hsum_z.hasSum

/-- **Burchnall–Chaundy two-variable product expansion for `₂F₁` (DLMF 15.16.3, ordinary form).**
When `c` avoids the nonpositive integers and `‖z‖ < 1`, `‖ζ‖ < 1`, `‖z + ζ - z * ζ‖ < 1`,
`₂F₁(a, b; c; z) * ₂F₁(a, b; c; ζ)` expands as a series in
`((a)_s (b)_s (c - a)_s (c - b)_s / (s! (c)_s (c)_{2s})) (z * ζ) ^ s ₂F₁(a + s, b + s; c + 2s; w)`
with `w = z + ζ - z * ζ`. -/
theorem hasSum_ordinaryHypergeometric_mul (a b : ℂ) {c z ζ : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hw : ‖z + ζ - z * ζ‖ < 1) :
    HasSum
      (fun s : ℕ ↦ (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * (ascPochhammer ℂ s).eval c * (ascPochhammer ℂ (2 * s)).eval c) * (z * ζ) ^ s *
        ₂F₁ (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (₂F₁ a b c z * ₂F₁ a b c ζ) := by
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hmul := (hasSum_regularizedGaussHGFun_mul a b c hz hζ hw).mul_left (Gamma c * Gamma c)
  have htarget : Gamma c * Gamma c *
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) =
      ₂F₁ a b c z * ₂F₁ a b c ζ := by
    rw [← ordinaryHypergeometric_div_Gamma_eq hc, ← ordinaryHypergeometric_div_Gamma_eq hc]
    field_simp
  rw [htarget] at hmul
  refine hmul.congr_fun fun s ↦ ?_
  have hc2s : ∀ k : ℕ, c + 2 * (s : ℂ) ≠ -k := fun k h ↦
    hc (2 * s + k) (by push_cast; linear_combination h)
  have hΓcs : Gamma (c + s) = (ascPochhammer ℂ s).eval c * Gamma c := by
    rw [← Gamma_add_nat_div_Gamma_eq c hc, div_mul_cancel₀ _ hΓc]
  have hΓc2s : Gamma (c + 2 * (s : ℂ)) = (ascPochhammer ℂ (2 * s)).eval c * Gamma c := by
    have h2 : c + 2 * (s : ℂ) = c + (2 * s : ℕ) := by push_cast; ring
    rw [h2, ← Gamma_add_nat_div_Gamma_eq c hc, div_mul_cancel₀ _ hΓc]
  have hps : (ascPochhammer ℂ s).eval c ≠ 0 := by
    rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩; exact hc k (by linear_combination hk)
  have hp2s : (ascPochhammer ℂ (2 * s)).eval c ≠ 0 := by
    rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩; exact hc k (by linear_combination hk)
  have hfs : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
  rw [← ordinaryHypergeometric_div_Gamma_eq hc2s, hΓcs, hΓc2s]
  field_simp

end Complex

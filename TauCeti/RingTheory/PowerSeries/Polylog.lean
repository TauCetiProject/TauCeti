/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Log

import TauCeti.RingTheory.PowerSeries.Geometric.Basic
import TauCeti.RingTheory.PowerSeries.Log

/-!
# The rational polylogarithm series

For an integer `k`, `TauCeti.rationalPolylogSeries k` is the power series

`q_k = ∑_{n ≥ 1} Xⁿ / nᵏ`

with rational coefficients. A polylogarithm `Li_k` given near `0` by its Taylor series, complex
or `p`-adic, has as coefficients the images of those of `q_k` in a field of characteristic zero.
The identities proved here are coefficientwise, need no convergence hypothesis, and pass to every
`ℚ`-algebra through `PowerSeries.map`; this is how the complex and the `p`-adic polylogarithm
series are compared.

In every integer weight, including `k ≤ 0`, the series satisfies the differential recursion
`X q_k' = q_{k-1}`, and it is the unique series with zero constant term doing so. In low weight
it has the closed forms `q_0 = X / (1 - X)`, `q_{-1} = X / (1 - X)²` and `q_1 = -log (1 - X)`,
the last with Mathlib's formal logarithm `PowerSeries.logOf`.

## Main definitions

* `TauCeti.rationalPolylogSeries`: the series `q_k = ∑_{n ≥ 1} Xⁿ / nᵏ` in `ℚ⟦X⟧`.

## Main results

* `TauCeti.coeff_rationalPolylogSeries`: its coefficients are `0` at `n = 0` and `n ^ (-k)` for
  `n ≥ 1`.
* `TauCeti.coeff_map_rationalPolylogSeries`: in a division ring of characteristic zero the
  coefficients of the image are `(n : F) ^ (-k)`.
* `TauCeti.map_map_rationalPolylogSeries`: ring homomorphisms between `ℚ`-algebras commute with the
  coefficient map.
* `TauCeti.X_mul_derivative_rationalPolylogSeries`: the recursion `X q_k' = q_{k-1}`.
* `TauCeti.eq_rationalPolylogSeries_iff`: `q_k` is the unique series with zero constant term and
  `X f' = q_{k-1}`.
* `TauCeti.rationalPolylogSeries_zero`, `TauCeti.rationalPolylogSeries_neg_one`,
  `TauCeti.rationalPolylogSeries_one`: the closed forms in weights `0`, `-1` and `1`.

## References

* Hidekazu Furusho, *p-adic multiple zeta values I: p-adic multiple polylogarithms and the p-adic
  KZ equation*, Invent. Math. 155 (2004), §2, Remark 2.29.
* Joaquín Rodrigues Jacinto and Chris Williams, *An introduction to p-adic L-functions*,
  Essential Number Theory 4 (2025), §6.2, Remark 6.6.
-/

public section

open PowerSeries

namespace TauCeti

/-- The rational polylogarithm series `q_k = ∑_{n ≥ 1} Xⁿ / nᵏ` of integer weight `k`: its
coefficient of `Xⁿ` is `n ^ (-k)` for `n ≥ 1`, and its constant coefficient is `0`. -/
noncomputable def rationalPolylogSeries (k : ℤ) : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then 0 else (n : ℚ) ^ (-k)

@[simp]
theorem coeff_rationalPolylogSeries (k : ℤ) (n : ℕ) :
    coeff n (rationalPolylogSeries k) = if n = 0 then 0 else (n : ℚ) ^ (-k) :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_rationalPolylogSeries (k : ℤ) :
    constantCoeff (rationalPolylogSeries k) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

/-- The coefficients of the image of `q_k` in a division ring `F` of characteristic zero are the
images `n ^ (-k)` of the rational coefficients. -/
theorem coeff_map_rationalPolylogSeries {F : Type*} [DivisionRing F] [CharZero F] (k : ℤ)
    (n : ℕ) :
    coeff n ((rationalPolylogSeries k).map (algebraMap ℚ F)) =
      if n = 0 then 0 else (n : F) ^ (-k) := by
  rw [coeff_map, coeff_rationalPolylogSeries]
  split_ifs <;> simp

/-- A ring homomorphism between `ℚ`-algebras carries the image of `q_k` to the image of `q_k`. -/
@[simp]
theorem map_map_rationalPolylogSeries {A B : Type*} [Semiring A] [Semiring B]
    [Algebra ℚ A] [Algebra ℚ B] (φ : A →+* B) (k : ℤ) :
    ((rationalPolylogSeries k).map (algebraMap ℚ A)).map φ =
      (rationalPolylogSeries k).map (algebraMap ℚ B) := by
  ext n
  simp [RingHom.map_rat_algebraMap]

/-- **The differential recursion** `X q_k' = q_{k-1}`, in every integer weight `k`. -/
theorem X_mul_derivative_rationalPolylogSeries (k : ℤ) :
    X * d⁄dX (rationalPolylogSeries k) = rationalPolylogSeries (k - 1) := by
  ext (_ | n)
  · simp
  · have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 n.succ_ne_zero
    simp only [coeff_succ_X_mul, coeff_derivative, coeff_rationalPolylogSeries,
      Nat.add_one_ne_zero, ↓reduceIte]
    rw [neg_sub, sub_eq_neg_add, zpow_add_one₀ hn, Nat.cast_succ]

/-- **Uniqueness of `q_k`**: it is the only power series with zero constant coefficient and
`X f' = q_{k-1}`. -/
theorem eq_rationalPolylogSeries_iff {f : ℚ⟦X⟧} {k : ℤ} :
    f = rationalPolylogSeries k ↔
      constantCoeff f = 0 ∧ X * d⁄dX f = rationalPolylogSeries (k - 1) := by
  refine ⟨fun h ↦ h ▸ ⟨constantCoeff_rationalPolylogSeries k,
    X_mul_derivative_rationalPolylogSeries k⟩, fun ⟨h₀, h₁⟩ ↦ ?_⟩
  rw [← X_mul_derivative_rationalPolylogSeries] at h₁
  ext (_ | n)
  · simp [h₀]
  · have h := congrArg (coeff (n + 1)) h₁
    simp only [coeff_succ_X_mul, coeff_derivative] at h
    exact mul_right_cancel₀ (by positivity) h

/-- **Weight zero**: `q_0 = ∑_{n ≥ 1} Xⁿ = X / (1 - X)`. -/
theorem rationalPolylogSeries_zero : rationalPolylogSeries 0 = X * (1 - X)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq (by simp)]
  ext (_ | _ | n) <;> simp [mul_sub, coeff_succ_mul_X, coeff_X]

/-- **Weight minus one**: `q_{-1} = ∑_{n ≥ 1} n Xⁿ = X / (1 - X)²`. -/
theorem rationalPolylogSeries_neg_one :
    rationalPolylogSeries (-1) = X * ((1 - X)⁻¹) ^ 2 := by
  have h : (1 - X : ℚ⟦X⟧)⁻¹ = mk 1 :=
    (inv_eq_iff_mul_eq_one (by simp)).2 (mk_one_mul_one_sub_eq_one ℚ)
  rw [h, mk_one_sq]
  ext (_ | n)
  · simp
  · simp [coeff_succ_X_mul]

/-- **Weight one**: `q_1 = ∑_{n ≥ 1} Xⁿ / n = -log (1 - X)`, where `logOf (1 - X)` is Mathlib's
formal logarithm series `log (1 + X)` evaluated at `-X`. -/
theorem rationalPolylogSeries_one : rationalPolylogSeries 1 = -logOf (1 - X) := by
  have h := logOf_one_sub_C_mul_X (1 : ℚ)
  rw [map_one, one_mul] at h
  rw [h]
  ext (_ | n)
  · simp
  · simp [smul_eq_mul]

end TauCeti

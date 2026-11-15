/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Thue.Nonvanishing
public import Mathlib.NumberTheory.Height.NumberField

import TauCeti.Algebra.Polynomial.Eval.Rat

/-!
# Arithmetic lower bounds for Thue's auxiliary polynomials

Suppose `(X - α)^r` divides `P - α Q`, where `P, Q` are integer polynomials,
not both zero, of degree at most `N < d r`, and `α` has degree `d ≥ 2`.
For any rational approximants `x, y`, the nonvanishing theorem supplies an
order `k` with `k + d (r - 1) ≤ 2 N` and `DᵏP(x) - y DᵏQ(x) ≠ 0`.
Clearing denominators then gives the lower bound

`|DᵏP(x) - y DᵏQ(x)| ≥ (H(x)^(N-k) H(y))⁻¹`.

Here `H` is the rational multiplicative height `Height.mulHeight₁`.
The exponent retains the degree drop from Hasse differentiation. This is
the arithmetic half of the gap argument: analytic smallness of the same
nonzero value can then contradict this bound for two sufficiently good
approximants. No coefficient-length or approximation hypothesis is needed
for the lower bound itself.

## Main results

* `TauCeti.exists_hasseDeriv_aeval_sub_lower_bound`: the natural-degree form.
* `TauCeti.exists_thue_hasseDeriv_lower_bound`: the degree and order bounds
  for Thue's auxiliary construction with parameter `ε`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019),
  ch. 6, proof of Theorem 6.14.
-/

public section

open Polynomial Height

namespace TauCeti

/-- The nonvanishing Hasse derivative difference for two rational points has an
explicit height lower bound. Its order is at most `N` and satisfies
`k + d (r - 1) ≤ 2 N`; differentiation lowers the height exponent to `N - k`. -/
theorem exists_hasseDeriv_aeval_sub_lower_bound {F : Type*} [Field F] [CharZero F]
    {α : F} (hd : 2 ≤ (minpoly ℚ α).natDegree) {P Q : ℤ[X]}
    (hPQ : P ≠ 0 ∨ Q ≠ 0) {N r : ℕ} (hP : P.natDegree ≤ N) (hQ : Q.natDegree ≤ N)
    (hN : N < (minpoly ℚ α).natDegree * r)
    (hdvd : (X - C α) ^ r ∣ P.map (Int.castRingHom F) - C α * Q.map (Int.castRingHom F))
    (x y : ℚ) :
    ∃ k : ℕ, k ≤ N ∧ k + (minpoly ℚ α).natDegree * (r - 1) ≤ 2 * N ∧
      (mulHeight₁ x ^ (N - k) * mulHeight₁ y)⁻¹ ≤
        |((aeval x (hasseDeriv k P) - y * aeval x (hasseDeriv k Q) : ℚ) : ℝ)| := by
  obtain ⟨k, hkN, hk, hne⟩ :=
    exists_hasseDeriv_aeval_ne_mul_of_natDegree_le hd hPQ hP hQ hN hdvd x y
  have hden := one_le_den_pow_mul_abs_aeval_sub_mul
    ((natDegree_hasseDeriv_le P k).trans (Nat.sub_le_sub_right hP k))
    ((natDegree_hasseDeriv_le Q k).trans (Nat.sub_le_sub_right hQ k)) (sub_ne_zero.2 hne)
  have hden' : (1 : ℝ) ≤ (x.den : ℝ) ^ (N - k) * y.den *
      |((aeval x (hasseDeriv k P) - y * aeval x (hasseDeriv k Q) : ℚ) : ℝ)| := by
    exact_mod_cast hden
  have hx : (x.den : ℝ) ≤ mulHeight₁ x := by
    rw [Rat.mulHeight₁_eq_max]
    exact_mod_cast (le_max_right x.num.natAbs x.den)
  have hy : (y.den : ℝ) ≤ mulHeight₁ y := by
    rw [Rat.mulHeight₁_eq_max]
    exact_mod_cast (le_max_right y.num.natAbs y.den)
  refine ⟨k, hkN, hk, ?_⟩
  rw [inv_le_iff_one_le_mul₀' (by positivity)]
  calc
    (1 : ℝ) ≤ _ := hden'
    _ ≤ _ := by gcongr

/-- **Arithmetic lower bound in Thue's gap argument.** For the auxiliary degree
`N = ⌊(1/2 + ε) d r⌋`, where `0 ≤ ε < 1/2` and `r ≥ 1`, there is an order
`k ≤ d (2 ε r + 1)` giving a derivative difference of size at least
`(H(x)^(N-k) H(y))⁻¹`. The estimate holds for every pair of rational points,
without assuming that they approximate `α`. -/
theorem exists_thue_hasseDeriv_lower_bound {F : Type*} [Field F] [CharZero F]
    {α : F} (hd : 2 ≤ (minpoly ℚ α).natDegree) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε : ε < 1 / 2)
    {r : ℕ} (hr : 0 < r) {P Q : ℤ[X]} (hPQ : P ≠ 0 ∨ Q ≠ 0)
    (hP : P.natDegree ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊)
    (hQ : Q.natDegree ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊)
    (hdvd : (X - C α) ^ r ∣ P.map (Int.castRingHom F) - C α * Q.map (Int.castRingHom F))
    (x y : ℚ) :
    ∃ k : ℕ, k ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊ ∧
      (k : ℝ) ≤ (minpoly ℚ α).natDegree * (2 * ε * r + 1) ∧
      (mulHeight₁ x ^ (⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊ - k) *
        mulHeight₁ y)⁻¹ ≤
          |((aeval x (hasseDeriv k P) - y * aeval x (hasseDeriv k Q) : ℚ) : ℝ)| := by
  set d := (minpoly ℚ α).natDegree
  set N := ⌊(1 / 2 + ε) * d * r⌋₊
  have hNle : (N : ℝ) ≤ (1 / 2 + ε) * d * r := Nat.floor_le (by positivity)
  have hN : N < d * r := by
    rw [Nat.floor_lt (by positivity)]
    push_cast
    have : (0 : ℝ) < d * r := by exact_mod_cast Nat.mul_pos (by omega) hr
    nlinarith
  obtain ⟨k, hkN, hk, hbound⟩ :=
    exists_hasseDeriv_aeval_sub_lower_bound hd hPQ hP hQ hN hdvd x y
  exact ⟨k, hkN, thue_order_le_of_add_mul_le hr hNle hk, hbound⟩

end TauCeti

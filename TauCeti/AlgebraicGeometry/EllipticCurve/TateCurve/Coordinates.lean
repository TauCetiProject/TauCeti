/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Evaluation
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The coordinate series for Tate uniformisation

For a unit `q` of norm less than one in a complete normed field, the
classical Tate coordinates are

`X(u) = ∑_{n ∈ ℤ} qⁿu / (1 - qⁿu)² - 2 s₁(q)`,
`Y(u) = ∑_{n ∈ ℤ} (qⁿu)² / (1 - qⁿu)³ + s₁(q)`.

This file proves convergence of both bilateral series, their invariance under `u ↦ qu`,
and the inversion laws `X(u⁻¹) = X(u)` and `Y(u⁻¹) = -Y(u) - X(u)`. These are the
analytic coordinates used to construct the map from the multiplicative group modulo `q^ℤ`
to the Tate curve over a non-archimedean field. The Weierstrass equation and the homomorphism
property are not proved here.

The coordinates are intended for `u ∉ q^ℤ`. The definitions are total: at an element of
`q^ℤ`, the summand with zero denominator is zero by the field's inverse convention. Such
values do not represent the point at infinity and are not asserted to lie on the curve.
Convergence and the reindexing identities hold even with this convention.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

open Filter Topology

namespace TauCeti

section Field

variable {K : Type*} [Field K]

private def xTerm (x : K) : K := x / (1 - x) ^ 2
private def yTerm (x : K) : K := x ^ 2 / (1 - x) ^ 3

private theorem xTerm_inv (x : K) (hx : x ≠ 0) : xTerm x⁻¹ = xTerm x := by
  by_cases h : x = 1
  · simp [h, xTerm]
  · dsimp [xTerm]
    field_simp
    ring

private theorem yTerm_inv (x : K) (hx : x ≠ 0) :
    yTerm x⁻¹ = -yTerm x - xTerm x := by
  by_cases h : x = 1
  · simp [h, xTerm, yTerm]
  · dsimp [xTerm, yTerm]
    field_simp
    ring

private theorem xTerm_zpow_neg (q u : Kˣ) (n : ℤ) :
    xTerm ((q : K) ^ (-n) * (u : K)) = xTerm ((q : K) ^ n * (u : K)⁻¹) := by
  rw [zpow_neg]
  simpa only [mul_inv, inv_inv] using
    xTerm_inv ((q : K) ^ n * (u : K)⁻¹)
      (mul_ne_zero (zpow_ne_zero _ q.ne_zero) (inv_ne_zero u.ne_zero))

private theorem yTerm_zpow_neg (q u : Kˣ) (n : ℤ) :
    yTerm ((q : K) ^ (-n) * (u : K)) =
      -yTerm ((q : K) ^ n * (u : K)⁻¹) - xTerm ((q : K) ^ n * (u : K)⁻¹) := by
  rw [zpow_neg]
  simpa only [mul_inv, inv_inv] using
    yTerm_inv ((q : K) ^ n * (u : K)⁻¹)
      (mul_ne_zero (zpow_ne_zero _ q.ne_zero) (inv_ne_zero u.ne_zero))

end Field

variable {K : Type*} [NormedField K] [CompleteSpace K]

private theorem summable_xTerm_nat (q : K) (hq : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℕ ↦ xTerm (q ^ n * u)) := by
  have hp : Tendsto (fun n : ℕ ↦ q ^ n * u) cofinite (𝓝 0) := by
    simpa [Nat.cofinite_eq_atTop] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const u
  have hs : Summable (fun n : ℕ ↦ ‖q ^ n * u‖) := by
    simpa only [norm_mul] using (summable_norm_geometric_of_norm_lt_one hq).mul_right ‖u‖
  have hi : Tendsto (fun n : ℕ ↦ ((1 - q ^ n * u) ^ 2)⁻¹) cofinite (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : K))).sub hp).pow 2 |>.inv₀ (by simp)
  simpa only [xTerm, div_eq_mul_inv] using hs.mul_tendsto_const hi

private theorem summable_yTerm_nat (q : K) (hq : ‖q‖ < 1) (u : K) :
    Summable (fun n : ℕ ↦ yTerm (q ^ n * u)) := by
  have hp : Tendsto (fun n : ℕ ↦ q ^ n * u) cofinite (𝓝 0) := by
    simpa [Nat.cofinite_eq_atTop] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const u
  have hs : Summable (fun n : ℕ ↦ ‖q ^ n * u‖) := by
    simpa only [norm_mul] using (summable_norm_geometric_of_norm_lt_one hq).mul_right ‖u‖
  have hi : Tendsto (fun n : ℕ ↦ q ^ n * u / (1 - q ^ n * u) ^ 3) cofinite (𝓝 0) := by
    simpa only [Pi.div_def, zero_div] using
      hp.div (((tendsto_const_nhds (x := (1 : K))).sub hp).pow 3) (by simp)
  simpa only [yTerm, pow_two, div_eq_mul_inv, mul_assoc] using hs.mul_tendsto_const hi

/-- The bilateral series defining the first Tate coordinate converges for every unit `u`
when `‖q‖ < 1`. -/
theorem summable_tateUniformizationX (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    Summable (fun n : ℤ ↦ (q : K) ^ n * (u : K) / (1 - (q : K) ^ n * (u : K)) ^ 2) := by
  suffices h : Summable (fun n : ℤ ↦ xTerm ((q : K) ^ n * (u : K))) by
    simpa only [xTerm] using h
  apply Summable.of_nat_of_neg
  · simpa only [zpow_natCast] using summable_xTerm_nat (q : K) hq (u : K)
  · simpa only [xTerm_zpow_neg, zpow_natCast] using
      summable_xTerm_nat (q : K) hq (u : K)⁻¹

/-- The bilateral series defining the second Tate coordinate converges for every unit `u`
when `‖q‖ < 1`. -/
theorem summable_tateUniformizationY (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    Summable (fun n : ℤ ↦ ((q : K) ^ n * (u : K)) ^ 2 /
      (1 - (q : K) ^ n * (u : K)) ^ 3) := by
  suffices h : Summable (fun n : ℤ ↦ yTerm ((q : K) ^ n * (u : K))) by
    simpa only [yTerm] using h
  apply Summable.of_nat_of_neg
  · simpa only [zpow_natCast] using summable_yTerm_nat (q : K) hq (u : K)
  · simpa only [yTerm_zpow_neg, zpow_natCast] using
      (summable_yTerm_nat (q : K) hq (u : K)⁻¹).neg.sub
        (summable_xTerm_nat (q : K) hq (u : K)⁻¹)

omit [CompleteSpace K] in
/-- The first Tate coordinate series, for a multiplicative parameter `u`.
It gives a uniformisation coordinate when `‖q‖ < 1` and `u ∉ q^ℤ`; at a pole its
zero-denominator summand is totalised to zero. -/
noncomputable def tateUniformizationX (q u : Kˣ) : K :=
  (∑' n : ℤ, (q : K) ^ n * (u : K) / (1 - (q : K) ^ n * (u : K)) ^ 2) -
    2 * divisorSumAt 1 (q : K)

omit [CompleteSpace K] in
/-- The second Tate coordinate series. The same convergence and pole conventions as
`tateUniformizationX` apply. -/
noncomputable def tateUniformizationY (q u : Kˣ) : K :=
  (∑' n : ℤ, ((q : K) ^ n * (u : K)) ^ 2 / (1 - (q : K) ^ n * (u : K)) ^ 3) +
    divisorSumAt 1 (q : K)

omit [CompleteSpace K] in
/-- The series formula for the first Tate coordinate. -/
theorem tateUniformizationX_def (q u : Kˣ) :
    tateUniformizationX q u =
      (∑' n : ℤ, (q : K) ^ n * (u : K) / (1 - (q : K) ^ n * (u : K)) ^ 2) -
        2 * divisorSumAt 1 (q : K) := (rfl)

omit [CompleteSpace K] in
/-- The series formula for the second Tate coordinate. -/
theorem tateUniformizationY_def (q u : Kˣ) :
    tateUniformizationY q u =
      (∑' n : ℤ, ((q : K) ^ n * (u : K)) ^ 2 / (1 - (q : K) ^ n * (u : K)) ^ 3) +
        divisorSumAt 1 (q : K) := (rfl)

omit [CompleteSpace K] in
/-- The first Tate coordinate is constant on the multiplicative cosets of `q^ℤ`. -/
@[simp]
theorem tateUniformizationX_zpow_mul (q u : Kˣ) (k : ℤ) :
    tateUniformizationX q (q ^ k * u) = tateUniformizationX q u := by
  rw [tateUniformizationX_def, tateUniformizationX_def]
  congr 1
  have h := (Equiv.addRight k).tsum_eq
    (fun n : ℤ ↦ (q : K) ^ n * (u : K) / (1 - (q : K) ^ n * (u : K)) ^ 2)
  simpa [zpow_add₀ q.ne_zero, mul_assoc] using h

omit [CompleteSpace K] in
/-- The second Tate coordinate is constant on the multiplicative cosets of `q^ℤ`. -/
@[simp]
theorem tateUniformizationY_zpow_mul (q u : Kˣ) (k : ℤ) :
    tateUniformizationY q (q ^ k * u) = tateUniformizationY q u := by
  rw [tateUniformizationY_def, tateUniformizationY_def]
  congr 1
  have h := (Equiv.addRight k).tsum_eq
    (fun n : ℤ ↦ ((q : K) ^ n * (u : K)) ^ 2 / (1 - (q : K) ^ n * (u : K)) ^ 3)
  simpa [zpow_add₀ q.ne_zero, mul_assoc] using h

omit [CompleteSpace K] in
/-- Multiplication of the parameter by `q` leaves the first Tate coordinate unchanged. -/
@[simp]
theorem tateUniformizationX_self_mul (q u : Kˣ) :
    tateUniformizationX q (q * u) = tateUniformizationX q u := by
  simpa using tateUniformizationX_zpow_mul q u 1

omit [CompleteSpace K] in
/-- Multiplication of the parameter by `q` leaves the second Tate coordinate unchanged. -/
@[simp]
theorem tateUniformizationY_self_mul (q u : Kˣ) :
    tateUniformizationY q (q * u) = tateUniformizationY q u := by
  simpa using tateUniformizationY_zpow_mul q u 1

omit [CompleteSpace K] in
/-- Multiplication of the parameter by a natural power of `q` leaves the first Tate
coordinate unchanged. -/
@[simp]
theorem tateUniformizationX_pow_mul (q u : Kˣ) (n : ℕ) :
    tateUniformizationX q (q ^ n * u) = tateUniformizationX q u := by
  simpa only [zpow_natCast] using tateUniformizationX_zpow_mul q u n

omit [CompleteSpace K] in
/-- Multiplication of the parameter by a natural power of `q` leaves the second Tate
coordinate unchanged. -/
@[simp]
theorem tateUniformizationY_pow_mul (q u : Kˣ) (n : ℕ) :
    tateUniformizationY q (q ^ n * u) = tateUniformizationY q u := by
  simpa only [zpow_natCast] using tateUniformizationY_zpow_mul q u n

omit [CompleteSpace K] in
/-- Multiplication of the parameter by `q⁻¹` leaves the first Tate coordinate unchanged. -/
@[simp]
theorem tateUniformizationX_inv_mul (q u : Kˣ) :
    tateUniformizationX q (q⁻¹ * u) = tateUniformizationX q u := by
  simpa only [zpow_neg_one] using tateUniformizationX_zpow_mul q u (-1)

omit [CompleteSpace K] in
/-- Multiplication of the parameter by `q⁻¹` leaves the second Tate coordinate unchanged. -/
@[simp]
theorem tateUniformizationY_inv_mul (q u : Kˣ) :
    tateUniformizationY q (q⁻¹ * u) = tateUniformizationY q u := by
  simpa only [zpow_neg_one] using tateUniformizationY_zpow_mul q u (-1)

omit [CompleteSpace K] in
/-- Inverting the multiplicative parameter leaves the first Tate coordinate unchanged. -/
@[simp]
theorem tateUniformizationX_inv (q u : Kˣ) :
    tateUniformizationX q u⁻¹ = tateUniformizationX q u := by
  rw [tateUniformizationX_def, tateUniformizationX_def]
  congr 1
  have h := (Equiv.neg ℤ).tsum_eq
    (fun n : ℤ ↦ xTerm ((q : K) ^ n * (u : K)))
  simp only [Equiv.neg_apply] at h
  simp_rw [xTerm_zpow_neg] at h
  simpa only [xTerm, Units.val_inv_eq_inv_val] using h

/-- Inversion gives the negation formula of the Tate equation `y² + xy = x³ + a₄x + a₆`:
`Y(u⁻¹) = -Y(u) - X(u)`. -/
@[simp]
theorem tateUniformizationY_inv (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    tateUniformizationY q u⁻¹ = -tateUniformizationY q u - tateUniformizationX q u := by
  have hx := summable_tateUniformizationX q hq u
  have hy := summable_tateUniformizationY q hq u
  have h := (Equiv.neg ℤ).tsum_eq
    (fun n : ℤ ↦ yTerm ((q : K) ^ n * (u⁻¹ : Kˣ)))
  simp only [Equiv.neg_apply] at h
  simp_rw [yTerm_zpow_neg, Units.val_inv_eq_inv_val, inv_inv] at h
  have hys : Summable (fun n : ℤ ↦ -yTerm ((q : K) ^ n * (u : K))) := by
    simpa only [yTerm] using hy.neg
  have hxs : Summable (fun n : ℤ ↦ xTerm ((q : K) ^ n * (u : K))) := by
    simpa only [xTerm] using hx
  rw [hys.tsum_sub hxs, tsum_neg] at h
  simp only [tateUniformizationY_def, tateUniformizationX_def, yTerm, xTerm,
    Units.val_inv_eq_inv_val] at h ⊢
  rw [← h]
  ring

end TauCeti

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# Lenstra's rigid critical-point polynomial

`TauCeti.lenstraPolynomial α` is the antiderivative of `X (X - 1)² (X - α)³` whose constant
coefficient is zero. For `α ≠ 0, 1`, its three critical points have distinct derivative-root
multiplicities `1, 2, 3`. Thus an affine change of variable identifying two such polynomials,
even up to scaling and addition of a constant, must fix `0`, `1`, and the parameter.

This is the critical-point encoding used to distinguish conjugate polynomial covers of the
projective line in Lenstra's proof of faithfulness of the Galois action on dessins.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, Theorem 4.49 (the proof attributed there to Lenstra).
-/

public noncomputable section

open Polynomial

namespace TauCeti

variable {K : Type*} [Field K]

/-- The explicit formula for Lenstra's polynomial. In characteristic zero it has derivative
`X (X - 1)² (X - α)³` and value zero at zero. -/
def lenstraPolynomial (α : K) : K[X] :=
  C (1 / 7) * X ^ 7 - C ((3 * α + 2) / 6) * X ^ 6 +
    C ((3 * α ^ 2 + 6 * α + 1) / 5) * X ^ 5 -
    C ((α ^ 3 + 6 * α ^ 2 + 3 * α) / 4) * X ^ 4 +
    C ((2 * α ^ 3 + 3 * α ^ 2) / 3) * X ^ 3 - C (α ^ 3 / 2) * X ^ 2

/-- Transporting coefficients transports the encoded parameter. -/
@[simp] theorem _root_.RingHom.map_lenstraPolynomial {L : Type*} [Field L] (f : K →+* L) (α : K) :
    (lenstraPolynomial α).map f = lenstraPolynomial (f α) := by
  simp [lenstraPolynomial, map_div₀, map_ofNat]

@[simp] theorem eval_zero_lenstraPolynomial (α : K) : (lenstraPolynomial α).eval 0 = 0 := by
  simp [lenstraPolynomial]

/-- The factored derivative records the three distinguished critical points. -/
@[simp] theorem derivative_lenstraPolynomial [CharZero K] (α : K) :
    (lenstraPolynomial α).derivative = X * (X - 1) ^ 2 * (X - C α) ^ 3 := by
  simp only [lenstraPolynomial, derivative_sub, derivative_add, derivative_mul,
    derivative_C, derivative_pow, derivative_X, zero_mul, zero_add, mul_one]
  simp only [div_eq_mul_inv, map_add, map_mul, map_pow, map_ofNat]
  ring_nf
  simp only [← C_pow, mul_assoc, ← C_mul]
  norm_num
  ring

variable [CharZero K]

/-- The polynomial has degree seven, including when critical points coincide. -/
@[simp] theorem natDegree_lenstraPolynomial (α : K) : (lenstraPolynomial α).natDegree = 7 := by
  have h : (lenstraPolynomial α).derivative.natDegree = 6 := by
    rw [derivative_lenstraPolynomial]
    compute_degree!
  rw [natDegree_derivative] at h
  have hle : (lenstraPolynomial α).natDegree ≤ 7 := by
    unfold lenstraPolynomial
    compute_degree
  omega

@[simp] theorem leadingCoeff_lenstraPolynomial (α : K) :
    (lenstraPolynomial α).leadingCoeff = 1 / 7 := by
  rw [leadingCoeff, natDegree_lenstraPolynomial]
  simp [lenstraPolynomial, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow]

/-- Characterization by the derivative and the normalization at zero. -/
theorem _root_.Polynomial.eq_lenstraPolynomial_iff (p : K[X]) (α : K) :
    p = lenstraPolynomial α ↔
      p.derivative = X * (X - 1) ^ 2 * (X - C α) ^ 3 ∧ p.eval 0 = 0 := by
  refine ⟨fun h ↦ h ▸ ⟨derivative_lenstraPolynomial α, eval_zero_lenstraPolynomial α⟩,
    fun ⟨hd, h0⟩ ↦ ?_⟩
  have h : (p - lenstraPolynomial α).derivative = 0 := by simp [hd]
  have hc := eq_C_of_derivative_eq_zero h
  exact sub_eq_zero.mp (by simpa [coeff_zero_eq_eval_zero, h0] using hc)

/-- The critical points are exactly `0`, `1`, and `α`. -/
theorem isRoot_derivative_lenstraPolynomial_iff (α x : K) :
    (lenstraPolynomial α).derivative.IsRoot x ↔ x = 0 ∨ x = 1 ∨ x = α := by
  simp [Polynomial.IsRoot, sub_eq_zero, or_assoc]

open Classical in
/-- The multiplicities of the three linear factors of the derivative, including collisions. -/
theorem rootMultiplicity_derivative_lenstraPolynomial (α x : K) :
    (lenstraPolynomial α).derivative.rootMultiplicity x =
      (if x = 0 then 1 else 0) + (if x = 1 then 2 else 0) +
        (if x = α then 3 else 0) := by
  classical
  rw [derivative_lenstraPolynomial]
  have hf : (X * (X - 1) ^ 2 * (X - C α) ^ 3 : K[X]) =
      (X - C 0) * (X - C 1) ^ 2 * (X - C α) ^ 3 := by simp
  rw [hf]
  simp only [rootMultiplicity_mul (mul_ne_zero
    (mul_ne_zero (X_sub_C_ne_zero (0 : K)) (pow_ne_zero 2 (X_sub_C_ne_zero (1 : K))))
    (pow_ne_zero 3 (X_sub_C_ne_zero α))),
    rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero (0 : K))
      (pow_ne_zero 2 (X_sub_C_ne_zero (1 : K))))]
  have hp (a : K) (n : ℕ) : ((X - C a) ^ n).rootMultiplicity x =
      if x = a then n else 0 := by
    by_cases h : x = a
    · subst x
      simp only [ite_true, rootMultiplicity_X_sub_C_pow]
    · simp only [h, ite_false]
      apply rootMultiplicity_eq_zero
      simp [Polynomial.IsRoot, sub_eq_zero, h]
  simp only [hp, rootMultiplicity_X_sub_C]

/-- Each of the three derivative-root multiplicities singles out one critical point. -/
theorem rootMultiplicity_derivative_lenstraPolynomial_eq_iff {α : K}
    (h0 : α ≠ 0) (h1 : α ≠ 1) (x : K) :
    ((lenstraPolynomial α).derivative.rootMultiplicity x = 1 ↔ x = 0) ∧
    ((lenstraPolynomial α).derivative.rootMultiplicity x = 2 ↔ x = 1) ∧
    ((lenstraPolynomial α).derivative.rootMultiplicity x = 3 ↔ x = α) := by
  rw [rootMultiplicity_derivative_lenstraPolynomial]
  by_cases hx0 : x = 0 <;> by_cases hx1 : x = 1 <;> by_cases hxα : x = α <;>
    simp_all

/-- Affine equivalence, even with independent scaling and translation of the values, cannot
change the parameter of Lenstra's polynomial or its two normalized critical points. -/
theorem lenstraPolynomial_comp_affine_eq_iff {α β a b c d : K}
    (hα0 : α ≠ 0) (hα1 : α ≠ 1) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    (lenstraPolynomial α).comp (C a * X + C b) = C c * lenstraPolynomial β + C d ↔
      a = 1 ∧ b = 0 ∧ α = β ∧ c = 1 ∧ d = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- Differentiation transports multiplicities through the affine source map;
    -- nonzero scalings on either side do not affect them.
    have hd := congrArg derivative h
    simp only [derivative_comp, derivative_add, derivative_mul, derivative_C,
      derivative_X, zero_mul, zero_add, mul_one, add_zero] at hd
    have hder (γ : K) : (lenstraPolynomial γ).derivative ≠ 0 := by
      rw [derivative_ne_zero, natDegree_lenstraPolynomial]
      decide
    have hcomp : ((lenstraPolynomial α).derivative.comp (C a * X + C b)) ≠ 0 := by
      rw [ne_eq, comp_eq_zero_iff]
      simp only [hder, false_or, not_and]
      intro _ heq
      have := congrArg (fun p : K[X] ↦ p.coeff 1) heq
      exact ha (by simpa using this)
    have hm (x : K) : (lenstraPolynomial α).derivative.rootMultiplicity (a * x + b) =
        (lenstraPolynomial β).derivative.rootMultiplicity x := by
      have hm := congrArg (rootMultiplicity x) hd
      rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr ha) hcomp),
        rootMultiplicity_C, zero_add,
        rootMultiplicity_comp_C_mul_X_add_C _ _ _ _ (isUnit_iff_ne_zero.mpr ha),
        rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc) (hder β)),
        rootMultiplicity_C, zero_add] at hm
      exact hm
    -- The distinct multiplicities force the source map to fix the normalized points.
    have hb : b = 0 := by
      apply (rootMultiplicity_derivative_lenstraPolynomial_eq_iff hα0 hα1 b).1.mp
      simpa only [mul_zero, zero_add] using (hm 0).trans
        ((rootMultiplicity_derivative_lenstraPolynomial_eq_iff hβ0 hβ1 0).1.mpr rfl)
    have ha1 : a = 1 := by
      apply (rootMultiplicity_derivative_lenstraPolynomial_eq_iff hα0 hα1 a).2.1.mp
      simpa [hb] using (hm 1).trans
        ((rootMultiplicity_derivative_lenstraPolynomial_eq_iff hβ0 hβ1 1).2.1.mpr rfl)
    have hβα : β = α := by
      apply (rootMultiplicity_derivative_lenstraPolynomial_eq_iff hα0 hα1 β).2.2.mp
      simpa [hb, ha1] using (hm β).trans
        ((rootMultiplicity_derivative_lenstraPolynomial_eq_iff hβ0 hβ1 β).2.2.mpr rfl)
    -- The constant and leading coefficients then fix the target normalization too.
    have hd0 : d = 0 := by
      have := congrArg (eval 0) h
      simpa [hb] using this.symm
    have hc1 : c = 1 := by
      simpa [ha1, hb, hd0, lenstraPolynomial, coeff_add, coeff_sub, coeff_C_mul,
        coeff_X_pow] using congrArg (fun p : K[X] ↦ p.coeff 7) h
    exact ⟨ha1, hb, hβα.symm, hc1, hd0⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp

end TauCeti

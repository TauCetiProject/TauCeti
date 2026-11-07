/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# The commutative vertex algebra of polynomials

The polynomial ring `R[X]` is a vertex algebra with vacuum `1`, translation `T = d/dX` and fields

`Y(a, z) b = a(X + z) b = ∑ₖ (D⁽ᵏ⁾ a) b zᵏ`,

where `D⁽ᵏ⁾ = Polynomial.hasseDeriv k` is the `k`-th Hasse derivative, so that `k! D⁽ᵏ⁾ = Tᵏ`
(`TauCeti.FormalVertexAxioms.polynomial`). All modes `a₍ₙ₎` with `n ≥ 0` vanish, and
`a₍₋ₖ₋₁₎` is multiplication by `D⁽ᵏ⁾ a`. Since all modes are multiplication operators they
commute, so the fields are local of order zero.

This is the basic example of a commutative vertex algebra: the construction works over every
commutative ring, because the Hasse derivatives supply the divided powers `Tᵏ a / k!` without
division.

## References

* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.4.
* R. Borcherds, *Vertex algebras, Kac–Moody algebras, and the Monster*, Proc. Natl. Acad. Sci.
  USA 83 (1986), the commutative vertex algebra of a commutative ring with a derivation.
-/

public section

noncomputable section

open scoped VertexOperator
open Polynomial

namespace TauCeti.FormalVertexAxioms

variable (R : Type*) [CommRing R]

/-- The Laurent coefficients of the polynomial fields: the coefficient of `zᵐ` in `Y(a, z)` is
multiplication by `D⁽ᵐ⁾ a` for `m ≥ 0`, and zero for `m < 0`. -/
private def polynomialCoeff (m : ℤ) : R[X] →ₗ[R] Module.End R R[X] :=
  if 0 ≤ m then LinearMap.mul R R[X] ∘ₗ hasseDeriv m.toNat else 0

private theorem bddBelow_support_polynomialCoeff (a b : R[X]) :
    BddBelow (Function.support fun m ↦ polynomialCoeff R m a b) := by
  refine ⟨0, fun m hm ↦ ?_⟩
  by_contra h
  simp [polynomialCoeff, not_le.mpr (not_le.mp h)] at hm

/-- The polynomial state–field correspondence `a ↦ Y(a, z)`, with `Y(a, z) b = a(X + z) b`. -/
private def polynomialY : R[X] →ₗ[R] VertexOperator R R[X] where
  toFun a := VertexOperator.of_coeff (fun m ↦ polynomialCoeff R m a)
    (bddBelow_support_polynomialCoeff R a)
  map_add' a b := VertexOperator.ext_ncoeff fun n ↦ by simp
  map_smul' r a := VertexOperator.ext_ncoeff fun n ↦ by simp

private theorem polynomialCoeff_natCast (k : ℕ) :
    polynomialCoeff R k = LinearMap.mul R R[X] ∘ₗ hasseDeriv k := by
  simp [polynomialCoeff]

private theorem polynomialCoeff_of_neg {m : ℤ} (hm : m < 0) : polynomialCoeff R m = 0 := by
  simp [polynomialCoeff, not_le.mpr hm]

private theorem ncoeff_polynomialY (a : R[X]) (n : ℤ) :
    (polynomialY R a)[[n]] = polynomialCoeff R (-n - 1) a := by
  simp [polynomialY]

private theorem ncoeff_polynomialY_neg_sub_one (a : R[X]) (k : ℕ) :
    (polynomialY R a)[[-k - 1]] = LinearMap.mulLeft R (hasseDeriv k a) := by
  rw [ncoeff_polynomialY, show -(-(k : ℤ) - 1) - 1 = k by omega, polynomialCoeff_natCast]
  exact LinearMap.ext fun b ↦ by simp

private theorem ncoeff_polynomialY_of_nonneg (a : R[X]) {n : ℤ} (hn : 0 ≤ n) :
    (polynomialY R a)[[n]] = 0 := by
  rw [ncoeff_polynomialY, polynomialCoeff_of_neg R (by omega), LinearMap.zero_apply]

/-- Every integer is either nonnegative or of the form `-k - 1` with `k : ℕ`. -/
private theorem nonneg_or_eq_neg_sub_one (n : ℤ) : 0 ≤ n ∨ ∃ k : ℕ, n = -k - 1 := by
  rcases le_or_gt 0 n with hn | hn
  · exact Or.inl hn
  · exact Or.inr ⟨(-n - 1).toNat, by omega⟩

/-- Each mode of a polynomial field is a multiplication operator. -/
private theorem exists_ncoeff_polynomialY_eq_mulLeft (a : R[X]) (n : ℤ) :
    ∃ p : R[X], (polynomialY R a)[[n]] = LinearMap.mulLeft R p := by
  rcases nonneg_or_eq_neg_sub_one n with hn | ⟨k, rfl⟩
  · exact ⟨0, by rw [ncoeff_polynomialY_of_nonneg R a hn, LinearMap.mulLeft_zero_eq_zero]⟩
  · exact ⟨_, ncoeff_polynomialY_neg_sub_one R a k⟩

/-- The **commutative vertex algebra of polynomials**: `R[X]` with vacuum `1`, translation
`T = d/dX` and fields `Y(a, z) b = a(X + z) b = ∑ₖ (D⁽ᵏ⁾ a) b zᵏ`, where `D⁽ᵏ⁾` is the `k`-th
Hasse derivative. -/
def polynomial : FormalVertexAxioms R R[X] where
  Y := polynomialY R
  vacuum := 1
  translation := derivative
  translation_vacuum := derivative_one
  ncoeff_Y_vacuum n := by
    rcases nonneg_or_eq_neg_sub_one n with hn | ⟨k, rfl⟩
    · rw [ncoeff_polynomialY_of_nonneg R 1 hn]
      simp [show n ≠ -1 by omega]
    · rw [ncoeff_polynomialY_neg_sub_one]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [LinearMap.mulLeft_one, Module.End.one_eq_id]
      · rw [hasseDeriv_apply_one k hk, LinearMap.mulLeft_zero_eq_zero]
        simp [show -(k : ℤ) - 1 ≠ -1 by omega]
  ncoeff_Y_apply_vacuum_of_nonneg a n hn := by
    rw [ncoeff_polynomialY_of_nonneg R a hn, LinearMap.zero_apply]
  factorial_smul_ncoeff_Y_apply_vacuum a k := by
    rw [ncoeff_polynomialY_neg_sub_one, LinearMap.mulLeft_apply, mul_one, pow_apply_eq_iterate,
      ← LinearMap.smul_apply, ← factorial_smul_hasseDeriv]
  Y_translation a := VertexOperator.ext_ncoeff fun n ↦ by
    rw [VertexOperator.ncoeff_derivative]
    rcases nonneg_or_eq_neg_sub_one n with hn | ⟨k, rfl⟩
    · rcases hn.eq_or_lt with rfl | hn
      · rw [ncoeff_polynomialY_of_nonneg R _ le_rfl, neg_zero, zero_smul]
      · rw [ncoeff_polynomialY_of_nonneg R _ hn.le, ncoeff_polynomialY_of_nonneg R _ (by omega),
          smul_zero]
    · rw [ncoeff_polynomialY_neg_sub_one, show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by
          push_cast; ring, ncoeff_polynomialY_neg_sub_one]
      -- `D⁽ᵏ⁾ (d/dX a) = (k + 1) D⁽ᵏ⁺¹⁾ a`, by composition of Hasse derivatives.
      have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) k 1) a
      rw [LinearMap.comp_apply, hasseDeriv_one, Nat.choose_succ_self_right] at h
      refine LinearMap.ext fun b ↦ ?_
      simp [h]
      ring
  lie_translation_ncoeff_Y a n := by
    rcases nonneg_or_eq_neg_sub_one n with hn | ⟨k, rfl⟩
    · rcases hn.eq_or_lt with rfl | hn
      · simp [Ring.lie_def, ncoeff_polynomialY_of_nonneg R _ le_rfl]
      · rw [ncoeff_polynomialY_of_nonneg R _ hn.le, ncoeff_polynomialY_of_nonneg R _ (by omega)]
        simp [Ring.lie_def]
    · rw [ncoeff_polynomialY_neg_sub_one, show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by
          push_cast; ring, ncoeff_polynomialY_neg_sub_one]
      -- `d/dX (D⁽ᵏ⁾ a) = (k + 1) D⁽ᵏ⁺¹⁾ a`, by composition of Hasse derivatives.
      have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) 1 k) a
      rw [LinearMap.comp_apply, hasseDeriv_one, add_comm 1 k, Nat.choose_one_right] at h
      refine LinearMap.ext fun b ↦ ?_
      simp [Ring.lie_def, derivative_mul, h]
      ring
  exists_isLocalOfOrder a b := ⟨0, VertexOperator.isLocalOfOrder_iff.mpr fun m n ↦ by
    obtain ⟨p, hp⟩ := exists_ncoeff_polynomialY_eq_mulLeft R a m
    obtain ⟨q, hq⟩ := exists_ncoeff_polynomialY_eq_mulLeft R b n
    refine LinearMap.ext fun c ↦ ?_
    simp [hp, hq, mul_left_comm]⟩

/-- The vacuum of the polynomial vertex algebra is `1`. -/
@[simp]
theorem vacuum_polynomial : (polynomial R).vacuum = 1 := (rfl)

/-- The translation operator of the polynomial vertex algebra is `d/dX`. -/
@[simp]
theorem translation_polynomial : (polynomial R).translation = derivative := (rfl)

/-- The negative modes of the polynomial vertex algebra: `a₍₋ₖ₋₁₎` is multiplication by the
`k`-th Hasse derivative of `a`. -/
@[simp]
theorem formalMode_polynomial_neg_sub_one (a : R[X]) (k : ℕ) :
    (polynomial R).formalMode a (-k - 1) = LinearMap.mulLeft R (hasseDeriv k a) := by
  rw [← ncoeff_Y]
  exact ncoeff_polynomialY_neg_sub_one R a k

/-- The nonnegative modes of the polynomial vertex algebra vanish. -/
theorem formalMode_polynomial_of_nonneg (a : R[X]) {n : ℤ} (hn : 0 ≤ n) :
    (polynomial R).formalMode a n = 0 := by
  rw [← ncoeff_Y]
  exact ncoeff_polynomialY_of_nonneg R a hn

end TauCeti.FormalVertexAxioms

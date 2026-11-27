/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.CharP.Algebra
import TauCeti.Algebra.MvPolynomial.Monomial

/-!
# Normal-crossing polynomial quotients

The quotient by the product of the coordinates kills exactly the monomials with positive
exponent in every coordinate. When there is at least one coordinate, evaluation at the
origin retracts the constant inclusion.
-/

public section

namespace TauCeti

open _root_.MvPolynomial

/-- The normal-crossing coordinate ring obtained by setting the product of the variables to zero. -/
abbrev MonomialRootAlgebra (R σ : Type*) [CommRing R] [Fintype σ] :=
  MvPolynomial σ R ⧸ Ideal.span {∏ i : σ, (X i : MvPolynomial σ R)}

namespace MonomialRootAlgebra

variable {R σ : Type*} [CommRing R] [Fintype σ]

local notation "P" => MvPolynomial σ R
local notation "A" => MonomialRootAlgebra R σ
local notation "J" => Ideal.span {∏ i : σ, (X i : P)}
local notation "π" => Ideal.Quotient.mk J

/-- The image of a coordinate monomial in the normal-crossing quotient. -/
noncomputable def monomialClass (d : σ →₀ ℕ) (c : R) : A :=
  π (monomial d c)

/-- The monomial class is the image of the polynomial monomial under the quotient map. -/
theorem monomialClass_eq_mk (d : σ →₀ ℕ) (c : R) :
    monomialClass d c = π (monomial d c) :=
  (rfl)

/-- The zero exponent gives the image of the coefficient. -/
@[simp]
theorem monomialClass_zero (c : R) :
    monomialClass (0 : σ →₀ ℕ) c = algebraMap R A c := by
  rw [monomialClass_eq_mk, monomial_zero', IsScalarTower.algebraMap_apply R P A,
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]

/-- Multiplication of coordinate monomial classes adds exponents and multiplies coefficients. -/
@[simp]
theorem monomialClass_mul (d e : σ →₀ ℕ) (c b : R) :
    monomialClass d c * monomialClass e b = monomialClass (d + e) (c * b) := by
  simp only [monomialClass_eq_mk, ← map_mul, monomial_mul_monomial]

/-- Raising a coordinate monomial class to a power scales its exponent vector. -/
@[simp]
theorem monomialClass_pow (d : σ →₀ ℕ) (c : R) (k : ℕ) :
    monomialClass d c ^ k = monomialClass (k • d) (c ^ k) := by
  simp only [monomialClass_eq_mk, ← map_pow, monomial_pow]

/-- A polynomial vanishes in the quotient exactly when every monomial in its support
is divisible by the product of the variables. -/
theorem mk_eq_zero_iff (f : P) : π f = 0 ↔ ∀ d ∈ f.support, ∀ i, 0 < d i :=
  (Ideal.Quotient.eq_zero_iff_mem).trans f.mem_span_prod_X_iff

/-- The defining relation kills exactly those monomials with zero coefficient or with
positive exponent in every coordinate. -/
@[simp]
theorem monomialClass_eq_zero_iff (d : σ →₀ ℕ) (c : R) :
    monomialClass d c = 0 ↔ c = 0 ∨ ∀ i, 0 < d i := by
  classical
  by_cases hc : c = 0
  · simp [monomialClass_eq_mk, hc]
  · simp [monomialClass_eq_mk, mk_eq_zero_iff, support_monomial, hc]

/-- The product of the coordinate functions vanishes in the hypersurface. -/
@[simp]
theorem prod_mk_X_eq_zero : ∏ i : σ, π (X i) = 0 := by
  rw [← map_prod]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- Evaluation at the origin of a normal-crossing hypersurface with at least one coordinate.
It retracts the constant inclusion by `AlgHom.commutes`. -/
noncomputable def evalZero [Nonempty σ] : A →ₐ[R] R :=
  Ideal.Quotient.liftₐ J (aeval (0 : σ → R)) <| by
    intro f hf
    have hJ : J ≤ RingHom.ker (aeval (0 : σ → R)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro g rfl
      simp [RingHom.mem_ker, map_prod]
    exact RingHom.mem_ker.mp (hJ hf)

/-- On polynomial representatives, evaluation at the origin returns the constant coefficient. -/
@[simp]
theorem evalZero_mk [Nonempty σ] (f : P) : evalZero (π f) = constantCoeff f := by
  unfold evalZero
  rw [Ideal.Quotient.liftₐ_apply]
  exact (Ideal.Quotient.lift_mk _ _ _).trans (by simp)

/-- For a nonempty coordinate type, the normal-crossing quotient inherits the characteristic
of its coefficient ring. -/
instance {p : ℕ} [CharP R p] [Nonempty σ] : CharP A p := by
  apply charP_of_injective_algebraMap (R := R) _ p
  intro a b h
  simpa using congrArg (evalZero (R := R) (σ := σ)) h

end MonomialRootAlgebra
end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.Tactic.Ring
import TauCeti.Data.Finsupp.Factorial
import TauCeti.RingTheory.MvPolynomial.Basic

/-!
# The jet pairing of polynomials with formal power series

A polynomial acts as a constant-coefficient differential operator. Its pairing with a
formal power series is the constant term after applying that operator. In monomial
coordinates the pairing weights each coefficient by its multi-index factorial.

The adjoint of multiplication by a variable is the corresponding formal partial
derivative. When the multi-index factorials are units, every linear functional on
polynomials is represented by a unique formal power series via this pairing.

## References

The pairing and its basic identities adapt `New.jet` and related lemmas in ShortProof
(`src/Lib/GLn/SchurModule/Basic.lean` in <https://github.com/lsernau/grh-lean>,
Apache 2.0, Copyright 2026 Anthropic, PBC).
ShortProof is Claude’s Lean rewriting of Levent Alpöge’s proof, published by Anthropic.
-/

public section

namespace MvPolynomial

open scoped BigOperators
open Finsupp

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Pairing a polynomial with a formal power series by applying the corresponding
constant-coefficient differential operator and taking the constant term. -/
noncomputable def jetPairing : MvPolynomial σ R →ₗ[R] MvPowerSeries σ R →ₗ[R] R :=
  (basisMonomials σ R).constr R fun d ↦
    (d.prod fun _ n ↦ (n.factorial : R)) • MvPowerSeries.coeff d

private theorem jetPairing_basisMonomials (d : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    jetPairing (basisMonomials σ R d) f =
      (d.prod fun _ n ↦ (n.factorial : R)) * MvPowerSeries.coeff d f := by
  simp only [jetPairing, Module.Basis.constr_basis, LinearMap.smul_apply, smul_eq_mul]

/-- A monomial tests the coefficient at its exponent, weighted by the multi-index factorial. -/
@[simp]
theorem jetPairing_monomial (d : σ →₀ ℕ) (a : R) (f : MvPowerSeries σ R) :
    jetPairing (monomial d a) f =
      a * (d.prod fun _ n ↦ (n.factorial : R)) * MvPowerSeries.coeff d f := by
  have hmon : monomial d a = a • basisMonomials σ R d := by
    simp [coe_basisMonomials, smul_monomial]
  simp only [hmon, map_smul, LinearMap.smul_apply, jetPairing_basisMonomials, smul_eq_mul,
    mul_assoc]

/-- A constant polynomial tests the constant term. -/
@[simp]
theorem jetPairing_C (a : R) (f : MvPowerSeries σ R) :
    jetPairing (C a) f = a * MvPowerSeries.constantCoeff f := by
  rw [← monomial_zero', jetPairing_monomial]
  simp [MvPowerSeries.coeff_zero_eq_constantCoeff]

/-- The unit polynomial tests the constant term. -/
@[simp]
theorem jetPairing_one (f : MvPowerSeries σ R) :
    jetPairing 1 f = MvPowerSeries.constantCoeff f := by
  simpa only [C_1, one_mul] using jetPairing_C 1 f

/-- A variable tests the coefficient of its degree-one monomial. -/
@[simp]
theorem jetPairing_X (i : σ) (f : MvPowerSeries σ R) :
    jetPairing (X i) f = MvPowerSeries.coeff (Finsupp.single i 1) f := by
  simp [X]

/-- The jet pairing in coefficient coordinates. -/
theorem jetPairing_eq_sum (p : MvPolynomial σ R) (f : MvPowerSeries σ R) :
    jetPairing p f =
      ∑ d ∈ p.support, p.coeff d * (d.prod fun _ n ↦ (n.factorial : R)) *
        MvPowerSeries.coeff d f := by
  have hrepr : (basisMonomials σ R).repr p = p.coeff :=
    Finsupp.ext fun d ↦ basisMonomials_repr_apply p d
  rw [jetPairing, Module.Basis.constr_apply, hrepr]
  simp only [Finsupp.sum, finsupp_support_eq_support, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, mul_assoc]

/-- Multiplying a polynomial by a variable is adjoint to differentiating the series. -/
theorem jetPairing_mul_X (p : MvPolynomial σ R) (f : MvPowerSeries σ R) (i : σ) :
    jetPairing (p * X i) f = jetPairing p (MvPowerSeries.pderiv i f) := by
  classical
  rw [jetPairing_eq_sum, jetPairing_eq_sum, support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [addRightEmbedding_apply, coeff_mul_X, MvPowerSeries.coeff_pderiv,
    Finsupp.prod_factorial_add_single]
  ring

/-- The jet pairing commutes with a change of coefficients. -/
theorem map_jetPairing {S : Type*} [CommSemiring S] (φ : R →+* S)
    (p : MvPolynomial σ R) (f : MvPowerSeries σ R) :
    φ (jetPairing p f) = jetPairing (map φ p) (MvPowerSeries.map φ f) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a => simp [map_finsuppProd, MvPowerSeries.coeff_map]
  | add p q hp hq => simp [hp, hq]

/-- When all the multi-index factorials are units, formal series represent the algebraic dual
of the polynomial module via the jet pairing. The representing series is obtained by dividing
the functional's values on monomials by their multi-index factorials. -/
noncomputable def jetPairingDualEquiv
    (h : ∀ d : σ →₀ ℕ, IsUnit (d.prod fun _ n ↦ (n.factorial : R))) :
    MvPowerSeries σ R ≃ₗ[R] (MvPolynomial σ R →ₗ[R] R) :=
  (LinearEquiv.piCongrRight fun d ↦ LinearEquiv.smulOfUnit (M := R) (h d).unit).trans
    ((basisMonomials σ R).constr R)

/-- Evaluating the functional represented by a series is the jet pairing. -/
@[simp]
theorem jetPairingDualEquiv_apply
    (h : ∀ d : σ →₀ ℕ, IsUnit (d.prod fun _ n ↦ (n.factorial : R)))
    (f : MvPowerSeries σ R) (p : MvPolynomial σ R) :
    jetPairingDualEquiv h f p = jetPairing p f := by
  have heq : jetPairingDualEquiv h f = jetPairing.flip f := by
    apply (basisMonomials σ R).ext
    intro d
    rw [LinearMap.flip_apply, jetPairing_basisMonomials, MvPowerSeries.coeff_apply,
      jetPairingDualEquiv]
    -- The equivalence rewrites use the coefficient-function type underlying MvPowerSeries.
    erw [LinearEquiv.trans_apply, Module.Basis.constr_basis, LinearEquiv.piCongrRight_apply]
    rw [LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv_apply, Units.smul_def,
      smul_eq_mul, (h d).unit_spec]
  exact LinearMap.congr_fun heq p

/-- The series representing a functional has its monomial values divided by the factorials. -/
@[simp]
theorem coeff_jetPairingDualEquiv_symm
    (h : ∀ d : σ →₀ ℕ, IsUnit (d.prod fun _ n ↦ (n.factorial : R)))
    (L : MvPolynomial σ R →ₗ[R] R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d ((jetPairingDualEquiv h).symm L) =
      ↑(h d).unit⁻¹ * L (monomial d 1) := by
  rw [MvPowerSeries.coeff_apply, jetPairingDualEquiv]
  -- The equivalence rewrites use the coefficient-function type underlying MvPowerSeries.
  erw [LinearEquiv.symm_trans_apply, LinearEquiv.piCongrRight_symm,
    LinearEquiv.piCongrRight_apply]
  rw [LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv_symm_apply, Units.smul_def,
    smul_eq_mul, Module.Basis.constr_symm_apply, coe_basisMonomials]

end CommSemiring

end MvPolynomial

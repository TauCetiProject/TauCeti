/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.Tactic.Ring

/-!
# The jet pairing of polynomials with formal power series

A polynomial acts as a constant-coefficient differential operator. Its pairing with a
formal power series is the constant term after applying that operator. In monomial
coordinates the pairing weights each coefficient by its multi-index factorial.

The adjoint of multiplication by a variable is the corresponding formal partial
derivative. When the multi-index factorials are units, every linear functional on
polynomials is represented by a unique formal power series via this pairing.
-/

@[expose] public section

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

/-- A monomial tests the coefficient at its exponent, weighted by the multi-index factorial. -/
@[simp]
theorem jetPairing_monomial (d : σ →₀ ℕ) (a : R) (f : MvPowerSeries σ R) :
    jetPairing (monomial d a) f =
      a * (d.prod fun _ n ↦ (n.factorial : R)) * MvPowerSeries.coeff d f := by
  rw [show monomial d a = a • monomial d 1 by simp [smul_monomial],
    map_smul, LinearMap.smul_apply]
  change a • jetPairing ((basisMonomials σ R) d) f = _
  rw [jetPairing, Module.Basis.constr_basis]
  simp [mul_assoc]

/-- A constant polynomial tests the constant term. -/
@[simp]
theorem jetPairing_C (a : R) (f : MvPowerSeries σ R) :
    jetPairing (C a) f = a * MvPowerSeries.constantCoeff f := by
  rw [← monomial_zero', jetPairing_monomial]
  simp [MvPowerSeries.coeff_zero_eq_constantCoeff]

/-- The jet pairing in coefficient coordinates. -/
theorem jetPairing_eq_sum (p : MvPolynomial σ R) (f : MvPowerSeries σ R) :
    jetPairing p f =
      ∑ d ∈ p.support, p.coeff d * (d.prod fun _ n ↦ (n.factorial : R)) *
        MvPowerSeries.coeff d f := by
  simp [jetPairing, Module.Basis.constr_apply, Finsupp.sum, mul_assoc]
  rfl

/-- Multiplying a polynomial by a variable is adjoint to differentiating the series. -/
theorem jetPairing_mul_X (p : MvPolynomial σ R) (f : MvPowerSeries σ R) (i : σ) :
    jetPairing (p * X i) f = jetPairing p (MvPowerSeries.pderiv i f) := by
  classical
  rw [jetPairing_eq_sum, jetPairing_eq_sum, support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [addRightEmbedding_apply, coeff_mul_X, MvPowerSeries.coeff_pderiv]
  have hfac :
      ((d + single i 1).prod fun _ n ↦ (n.factorial : R)) =
        ((d i : R) + 1) * d.prod fun _ n ↦ (n.factorial : R) := by
    rw [← mul_prod_erase' (d + single i 1) i _ (by simp),
      ← mul_prod_erase' d i _ (by simp), erase_add, erase_single, add_zero,
      Finsupp.add_apply, single_eq_same, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    rw [mul_assoc]
  rw [hfac]
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
  LinearEquiv.ofBijective jetPairing.flip (by
    refine ⟨?_, ?_⟩
    · intro f g hfg
      ext d
      have hd := LinearMap.congr_fun hfg (monomial d 1)
      simp only [LinearMap.flip_apply, jetPairing_monomial, one_mul] at hd
      exact (h d).mul_left_cancel hd
    · intro L
      let f : MvPowerSeries σ R := fun d ↦ ((h d).unit⁻¹ : Rˣ) • L (monomial d 1)
      refine ⟨f, (basisMonomials σ R).ext fun d ↦ ?_⟩
      change jetPairing (monomial d 1) f = L (monomial d 1)
      rw [jetPairing_monomial, one_mul]
      let u := (h d).unit
      have hu : (↑u : R) = d.prod fun _ n ↦ (n.factorial : R) := (h d).unit_spec
      change (d.prod fun _ n ↦ (n.factorial : R)) * (↑u⁻¹ * L (monomial d 1)) = _
      rw [← mul_assoc, ← hu, Units.mul_inv, one_mul])

/-- Evaluating the functional represented by a series is the jet pairing. -/
@[simp]
theorem jetPairingDualEquiv_apply
    (h : ∀ d : σ →₀ ℕ, IsUnit (d.prod fun _ n ↦ (n.factorial : R)))
    (f : MvPowerSeries σ R) (p : MvPolynomial σ R) :
    jetPairingDualEquiv h f p = jetPairing p f := rfl

end CommSemiring

end MvPolynomial

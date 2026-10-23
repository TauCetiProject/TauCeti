/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Tangent vectors of polynomial curves

A polynomial curve in an affine monoid that starts at the identity has a tangent vector
there. On coordinate rings its velocity takes the coefficient of degree one. The constant
coefficient is the counit, so the polynomial product formula gives the counit-valued
Leibniz rule. This construction lets polynomial one-parameter curves supply actual tangent
vectors without any smoothness or reducedness assumption.

The tangent carrier is the existing `TauCeti.Bialgebra.CounitAlgebra`; no new tangent-space
model is introduced.
-/

public section

namespace TauCeti.Bialgebra

open Polynomial

variable {R H : Type*} [CommSemiring R] [CommSemiring H] [_root_.Bialgebra R H]

/-- The velocity at zero of a polynomial curve starting at the identity. Its coordinate
map has direction `H →ₐ[R] R[X]`. -/
noncomputable def polynomialCurveTangent (φ : H →ₐ[R] R[X])
    (hφ : (aeval (0 : R)).comp φ = _root_.Bialgebra.counitAlgHom R H) :
    Derivation R H (CounitAlgebra R H R) where
  toLinearMap := (CounitAlgebra.algEquivSelf R H R).symm.toLinearMap.comp
    ((lcoeff R 1).comp φ.toLinearMap)
  map_one_eq_zero' := by
    -- The linear-map fields return the counit coefficient synonym.
    simp [Polynomial.coeff_one]
    rfl
  leibniz' a b := by
    apply (CounitAlgebra.algEquivSelf R H R).injective
    have hzero (x : H) : (φ x).coeff 0 = Coalgebra.counit (R := R) x := by
      simpa only [AlgHom.comp_apply, Polynomial.coeff_zero_eq_aeval_zero,
        _root_.Bialgebra.counitAlgHom_apply] using AlgHom.congr_fun hφ x
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, lcoeff_apply,
      AlgHom.toLinearMap_apply, map_mul, map_add, AlgEquiv.apply_symm_apply,
      CounitAlgebra.algEquivSelf_smul, Algebra.algebraMap_self, RingHom.id_apply]
    rw [mul_coeff_one, hzero, hzero]
    ring

/-- The velocity reads the linear coefficient of each pulled-back coordinate function. -/
@[simp]
theorem polynomialCurveTangent_apply (φ : H →ₐ[R] R[X])
    (hφ : (aeval (0 : R)).comp φ = _root_.Bialgebra.counitAlgHom R H) (x : H) :
    polynomialCurveTangent φ hφ x = (φ x).coeff 1 := by
  -- The simplification leaves only the definitional identification of the coefficient synonym.
  simp [polynomialCurveTangent]
  rfl

end TauCeti.Bialgebra

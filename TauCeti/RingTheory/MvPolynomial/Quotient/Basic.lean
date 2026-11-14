/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Polynomial quotients and coefficient extension

Monomials span every polynomial quotient. The canonical tensor-product equivalence identifies
coefficient extension of a quotient with the quotient by the extended ideal.
-/

public section

open TensorProduct

namespace MvPolynomial

variable {n A B : Type*} [CommRing A] [CommRing B]

/-- The images of the monomials span `A[n] ⧸ I` as an `A`-module. -/
@[simp]
theorem _root_.Ideal.span_range_mk_monomial_eq_top (I : Ideal (MvPolynomial n A)) :
    Submodule.span A (Set.range fun m : n →₀ ℕ ↦ Ideal.Quotient.mk I (monomial m 1)) = ⊤ := by
  have := congrArg (Submodule.map (Ideal.Quotient.mkₐ A I).toLinearMap)
    (basisMonomials n A).span_eq
  rwa [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr
    (Ideal.Quotient.mkₐ_surjective A I), ← Set.range_comp, coe_basisMonomials] at this

variable [Algebra A B]

/-- Coefficient extension commutes with forming a polynomial quotient. -/
noncomputable def _root_.Ideal.tensorQuotientMvPolynomialEquiv (I : Ideal (MvPolynomial n A)) :
    B ⊗[A] (MvPolynomial n A ⧸ I) ≃ₐ[B]
      MvPolynomial n B ⧸ I.map (map (algebraMap A B)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv B (MvPolynomial n A) B I).trans
    (Ideal.quotientEquivAlg _ _ (algebraTensorAlgEquiv A B) (by
      -- Make the algebra-equivalence and inclusion coercions explicit as ring maps.
      change I.map (map (algebraMap A B)) =
        (I.map (Algebra.TensorProduct.includeRight (A := B) (R := A)).toRingHom).map
          (algebraTensorAlgEquiv A B).toAlgHom.toRingHom
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun p ↦ by simp))

/-- The coefficient-extension comparison sends a pure tensor to its scalar polynomial class. -/
@[simp]
theorem _root_.Ideal.tensorQuotientMvPolynomialEquiv_tmul
    (I : Ideal (MvPolynomial n A)) (b : B) (p : MvPolynomial n A) :
    I.tensorQuotientMvPolynomialEquiv (b ⊗ₜ[A] Ideal.Quotient.mk I p) =
      b • Ideal.Quotient.mk (I.map (map (algebraMap A B))) (map (algebraMap A B) p) := by
  -- Both quotient equivalences evaluate a quotient class on its polynomial representative.
  change Ideal.Quotient.mk _ (algebraTensorAlgEquiv A B (b ⊗ₜ[A] p)) = _
  rw [algebraTensorAlgEquiv_tmul, ← Ideal.Quotient.mkₐ_eq_mk B, map_smul]

end MvPolynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral closure in a finite product

An element of a finite product of algebras is integral exactly when each coordinate is
integral. Consequently, integral closure commutes with finite products. This comparison
allows normalization and étaleness questions for finite products of fields to be checked
on the individual field factors.

The finiteness assumption is essential: the integral equations for infinitely many
coordinates need not have a common degree or common coefficients.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

/-- A tuple in a finite product of algebras is integral if and only if every coordinate is
integral. A common monic equation is the product of the coordinate equations. -/
@[simp]
theorem isIntegral_pi_iff {B : ι → Type*} [∀ i, Ring (B i)] [∀ i, Algebra R (B i)]
    {x : ∀ i, B i} : IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨fun hx i ↦ hx.map (Pi.evalAlgHom R B i), fun hx ↦ ?_⟩
  choose p hp hroot using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ ↦ hp i), ?_⟩
  ext i
  exact (aeval_algHom_apply (Pi.evalAlgHom R B i) x _).symm.trans (by
    rw [Fintype.prod_eq_mul_prod_compl i, aeval_mul]
    exact mul_eq_zero_of_left (hroot i) _)

variable (R) (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

/-- Integral closure commutes with finite products, by taking coordinates of integral tuples. -/
def integralClosurePiAlgEquiv :
    integralClosure R (∀ i, B i) ≃ₐ[R] ∀ i, integralClosure R (B i) where
  toFun x i := ⟨x.1 i, (isIntegral_pi_iff.mp x.2) i⟩
  invFun x := ⟨fun i ↦ (x i).1, isIntegral_pi_iff.mpr fun i ↦ (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The product comparison takes an integral tuple to its coordinates. -/
@[simp]
theorem integralClosurePiAlgEquiv_apply (x : integralClosure R (∀ i, B i)) (i : ι) :
    (integralClosurePiAlgEquiv R B x i : B i) = x.1 i := (rfl)

/-- The inverse product comparison assembles the coordinates into an integral tuple. -/
@[simp]
theorem integralClosurePiAlgEquiv_symm_apply (x : ∀ i, integralClosure R (B i)) (i : ι) :
    ((integralClosurePiAlgEquiv R B).symm x : ∀ i, B i) i = x i := (rfl)

end TauCeti

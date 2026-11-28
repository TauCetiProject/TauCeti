/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Equivalences and dimension of Jacobson radical quotients

A ring equivalence descends to the quotients by the Jacobson radicals. When an algebra is
isomorphic to a semisimple algebra, its radical quotient has the dimension of that algebra.
-/

public section

/-- A ring equivalence descends to an equivalence of the quotients by the Jacobson radicals. -/
def RingEquiv.quotientJacobsonCongr {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    R ⧸ Ring.jacobson R ≃+* S ⧸ Ring.jacobson S :=
  Ideal.quotientEquiv _ _ e (by
    rw [Ideal.map_eq_submodule_map, Module.map_jacobson_of_bijective e.bijective])

/-- The induced equivalence sends the class of an element to the class of its image. -/
@[simp]
theorem RingEquiv.quotientJacobsonCongr_mk {R S : Type*} [Ring R] [Ring S]
    (e : R ≃+* S) (r : R) :
    e.quotientJacobsonCongr (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (e r) :=
  Ideal.quotientEquiv_mk _ _ e _ r

/-- If an algebra is isomorphic to a semisimple algebra, its quotient by the Jacobson radical
has the same dimension over the base as the semisimple algebra. -/
theorem AlgEquiv.finrank_quotient_jacobson_eq {k A B : Type*} [CommSemiring k]
    [Ring A] [Ring B] [Algebra k A] [Algebra k B] [IsSemisimpleRing B] (e : A ≃ₐ[k] B) :
    Module.finrank k (A ⧸ Ring.jacobson A) = Module.finrank k B := by
  have : IsSemisimpleRing A := e.toRingEquiv.isSemisimpleRing_iff.mpr inferInstance
  exact ((Ideal.quotientEquivAlgOfEq k (IsSemisimpleRing.jacobson_eq_bot A)).trans
    ((AlgEquiv.quotientBot k A).trans e)).toLinearEquiv.finrank_eq

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Finite

/-!
# Base change of finite étale algebras

Functoriality of `CommAlgCat.FiniteEtale.baseChange`: in a scalar tower `R → S → T`, composing base
change from `R` to `S` with base change from `S` to `T` is naturally isomorphic to base change from
`R` to `T` (`CommAlgCat.FiniteEtale.baseChangeCompIso`). As a consequence, base change along a
bijective ring homomorphism is an equivalence of categories
(`CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_bijective`).
-/

public section

open CategoryTheory

universe u v

namespace CommAlgCat.FiniteEtale

section Tower

variable (R : Type v) (S T : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Base change of finite étale algebras composes up to natural isomorphism in a scalar tower. -/
noncomputable def baseChangeCompIso :
    baseChange.{u} R S ⋙ baseChange.{u} S T ≅ baseChange.{u} R T :=
  NatIso.ofComponents
    (fun A ↦ isoMk (Algebra.TensorProduct.cancelBaseChange R S T T A))
    fun {A B} f ↦ by
      dsimp [baseChange]
      ext
      simp

/-- Component of `(baseChangeCompIso R S T).hom` at `A`. -/
@[simp]
theorem baseChangeCompIso_hom_app (A : FiniteEtale.{u} R) :
    (baseChangeCompIso R S T).hom.app A =
      (isoMk (Algebra.TensorProduct.cancelBaseChange R S T T A)).hom :=
  (rfl)

/-- Component of `(baseChangeCompIso R S T).inv` at `A`. -/
@[simp]
theorem baseChangeCompIso_inv_app (A : FiniteEtale.{u} R) :
    (baseChangeCompIso R S T).inv.app A =
      (isoMk (Algebra.TensorProduct.cancelBaseChange R S T T A)).inv :=
  (rfl)

end Tower

/-- Base change of finite étale algebras along a bijective ring homomorphism is an equivalence of
categories. -/
theorem isEquivalence_baseChange_of_bijective {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) :
    (baseChange.{u} R S).IsEquivalence := by
  let e : R ≃+* S := RingEquiv.ofBijective (algebraMap R S) h
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R S R := .of_algebraMap_eq fun r ↦ (e.symm_apply_apply r).symm
  have : IsScalarTower S R S := .of_algebraMap_eq fun s ↦ (e.apply_symm_apply s).symm
  exact Functor.IsEquivalence.mk' (baseChange.{u} S R)
    ((baseChangeSelfIso R).symm ≪≫ (baseChangeCompIso R S R).symm)
    (baseChangeCompIso S R S ≪≫ baseChangeSelfIso S)

end CommAlgCat.FiniteEtale

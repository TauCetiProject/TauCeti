/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.RestrictScalars
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Base change of commutative algebras

Extension of scalars sends a commutative `R`-algebra `A` to `S ⊗[R] A`. It is left adjoint
to restriction of scalars, and therefore preserves colimits. In particular, a filtered
presentation of an algebra base changes to a filtered presentation over the new base.

The adjunction packages Mathlib's `Algebra.TensorProduct.liftEquivRight`, with the forward
map given by restriction to `1 ⊗ a` and the inverse by `s ⊗ a ↦ s • f(a)`.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe u v w

namespace CommAlgCat

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Extension of scalars for commutative algebras, with scalar ring `S`. -/
noncomputable abbrev extendScalars : CommAlgCat.{w} R ⥤ CommAlgCat.{max v w} S where
  obj A := of S (S ⊗[R] A)
  map f := ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f.hom)
  map_id A := by ext; simp
  map_comp f g := by ext; simp

/-- The algebra underlying extension of scalars is the tensor product. -/
lemma extendScalars_obj (A : CommAlgCat.{w} R) :
    (extendScalars R S).obj A = of S (S ⊗[R] A) :=
  (rfl)

/-- The morphism part of base change tensors a morphism with the identity on `S`. -/
lemma extendScalars_map_hom {A A' : CommAlgCat.{w} R} (f : A ⟶ A') :
    ((extendScalars R S).map f).hom = Algebra.TensorProduct.map (AlgHom.id S S) f.hom :=
  (rfl)

/-- The Hom equivalence for extension and restriction of scalars. -/
noncomputable def extendScalarsHomEquiv (A : CommAlgCat.{max v w} R)
    (B : CommAlgCat.{max v w} S) :
    ((extendScalars R S).obj A ⟶ B) ≃
      (A ⟶ (restrictScalars (algebraMap R S)).obj B) := by
  letI : Algebra R B := Algebra.compHom B (algebraMap R S)
  letI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  exact (ConcreteCategory.homEquiv (C := CommAlgCat S)
    (X := (extendScalars R S).obj A) (Y := B)).trans
    ((Algebra.TensorProduct.liftEquivRight R S A B).symm.trans
      (ConcreteCategory.homEquiv (C := CommAlgCat R)
        (X := A) (Y := (restrictScalars (algebraMap R S)).obj B)).symm)

/-- The adjunction's forward map is evaluation on the second tensor factor. -/
@[simp]
lemma extendScalarsHomEquiv_apply (A : CommAlgCat.{max v w} R)
    (B : CommAlgCat.{max v w} S) (f : (extendScalars R S).obj A ⟶ B) (a : A) :
    (extendScalarsHomEquiv R S A B f).hom a = f.hom (1 ⊗ₜ[R] a) :=
  (rfl)

/-- The adjunction's inverse extends a map by `S`-linearity. -/
@[simp]
lemma extendScalarsHomEquiv_symm_tmul (A : CommAlgCat.{max v w} R)
    (B : CommAlgCat.{max v w} S)
    (f : A ⟶ (restrictScalars (algebraMap R S)).obj B) (s : S) (a : A) :
    ((extendScalarsHomEquiv R S A B).symm f).hom (s ⊗ₜ[R] a) = s • f.hom a := by
  simp [extendScalarsHomEquiv, ConcreteCategory.homEquiv,
    Algebra.TensorProduct.liftEquivRight, Algebra.smul_def]

/-- Tensor-product base change is left adjoint to restriction of scalars. -/
noncomputable def extendRestrictScalarsAdj :
    extendScalars.{u, v, max v w} R S ⊣ restrictScalars (algebraMap R S) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extendScalarsHomEquiv R S
      homEquiv_naturality_left_symm := by
        intro A A' B f g
        apply (extendScalarsHomEquiv R S A B).injective
        ext a
        simp [extendScalarsHomEquiv_apply R S A B,
          extendScalarsHomEquiv_symm_tmul R S A' B, Algebra.TensorProduct.map_tmul]
      homEquiv_naturality_right := by
        intro A B B' f g
        ext a
        rfl }

/-- The adjunction uses the tensor-product Hom equivalence. -/
@[simp]
lemma extendRestrictScalarsAdj_homEquiv (A : CommAlgCat.{max v w} R)
    (B : CommAlgCat.{max v w} S) :
    (extendRestrictScalarsAdj R S).homEquiv A B = extendScalarsHomEquiv R S A B := by
  simp [extendRestrictScalarsAdj]

/-- Base change is a left adjoint, so the general adjunction API makes it preserve colimits. -/
noncomputable instance extendScalars_isLeftAdjoint :
    (extendScalars.{u, v, max v w} R S).IsLeftAdjoint :=
  (extendRestrictScalarsAdj R S).isLeftAdjoint

end CommAlgCat

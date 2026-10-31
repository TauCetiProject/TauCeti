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

universe u v

namespace CommAlgCat

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Extension of scalars for commutative algebras, with scalar ring `S`. -/
noncomputable abbrev baseChange : CommAlgCat.{v} R ⥤ CommAlgCat.{v} S where
  obj A := of S (S ⊗[R] A)
  map f := ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f.hom)
  map_id A := by ext; simp
  map_comp f g := by ext; simp

/-- The algebra underlying extension of scalars is the tensor product. -/
lemma baseChange_obj (A : CommAlgCat.{v} R) :
    (baseChange R S).obj A = of S (S ⊗[R] A) :=
  (rfl)

/-- The Hom equivalence for extension and restriction of scalars. -/
noncomputable def baseChangeHomEquiv (A : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) :
    ((baseChange R S).obj A ⟶ B) ≃
      (A ⟶ (restrictScalars (algebraMap R S)).obj B) := by
  letI : Algebra R B := Algebra.compHom B (algebraMap R S)
  letI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  exact (ConcreteCategory.homEquiv (C := CommAlgCat S)
    (X := (baseChange R S).obj A) (Y := B)).trans
    ((Algebra.TensorProduct.liftEquivRight R S A B).symm.trans
      (ConcreteCategory.homEquiv (C := CommAlgCat R)
        (X := A) (Y := (restrictScalars (algebraMap R S)).obj B)).symm)

/-- The adjunction's forward map is evaluation on the second tensor factor. -/
@[simp]
lemma baseChangeHomEquiv_apply (A : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) (f : (baseChange R S).obj A ⟶ B) (a : A) :
    (baseChangeHomEquiv R S A B f).hom a = f.hom (1 ⊗ₜ[R] a) :=
  (rfl)

/-- The adjunction's inverse extends a map by `S`-linearity. -/
@[simp]
lemma baseChangeHomEquiv_symm_tmul (A : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S)
    (f : A ⟶ (restrictScalars (algebraMap R S)).obj B) (s : S) (a : A) :
    ((baseChangeHomEquiv R S A B).symm f).hom (s ⊗ₜ[R] a) = s • f.hom a := by
  simp [baseChangeHomEquiv, ConcreteCategory.homEquiv,
    Algebra.TensorProduct.liftEquivRight, Algebra.smul_def]

/-- Tensor-product base change is left adjoint to restriction of scalars. -/
noncomputable def baseChangeRestrictScalarsAdj :
    baseChange.{u, v} R S ⊣ restrictScalars (algebraMap R S) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := baseChangeHomEquiv R S
      homEquiv_naturality_left_symm := by
        intro A A' B f g
        apply (baseChangeHomEquiv R S A B).injective
        ext a
        rw [Equiv.apply_symm_apply, baseChangeHomEquiv_apply]
        simp only [hom_comp, AlgHom.comp_apply, hom_ofHom, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply]
        rw [baseChangeHomEquiv_symm_tmul]
        simp
      homEquiv_naturality_right := by
        intro A B B' f g
        ext a
        rfl }

/-- The adjunction uses the tensor-product Hom equivalence. -/
@[simp]
lemma baseChangeRestrictScalarsAdj_homEquiv (A : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) :
    (baseChangeRestrictScalarsAdj R S).homEquiv A B = baseChangeHomEquiv R S A B := by
  simp [baseChangeRestrictScalarsAdj]

/-- Base change is a left adjoint, so the general adjunction API makes it preserve colimits. -/
noncomputable instance baseChange_isLeftAdjoint :
    (baseChange.{u, v} R S).IsLeftAdjoint :=
  (baseChangeRestrictScalarsAdj R S).isLeftAdjoint

end CommAlgCat

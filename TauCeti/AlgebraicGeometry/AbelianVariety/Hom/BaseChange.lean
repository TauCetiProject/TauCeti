/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Basic

/-!
# Base change of abelian-variety homomorphisms

This file makes extension of the base field functorial on abelian varieties. For a field
extension `K → L`, pullback from schemes over `Spec K` to schemes over `Spec L` carries an
abelian-variety homomorphism `A ⟶ B` to a homomorphism `A.baseChange L ⟶ B.baseChange L`.
These maps assemble into `AbelianVariety.baseChangeFunctor`.

The construction advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E's basic
abelian-variety API and the base-change compatibility required in the end goal. It will allow
the Jacobian base-change comparison to be stated and used as an isomorphism of abelian varieties,
not merely as an isomorphism of their underlying schemes.

No external mathematics is vendored. The implementation uses Mathlib's lax monoidal pullback
functor on `Over` categories, whose action on group objects proves that the pulled-back morphism
preserves the unit and multiplication.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

/-- Base change of a homomorphism of abelian varieties along a field extension.

This is the morphism obtained by applying pullback in the appropriate `Over` category. The
monoidal structure on pullback ensures that it is again a group-scheme homomorphism. -/
noncomputable def Hom.baseChange {A B : AbelianVariety K} (f : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] : A.baseChange L ⟶ B.baseChange L := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  exact InducedCategory.homMk
    (eqToHom (baseChange_toCommGrp A L) ≫ F.mapCommGrp.map f.hom ≫
      eqToHom (baseChange_toCommGrp B L).symm)

/-- The underlying morphism over `Spec L` of a base-changed homomorphism is the pullback of its
underlying morphism over `Spec K`. -/
@[simp]
lemma Hom.toOverHom_baseChange {A B : AbelianVariety K} (f : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.toOverHom (Hom.baseChange f L) =
      (CommGrp.forget _).map
        (eqToHom (baseChange_toCommGrp A L) ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map f.hom ≫
          eqToHom (baseChange_toCommGrp B L).symm) := by
  change (CommGrp.forget _).map
      (eqToHom (baseChange_toCommGrp A L) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map f.hom ≫
        eqToHom (baseChange_toCommGrp B L).symm) = _
  simp

/-- Base change preserves identity homomorphisms. -/
@[simp]
lemma Hom.baseChange_id (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange (𝟙 A) L = 𝟙 (A.baseChange L) := by
  apply InducedCategory.hom_ext
  change eqToHom (baseChange_toCommGrp A L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map
        (𝟙 (CommGrp.mk A.toOver)) ≫
      eqToHom (baseChange_toCommGrp A L).symm = 𝟙 (CommGrp.mk (A.baseChange L).toOver)
  simp

/-- Base change preserves composition of homomorphisms. -/
@[simp]
lemma Hom.baseChange_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.baseChange (f ≫ g) L = Hom.baseChange f L ≫ Hom.baseChange g L := by
  apply InducedCategory.hom_ext
  change eqToHom (baseChange_toCommGrp A L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map
        (f.hom ≫ g.hom) ≫ eqToHom (baseChange_toCommGrp C L).symm =
    (eqToHom (baseChange_toCommGrp A L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map f.hom ≫
      eqToHom (baseChange_toCommGrp B L).symm) ≫
    (eqToHom (baseChange_toCommGrp B L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.map g.hom ≫
      eqToHom (baseChange_toCommGrp C L).symm)
  simp [Category.assoc]

/-- Extension of the base field defines a functor between the categories of abelian varieties.
-/
noncomputable def baseChangeFunctor (L : Type u) [Field L] [Algebra K L] :
    AbelianVariety K ⥤ AbelianVariety L where
  obj A := A.baseChange L
  map f := Hom.baseChange f L
  map_id A := Hom.baseChange_id A L
  map_comp f g := Hom.baseChange_comp f g L

@[simp]
lemma baseChangeFunctor_obj (L : Type u) [Field L] [Algebra K L]
    (A : AbelianVariety K) :
    (baseChangeFunctor L).obj A = A.baseChange L :=
  (rfl)

@[simp]
lemma baseChangeFunctor_map {A B : AbelianVariety K} (L : Type u) [Field L] [Algebra K L]
    (f : A ⟶ B) :
    (baseChangeFunctor L).map f =
      eqToHom (baseChangeFunctor_obj L A) ≫ Hom.baseChange f L ≫
        eqToHom (baseChangeFunctor_obj L B).symm :=
  (rfl)

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti

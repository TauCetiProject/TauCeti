/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Endomorphism `⋆`-algebras of linear dagger categories

In an `R`-linear dagger category, `CategoryTheory.End X` carries a `Star` operation induced by
`TauCeti.dagger` alongside its `R`-algebra structure from `CategoryTheory.Linear`. Every additive
`R`-linear dagger-preserving functor `F : C ⥤ D` refines `Functor.mapEndAlgHom R X` to a unital
`⋆`-algebra homomorphism `F.mapEndStarAlgHom R X : End X →⋆ₐ[R] End (F.obj X)`, which is injective
when `F` is faithful and upgrades to a `⋆`-algebra equivalence when `F` is fully faithful.
-/

public section

open CategoryTheory TauCeti

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.End

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C] {X : C}

/-- `End.of` commutes with taking the dagger and `star`. -/
@[simp] theorem of_dagger (f : X ⟶ X) : End.of (dagger f) = star (End.of f) := (rfl)

end CategoryTheory.End

namespace CategoryTheory.Functor

section Hom

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [DaggerCategory C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [DaggerCategory D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [DaggerCategory E]
  (F : C ⥤ D) (R : Type w) [CommSemiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [F.Additive] [F.Linear R] [F.PreservesDagger]

/-- An `R`-linear dagger-preserving functor induces a unital `⋆`-algebra homomorphism on
endomorphism algebras, refining `Functor.mapEndAlgHom`. -/
def mapEndStarAlgHom (X : C) : End X →⋆ₐ[R] End (F.obj X) :=
  StarAlgHom.mk (F.mapEndAlgHom R X) fun f => End.ext (by simp)

/-- Forgetting `star` from `Functor.mapEndStarAlgHom` recovers `Functor.mapEndAlgHom`. -/
@[simp] theorem toAlgHom_mapEndStarAlgHom (X : C) :
    (F.mapEndStarAlgHom R X).toAlgHom = F.mapEndAlgHom R X := (rfl)

/-- `Functor.mapEndStarAlgHom` acts on underlying endomorphisms via `F.map`. -/
@[simp] theorem mapEndStarAlgHom_asHom (X : C) (f : End X) :
    (F.mapEndStarAlgHom R X f).asHom = F.map f.asHom :=
  F.mapEndAlgHom_asHom R X f

/-- Evaluating `Functor.mapEndStarAlgHom` on `End.of f` gives `End.of (F.map f)`. -/
@[simp] theorem mapEndStarAlgHom_of (X : C) (f : X ⟶ X) :
    F.mapEndStarAlgHom R X (End.of f) = End.of (F.map f) :=
  End.ext (F.mapEndAlgHom_asHom R X (End.of f))

/-- The identity functor induces the identity `⋆`-algebra homomorphism on `End X`. -/
@[simp] theorem mapEndStarAlgHom_id (X : C) :
    (𝟭 C).mapEndStarAlgHom R X = StarAlgHom.id R (End X) := by
  ext f
  exact (mapEndStarAlgHom_asHom (𝟭 C) R X f).trans (Functor.id_map f.asHom)

/-- `Functor.mapEndStarAlgHom` respects composition of `R`-linear dagger functors. -/
theorem mapEndStarAlgHom_comp (G : D ⥤ E) [CategoryTheory.Linear R E]
    [G.Additive] [G.Linear R] [G.PreservesDagger] (X : C) :
    (F ⋙ G).mapEndStarAlgHom R X =
      (G.mapEndStarAlgHom R (F.obj X)).comp (F.mapEndStarAlgHom R X) := by
  ext
  simp

/-- A faithful `R`-linear dagger functor embeds each endomorphism `⋆`-algebra injectively. -/
theorem mapEndStarAlgHom_injective [F.Faithful] (X : C) :
    Function.Injective (F.mapEndStarAlgHom R X) :=
  F.mapEndAlgHom_injective R X

end Hom

section Equiv

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [DaggerCategory C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [DaggerCategory D]
  {F : C ⥤ D} (hF : F.FullyFaithful) (R : Type w) [CommSemiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [F.Additive] [F.Linear R] [F.PreservesDagger]

/-- A fully faithful `R`-linear dagger functor induces a `⋆`-algebra isomorphism on endomorphism
algebras. -/
def FullyFaithful.mapEndStarAlgEquiv (X : C) : End X ≃⋆ₐ[R] End (F.obj X) where
  toFun f := End.of (F.map f.asHom)
  invFun g := End.of (hF.preimage g.asHom)
  left_inv f := End.ext (hF.preimage_map f.asHom)
  right_inv g := End.ext (hF.map_preimage g.asHom)
  map_mul' f g := End.ext (F.map_comp g.asHom f.asHom)
  map_add' _ _ := End.ext F.map_add
  map_smul' r f := End.ext (F.map_smul r f.asHom)
  map_star' f := End.ext (F.map_dagger f.asHom)

/-- Forward evaluation of `FullyFaithful.mapEndStarAlgEquiv`. -/
@[simp] theorem FullyFaithful.mapEndStarAlgEquiv_apply (X : C) (f : End X) :
    hF.mapEndStarAlgEquiv R X f = F.mapEndStarAlgHom R X f :=
  End.ext (F.mapEndAlgHom_asHom R X f).symm

/-- Inverse evaluation of `FullyFaithful.mapEndStarAlgEquiv` on underlying endomorphisms. -/
@[simp] theorem FullyFaithful.mapEndStarAlgEquiv_symm_asHom (X : C) (g : End (F.obj X)) :
    ((hF.mapEndStarAlgEquiv R X).symm g).asHom = hF.preimage g.asHom := (rfl)

end Equiv

end CategoryTheory.Functor

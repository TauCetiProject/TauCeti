/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.CategoryTheory.NatIso
public import TauCeti.CategoryTheory.Dagger.Basic
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Dagger-preserving functors and natural transformations

Preserving a chosen dagger is a property of a native functor. Induced and full-subcategory
inclusions preserve the inherited dagger, and fully faithful dagger-preserving functors commute
with daggers on preimages. When the categories and functor are additive and scalar-linear,
`Functor.mapEndAlgHom` upgrades to a unital star-algebra homomorphism `Functor.mapEndStarAlgHom`,
and unitary object isomorphisms conjugate endomorphism algebras by star-algebra equivalences.

Natural transformations between dagger-preserving functors admit a pointwise dagger, and
pointwise unitary transformations give natural isomorphisms.
-/

public section

open CategoryTheory TauCeti

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
variable {E : Type u₃} [Category.{v₃} E] [DaggerCategory E]

/-- A functor preserves the chosen daggers if it commutes with taking daggers. -/
class PreservesDagger (F : C ⥤ D) : Prop where
  /-- Mapping an arrow commutes with taking its dagger. -/
  map_dagger : ∀ {X Y : C} (f : X ⟶ Y), F.map (dagger f) = dagger (F.map f)

/-- Mapping an arrow by a dagger-preserving functor commutes with its dagger. -/
@[simp, grind _=_] theorem map_dagger (F : C ⥤ D) [F.PreservesDagger] {X Y : C} (f : X ⟶ Y) :
    F.map (dagger f) = dagger (F.map f) := PreservesDagger.map_dagger f

/-- Identity functors preserve daggers. -/
instance : (𝟭 C).PreservesDagger where
  map_dagger _ := (rfl)

/-- Composites of dagger-preserving functors preserve daggers. -/
instance (F : C ⥤ D) (G : D ⥤ E) [F.PreservesDagger] [G.PreservesDagger] :
    (F ⋙ G).PreservesDagger where
  map_dagger f := by simp

/-- The canonical functor from an induced category preserves the inherited dagger. -/
instance instPreservesDaggerInducedFunctor {S : Type*} (F : S → C) :
    (inducedFunctor F).PreservesDagger where
  map_dagger _ := (rfl)

/-- Full subcategory inclusions preserve the inherited dagger. -/
instance instPreservesDaggerFullSubcategoryInclusion (P : ObjectProperty C) :
    P.ι.PreservesDagger where
  map_dagger _ := (rfl)

/-- Preimages along a fully faithful dagger-preserving functor commute with daggers. -/
@[simp] theorem preimage_dagger (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesDagger]
    {X Y : C} (g : F.obj X ⟶ F.obj Y) :
    F.preimage (dagger g) = dagger (F.preimage g) :=
  F.map_injective (by simp)

/-- Dagger-preserving functors take unitary arrows to unitary arrows. -/
theorem map_isUnitary (F : C ⥤ D) [F.PreservesDagger] {X Y : C} {f : X ⟶ Y}
    (hf : IsUnitary f) : IsUnitary (F.map f) := by
  rw [isUnitary_iff] at hf ⊢
  constructor
  · simpa only [Functor.map_comp, map_dagger, Functor.map_id] using
      congrArg F.map hf.1
  · simpa only [Functor.map_comp, map_dagger, Functor.map_id] using
      congrArg F.map hf.2

/-- Faithful dagger-preserving functors detect unitary arrows. -/
@[simp] theorem isUnitary_map_iff (F : C ⥤ D) [F.PreservesDagger] [F.Faithful]
    {X Y : C} (f : X ⟶ Y) : IsUnitary (F.map f) ↔ IsUnitary f := by
  simp only [isUnitary_iff, ← map_dagger, ← Functor.map_comp, ← Functor.map_id,
    F.map_injective.eq_iff]

section EndStarAlgHom

variable (F : C ⥤ D) (R : Type w) [CommSemiring R]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [F.Additive] [F.Linear R] [F.PreservesDagger]

/-- An additive scalar-linear dagger-preserving functor induces a unital star-algebra
homomorphism on endomorphism algebras, refining `CategoryTheory.Functor.mapEndAlgHom`. -/
def mapEndStarAlgHom (X : C) : End X →⋆ₐ[R] End (F.obj X) where
  __ := F.mapEndAlgHom R X
  map_star' f := by ext; simp

/-- Forgetting the star structure recovers `CategoryTheory.Functor.mapEndAlgHom`. -/
@[simp] theorem mapEndStarAlgHom_toAlgHom (X : C) :
    (F.mapEndStarAlgHom R X).toAlgHom = F.mapEndAlgHom R X := (rfl)

/-- The induced star-algebra homomorphism acts by the functor on underlying arrows. -/
@[simp, grind =] theorem mapEndStarAlgHom_apply_asHom (X : C) (f : End X) :
    (F.mapEndStarAlgHom R X f).asHom = F.map f.asHom :=
  F.mapEndAlgHom_asHom R X f

/-- A faithful linear dagger functor embeds each endomorphism star-algebra. -/
theorem mapEndStarAlgHom_injective [F.Faithful] (X : C) :
    Function.Injective (F.mapEndStarAlgHom R X) :=
  F.mapEndAlgHom_injective R X

/-- A full linear dagger functor surjects onto the image object's endomorphism star-algebra. -/
theorem mapEndStarAlgHom_surjective [F.Full] (X : C) :
    Function.Surjective (F.mapEndStarAlgHom R X) := fun g =>
  ⟨End.of (F.preimage g.asHom), by ext; simp⟩

end EndStarAlgHom

section EndStarAlgEquiv

variable (F : C ⥤ D) (R : Type w) [Semiring R]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [F.Additive] [F.Linear R] [F.PreservesDagger] [F.Full] [F.Faithful]

/-- A fully faithful linear dagger functor induces a star-algebra equivalence on endomorphism
algebras over any `Semiring R`. -/
noncomputable def mapEndStarAlgEquiv (X : C) :
    End X ≃⋆ₐ[R] End (F.obj X) where
  toFun f := End.of (F.map f.asHom)
  invFun g := End.of (F.preimage g.asHom)
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_mul' f g := by ext; simp
  map_add' f g := by ext; simp
  map_smul' r f := by ext; simp
  map_star' f := by ext; simp

/-- Forward evaluation of `CategoryTheory.Functor.mapEndStarAlgEquiv` on underlying arrows. -/
@[simp, grind =] theorem mapEndStarAlgEquiv_apply_asHom (X : C) (f : End X) :
    (F.mapEndStarAlgEquiv R X f).asHom = F.map f.asHom := (rfl)

/-- Inverse evaluation of `CategoryTheory.Functor.mapEndStarAlgEquiv` on underlying arrows. -/
@[simp, grind =] theorem mapEndStarAlgEquiv_symm_apply_asHom (X : C) (g : End (F.obj X)) :
    ((F.mapEndStarAlgEquiv R X).symm g).asHom = F.preimage g.asHom := (rfl)

end EndStarAlgEquiv

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
variable {F G H : C ⥤ D} [F.PreservesDagger] [G.PreservesDagger]

/-- The pointwise dagger of a natural transformation between dagger-preserving functors.
For `α : F ⟶ G`, this gives `G ⟶ F` with components `dagger (α.app X)`. -/
def dagger (α : F ⟶ G) : G ⟶ F where
  app X := TauCeti.dagger (α.app X)
  naturality X Y f := by
    simpa using (congrArg TauCeti.dagger (α.naturality (TauCeti.dagger f))).symm

/-- The dagger of a natural transformation acts componentwise. -/
@[simp, grind =] theorem dagger_app (α : F ⟶ G) (X : C) :
    α.dagger.app X = TauCeti.dagger (α.app X) := (rfl)

/-- Taking the pointwise dagger twice recovers the natural transformation. -/
@[simp, grind =] theorem dagger_dagger (α : F ⟶ G) : α.dagger.dagger = α := by
  ext X
  simp

/-- The pointwise dagger fixes identity natural transformations. -/
@[simp, grind =] theorem dagger_id (F : C ⥤ D) [F.PreservesDagger] :
    (𝟙 F : F ⟶ F).dagger = 𝟙 F := by
  ext X
  simp

/-- Taking the pointwise dagger reverses an equality natural transformation. -/
@[simp, grind =] theorem dagger_eqToHom (h : F = G) :
    (eqToHom h : F ⟶ G).dagger = eqToHom h.symm := by
  cases h
  simp

/-- Taking pointwise daggers reverses vertical composition. -/
@[simp, grind =] theorem dagger_comp [H.PreservesDagger] (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).dagger = β.dagger ≫ α.dagger := by
  ext X
  simp

/-- A natural transformation with unitary components is a natural isomorphism. -/
def unitaryIso (α : F ⟶ G) (hα : ∀ X, IsUnitary (α.app X)) : F ≅ G :=
  NatIso.ofComponents (fun X => (hα X).toIso) (by simp)

omit [DaggerCategory C] [F.PreservesDagger] [G.PreservesDagger] in
/-- The forward natural transformation of the pointwise unitary isomorphism. -/
@[simp, grind =] theorem unitaryIso_hom (α : F ⟶ G) (hα : ∀ X, IsUnitary (α.app X)) :
    (α.unitaryIso hα).hom = α := by
  ext X
  simp [unitaryIso]

/-- The inverse of the pointwise unitary isomorphism is the pointwise dagger. -/
@[simp, grind =] theorem unitaryIso_inv (α : F ⟶ G) (hα : ∀ X, IsUnitary (α.app X)) :
    (α.unitaryIso hα).inv = α.dagger := by
  ext X
  simp [unitaryIso]

omit [DaggerCategory C] [F.PreservesDagger] [G.PreservesDagger] in
/-- The inverse of the pointwise unitary isomorphism acts by the component's dagger. -/
@[simp, grind =] theorem unitaryIso_inv_app (α : F ⟶ G)
    (hα : ∀ X, IsUnitary (α.app X)) (X : C) :
    (α.unitaryIso hα).inv.app X = TauCeti.dagger (α.app X) := by
  simp [unitaryIso]

end CategoryTheory.NatTrans

namespace CategoryTheory.Iso

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
variable {F G : C ⥤ D} [F.PreservesDagger] [G.PreservesDagger]

/-- A natural isomorphism has pointwise dagger as inverse exactly when its components are
unitary. This characterizes unitary natural isomorphisms using native natural isomorphisms. -/
theorem inv_eq_dagger_iff (e : F ≅ G) :
    e.inv = e.hom.dagger ↔ ∀ X, IsUnitary (e.hom.app X) := by
  constructor
  · intro h X
    apply (e.app X).isUnitary_hom_iff.mpr
    exact (congrArg (fun α : G ⟶ F => α.app X) h).symm
  · intro h
    ext X
    exact ((e.app X).isUnitary_hom_iff.mp (h X)).symm

section EndStarAlgEquiv

variable (R : Type w) [Semiring R] [Preadditive C] [CategoryTheory.Linear R C]

/-- A unitary isomorphism between objects conjugates their endomorphism star-algebras by a
star-algebra equivalence. -/
def endStarAlgEquiv {X Y : C} (e : X ≅ Y) (he : IsUnitary e.hom) :
    End X ≃⋆ₐ[R] End Y where
  toFun f := End.of (dagger e.hom ≫ f.asHom ≫ e.hom)
  invFun g := End.of (e.hom ≫ g.asHom ≫ dagger e.hom)
  left_inv f := by ext; simp [he.hom_dagger_id_assoc, he.hom_dagger_id]
  right_inv g := by ext; simp [he.dagger_hom_id_assoc, he.dagger_hom_id]
  map_mul' f g := by ext; simp [he.hom_dagger_id_assoc]
  map_add' f g := by ext; simp
  map_smul' r f := by ext; simp
  map_star' f := by ext; simp

/-- Conjugation by a unitary isomorphism acts as `dagger e.hom ≫ f.asHom ≫ e.hom`. -/
@[simp, grind =] theorem endStarAlgEquiv_apply_asHom {X Y : C} (e : X ≅ Y)
    (he : IsUnitary e.hom) (f : End X) :
    (e.endStarAlgEquiv R he f).asHom = dagger e.hom ≫ f.asHom ≫ e.hom := (rfl)

/-- Inverse conjugation by a unitary isomorphism acts as `e.hom ≫ g.asHom ≫ dagger e.hom`. -/
@[simp, grind =] theorem endStarAlgEquiv_symm_apply_asHom {X Y : C} (e : X ≅ Y)
    (he : IsUnitary e.hom) (g : End Y) :
    ((e.endStarAlgEquiv R he).symm g).asHom = e.hom ≫ g.asHom ≫ dagger e.hom := (rfl)

end EndStarAlgEquiv

end CategoryTheory.Iso

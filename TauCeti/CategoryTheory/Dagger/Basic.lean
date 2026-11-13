/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Dagger categories

A *dagger structure* on a category `C` assigns to every morphism `f : X ⟶ Y` a morphism
`dagger f : Y ⟶ X` in the opposite direction, such that `dagger (f ≫ g) = dagger g ≫ dagger f`
and `dagger (dagger f) = f`. It is chosen data on Mathlib's native `Category`, not a property:
the same category can carry several daggers. The identity law `dagger (𝟙 X) = 𝟙 X` follows from
the other two axioms (`TauCeti.DaggerCategory.dagger_id`).

The standard example is the category of Hilbert spaces and bounded operators, with the operator
adjoint as dagger; its skeleton on finite-dimensional spaces is the matrix category with the
conjugate transpose (`TauCeti/CategoryTheory/Dagger/Mat.lean`). The dagger is distinct from any
duality of a rigid category: it reverses arrows but fixes every object.

In a dagger category the dagger turns each endomorphism monoid `End X` into a star monoid, so
that the theory of `star` (self-adjoint elements, Mathlib's `unitary` submonoid) applies to
endomorphisms. A morphism is *unitary* if its dagger is a two-sided inverse; for an endomorphism
this is membership in `unitary (End X)`. A *dagger functor* is a functor commuting with the
daggers; it preserves unitary morphisms.

Additivity and conjugate-linearity of the dagger on a preadditive or linear category are the
separate mixins of `TauCeti/CategoryTheory/Dagger/Linear.lean`.

## Main declarations

* `TauCeti.DaggerCategory`: a dagger structure on a category, with the laws
  `TauCeti.DaggerCategory.dagger_comp`, `TauCeti.DaggerCategory.dagger_dagger` and
  `TauCeti.DaggerCategory.dagger_id`;
* `TauCeti.DaggerCategory.dagger_inv`: the dagger of an isomorphism is an isomorphism, with
  `dagger (inv f) = inv (dagger f)`;
* `TauCeti.IsUnitary`: unitary morphisms, closed under identities, composition and the dagger;
  `TauCeti.IsUnitary.inv_eq` identifies the inverse of a unitary with its dagger, and
  `TauCeti.isUnitary_iff_dagger_eq_inv` characterises unitary isomorphisms;
* `CategoryTheory.End.instStarMul`: the star monoid structure on `End X`, with
  `CategoryTheory.End.star_asHom`; `CategoryTheory.End.mem_unitary_iff` and
  `CategoryTheory.End.isSelfAdjoint_iff` identify its unitary and self-adjoint elements;
* `CategoryTheory.Functor.IsDagger`: dagger functors, closed under identities and composition,
  and `TauCeti.IsUnitary.map`: they preserve unitary morphisms.

## References

* P. Selinger, *Dagger compact closed categories and completely positive maps*, Electron. Notes
  Theor. Comput. Sci. 170 (2007), 139–163
* C. Heunen, J. Vicary, *Categories for Quantum Theory*, Oxford University Press (2019), Chapter 2
-/

public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

/-- A *dagger structure* on a category `C`: an operation sending each morphism `f : X ⟶ Y` to a
morphism `dagger f : Y ⟶ X`, which reverses composition and is involutive. It preserves
identities by `TauCeti.DaggerCategory.dagger_id`. -/
@[ext]
class DaggerCategory (C : Type u₁) [Category.{v₁} C] where
  /-- The dagger `Y ⟶ X` of a morphism `X ⟶ Y`. -/
  dagger {X Y : C} : (X ⟶ Y) → (Y ⟶ X)
  /-- The dagger reverses composition. -/
  dagger_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : dagger (f ≫ g) = dagger g ≫ dagger f
  /-- The dagger is involutive. -/
  dagger_dagger {X Y : C} (f : X ⟶ Y) : dagger (dagger f) = f

namespace DaggerCategory

attribute [simp] dagger_comp dagger_dagger

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]

/-- The dagger preserves identities. -/
@[simp]
theorem dagger_id (X : C) : dagger (𝟙 X) = 𝟙 X :=
  calc dagger (𝟙 X) = dagger (𝟙 X) ≫ dagger (dagger (𝟙 X)) := by simp
    _ = 𝟙 X := by rw [← dagger_comp, Category.comp_id, dagger_dagger]

theorem dagger_injective {X Y : C} :
    Function.Injective (dagger : (X ⟶ Y) → (Y ⟶ X)) :=
  fun f g h => by rw [← dagger_dagger f, h, dagger_dagger]

@[simp]
theorem dagger_inj {X Y : C} {f g : X ⟶ Y} : dagger f = dagger g ↔ f = g :=
  dagger_injective.eq_iff

theorem dagger_eq_iff_eq_dagger {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} :
    dagger f = g ↔ f = dagger g := by
  rw [← dagger_inj, dagger_dagger]

instance isIso_dagger {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso (dagger f) :=
  ⟨⟨dagger (inv f), by simp [← dagger_comp], by simp [← dagger_comp]⟩⟩

/-- The dagger of the inverse of an isomorphism is the inverse of its dagger. -/
@[simp]
theorem dagger_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : dagger (inv f) = inv (dagger f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← dagger_comp]

end DaggerCategory

open DaggerCategory

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]

/-- A morphism `f` of a dagger category is *unitary* if its dagger is a two-sided inverse:
`f ≫ dagger f = 𝟙 X` and `dagger f ≫ f = 𝟙 Y`. -/
@[mk_iff]
structure IsUnitary {X Y : C} (f : X ⟶ Y) : Prop where
  /-- First `f`, then its dagger, is the identity. -/
  hom_dagger_id : f ≫ dagger f = 𝟙 X
  /-- First the dagger of `f`, then `f`, is the identity. -/
  dagger_hom_id : dagger f ≫ f = 𝟙 Y

namespace IsUnitary

attribute [reassoc (attr := simp)] hom_dagger_id dagger_hom_id

variable {X Y Z : C} {f : X ⟶ Y}

/-- A unitary morphism is an isomorphism. -/
theorem isIso (hf : IsUnitary f) : IsIso f :=
  ⟨⟨dagger f, hf.hom_dagger_id, hf.dagger_hom_id⟩⟩

/-- The inverse of a unitary morphism is its dagger. -/
theorem inv_eq (hf : IsUnitary f) [IsIso f] : inv f = dagger f :=
  IsIso.inv_eq_of_hom_inv_id hf.hom_dagger_id

/-- The dagger of a unitary morphism is unitary. -/
theorem dagger (hf : IsUnitary f) : IsUnitary (dagger f) :=
  ⟨by simpa using hf.dagger_hom_id, by simpa using hf.hom_dagger_id⟩

/-- The composite of two unitary morphisms is unitary. -/
theorem comp (hf : IsUnitary f) {g : Y ⟶ Z} (hg : IsUnitary g) : IsUnitary (f ≫ g) :=
  ⟨by simp [hg.hom_dagger_id_assoc, hf.hom_dagger_id],
    by simp [hf.dagger_hom_id_assoc, hg.dagger_hom_id]⟩

end IsUnitary

/-- Identities are unitary. -/
@[simp]
theorem isUnitary_id (X : C) : IsUnitary (𝟙 X) :=
  ⟨by simp, by simp⟩

@[simp]
theorem isUnitary_dagger_iff {X Y : C} {f : X ⟶ Y} : IsUnitary (dagger f) ↔ IsUnitary f :=
  ⟨fun hf => by simpa using hf.dagger, IsUnitary.dagger⟩

/-- An isomorphism is unitary exactly when its dagger is its inverse. -/
theorem isUnitary_iff_dagger_eq_inv {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsUnitary f ↔ dagger f = inv f :=
  ⟨fun hf => hf.inv_eq.symm, fun h => ⟨by simp [h], by simp [h]⟩⟩

end TauCeti

namespace CategoryTheory

open TauCeti TauCeti.DaggerCategory

namespace End

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]

/-- In a dagger category the dagger makes `End X` a star monoid. Multiplication in `End X` is
composition in operator order, which the dagger reverses. -/
instance instStarMul (X : C) : StarMul (End X) where
  star f := .of (dagger f.asHom)
  star_involutive f := End.ext (dagger_dagger f.asHom)
  star_mul f g := End.ext (dagger_comp g.asHom f.asHom)

@[simp]
theorem star_asHom {X : C} (f : End X) : (star f).asHom = dagger f.asHom :=
  (rfl)

/-- An endomorphism is unitary in the sense of the star monoid `End X` exactly when it is a
unitary morphism. -/
theorem mem_unitary_iff {X : C} (f : End X) : f ∈ unitary (End X) ↔ IsUnitary f.asHom := by
  simp [Unitary.mem_iff, End.ext_iff, isUnitary_iff]

/-- An endomorphism is self-adjoint in the star monoid `End X` exactly when it equals its
dagger. -/
theorem isSelfAdjoint_iff {X : C} (f : End X) : IsSelfAdjoint f ↔ dagger f.asHom = f.asHom := by
  rw [IsSelfAdjoint, End.ext_iff, star_asHom]

end End

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
  {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
  {E : Type u₃} [Category.{v₃} E] [DaggerCategory E]

/-- A functor between dagger categories is a *dagger functor* if it commutes with the
daggers. -/
class IsDagger (F : C ⥤ D) : Prop where
  /-- The functor commutes with the daggers. -/
  map_dagger {X Y : C} (f : X ⟶ Y) : F.map (dagger f) = dagger (F.map f)

@[simp]
theorem map_dagger (F : C ⥤ D) [F.IsDagger] {X Y : C} (f : X ⟶ Y) :
    F.map (dagger f) = dagger (F.map f) :=
  IsDagger.map_dagger f

instance isDagger_id : (𝟭 C).IsDagger :=
  ⟨fun _ => by simp⟩

instance isDagger_comp (F : C ⥤ D) (G : D ⥤ E) [F.IsDagger] [G.IsDagger] :
    (F ⋙ G).IsDagger :=
  ⟨fun f => by simp⟩

end Functor

end CategoryTheory

namespace TauCeti.IsUnitary

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
  {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]

/-- A dagger functor maps unitary morphisms to unitary morphisms. -/
theorem map {X Y : C} {f : X ⟶ Y} (hf : IsUnitary f) (F : C ⥤ D) [F.IsDagger] :
    IsUnitary (F.map f) :=
  ⟨by rw [← F.map_dagger, ← F.map_comp, hf.hom_dagger_id, F.map_id],
    by rw [← F.map_dagger, ← F.map_comp, hf.dagger_hom_id, F.map_id]⟩

end TauCeti.IsUnitary

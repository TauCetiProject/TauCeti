/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Skeletal

/-!
# Functors into and between cores of categories

A functor `F : D ⥤ C` sending every morphism of `D` to an isomorphism of `C` factors through the
core `Core C`, the groupoid of objects of `C` and isomorphisms between them. Mathlib's
`CategoryTheory.Core.functorToCore` is the case where `D` is a groupoid.

The inclusion `Core C ⥤ C` is essentially surjective, and it is an equivalence when `C` is a
groupoid. Since two objects are isomorphic in `Core C` exactly when they are isomorphic in `C`,
the inclusion identifies the isomorphism classes `Skeleton (Core C)` with `Skeleton C`
(`CategoryTheory.Core.skeletonEquiv`), and the automorphism group of an object of `Core C` with
that of the underlying object of `C` (`CategoryTheory.Core.autMulEquiv`).

The core functor `F.core : Core C ⥤ Core D` preserves faithfulness, and preserves fullness when `F`
is fully faithful: a full functor that is not faithful need not lift isomorphisms to isomorphisms,
whereas a fully faithful functor reflects isomorphisms via `FullyFaithful.preimageIso`.
-/

public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

namespace Core

/-- A functor sending every morphism to an isomorphism, as a functor to the core. -/
@[expose, simps obj map_iso]
noncomputable def functorToCoreOfIsIso (F : D ⥤ C)
    (hF : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), IsIso (F.map f)) : D ⥤ Core C where
  obj X := .mk (F.obj X)
  map f := have := hF f; .mk (asIso (F.map f))
  map_id X := Core.hom_ext (by simp)
  map_comp f g := Core.hom_ext (by simp)

@[simp]
lemma functorToCoreOfIsIso_comp_inclusion (F : D ⥤ C)
    (hF : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), IsIso (F.map f)) :
    functorToCoreOfIsIso F hF ⋙ inclusion C = F :=
  rfl

/-- The functor `functorToCoreOfIsIso (G ⋙ F)` factors through `functorToCoreOfIsIso F`. -/
lemma functorToCoreOfIsIso_comp_left (G : E ⥤ D) (F : D ⥤ C)
    (hF : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), IsIso (F.map f)) :
    functorToCoreOfIsIso (G ⋙ F) (fun _ _ f ↦ hF (G.map f)) = G ⋙ functorToCoreOfIsIso F hF :=
  rfl

/-- A functor to the core is recovered from its composite with the inclusion of the core. -/
@[simp]
lemma functorToCoreOfIsIso_comp_inclusion_self (G : D ⥤ Core C) :
    functorToCoreOfIsIso (G ⋙ inclusion C) (fun _ _ f ↦ (G.map f).iso.isIso_hom) = G :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (Core.hom_ext rfl)

/-- The inclusion of the core is essentially surjective. -/
instance : (inclusion C).EssSurj where
  mem_essImage X := ⟨⟨X⟩, ⟨Iso.refl _⟩⟩

section Groupoid

variable [IsGroupoid C]

/-- For a groupoid `C`, the inclusion `Core C ⥤ C` is full. -/
instance : (inclusion C).Full where
  map_surjective f := ⟨⟨asIso f⟩, rfl⟩

/-- For a groupoid `C`, the inclusion `Core C ⥤ C` is an equivalence of categories. -/
instance : (inclusion C).IsEquivalence where

end Groupoid

/-- Two objects of `Core C` are isomorphic exactly when they are isomorphic in `C`, so the
inclusion identifies the isomorphism classes of `Core C` with those of `C`. -/
noncomputable def skeletonEquiv : Skeleton (Core C) ≃ Skeleton C :=
  .ofBijective (inclusion C).mapSkeleton.obj <| by
    refine ⟨fun X Y h ↦ ?_, (inclusion C).mapSkeleton_surjective⟩
    rw [← toSkeleton_fromSkeleton_obj X, ← toSkeleton_fromSkeleton_obj Y] at h ⊢
    simp only [Functor.mapSkeleton_obj_toSkeleton] at h
    obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 h
    exact congr_toSkeleton_of_iso (isoMk e)

@[simp]
lemma skeletonEquiv_toSkeleton (X : Core C) : skeletonEquiv (toSkeleton X) = toSkeleton X.of :=
  (inclusion C).mapSkeleton_obj_toSkeleton X

@[simp]
lemma skeletonEquiv_symm_toSkeleton (X : C) :
    skeletonEquiv.symm (toSkeleton X) = toSkeleton (⟨X⟩ : Core C) :=
  skeletonEquiv.symm_apply_eq.2 (skeletonEquiv_toSkeleton _).symm

/-- The automorphisms of an object of `Core C` are the automorphisms of the underlying object
of `C`. -/
def autMulEquiv (X : Core C) : Aut X ≃* Aut X.of where
  toFun e := .of e.asIso.hom.iso
  invFun e := .of (isoMk e.asIso)
  left_inv _ := Aut.ext (Iso.ext (hom_ext rfl))
  right_inv _ := Aut.ext (Iso.ext rfl)
  map_mul' _ _ := Aut.ext (Iso.ext rfl)

@[simp]
lemma autMulEquiv_apply_asIso (X : Core C) (e : Aut X) :
    (autMulEquiv X e).asIso = e.asIso.hom.iso :=
  (rfl)

@[simp]
lemma autMulEquiv_symm_apply_asIso (X : Core C) (e : Aut X.of) :
    ((autMulEquiv X).symm e).asIso = isoMk e.asIso :=
  (rfl)

end Core

namespace Functor

/-- A faithful functor induces a faithful functor on cores. -/
instance core_faithful (F : C ⥤ D) [F.Faithful] : F.core.Faithful where
  map_injective {X Y} {_ _} h :=
    Core.hom_ext (F.map_injective (congrArg (fun e : F.core.obj X ⟶ F.core.obj Y ↦ e.iso.hom) h))

/-- A fully faithful functor induces a fully faithful functor on cores, lifting isomorphisms by
`FullyFaithful.preimageIso`. -/
def FullyFaithful.core {F : C ⥤ D} (hF : F.FullyFaithful) : F.core.FullyFaithful where
  preimage g := ⟨hF.preimageIso g.iso⟩
  map_preimage g := Core.hom_ext (hF.map_preimage g.iso.hom)
  preimage_map f := Core.hom_ext (hF.preimage_map f.iso.hom)

/-- The preimage of an isomorphism in `Core D` along `hF.core` is `hF.preimageIso` of its
underlying isomorphism. -/
@[simp]
theorem FullyFaithful.core_preimage_iso {F : C ⥤ D} (hF : F.FullyFaithful) {X Y : Core C}
    (g : F.core.obj X ⟶ F.core.obj Y) :
    (hF.core.preimage g).iso = hF.preimageIso g.iso :=
  (rfl)

/-- A full and faithful functor induces a full functor on cores. -/
instance core_full (F : C ⥤ D) [F.Full] [F.Faithful] : F.core.Full :=
  (FullyFaithful.ofFullyFaithful F).core.full

end Functor

end CategoryTheory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import TauCeti.CategoryTheory.Sums.Basic

/-!
# Functors on isomorphism classes

Mathlib's `CategoryTheory.isomorphismClasses` already supplies the action of functors on
isomorphism classes. Here we record its representative formula, invariance under natural
isomorphism, injectivity for full functors reflecting isomorphisms, such as fully faithful
functors or full functors out of groupoids, and surjectivity for essentially surjective
functors. These facts allow comparisons of presentations to descend to their spaces of objects up
to isomorphism.

For categories in arbitrary universes we also identify the isomorphism classes of a product
`C × D` with pairs of classes (`CategoryTheory.Prod.isomorphismClassesEquiv`), those of a
disjoint union `C ⊕ D` with the disjoint union of the classes
(`CategoryTheory.Sum.isomorphismClassesEquiv`), and those of equivalent categories
(`CategoryTheory.Equivalence.isomorphismClassesEquiv`).
-/

public section

universe v u

namespace CategoryTheory.Functor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

-- The representative formula records the defining computation of Mathlib's bundled `Quot.map`.
/-- The map on isomorphism classes sends an object's class to the class of its image. -/
@[simp]
theorem isomorphismClasses_map_mk (F : C ⥤ D) (x : C) :
    @Eq (Quotient (isIsomorphicSetoid D))
      (isomorphismClasses.map F.toCatHom (Quotient.mk (isIsomorphicSetoid C) x))
      (Quotient.mk (isIsomorphicSetoid D) (F.obj x)) := (rfl)

/-- The map on isomorphism classes commutes with the quotient projections. -/
@[simp]
theorem isomorphismClasses_map_comp_mk (F : C ⥤ D) :
    (isomorphismClasses.map F.toCatHom :
      Quotient (isIsomorphicSetoid C) → Quotient (isIsomorphicSetoid D)) ∘
        Quotient.mk (isIsomorphicSetoid C) =
      Quotient.mk (isIsomorphicSetoid D) ∘ F.obj := by
  funext x
  exact F.isomorphismClasses_map_mk x

/-- Naturally isomorphic functors induce the same map on isomorphism classes. -/
theorem isomorphismClasses_map_eq_of_iso (F : C ⥤ D) {G : C ⥤ D} (e : F ≅ G) :
    isomorphismClasses.map F.toCatHom = isomorphismClasses.map G.toCatHom := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => exact Quotient.sound ⟨e.app x⟩

/-- A full functor reflecting isomorphisms, for instance a fully faithful functor, induces an
injection on isomorphism classes. -/
theorem isomorphismClasses_map_injective (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms] :
    Function.Injective (isomorphismClasses.map F.toCatHom) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      intro h
      obtain ⟨e⟩ := Quotient.exact h
      -- The preimage of `e.hom` is an isomorphism because `F` reflects isomorphisms.
      have : IsIso (F.map (F.preimage e.hom)) := by rw [F.map_preimage]; infer_instance
      have := isIso_of_reflects_iso (F.preimage e.hom) F
      exact Quotient.sound ⟨asIso (F.preimage e.hom)⟩

/-- An essentially surjective functor induces a surjection on isomorphism classes. -/
theorem isomorphismClasses_map_surjective (F : C ⥤ D) [F.EssSurj] :
    Function.Surjective (isomorphismClasses.map F.toCatHom) := by
  intro q
  induction q using Quotient.inductionOn with
  | h y =>
    exact ⟨Quotient.mk _ (F.objPreimage y),
      (F.isomorphismClasses_map_mk _).trans (Quotient.sound ⟨F.objObjPreimageIso y⟩)⟩

end CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Prod

variable (C D) in
/-- The isomorphism classes of a product category are the pairs of isomorphism classes of the
factors. The inverse sends a pair of classes to the class of the pair of chosen
representatives. -/
noncomputable def isomorphismClassesEquiv :
    Quotient (isIsomorphicSetoid (C × D)) ≃
      Quotient (isIsomorphicSetoid C) × Quotient (isIsomorphicSetoid D) where
  toFun := Quotient.lift (fun z => (⟦z.1⟧, ⟦z.2⟧)) fun _ _ ⟨e⟩ =>
    _root_.Prod.ext (Quotient.sound ⟨(CategoryTheory.Prod.fst C D).mapIso e⟩)
      (Quotient.sound ⟨(CategoryTheory.Prod.snd C D).mapIso e⟩)
  invFun p := ⟦(p.1.out, p.2.out)⟧
  left_inv := Quotient.ind fun z => Quotient.sound
    ⟨Iso.prod (Quotient.mk_out (s := isIsomorphicSetoid C) z.1).some
      (Quotient.mk_out (s := isIsomorphicSetoid D) z.2).some⟩
  right_inv p := _root_.Prod.ext p.1.out_eq p.2.out_eq

@[simp]
theorem isomorphismClassesEquiv_mk (z : C × D) :
    isomorphismClassesEquiv C D ⟦z⟧ = (⟦z.1⟧, ⟦z.2⟧) := (rfl)

@[simp]
theorem isomorphismClassesEquiv_symm_apply
    (p : Quotient (isIsomorphicSetoid C) × Quotient (isIsomorphicSetoid D)) :
    (isomorphismClassesEquiv C D).symm p = ⟦(p.1.out, p.2.out)⟧ := (rfl)

end CategoryTheory.Prod

namespace CategoryTheory.Sum

variable (C D) in
/-- The isomorphism classes of a disjoint union of categories are the disjoint union of the
isomorphism classes of the summands. The inverse sends a class to the class of the image of its
chosen representative. -/
noncomputable def isomorphismClassesEquiv :
    Quotient (isIsomorphicSetoid (C ⊕ D)) ≃
      Quotient (isIsomorphicSetoid C) ⊕ Quotient (isIsomorphicSetoid D) where
  toFun := Quotient.lift (_root_.Sum.map (⟦·⟧) (⟦·⟧)) <| by
    rintro (a | b) (a' | b') ⟨e⟩
    · exact congrArg _root_.Sum.inl (Quotient.sound ⟨(fullyFaithfulInl C D).preimageIso e⟩)
    · exact (hom_inl_inr_false C D e.hom).elim
    · exact (hom_inr_inl_false D C e.hom).elim
    · exact congrArg _root_.Sum.inr (Quotient.sound ⟨(fullyFaithfulInr C D).preimageIso e⟩)
  invFun p := ⟦p.elim (fun a => _root_.Sum.inl a.out) (fun b => _root_.Sum.inr b.out)⟧
  left_inv := Quotient.ind <| by
    rintro (a | b)
    · exact Quotient.sound
        ⟨(inl_ C D).mapIso (Quotient.mk_out (s := isIsomorphicSetoid C) a).some⟩
    · exact Quotient.sound
        ⟨(inr_ C D).mapIso (Quotient.mk_out (s := isIsomorphicSetoid D) b).some⟩
  right_inv := by
    rintro (a | b)
    · exact congrArg _root_.Sum.inl a.out_eq
    · exact congrArg _root_.Sum.inr b.out_eq

@[simp]
theorem isomorphismClassesEquiv_mk_inl (x : C) :
    isomorphismClassesEquiv C D ⟦_root_.Sum.inl x⟧ = _root_.Sum.inl ⟦x⟧ := (rfl)

@[simp]
theorem isomorphismClassesEquiv_mk_inr (y : D) :
    isomorphismClassesEquiv C D ⟦_root_.Sum.inr y⟧ = _root_.Sum.inr ⟦y⟧ := (rfl)

@[simp]
theorem isomorphismClassesEquiv_symm_inl (a : Quotient (isIsomorphicSetoid C)) :
    (isomorphismClassesEquiv C D).symm (_root_.Sum.inl a) = ⟦_root_.Sum.inl a.out⟧ := (rfl)

@[simp]
theorem isomorphismClassesEquiv_symm_inr (b : Quotient (isIsomorphicSetoid D)) :
    (isomorphismClassesEquiv C D).symm (_root_.Sum.inr b) = ⟦_root_.Sum.inr b.out⟧ := (rfl)

end CategoryTheory.Sum

namespace CategoryTheory.Equivalence

/-- An equivalence of categories induces an equivalence of their isomorphism classes, sending the
class of `x` to the class of `e.functor.obj x`. -/
def isomorphismClassesEquiv (e : C ≌ D) :
    Quotient (isIsomorphicSetoid C) ≃ Quotient (isIsomorphicSetoid D) where
  toFun := Quotient.map' e.functor.obj fun _ _ ⟨i⟩ => ⟨e.functor.mapIso i⟩
  invFun := Quotient.map' e.inverse.obj fun _ _ ⟨i⟩ => ⟨e.inverse.mapIso i⟩
  left_inv := Quotient.ind fun x => Quotient.sound ⟨(e.unitIso.app x).symm⟩
  right_inv := Quotient.ind fun y => Quotient.sound ⟨e.counitIso.app y⟩

@[simp]
theorem isomorphismClassesEquiv_mk (e : C ≌ D) (x : C) :
    e.isomorphismClassesEquiv ⟦x⟧ = ⟦e.functor.obj x⟧ := (rfl)

@[simp]
theorem isomorphismClassesEquiv_symm_mk (e : C ≌ D) (y : D) :
    e.isomorphismClassesEquiv.symm ⟦y⟧ = ⟦e.inverse.obj y⟧ := (rfl)

end CategoryTheory.Equivalence

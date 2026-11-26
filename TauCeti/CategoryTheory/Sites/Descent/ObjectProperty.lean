/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import TauCeti.CategoryTheory.Sites.Descent.StrongTrans
public import TauCeti.CategoryTheory.Sites.Descent.DescentData

/-!
# Full substacks defined by local properties

A property of objects of a stack defines a full substack when it is preserved by pullback,
invariant under isomorphisms, and local on the base. Conversely, if the full sub-pseudofunctor
is a stack, its isomorphism-invariant object property is local. This characterizes which
strictly full sub-pseudofunctors are substacks, without any algebraicity assumption.

The construction reuses Joël Riou's `Pseudofunctor.ObjectProperty.fullsubcategory` and its
inclusion `ι`; descent data and their transport are those of Mathlib and
`Pseudofunctor.StrongTrans.mapDescentData`.
-/

public section

open CategoryTheory Bicategory Opposite

namespace CategoryTheory.Pseudofunctor.ObjectProperty

universe t v v' u u'

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (P : F.ObjectProperty) (J : GrothendieckTopology C)

/-- A local object property of a pseudofunctor is invariant under isomorphism, preserved by
pullback, and holds for an object whenever it holds after pullback along a covering sieve. -/
class IsLocal : Prop extends IsClosedUnderMapObj P, IsClosedUnderIsomorphisms P where
  /-- Membership descends along covering sieves. -/
  of_sieve {S : C} {R : Sieve S} (hR : R ∈ J S) {M : F.obj (.mk (op S))}
    (h : ∀ ⦃T : C⦄ (f : T ⟶ S), R f →
      P.prop (.mk (op T)) ((F.map f.op.toLoc).toFunctor.obj M)) : P.prop (.mk (op S)) M

/-- Membership in a local object property can be checked on any covering sieve. -/
lemma prop_iff_of_sieve [P.IsLocal J] {S : C} {R : Sieve S} (hR : R ∈ J S)
    (M : F.obj (.mk (op S))) :
    P.prop (.mk (op S)) M ↔ ∀ ⦃T : C⦄ (f : T ⟶ S), R f →
      P.prop (.mk (op T)) ((F.map f.op.toLoc).toFunctor.obj M) :=
  ⟨fun h _ f _ ↦ P.map_obj h f.op.toLoc, IsLocal.of_sieve hR⟩

/-- A full sub-pseudofunctor of a prestack is a prestack. No locality of the object property
is needed for descent of morphisms. -/
instance isPrestack_fullsubcategory [P.IsClosedUnderMapObj] [F.IsPrestack J] :
    P.fullsubcategory.IsPrestack J :=
  isPrestack_source_of_fullyFaithful P.ι fun U ↦ (P.prop (.mk (op U))).fullyFaithfulι

/-- A local object property of a stack defines a full substack. Gluing in the ambient stack
produces an object of the subcategory because its restrictions satisfy the property. -/
instance isStack_fullsubcategory [P.IsLocal J] [F.IsStack J] :
    P.fullsubcategory.IsStack J where
  essSurj_of_sieve {S} R hR := by
    let f := fun r : R.arrows.category ↦ r.obj.hom
    have hff (U : C) := (P.prop (.mk (op U))).fullyFaithfulι
    have := IsStack.essSurj_of_sieve F R hR
    refine ⟨fun D ↦ ?_⟩
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F.toDescentData f)
      ((P.ι.mapDescentData f).obj D)
    have hM : P.prop (.mk (op S)) M := by
      apply IsLocal.of_sieve hR
      intro T g hg
      exact (P.prop (.mk (op T))).prop_of_iso
        (DescentData.isoApp e ⟨Over.mk g, hg⟩).symm (D.obj ⟨Over.mk g, hg⟩).property
    let M' : P.Obj (.mk (op S)) := ⟨M, hM⟩
    refine ⟨M', ⟨(P.ι.fullyFaithfulMapDescentData f hff).preimageIso ?_⟩⟩
    exact (P.ι.toDescentDataCompMapDescentDataIso f).app M' ≪≫ e

/-- If a strictly full sub-pseudofunctor of a prestack is a stack, its object property is
local. The ambient prestack condition identifies an ambient object with the gluing of its
restrictions inside the substack. -/
theorem isLocal_of_isStack_fullsubcategory [P.IsClosedUnderMapObj]
    [P.IsClosedUnderIsomorphisms] [F.IsPrestack J] [P.fullsubcategory.IsStack J] :
    P.IsLocal J where
  of_sieve {S R} hR {M} h := by
    let f := fun r : R.arrows.category ↦ r.obj.hom
    let D := (F.toDescentData f).obj M
    let M' (r : R.arrows.category) : P.Obj (.mk (op r.obj.left)) :=
      ⟨D.obj r, h r.obj.hom r.property⟩
    have hff (U : C) := (P.prop (.mk (op U))).fullyFaithfulι
    let e (r : R.arrows.category) : (P.ι.app _).toFunctor.obj (M' r) ≅ D.obj r := Iso.refl _
    let D' := P.ι.liftDescentData f hff D e
    have := IsStack.essSurj_of_sieve P.fullsubcategory R hR
    obtain ⟨N, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := P.fullsubcategory.toDescentData f) D'
    let j : (F.toDescentData f).obj N.obj ≅ (F.toDescentData f).obj M :=
      ((P.ι.toDescentDataCompMapDescentDataIso f).app N).symm ≪≫
        (P.ι.mapDescentData f).mapIso i ≪≫ P.ι.mapDescentDataLiftDescentDataIso f hff D e
    exact (P.prop (.mk (op S))).prop_of_iso
      ((F.isPrestackFor' R hR).fullyFaithful.preimageIso j) N.property

/-- For an isomorphism-invariant, pullback-stable object property of a stack, locality is
equivalent to the full sub-pseudofunctor being a stack. -/
theorem isLocal_iff_isStack_fullsubcategory [P.IsClosedUnderMapObj]
    [P.IsClosedUnderIsomorphisms] [F.IsStack J] :
    P.IsLocal J ↔ P.fullsubcategory.IsStack J :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ P.isLocal_of_isStack_fullsubcategory J⟩

variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- Inverse images of local object properties are local. Naturality transports the pullback
condition through the component functors of the strong transformation. -/
instance isLocal_inverseImage (Q : G.ObjectProperty) [Q.IsLocal J]
    (η : StrongTrans F G) : (Q.inverseImage η).IsLocal J where
  map_obj {X Y M} hM f := by
    simp only [inverseImage_prop] at hM ⊢
    exact (Q.prop Y).prop_of_iso ((Cat.Hom.toNatIso (η.naturality f)).app M).symm
      (Q.map_obj hM f)
  isClosedUnderIsomorphisms U := by
    refine ⟨fun e h ↦ ?_⟩
    simp only [inverseImage_prop] at h ⊢
    exact (Q.prop U).prop_of_iso ((η.app U).toFunctor.mapIso e) h
  of_sieve {S R} hR {M} h := by
    simp only [inverseImage_prop] at h ⊢
    apply IsLocal.of_sieve (P := Q) hR
    intro T f hf
    exact (Q.prop (.mk (op T))).prop_of_iso
      ((Cat.Hom.toNatIso (η.naturality f.op.toLoc)).app M) (h f hf)

end CategoryTheory.Pseudofunctor.ObjectProperty

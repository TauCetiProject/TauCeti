/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Sites.Descent.Over
public import TauCeti.CategoryTheory.Sites.Descent.StrongTrans

/-!
# Gerbes over a site

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `J` a Grothendieck topology on `C`.
`F` is a gerbe for `J` (Stacks, Section 06NY, Definition 8.11.1) if it is a stack for `J`, every
fibre category is a groupoid, every object `U` of `C` has a `J`-covering sieve over whose arrows
`V ⟶ U` the fibre over `V` is nonempty, and any two objects of a fibre become isomorphic after
pullback along every arrow of some `J`-covering sieve.

## Main declarations

* `CategoryTheory.Pseudofunctor.IsGerbe`: the property that `F` is a gerbe for `J`.
* `CategoryTheory.Pseudofunctor.IsGerbe.exists_covering_hom`: in a gerbe, any two objects over
  `U` have morphisms between their pullbacks along every arrow of some covering sieve.
* `CategoryTheory.Pseudofunctor.isGerbe_target_of_isEquivalence`,
  `CategoryTheory.Pseudofunctor.isGerbe_source_of_isEquivalence`: for a strong transformation
  `F ⟶ G` whose components are equivalences, if one of `F` and `G` is a gerbe, then so is the
  other.
* `CategoryTheory.Pseudofunctor.isGerbe_iff_of_isEquivalence`: for such a transformation, `F` is a
  gerbe if and only if `G` is. The stack conditions are transported by
  `CategoryTheory.Pseudofunctor.isStack_iff_of_isEquivalence`.
* `CategoryTheory.Pseudofunctor.isGerbe_over`: the restriction `F.over U` of a gerbe for `J` to
  the slice site `(Over U, J.over U)` is a gerbe for `J.over U`.
* `CategoryTheory.Pseudofunctor.isGerbe_constant`: the constant pseudofunctor with a nonempty
  groupoid fibre any two of whose objects are isomorphic is a gerbe for any topology for which it
  is a stack.

## References

* [Stacks Project, Section 06NY](https://stacks.math.columbia.edu/tag/06NY), Definition 8.11.1
  and Lemma 8.11.2
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- A pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` is a gerbe for a Grothendieck topology `J`
if it is a stack for `J` whose fibre categories are groupoids, which has objects locally, and any
two of whose objects over the same base are locally isomorphic (Stacks, Section 06NY,
Definition 8.11.1). The locality conditions are stated with `J`-covering sieves. -/
class IsGerbe (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (J : GrothendieckTopology C) : Prop
    extends F.IsStack J where
  /-- Every fibre category is a groupoid. -/
  isGroupoid (U : C) : IsGroupoid (F.obj (.mk (op U)))
  /-- Every object `U` has a covering sieve over whose arrows `V ⟶ U` the fibre is nonempty. -/
  exists_covering_nonempty (U : C) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Nonempty (F.obj (.mk (op V)))
  /-- Any two objects over `U` become isomorphic after pullback along every arrow of some
  covering sieve of `U`. -/
  exists_covering_iso {U : C} (x y : F.obj (.mk (op U))) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)

attribute [instance] IsGerbe.isGroupoid

variable {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {J : GrothendieckTopology C}

/-- **Local sections of `Hom(x, y)`.** For a gerbe, any two objects over `U` have a morphism
between their pullbacks along every arrow of some covering sieve of `U`. -/
theorem IsGerbe.exists_covering_hom [F.IsGerbe J] {U : C} (x y : F.obj (.mk (op U))) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y) := by
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_iso (J := J) x y
  exact ⟨R, hR, fun _ f hf ↦ (h f hf).map Iso.hom⟩

/-- Local isomorphy of objects transfers along a strong transformation whose components are
essentially surjective. -/
private lemma exists_covering_iso_of_essSurj [F.IsGerbe J] (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.EssSurj) {U : C}
    (y y' : G.obj (.mk (op U))) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((G.map f.op.toLoc).toFunctor.obj y ≅ (G.map f.op.toLoc).toFunctor.obj y') := by
  let e := (η.app (.mk (op U))).toFunctor
  have := hη U
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_iso (J := J) (e.objPreimage y) (e.objPreimage y')
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨i⟩ := h f hf
  let p := (G.map f.op.toLoc).toFunctor
  exact ⟨p.mapIso (e.objObjPreimageIso y).symm ≪≫ (η.naturalityObjIso f.op.toLoc _).symm ≪≫
    (η.app (.mk (op V))).toFunctor.mapIso i ≪≫ η.naturalityObjIso f.op.toLoc _ ≪≫
    p.mapIso (e.objObjPreimageIso y')⟩

/-- Local isomorphy of objects is reflected by a strong transformation whose components are
fully faithful. -/
private lemma exists_covering_iso_of_fullyFaithful [G.IsGerbe J] (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful) {U : C}
    (x x' : F.obj (.mk (op U))) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj x') := by
  let e := (η.app (.mk (op U))).toFunctor
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_iso (J := J) (e.obj x) (e.obj x')
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨i⟩ := h f hf
  exact ⟨(hη V).preimageIso (η.naturalityObjIso f.op.toLoc x ≪≫ i ≪≫
    (η.naturalityObjIso f.op.toLoc x').symm)⟩

/-- Let `η : F ⟶ G` be a strong transformation whose components are equivalences of fibre
categories. If `F` is a gerbe, then `G` is a gerbe (Stacks, Section 06NY, Lemma 8.11.2). -/
theorem isGerbe_target_of_isEquivalence [F.IsGerbe J] (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence) : G.IsGerbe J :=
  { toIsStack := (isStack_iff_of_isEquivalence η hη).1 inferInstance
    isGroupoid U := by
      have := hη U
      exact isGroupoid_of_reflects_iso (η.app (.mk (op U))).toFunctor.inv
    exists_covering_nonempty U := by
      obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_nonempty (F := F) (J := J) U
      exact ⟨R, hR, fun V f hf ↦ (h f hf).map (η.app (.mk (op V))).toFunctor.obj⟩
    exists_covering_iso x y :=
      exists_covering_iso_of_essSurj η (fun U ↦ have := hη U; inferInstance) x y }

/-- Let `η : F ⟶ G` be a strong transformation whose components are equivalences of fibre
categories. If `G` is a gerbe, then `F` is a gerbe (Stacks, Section 06NY, Lemma 8.11.2). -/
theorem isGerbe_source_of_isEquivalence [G.IsGerbe J] (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence) : F.IsGerbe J :=
  { toIsStack := (isStack_iff_of_isEquivalence η hη).2 inferInstance
    isGroupoid U := by
      have := hη U
      exact isGroupoid_of_reflects_iso (η.app (.mk (op U))).toFunctor
    exists_covering_nonempty U := by
      obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_nonempty (F := G) (J := J) U
      exact ⟨R, hR, fun V f hf ↦ (h f hf).map (η.app (.mk (op V))).toFunctor.inv.obj⟩
    exists_covering_iso x y :=
      exists_covering_iso_of_fullyFaithful η (fun U ↦ have := hη U; .ofFullyFaithful _) x y }

/-- Let `η : F ⟶ G` be a strong transformation whose components are equivalences of fibre
categories. Then `F` is a gerbe if and only if `G` is (Stacks, Section 06NY, Lemma 8.11.2). -/
theorem isGerbe_iff_of_isEquivalence (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence) :
    F.IsGerbe J ↔ G.IsGerbe J :=
  ⟨fun _ ↦ isGerbe_target_of_isEquivalence η hη, fun _ ↦ isGerbe_source_of_isEquivalence η hη⟩

/-- The restriction `F.over U` of a gerbe for `J` to the slice site `(Over U, J.over U)` is a gerbe
for `J.over U`. Its fibre over `X : Over U` is the fibre of `F` over `X.left`. -/
instance isGerbe_over [F.IsGerbe J] (U : C) : (F.over U).IsGerbe (J.over U) where
  isGroupoid X := IsGerbe.isGroupoid (F := F) (J := J) X.left
  exists_covering_nonempty X := by
    obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_nonempty (F := F) (J := J) X.left
    exact ⟨(Sieve.overEquiv X).symm R, J.overEquiv_symm_mem_over X R hR,
      fun _ g hg ↦ h g.left ((Sieve.overEquiv_symm_iff R g).1 hg)⟩
  exists_covering_iso {X} x y := by
    obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_iso (F := F) (J := J) (U := X.left) x y
    exact ⟨(Sieve.overEquiv X).symm R, J.overEquiv_symm_mem_over X R hR,
      fun _ g hg ↦ h g.left ((Sieve.overEquiv_symm_iff R g).1 hg)⟩

section constant

variable {D : Type u'} [Category.{v'} D]

/-- **A constant diagram with a nonempty connected groupoid fibre is a gerbe** for any topology
`J` for which it is a stack: its fibres are groupoids, the maximal sieve has an object over every
arrow, and any two objects of the fibre are isomorphic. For `J = ⊥` the stack property is
`isStack_bot`. -/
theorem isGerbe_constant (J : GrothendieckTopology C) [(constant C D).IsStack J] [IsGroupoid D]
    [Nonempty D] (h : ∀ x y : D, Nonempty (x ≅ y)) : (constant C D).IsGerbe J where
  isGroupoid _ := inferInstanceAs (IsGroupoid D)
  exists_covering_nonempty U := ⟨⊤, J.top_mem U, fun _ _ _ ↦ inferInstanceAs (Nonempty D)⟩
  exists_covering_iso x y := ⟨⊤, J.top_mem _, fun _ _ _ ↦ h x y⟩

end constant

end CategoryTheory.Pseudofunctor

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Functor
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation
-- `whiskerLeftAut` and `whiskerLeftAutEquiv` retype the automorphism maps of
-- `Functor.precomposeLaxMonoidal`, whose objects are `LaxMonoidalFunctor.of (F ⋙ G)` only by
-- unfolding its definition.
import all TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Whiskering monoidal natural automorphisms

For a lax monoidal functor `F`, the group `Aut (LaxMonoidalFunctor.of F)` is the group of monoidal
natural automorphisms of `F`. This file records how these groups change along composition of
lax monoidal functors.

* Whiskering on the right with a lax monoidal functor `G` is a group homomorphism
  `Aut (LaxMonoidalFunctor.of F) →* Aut (LaxMonoidalFunctor.of (F ⋙ G))`
  (`CategoryTheory.LaxMonoidalFunctor.whiskerRightAut`), and whiskering on the left with a lax
  monoidal functor `F` is a group homomorphism
  `Aut (LaxMonoidalFunctor.of G) →* Aut (LaxMonoidalFunctor.of (F ⋙ G))`
  (`CategoryTheory.LaxMonoidalFunctor.whiskerLeftAut`), the automorphism-group map of
  `CategoryTheory.Functor.precomposeLaxMonoidal F`.
* Whiskering on the left with the functor of an equivalence `e` whose functor is strong monoidal
  is an isomorphism of groups (`CategoryTheory.LaxMonoidalFunctor.whiskerLeftAutEquiv`), with
  the inverse of `e` monoidal by `Equivalence.inverseMonoidal`. This is the automorphism-group
  equivalence of the fully faithful functor of
  `CategoryTheory.Equivalence.precomposeLaxMonoidalEquivalence`, stated for the bundled functor
  `LaxMonoidalFunctor.of (e.functor ⋙ G)` so that its components are those of the composite.

A monoidal natural isomorphism `e : F ≅ G` between lax monoidal functors is an isomorphism
`LaxMonoidalFunctor.isoMk e` of the bundled functors, so conjugation by it identifies their
monoidal automorphism groups (Mathlib's `CategoryTheory.Aut.autMulEquivOfIso`).

These operations transport tensor automorphisms of fibre functors: base change of the value
algebra of a fibre functor is right whiskering, and changing the source category along a monoidal
equivalence is left whiskering.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LaxMonoidalFunctor

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- Right whiskering of a monoidal natural isomorphism is monoidal. -/
instance {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (H : D ⥤ E) [H.LaxMonoidal]
    (u : F ≅ G) [NatTrans.IsMonoidal u.hom] :
    NatTrans.IsMonoidal (Functor.isoWhiskerRight u H).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.whiskerRight u.hom H))

/-- Left whiskering of a monoidal natural isomorphism is monoidal. -/
instance {G H : D ⥤ E} [G.LaxMonoidal] [H.LaxMonoidal] (F : C ⥤ D) [F.LaxMonoidal] (u : G ≅ H)
    [NatTrans.IsMonoidal u.hom] :
    NatTrans.IsMonoidal (Functor.isoWhiskerLeft F u).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.whiskerLeft F u.hom))

/-- Whiskering monoidal natural automorphisms of `F` on the right with a lax monoidal functor
`G`. -/
def whiskerRightAut (F : C ⥤ D) [F.LaxMonoidal] (G : D ⥤ E) [G.LaxMonoidal] :
    Aut (LaxMonoidalFunctor.of F) →* Aut (LaxMonoidalFunctor.of (F ⋙ G)) where
  -- Instance search does not see through the objects of `LaxMonoidalFunctor.of (F ⋙ G)`, so
  -- the monoidality witness is passed explicitly.
  toFun u := Aut.of (@isoMk _ _ _ _ _ _ (of (F ⋙ G)) (of (F ⋙ G))
    (Functor.isoWhiskerRight (forgetAut F u).asIso G)
    (inferInstanceAs (NatTrans.IsMonoidal (Functor.whiskerRight (forgetAut F u).asIso.hom G))))
  map_one' := by
    ext X
    simp only [map_one, Aut.one_asIso, Functor.isoWhiskerRight_refl, Iso.refl_hom, id_hom,
      NatTrans.id_app]
    -- Normalize the bundling constructors across the `of` wrapper.
    dsimp only [isoMk, homMk, of]
    simp only [Iso.refl_hom, NatTrans.id_app]
  map_mul' u v := by
    ext X
    simp only [map_mul, Aut.mul_asIso, Functor.isoWhiskerRight_trans, Iso.trans_hom, comp_hom,
      NatTrans.comp_app]
    dsimp only [isoMk, homMk, of]
    simp only [Iso.trans_hom, NatTrans.comp_app]

/-- The components of a right whiskered monoidal natural automorphism. -/
@[simp]
theorem whiskerRightAut_apply_asIso_hom_hom_app (F : C ⥤ D) [F.LaxMonoidal] (G : D ⥤ E)
    [G.LaxMonoidal] (u : Aut (LaxMonoidalFunctor.of F)) (X : C) :
    (whiskerRightAut F G u).asIso.hom.hom.app X = G.map (u.asIso.hom.hom.app X) := by
  rw [← forgetAut_apply_asIso_hom F u]
  simp only [whiskerRightAut, MonoidHom.coe_mk, OneHom.coe_mk]
  dsimp only [isoMk, homMk, of]
  simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]

/-- Whiskering monoidal natural automorphisms of `G` on the left with a lax monoidal functor
`F`. This is `Functor.mapAut` for `F.precomposeLaxMonoidal`, typed through
`LaxMonoidalFunctor.of (F ⋙ G)`. -/
def whiskerLeftAut (F : C ⥤ D) [F.LaxMonoidal] (G : D ⥤ E) [G.LaxMonoidal] :
    Aut (LaxMonoidalFunctor.of G) →* Aut (LaxMonoidalFunctor.of (F ⋙ G)) :=
  F.precomposeLaxMonoidal.mapAut (LaxMonoidalFunctor.of G)

/-- The components of a left whiskered monoidal natural automorphism. -/
@[simp]
theorem whiskerLeftAut_apply_asIso_hom_hom_app (F : C ⥤ D) [F.LaxMonoidal] (G : D ⥤ E)
    [G.LaxMonoidal] (u : Aut (LaxMonoidalFunctor.of G)) (X : C) :
    (whiskerLeftAut F G u).asIso.hom.hom.app X = u.asIso.hom.hom.app (F.obj X) :=
  (rfl)

section Equivalence

variable (e : C ≌ D) [e.functor.Monoidal]

/-- Whiskering on the left with an equivalence `e` whose functor is strong monoidal identifies
the monoidal natural automorphisms of `G` with those of `e.functor ⋙ G`. The inverse of `e`
carries the monoidal structure `Equivalence.inverseMonoidal`. This is the automorphism-group
equivalence of the fully faithful functor of `Equivalence.precomposeLaxMonoidalEquivalence`. -/
noncomputable def whiskerLeftAutEquiv (G : D ⥤ E) [G.LaxMonoidal] :
    Aut (LaxMonoidalFunctor.of G) ≃* Aut (LaxMonoidalFunctor.of (e.functor ⋙ G)) :=
  letI := e.inverseMonoidal
  (e.precomposeLaxMonoidalEquivalence (E := E)).fullyFaithfulFunctor.autMulEquivOfFullyFaithful
    (LaxMonoidalFunctor.of G)

/-- `whiskerLeftAutEquiv e G` is left whiskering with `e.functor`. -/
@[simp]
theorem whiskerLeftAutEquiv_apply (G : D ⥤ E) [G.LaxMonoidal]
    (u : Aut (LaxMonoidalFunctor.of G)) :
    whiskerLeftAutEquiv e G u = whiskerLeftAut e.functor G u :=
  (rfl)

end Equivalence

end CategoryTheory.LaxMonoidalFunctor

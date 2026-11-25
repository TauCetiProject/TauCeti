/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Functor
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation

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
  (`CategoryTheory.LaxMonoidalFunctor.whiskerLeftAut`).
* Whiskering on the left with the functor of an equivalence `e` whose functor is strong monoidal
  is an isomorphism of groups (`CategoryTheory.LaxMonoidalFunctor.whiskerLeftAutEquiv`). Its
  inverse whiskers with the inverse of `e`, monoidal by `Equivalence.inverseMonoidal`, and
  conjugates by the round-trip comparison
  `CategoryTheory.Equivalence.laxMonoidalRoundTripIso`. This is the automorphism-group form of
  `CategoryTheory.Equivalence.precomposeLaxMonoidalEquivalence`, stated for the bundled functor
  `LaxMonoidalFunctor.of (e.functor ⋙ G)` so that its components are those of the composite.

A monoidal natural isomorphism `e : F ≅ G` between lax monoidal functors is an isomorphism
`LaxMonoidalFunctor.ofIso e` of the bundled functors, so conjugation by it identifies their
monoidal automorphism groups (Mathlib's `CategoryTheory.Aut.autMulEquivOfIso`).

These operations transport tensor automorphisms of fibre functors: base change of the value
algebra of a fibre functor is right whiskering, and changing the source category along a monoidal
equivalence is left whiskering.
-/

public section

-- Components of monoidal natural transformations between bundled functors
-- `LaxMonoidalFunctor.of F` are typed through the objects of `LaxMonoidalFunctor.of F`, which
-- agree with those of `F` only after unfolding. Several proofs below therefore end with `rfl`
-- after `simp` has computed both sides, or rewrite with `erw`.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LaxMonoidalFunctor

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- A monoidal natural isomorphism between lax monoidal functors, as an isomorphism of the
bundled lax monoidal functors. -/
def ofIso {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (e : F ≅ G)
    [h : NatTrans.IsMonoidal e.hom] : LaxMonoidalFunctor.of F ≅ LaxMonoidalFunctor.of G :=
  @isoMk _ _ _ _ _ _ (of F) (of G) e h

/-- The underlying natural transformation of `ofIso e` is `e.hom`. -/
@[simp]
theorem ofIso_hom_hom {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (e : F ≅ G)
    [NatTrans.IsMonoidal e.hom] : (ofIso e).hom.hom = e.hom :=
  (rfl)

/-- The underlying natural transformation of the inverse of `ofIso e` is `e.inv`. -/
@[simp]
theorem ofIso_inv_hom {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (e : F ≅ G)
    [NatTrans.IsMonoidal e.hom] : (ofIso e).inv.hom = e.inv :=
  (rfl)

/-- The components of `ofIso e` are those of `e`. Not a `simp` lemma, since `ofIso_hom_hom`
proves it; it is stated for rewriting components without changing their types. -/
theorem ofIso_hom_hom_app {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (e : F ≅ G)
    [NatTrans.IsMonoidal e.hom] (X : C) : (ofIso e).hom.hom.app X = e.hom.app X :=
  (rfl)

/-- The components of the inverse of `ofIso e` are those of `e.inv`. Not a `simp` lemma, since
`ofIso_inv_hom` proves it. -/
theorem ofIso_inv_hom_app {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (e : F ≅ G)
    [NatTrans.IsMonoidal e.hom] (X : C) : (ofIso e).inv.hom.app X = e.inv.app X :=
  (rfl)

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
  toFun u := Aut.of (ofIso (Functor.isoWhiskerRight (forgetAut F u).asIso G))
  map_one' := by
    ext X
    simp [map_one]
    rfl
  map_mul' u v := by
    ext X
    simp [map_mul, forgetAut_apply_asIso_hom]
    rfl

/-- The components of a right whiskered monoidal natural automorphism. -/
@[simp]
theorem whiskerRightAut_apply_asIso_hom_hom_app (F : C ⥤ D) [F.LaxMonoidal] (G : D ⥤ E)
    [G.LaxMonoidal] (u : Aut (LaxMonoidalFunctor.of F)) (X : C) :
    (whiskerRightAut F G u).asIso.hom.hom.app X = G.map (u.asIso.hom.hom.app X) := by
  simp [whiskerRightAut, forgetAut_apply_asIso_hom]
  rfl

/-- Whiskering monoidal natural automorphisms of `G` on the left with a lax monoidal functor
`F`. This is `Functor.mapAut` for `F.precomposeLaxMonoidal`, typed through
`LaxMonoidalFunctor.of (F ⋙ G)`. -/
def whiskerLeftAut (F : C ⥤ D) [F.LaxMonoidal] (G : D ⥤ E) [G.LaxMonoidal] :
    Aut (LaxMonoidalFunctor.of G) →* Aut (LaxMonoidalFunctor.of (F ⋙ G)) where
  toFun u := Aut.of (ofIso (Functor.isoWhiskerLeft F (forgetAut G u).asIso))
  map_one' := by
    ext X
    simp [map_one]
    rfl
  map_mul' u v := by
    ext X
    simp [map_mul, forgetAut_apply_asIso_hom]
    rfl

/-- The components of a left whiskered monoidal natural automorphism. -/
@[simp]
theorem whiskerLeftAut_apply_asIso_hom_hom_app (F : C ⥤ D) [F.LaxMonoidal] (G : D ⥤ E)
    [G.LaxMonoidal] (u : Aut (LaxMonoidalFunctor.of G)) (X : C) :
    (whiskerLeftAut F G u).asIso.hom.hom.app X = u.asIso.hom.hom.app (F.obj X) := by
  simp [whiskerLeftAut, forgetAut_apply_asIso_hom]
  rfl

section Equivalence

variable (e : C ≌ D) [e.functor.Monoidal]

section Inverse

variable [e.inverse.Monoidal] [e.IsMonoidal]

/-- The round-trip comparison `G ≅ e.inverse ⋙ e.functor ⋙ G` of a monoidal equivalence, typed
through the composite functor. -/
private noncomputable def counitCompIso (G : D ⥤ E) [G.LaxMonoidal] :
    LaxMonoidalFunctor.of G ≅ LaxMonoidalFunctor.of (e.inverse ⋙ e.functor ⋙ G) :=
  e.laxMonoidalRoundTripIso (LaxMonoidalFunctor.of G)

private theorem counitCompIso_hom_hom_app (G : D ⥤ E) [G.LaxMonoidal] (Y : D) :
    (counitCompIso e G).hom.hom.app Y = G.map (e.counitIso.inv.app Y) :=
  e.laxMonoidalRoundTripIso_hom_app _ Y

private theorem counitCompIso_inv_hom_app (G : D ⥤ E) [G.LaxMonoidal] (Y : D) :
    (counitCompIso e G).inv.hom.app Y = G.map (e.counitIso.hom.app Y) := by
  have h := congrArg (fun α ↦ α.hom.app Y) (counitCompIso e G).inv_hom_id
  simp only [comp_hom, NatTrans.comp_app, counitCompIso_hom_hom_app, id_hom, NatTrans.id_app] at h
  exact (Iso.comp_inv_eq_id (G.mapIso (e.counitIso.app Y))).1 h

end Inverse

/-- Whiskering on the left with an equivalence `e` whose functor is strong monoidal identifies
the monoidal natural automorphisms of `G` with those of `e.functor ⋙ G`. The inverse of `e`
carries the monoidal structure `Equivalence.inverseMonoidal`. -/
noncomputable def whiskerLeftAutEquiv (G : D ⥤ E) [G.LaxMonoidal] :
    Aut (LaxMonoidalFunctor.of G) ≃* Aut (LaxMonoidalFunctor.of (e.functor ⋙ G)) :=
  letI := e.inverseMonoidal
  { toFun := whiskerLeftAut e.functor G
    invFun v := Aut.autMulEquivOfIso (counitCompIso e G).symm (whiskerLeftAut e.inverse _ v)
    left_inv u := by
      ext Y
      simp only [Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom, Iso.symm_symm_eq,
        comp_hom, NatTrans.comp_app, counitCompIso_hom_hom_app, counitCompIso_inv_hom_app,
        whiskerLeftAut_apply_asIso_hom_hom_app]
      have h : u.asIso.hom.hom.app _ ≫ G.map (e.counitIso.hom.app Y) =
          G.map (e.counitIso.hom.app Y) ≫ u.asIso.hom.hom.app Y :=
        (u.asIso.hom.hom.naturality (e.counitIso.hom.app Y)).symm
      -- The composite is typed through the objects of `LaxMonoidalFunctor.of G`, which agree with
      -- those of `G` only up to unfolding, so the rewrites need `erw`.
      erw [h, ← G.map_comp_assoc, Iso.inv_hom_id_app, G.map_id, Category.id_comp]
    right_inv v := by
      ext X
      simp only [Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom, Iso.symm_symm_eq,
        comp_hom, NatTrans.comp_app, counitCompIso_hom_hom_app, counitCompIso_inv_hom_app,
        whiskerLeftAut_apply_asIso_hom_hom_app]
      have h : G.map (e.functor.map (e.unitIso.hom.app X)) ≫ v.asIso.hom.hom.app _ =
          v.asIso.hom.hom.app X ≫ G.map (e.functor.map (e.unitIso.hom.app X)) :=
        v.asIso.hom.hom.naturality (e.unitIso.hom.app X)
      rw [show e.counitIso.inv.app (e.functor.obj X) = e.functor.map (e.unitIso.hom.app X) from
          e.counitInv_app_functor X,
        show e.counitIso.hom.app (e.functor.obj X) = e.functor.map (e.unitIso.inv.app X) from
          e.counit_app_functor X]
      -- As above, the composite is typed through `LaxMonoidalFunctor.of`.
      erw [← Category.assoc, h, Category.assoc, ← G.map_comp, ← e.functor.map_comp,
        Iso.hom_inv_id_app, e.functor.map_id, G.map_id, Category.comp_id]
    map_mul' u v := map_mul (whiskerLeftAut e.functor G) u v }

/-- `whiskerLeftAutEquiv e G` is left whiskering with `e.functor`. -/
@[simp]
theorem whiskerLeftAutEquiv_apply (G : D ⥤ E) [G.LaxMonoidal]
    (u : Aut (LaxMonoidalFunctor.of G)) :
    whiskerLeftAutEquiv e G u = whiskerLeftAut e.functor G u :=
  (rfl)

end Equivalence

end CategoryTheory.LaxMonoidalFunctor

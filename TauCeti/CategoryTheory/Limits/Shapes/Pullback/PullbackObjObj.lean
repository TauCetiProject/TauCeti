/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Functoriality and natural-isomorphism transport for Leibniz pullbacks

For a bifunctor `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂` and morphisms `f₁ : X₁ ⟶ Y₁` and `f₃ : X₃ ⟶ Y₃`,
a `Functor.PullbackObjObj` square records a pullback of `(G.obj (op X₁)).obj X₃` and
`(G.obj (op Y₁)).obj Y₃` over `(G.obj (op X₁)).obj Y₃`, together with its induced corner map
`π`.

This file supplies four operations on `Functor.PullbackObjObj`, complementing
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj`:

* `Functor.PullbackObjObj.ofNatIso`: transport along a natural isomorphism `G ≅ G'`, dual to
  `Functor.PushoutObjObj.ofNatIso`.
* `Functor.PullbackObjObj.map`: image under a functor `H : C₂ ⥤ C₂'` that preserves the
  defining pullback cospan, producing a `PullbackObjObj` for `G` postcomposed with whiskering
  by `H`, whose corner map is `H.map sq.π`.
* `Functor.PullbackObjObj.ofWhiskeringLeft`: reinterpret a `PullbackObjObj` square for `G`
  precomposed in its covariant variable by `L : C₃' ⥤ C₃` as a `PullbackObjObj` square for `G`
  along `L.map f₃'`.
* `Functor.PullbackObjObj.ofOpComp`: reinterpret a `PullbackObjObj` square for `K.op ⋙ G`
  as a `PullbackObjObj` square for `G` along `K.map f₁'`.

## References

* E. Riehl and D. Verity, *Elements of ∞-Category Theory*, Cambridge Studies in Advanced
  Mathematics 194, 2022, Definition C.2.8.
-/

public section

universe v₁ v₁' v₂ v₂' v₃ v₃' u₁ u₁' u₂ u₂' u₃ u₃'

namespace CategoryTheory.Functor.PullbackObjObj

open Opposite Limits

variable {C₁ : Type u₁} {C₁' : Type u₁'} {C₂ : Type u₂} {C₂' : Type u₂'}
  {C₃ : Type u₃} {C₃' : Type u₃'}
  [Category.{v₁} C₁] [Category.{v₁'} C₁'] [Category.{v₂} C₂] [Category.{v₂'} C₂']
  [Category.{v₃} C₃] [Category.{v₃'} C₃']
  {G G' : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
  {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {X₃ Y₃ : C₃} {f₃ : X₃ ⟶ Y₃}

/-- Transport a `Functor.PullbackObjObj` structure along a natural isomorphism of bifunctors. -/
-- Exposed so `(sq.ofNatIso e).pt` reduces to `sq.pt` in the types of `fst`, `snd`, and `π`.
@[expose]
def ofNatIso (sq : G.PullbackObjObj f₁ f₃) (e : G ≅ G') : G'.PullbackObjObj f₁ f₃ where
  pt := sq.pt
  fst := sq.fst ≫ (e.hom.app (op X₁)).app X₃
  snd := sq.snd ≫ (e.hom.app (op Y₁)).app Y₃
  isPullback :=
    sq.isPullback.of_iso (Iso.refl _) ((e.app _).app _) ((e.app _).app _) ((e.app _).app _)
      (by simp) (by simp) (by simp) (by simp)
  π := (e.inv.app (op Y₁)).app X₃ ≫ sq.π
  π_fst := by
    have h := congrArg (fun η ↦ η.app X₃) (e.hom.naturality f₁.op)
    simp only [NatTrans.comp_app] at h
    rw [Category.assoc, sq.π_fst_assoc, h, Iso.inv_hom_id_app_app_assoc]
  π_snd := by
    rw [Category.assoc, sq.π_snd_assoc, (e.hom.app (op Y₁)).naturality f₃,
      Iso.inv_hom_id_app_app_assoc]

/-- Transporting a `Functor.PullbackObjObj` along a natural isomorphism keeps the same pullback
object. -/
@[simp]
lemma ofNatIso_pt (sq : G.PullbackObjObj f₁ f₃) (e : G ≅ G') :
    (sq.ofNatIso e).pt = sq.pt := (rfl)

/-- The first projection of `sq.ofNatIso e` postcomposes `sq.fst` with `e.hom`. -/
@[simp]
lemma ofNatIso_fst (sq : G.PullbackObjObj f₁ f₃) (e : G ≅ G') :
    (sq.ofNatIso e).fst = sq.fst ≫ (e.hom.app (op X₁)).app X₃ := (rfl)

/-- The second projection of `sq.ofNatIso e` postcomposes `sq.snd` with `e.hom`. -/
@[simp]
lemma ofNatIso_snd (sq : G.PullbackObjObj f₁ f₃) (e : G ≅ G') :
    (sq.ofNatIso e).snd = sq.snd ≫ (e.hom.app (op Y₁)).app Y₃ := (rfl)

/-- The corner map of `sq.ofNatIso e` precomposes `sq.π` with `e.inv`. -/
@[simp]
lemma ofNatIso_π (sq : G.PullbackObjObj f₁ f₃) (e : G ≅ G') :
    (sq.ofNatIso e).π = (e.inv.app (op Y₁)).app X₃ ≫ sq.π := (rfl)

/-- Postcomposing `sq.ofNatIso e` with `e.hom` on the domain recovers `sq.π`. -/
@[reassoc]
lemma hom_comp_ofNatIso_π (sq : G.PullbackObjObj f₁ f₃) (e : G ≅ G') :
    (e.hom.app (op Y₁)).app X₃ ≫ (sq.ofNatIso e).π = sq.π :=
  Iso.hom_inv_id_app_app_assoc e (op Y₁) X₃ sq.π

/-- Apply a pullback-preserving functor `H` to a `Functor.PullbackObjObj` square. -/
-- Exposed so `(sq.map H).pt` reduces to `H.obj sq.pt` in the types of `fst`, `snd`, and `π`.
@[expose]
noncomputable def map (sq : G.PullbackObjObj f₁ f₃) (H : C₂ ⥤ C₂')
    [PreservesLimit (cospan ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)) H] :
    (G ⋙ (whiskeringRight C₃ C₂ C₂').obj H).PullbackObjObj f₁ f₃ where
  pt := H.obj sq.pt
  fst := H.map sq.fst
  snd := H.map sq.snd
  isPullback := sq.isPullback.map H
  π := H.map sq.π
  π_fst := by simp [← H.map_comp]
  π_snd := by simp [← H.map_comp]

/-- Mapping a `Functor.PullbackObjObj` square by `H` applies `H` to the pullback object. -/
@[simp]
lemma map_pt (sq : G.PullbackObjObj f₁ f₃) (H : C₂ ⥤ C₂')
    [PreservesLimit (cospan ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)) H] :
    (sq.map H).pt = H.obj sq.pt := (rfl)

/-- Mapping a `Functor.PullbackObjObj` square by `H` applies `H` to the first projection. -/
@[simp]
lemma map_fst (sq : G.PullbackObjObj f₁ f₃) (H : C₂ ⥤ C₂')
    [PreservesLimit (cospan ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)) H] :
    (sq.map H).fst = H.map sq.fst := (rfl)

/-- Mapping a `Functor.PullbackObjObj` square by `H` applies `H` to the second projection. -/
@[simp]
lemma map_snd (sq : G.PullbackObjObj f₁ f₃) (H : C₂ ⥤ C₂')
    [PreservesLimit (cospan ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)) H] :
    (sq.map H).snd = H.map sq.snd := (rfl)

/-- Mapping a `Functor.PullbackObjObj` square by `H` applies `H` to the corner map. -/
@[simp]
lemma map_π (sq : G.PullbackObjObj f₁ f₃) (H : C₂ ⥤ C₂')
    [PreservesLimit (cospan ((G.obj (op X₁)).map f₃) ((G.map f₁.op).app Y₃)) H] :
    (sq.map H).π = H.map sq.π := (rfl)

/-- Reinterpret a `Functor.PullbackObjObj` square for `G` precomposed in its covariant variable
by `L : C₃' ⥤ C₃` as a `Functor.PullbackObjObj` square for `G` along `L.map f₃'`. -/
-- Exposed so `sq.ofWhiskeringLeft.pt` reduces to `sq.pt` in the types of `fst`, `snd`, and `π`.
@[expose]
def ofWhiskeringLeft {L : C₃' ⥤ C₃} {X₃' Y₃' : C₃'} {f₃' : X₃' ⟶ Y₃'}
    (sq : (G ⋙ (whiskeringLeft C₃' C₃ C₂).obj L).PullbackObjObj f₁ f₃') :
    G.PullbackObjObj f₁ (L.map f₃') where
  pt := sq.pt
  fst := sq.fst
  snd := sq.snd
  isPullback := sq.isPullback
  π := sq.π
  π_fst := sq.π_fst
  π_snd := sq.π_snd

/-- Reinterpreting a precomposed `Functor.PullbackObjObj` square keeps the same pullback object. -/
@[simp]
lemma ofWhiskeringLeft_pt {L : C₃' ⥤ C₃} {X₃' Y₃' : C₃'} {f₃' : X₃' ⟶ Y₃'}
    (sq : (G ⋙ (whiskeringLeft C₃' C₃ C₂).obj L).PullbackObjObj f₁ f₃') :
    sq.ofWhiskeringLeft.pt = sq.pt := (rfl)

/-- Reinterpreting a precomposed `Functor.PullbackObjObj` square keeps the first projection. -/
@[simp]
lemma ofWhiskeringLeft_fst {L : C₃' ⥤ C₃} {X₃' Y₃' : C₃'} {f₃' : X₃' ⟶ Y₃'}
    (sq : (G ⋙ (whiskeringLeft C₃' C₃ C₂).obj L).PullbackObjObj f₁ f₃') :
    sq.ofWhiskeringLeft.fst = sq.fst := (rfl)

/-- Reinterpreting a precomposed `Functor.PullbackObjObj` square keeps the second projection. -/
@[simp]
lemma ofWhiskeringLeft_snd {L : C₃' ⥤ C₃} {X₃' Y₃' : C₃'} {f₃' : X₃' ⟶ Y₃'}
    (sq : (G ⋙ (whiskeringLeft C₃' C₃ C₂).obj L).PullbackObjObj f₁ f₃') :
    sq.ofWhiskeringLeft.snd = sq.snd := (rfl)

/-- Reinterpreting a precomposed `Functor.PullbackObjObj` square keeps the corner map. -/
@[simp]
lemma ofWhiskeringLeft_π {L : C₃' ⥤ C₃} {X₃' Y₃' : C₃'} {f₃' : X₃' ⟶ Y₃'}
    (sq : (G ⋙ (whiskeringLeft C₃' C₃ C₂).obj L).PullbackObjObj f₁ f₃') :
    sq.ofWhiskeringLeft.π = sq.π := (rfl)

/-- Reinterpret a `Functor.PullbackObjObj` square for `K.op ⋙ G` as a `Functor.PullbackObjObj`
square for `G` along `K.map f₁'`. -/
-- Exposed so `sq.ofOpComp.pt` reduces to `sq.pt` in the types of `fst`, `snd`, and `π`.
@[expose]
def ofOpComp {K : C₁' ⥤ C₁} {X₁' Y₁' : C₁'} {f₁' : X₁' ⟶ Y₁'}
    (sq : (K.op ⋙ G).PullbackObjObj f₁' f₃) :
    G.PullbackObjObj (K.map f₁') f₃ where
  pt := sq.pt
  fst := sq.fst
  snd := sq.snd
  isPullback := sq.isPullback
  π := sq.π
  π_fst := sq.π_fst
  π_snd := sq.π_snd

/-- Reinterpreting a contravariantly precomposed `Functor.PullbackObjObj` square keeps the same
pullback object. -/
@[simp]
lemma ofOpComp_pt {K : C₁' ⥤ C₁} {X₁' Y₁' : C₁'} {f₁' : X₁' ⟶ Y₁'}
    (sq : (K.op ⋙ G).PullbackObjObj f₁' f₃) :
    sq.ofOpComp.pt = sq.pt := (rfl)

/-- Reinterpreting a contravariantly precomposed `Functor.PullbackObjObj` square keeps the first
projection. -/
@[simp]
lemma ofOpComp_fst {K : C₁' ⥤ C₁} {X₁' Y₁' : C₁'} {f₁' : X₁' ⟶ Y₁'}
    (sq : (K.op ⋙ G).PullbackObjObj f₁' f₃) :
    sq.ofOpComp.fst = sq.fst := (rfl)

/-- Reinterpreting a contravariantly precomposed `Functor.PullbackObjObj` square keeps the second
projection. -/
@[simp]
lemma ofOpComp_snd {K : C₁' ⥤ C₁} {X₁' Y₁' : C₁'} {f₁' : X₁' ⟶ Y₁'}
    (sq : (K.op ⋙ G).PullbackObjObj f₁' f₃) :
    sq.ofOpComp.snd = sq.snd := (rfl)

/-- Reinterpreting a contravariantly precomposed `Functor.PullbackObjObj` square keeps the corner
map. -/
@[simp]
lemma ofOpComp_π {K : C₁' ⥤ C₁} {X₁' Y₁' : C₁'} {f₁' : X₁' ⟶ Y₁'}
    (sq : (K.op ⋙ G).PullbackObjObj f₁' f₃) :
    sq.ofOpComp.π = sq.π := (rfl)

end CategoryTheory.Functor.PullbackObjObj

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor.RestrictionComparison
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Extension and restriction on slice sites

The extension comparison applies to `Over.map` on a site whose object universe is larger
than its arrow and coefficient universes. These examples also compute its generator formula
at an actual object of the slice, retaining an arbitrary equivariant sheaf identification.
-/

public section

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Sheaf
universe u

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  {U V : C} (f : V ⟶ U) {G H : Sheaf (J.over U) GrpCat.{u}}
  (P : Torsor G) (φ : G ⟶ H)
  [HasWeakSheafify (J.over U) (Type u)] [(J.over U).WEqualsLocallyBijective (Type u)]
  [HasWeakSheafify (J.over V) (Type u)] [(J.over V).WEqualsLocallyBijective (Type u)]
  (P' : Torsor ((J.overMapPullback GrpCat.{u} f).obj G))
  (e : P'.sheaf ≅ (J.overMapPullback (Type u) f).obj P.sheaf)
  (he : ∀ (T : (Over V)ᵒᵖ)
    (g : ((J.overMapPullback GrpCat.{u} f).obj G).obj.obj T)
    (p : P'.sheaf.obj.obj T),
    e.hom.hom.app T (g • p) = (P.mulAction ((Over.map f).op.obj T)).smul g
      (e.hom.hom.app T p))

example : P'.map ((J.overMapPullback GrpCat.{u} f).map φ) ≅
    P.mapRestrict (Over.map f) φ P' e.hom :=
  P.mapRestrictIso (Over.map f) φ P' e.hom he

example (T : C) (t : T ⟶ V) (p : P'.sheaf.obj.obj (op (Over.mk t))) :
    (P.mapRestrictIso (Over.map f) φ P' e.hom he).hom.hom.hom.app (op (Over.mk t))
        ((P'.toMap ((J.overMapPullback GrpCat.{u} f).map φ)).hom.app (op (Over.mk t)) p) =
      (P.toMap φ).hom.app (op (Over.mk (t ≫ f)))
        (e.hom.hom.app (op (Over.mk t)) p) := by
  exact congrArg (fun k ↦ k.hom.app (op (Over.mk t)) p)
    (P.toMap_mapRestrictIso_hom (Over.map f) φ P' e.hom he)

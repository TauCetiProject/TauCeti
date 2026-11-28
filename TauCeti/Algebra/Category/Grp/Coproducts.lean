/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.DirectSum.Basic

import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Direct-sum coproducts in `AddCommGrpCat`

This file complements `Mathlib.Algebra.Category.Grp.Limits` with the explicit identification of
indexed coproducts in `AddCommGrpCat` via external direct sums (the abelian-group counterpart of
`Mathlib.Algebra.Category.ModuleCat.Products`):

* `AddCommGrpCat.coproductCocone` and `AddCommGrpCat.coproductCoconeIsColimit` show that the
  external direct sum `⨁ j, f j`, equipped with the summand inclusions `DirectSum.of`, is a
  coproduct in `AddCommGrpCat`.
* `AddCommGrpCat.coprodIsoDirectSum` identifies the categorical coproduct `∐ f` with `⨁ j, f j`,
  compatibly with `Sigma.ι` and `DirectSum.of`.
-/

public section

open CategoryTheory Limits
open scoped DirectSum

universe w u

namespace AddCommGrpCat

variable {J : Type w} (f : J → AddCommGrpCat.{max w u}) [DecidableEq J]

/-- The coproduct cofan on a family of abelian groups given by their external direct sum. -/
@[expose]
def coproductCocone : Cofan f :=
  Cofan.mk (of (⨁ j, f j)) fun j ↦ ofHom (DirectSum.of (fun j ↦ f j) j)

@[simp]
theorem coproductCocone_pt : (coproductCocone f).pt = of (⨁ j, f j) := (rfl)

@[simp]
theorem coproductCocone_inj (j : J) :
    (coproductCocone f).inj j = ofHom (DirectSum.of (fun j ↦ f j) j) := (rfl)

/-- The external direct sum, with its canonical summand inclusions `DirectSum.of`, is a coproduct
in `AddCommGrpCat`. -/
noncomputable def coproductCoconeIsColimit : IsColimit (coproductCocone f) :=
  let fM : J → ModuleCat.{max w u} ℤ := fun j ↦ ModuleCat.of ℤ (f j)
  let F := forget₂ (ModuleCat.{max w u} ℤ) AddCommGrpCat.{max w u}
  let iso : Discrete.functor fM ⋙ F ≅ Discrete.functor f :=
    Discrete.natIso fun ⟨j⟩ ↦ Iso.refl (f j)
  let hcM := isColimitOfPreserves F (ModuleCat.coproductCoconeIsColimit fM)
  IsColimit.ofIsoColimit ((IsColimit.precomposeInvEquiv iso _).symm hcM) <|
    Cocone.ext (Iso.refl _) fun ⟨j⟩ ↦ by
      ext x
      simp only [iso, F, Functor.mapCocone_ι_app, Cocone.precompose_obj_ι, NatTrans.comp_app,
        Discrete.natIso_inv_app, Iso.refl_hom, Category.comp_id, ModuleCat.coproductCocone,
        Cofan.mk_ι_app, coproductCocone]
      exact DirectSum.lof_eq_of ℤ J (fun j ↦ f j) j x

@[simp]
theorem coproductCoconeIsColimit_desc (s : Cofan f) :
    (coproductCoconeIsColimit f).desc s =
      ofHom (DirectSum.toAddMonoid fun j ↦ (s.ι.app ⟨j⟩).hom) := by
  refine hom_ext <| DirectSum.addHom_ext fun j x ↦ ?_
  have hfac := congrArg (fun φ : f j ⟶ s.pt ↦ φ x) ((coproductCoconeIsColimit f).fac s ⟨j⟩)
  simpa only [hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, coproductCocone,
    Cofan.mk_ι_app, hom_ofHom, DirectSum.toAddMonoid_of] using hfac

variable [HasCoproduct f]

/-- The categorical coproduct of a family of abelian groups is isomorphic to their external direct
sum. -/
noncomputable def coprodIsoDirectSum : ∐ f ≅ of (⨁ j, f j) :=
  colimit.isoColimitCocone ⟨_, coproductCoconeIsColimit f⟩

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem ι_coprodIsoDirectSum_hom (j : J) :
    Sigma.ι f j ≫ (coprodIsoDirectSum f).hom = ofHom (DirectSum.of (fun j ↦ f j) j) :=
  colimit.isoColimitCocone_ι_hom ⟨_, coproductCoconeIsColimit f⟩ ⟨j⟩

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem of_coprodIsoDirectSum_inv (j : J) :
    ofHom (DirectSum.of (fun j ↦ f j) j) ≫ (coprodIsoDirectSum f).inv = Sigma.ι f j :=
  (coproductCoconeIsColimit f).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨j⟩

end AddCommGrpCat

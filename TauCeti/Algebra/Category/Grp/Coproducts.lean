/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Direct sums as coproducts in `AddCommGrpCat`

In `AddCommGrpCat`, the categorical coproduct of an indexed family `Z : ι → AddCommGrpCat` is
represented by the direct sum `⨁ i, Z i` equipped with the canonical inclusions
`DirectSum.of _ i`. This mirrors `ModuleCat.coproductCocone` and `ModuleCat.coprodIsoDirectSum` in
`Mathlib.Algebra.Category.ModuleCat.Products`.

## Main definitions

* `AddCommGrpCat.coproductCocone`: the cofan on `Z` with apex `AddCommGrpCat.of (⨁ i, Z i)` and
  injections `DirectSum.of _ i`.
* `AddCommGrpCat.coproductCoconeIsColimit`: `coproductCocone Z` is a colimit cofan.
* `AddCommGrpCat.coprodIsoDirectSum`: the canonical isomorphism `∐ Z ≅ AddCommGrpCat.of (⨁ i, Z i)`.

## Main results

* `AddCommGrpCat.isColimit_cofan_iff_bijective`: a cofan `c` on `Z` is a colimit cofan if and only
  if `DirectSum.toAddMonoid (fun i ↦ (c.inj i).hom)` is bijective.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped DirectSum

universe v w

namespace AddCommGrpCat

variable {ι : Type v} [DecidableEq ι] (Z : ι → AddCommGrpCat.{max v w})

/-- The coproduct cofan on a family of abelian groups given by their direct sum. -/
abbrev coproductCocone : Cofan Z :=
  Cofan.mk (of (⨁ i : ι, Z i)) fun i ↦ ofHom (DirectSum.of (fun i ↦ Z i) i)

/-- The concrete direct-sum cofan in `AddCommGrpCat` is a colimit cofan. -/
def coproductCoconeIsColimit : IsColimit (coproductCocone Z) :=
  Cofan.IsColimit.mk (coproductCocone Z)
    (fun s ↦ ofHom <| DirectSum.toAddMonoid fun i ↦ (s.inj i).hom)
    (fun s i ↦ AddCommGrpCat.ext fun x ↦
      DirectSum.toAddMonoid_of (fun j ↦ (s.inj j).hom) i x)
    (fun s f hf ↦ by
      apply hom_ext
      refine DirectSum.addHom_ext fun i x ↦ ?_
      have h := ConcreteCategory.congr_hom (hf i) x
      simpa [DirectSum.toAddMonoid_of] using h)

@[simp]
lemma coproductCoconeIsColimit_desc (s : Cofan Z) :
    (coproductCoconeIsColimit Z).desc s =
      ofHom (DirectSum.toAddMonoid fun i ↦ (s.inj i).hom) := by
  rfl

/-- A cofan `c` on a family of abelian groups is a colimit cofan if and only if the induced
homomorphism from the direct sum is bijective. -/
theorem isColimit_cofan_iff_bijective {Z : ι → AddCommGrpCat.{max v w}} (c : Cofan Z) :
    Nonempty (IsColimit c) ↔
      Function.Bijective (DirectSum.toAddMonoid (β := fun i ↦ Z i) fun i ↦ (c.inj i).hom) := by
  set φ : (⨁ i : ι, Z i) →+ c.pt := DirectSum.toAddMonoid fun i ↦ (c.inj i).hom
  constructor
  · rintro ⟨hc⟩
    let e := (coproductCoconeIsColimit Z).coconePointUniqueUpToIso hc
    have hEq : ofHom φ = e.hom := by
      rw [← coproductCoconeIsColimit_desc]
      exact (coproductCoconeIsColimit Z).hom_ext fun j ↦ by
        rw [IsColimit.fac, IsColimit.comp_coconePointUniqueUpToIso_hom]
    have hbij : Function.Bijective e.hom.hom := e.addCommGroupIsoToAddEquiv.bijective
    simpa [← hEq] using hbij
  · intro hbij
    let e : of (⨁ i : ι, Z i) ≅ c.pt := (AddEquiv.ofBijective φ hbij).toAddCommGrpIso
    have hIso : IsIso ((coproductCoconeIsColimit Z).desc c) := by
      rw [coproductCoconeIsColimit_desc]
      exact (inferInstance : IsIso e.hom)
    exact ⟨IsColimit.ofPointIso (coproductCoconeIsColimit Z)⟩

/-- The categorical coproduct of a family of abelian groups is isomorphic to their direct sum. -/
def coprodIsoDirectSum [HasCoproduct Z] : ∐ Z ≅ of (⨁ i, Z i) :=
  colimit.isoColimitCocone ⟨_, coproductCoconeIsColimit Z⟩

@[reassoc (attr := simp)]
lemma ι_coprodIsoDirectSum_hom [HasCoproduct Z] (i : ι) :
    Sigma.ι Z i ≫ (coprodIsoDirectSum Z).hom = ofHom (DirectSum.of (fun i ↦ Z i) i) :=
  colimit.isoColimitCocone_ι_hom _ _

@[reassoc (attr := simp)]
lemma of_coprodIsoDirectSum_inv [HasCoproduct Z] (i : ι) :
    ofHom (DirectSum.of (fun i ↦ Z i) i) ≫ (coprodIsoDirectSum Z).inv = Sigma.ι Z i :=
  (coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) _

end AddCommGrpCat

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.SingleObj
public import TauCeti.GroupTheory.CompletedGroup.Basic

/-!
# Completed groups as section labels

The completed group of a tower is the automorphism group of the identity-transport section of
its one-object groupoids. Each component of a label is the corresponding finite-order
projection, so these labels combine with `CompletedGroup.map_projection` and the projection
rules for ordered products and reindexed maps.

The identification composes `CompletedGroup.sectionsSubgroupEquiv` with
`Functor.singleObjSectionAutEquiv`.

## Attribution

Adapted from `Mei/GroupTheory/CompletedGroup/Section.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author credit is retained; the file uses the requested Tau Ceti copyright header.
-/

public section

open CategoryTheory TauCeti TauCeti.CompletedGroup Opposite

universe w

namespace CategoryTheory.Functor

variable (F : ℕᵒᵖ ⥤ GrpCat.{w})

/-- A completed group is the automorphism group of the tower's identity-transport section. -/
noncomputable def completedGroupAutEquiv : completedGroup F ≃* Aut F.singleObjSection :=
  (sectionsSubgroupEquiv F).trans F.singleObjSectionAutEquiv

/-- The completed-group identification is the composition of the section-subgroup
identification with the one-object section-automorphism identification. -/
theorem completedGroupAutEquiv_def :
    completedGroupAutEquiv F =
      (sectionsSubgroupEquiv F).trans F.singleObjSectionAutEquiv := by
  rw [completedGroupAutEquiv]

/-- Each fiber arrow is the corresponding finite-order projection, at every object
of the opposite index category. -/
@[simp]
theorem completedGroupAutEquiv_hom_app (g : completedGroup F) (j : ℕᵒᵖ) :
    (completedGroupAutEquiv F g).asIso.hom.app j = projection j.unop g := by
  obtain ⟨k⟩ := j
  rw [completedGroupAutEquiv_def, MulEquiv.trans_apply, singleObjSectionAutEquiv_hom_app]
  exact sectionsSubgroupEquiv_apply_val F g (op k)

/-- Each inverse fiber arrow is the inverse of the corresponding finite-order projection. -/
@[simp]
theorem completedGroupAutEquiv_inv_app (g : completedGroup F) (j : ℕᵒᵖ) :
    (completedGroupAutEquiv F g).asIso.inv.app j = (projection j.unop g)⁻¹ := by
  simpa using completedGroupAutEquiv_hom_app F g⁻¹ j

/-- Recovering a completed group element from a label retains every finite projection. -/
@[simp]
theorem projection_completedGroupAutEquiv_symm (a : Aut F.singleObjSection) (k : ℕ) :
    projection k ((completedGroupAutEquiv F).symm a) = a.asIso.hom.app (op k) := by
  rw [completedGroupAutEquiv, MulEquiv.symm_trans_apply, projection_sectionsSubgroupEquiv_symm]
  exact F.singleObjSectionAutEquiv_symm_apply a (op k)

end CategoryTheory.Functor

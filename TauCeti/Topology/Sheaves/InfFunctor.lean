/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Intersecting with a fixed open

For an open subset `U` of a topological space, `W ↦ W ⊓ U` is a functor on open subsets. For a
sheaf `F`, the presheaf `W ↦ F(W ⊓ U)` is again a sheaf: it is the pushforward along the inclusion
of `U` of the restriction of `F` to `U`, and both operations preserve sheaves
(`TopCat.Sheaf.pushforward_sheaf_of_sheaf`, `TopCat.Presheaf.isSheaf_of_isOpenEmbedding`).

## Main definitions

* `TopologicalSpace.Opens.infFunctor U`: the functor `W ↦ W ⊓ U` on open subsets.

## Main results

* `TopCat.Presheaf.isSheaf_infFunctor_op_comp`: for a sheaf `F` and an open `U`, the presheaf
  `W ↦ F(W ⊓ U)` is a sheaf.
-/

public section

universe w v u

open CategoryTheory TopologicalSpace

/-- The functor `W ↦ W ⊓ U` on the open subsets of a topological space. -/
abbrev TopologicalSpace.Opens.infFunctor {α : Type*} [TopologicalSpace α] (U : Opens α) :
    Opens α ⥤ Opens α :=
  Monotone.functor (f := (· ⊓ U)) fun _ _ h ↦ inf_le_inf_right U h

@[simp]
theorem TopologicalSpace.Opens.infFunctor_obj {α : Type*} [TopologicalSpace α] (U W : Opens α) :
    (Opens.infFunctor U).obj W = W ⊓ U :=
  rfl

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}

/-- For a sheaf `F` and an open `U`, the presheaf `W ↦ F(W ⊓ U)` is a sheaf: it is the
pushforward along the inclusion `U ⟶ X` of the restriction of `F` to `U`. -/
theorem isSheaf_infFunctor_op_comp {F : X.Presheaf C} (hF : F.IsSheaf) (U : Opens X) :
    IsSheaf ((Opens.infFunctor U).op ⋙ F) := by
  have h := U.isOpenEmbedding
  refine isSheaf_of_iso (Functor.isoWhiskerRight (NatIso.op
    (NatIso.ofComponents (F := Opens.infFunctor U) (G := Opens.map U.inclusion' ⋙ h.functor)
      (fun W ↦ eqToIso (Opens.ext ?_)) (fun _ ↦ Subsingleton.elim _ _))) F)
    (Sheaf.pushforward_sheaf_of_sheaf (f := U.inclusion') (isSheaf_of_isOpenEmbedding h hF))
  ext x
  simp

end TopCat.Presheaf

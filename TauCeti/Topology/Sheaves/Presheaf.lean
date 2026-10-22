/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Restriction maps of presheaves

Composing restriction maps along inclusions of opens in both directions gives the identity after
any morphism into the starting section object, since the inclusions force the opens to be equal, and
two proofs of the same inclusion of opens give the same restriction map.

## Main results

* `TopCat.Presheaf.comp_map_comp_map_eq_self`: composing restriction maps along inclusions in both
  directions gives the identity after any morphism into the starting section object.
* `TopCat.Presheaf.map_homOfLE_congr`: two proofs of the same inclusion of opens give the same
  restriction map.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Presheaf

universe w v u

variable {C : Type u} [Category.{v} C] {T : TopCat.{w}}

/-- Composing restriction maps along inclusions of opens in both directions gives the identity
after any morphism into the starting section object, since those inclusions force the opens to be
equal. The sections are given by a morphism `a` into `F.obj (op V)`, so that the lemma applies by
`exact` even when the intermediate open is only definitionally equal to the one in the composite. -/
theorem comp_map_comp_map_eq_self {F : T.Presheaf C} {A : C} {V V' : Opens T}
    (a : A ⟶ F.obj (op V)) (i : op V ⟶ op V') (j : op V' ⟶ op V) :
    (a ≫ F.map i) ≫ F.map j = a := by
  rw [Category.assoc, ← F.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _), F.map_id, Category.comp_id]

/-- Two proofs of the same inclusion of open sets give the same restriction map. -/
theorem map_homOfLE_congr {F : T.Presheaf C} {U V : Opens T} (h h' : U ≤ V) :
    F.map (homOfLE h).op = F.map (homOfLE h').op := by
  rw [Subsingleton.elim h h']

end TopCat.Presheaf

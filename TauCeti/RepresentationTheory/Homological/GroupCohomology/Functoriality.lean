/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Functoriality of group cohomology

The map on group cohomology along the trivial homomorphism `1 : G →* H` factors through the
cohomology of the trivial group, so it vanishes in every positive degree. In degree one this is
Mathlib's `groupCohomology.map₁_one`.

## Main statements

* `TauCeti.groupCohomology.map_one_succ`: the map along the trivial homomorphism vanishes in
  positive degrees.
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- The map on cohomology along the trivial homomorphism vanishes in positive degrees, because it
factors through the cohomology of the trivial group. In degree one this is Mathlib's
`groupCohomology.map₁_one`. -/
@[simp]
theorem map_one_succ {H : Type u} [Group H] {B : Rep k H} {C : Rep k G}
    (φ : res (1 : G →* H) B ⟶ C) (n : ℕ) :
    map (1 : G →* H) φ (n + 1) = 0 := by
  have h := map_comp (1 : PUnit.{u + 1} →* H) (1 : G →* PUnit.{u + 1}) (𝟙 _) φ (n + 1)
  -- `1 : G →* H` factors through `PUnit`, whose positive-degree cohomology vanishes.
  have e : (resFunctor (1 : G →* PUnit.{u + 1})).map (𝟙 (res (1 : PUnit.{u + 1} →* H) B)) ≫ φ =
      φ := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.id_comp φ
  rw [e] at h
  -- `(1 : PUnit →* H).comp 1` is `1 : G →* H` by definition.
  refine (h : map (1 : G →* H) φ (n + 1) = _).trans ?_
  rw [(isZero_groupCohomology_succ_of_subsingleton _ n).eq_zero_of_tgt
    (map (1 : PUnit.{u + 1} →* H) (𝟙 _) (n + 1)), zero_comp]

end TauCeti.groupCohomology

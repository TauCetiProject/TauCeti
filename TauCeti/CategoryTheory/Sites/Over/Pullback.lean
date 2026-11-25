/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Over

/-!
# Restriction along a morphism of bases and comparison of topologies

Let `J` and `K` be Grothendieck topologies on `C` such that `K`-sheaves on the slices `Over X` are
`J`-sheaves, for instance a finer and a coarser topology on schemes. Every `K`-sheaf on `Over Y`
can be regarded as a `J`-sheaf, through the pushforward along the identity functor of `Over Y`.
This file shows that this comparison commutes with the restriction
`CategoryTheory.GrothendieckTopology.overMapPullback` of sheaves along a morphism `f : X ⟶ Y`.

For instance, a sheaf on the big fpqc site of a scheme `S`, regarded as an étale sheaf and then
restricted to the big étale site of a scheme `T` over `S`, is the restriction of the fpqc sheaf
to the big fpqc site of `T`, regarded as an étale sheaf.

## Main declarations

* `CategoryTheory.GrothendieckTopology.sheafPushforwardContinuousIdCompOverMapPullbackIso`: the
  comparison of `K`-sheaves with `J`-sheaves commutes with `overMapPullback`.
-/

public section

open CategoryTheory

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C] (J K : GrothendieckTopology C) (A : Type*) [Category* A]
  {X Y : C} (f : X ⟶ Y) [(𝟭 (Over X)).IsContinuous (J.over X) (K.over X)]
  [(𝟭 (Over Y)).IsContinuous (J.over Y) (K.over Y)]

/-- Regarding `K`-sheaves on `Over Y` as `J`-sheaves commutes with the restriction of sheaves
along `f : X ⟶ Y`: both composites send a `K`-sheaf `F` on `Over Y` to the presheaf
`U ↦ F (U ⟶ X ⟶ Y)` on `Over X`. -/
noncomputable def sheafPushforwardContinuousIdCompOverMapPullbackIso :
    (𝟭 (Over Y)).sheafPushforwardContinuous A (J.over Y) (K.over Y) ⋙ J.overMapPullback A f ≅
      K.overMapPullback A f ⋙ (𝟭 (Over X)).sheafPushforwardContinuous A (J.over X) (K.over X) :=
  -- Both composites are the pushforward along `Over.map f`, by definition.
  Iso.refl _

@[simp]
lemma sheafPushforwardContinuousIdCompOverMapPullbackIso_hom_app
    (F : Sheaf (K.over Y) A) :
    (sheafPushforwardContinuousIdCompOverMapPullbackIso J K A f).hom.app F = 𝟙 _ :=
  (rfl)

@[simp]
lemma sheafPushforwardContinuousIdCompOverMapPullbackIso_inv_app
    (F : Sheaf (K.over Y) A) :
    (sheafPushforwardContinuousIdCompOverMapPullbackIso J K A f).inv.app F = 𝟙 _ :=
  (rfl)

end CategoryTheory.GrothendieckTopology

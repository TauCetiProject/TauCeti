/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Functors

/-!
# The sheaf condition along a homeomorphism

Mathlib's `TopCat.Sheaf.pushforward_sheaf_of_sheaf` says that the pushforward of a sheaf along a
continuous map is a sheaf. Along a homeomorphism the converse holds as well, since pushing forward
along the inverse undoes the pushforward. This file records the resulting criterion: a presheaf
isomorphic to the pushforward of another along a homeomorphism is a sheaf exactly when the other
is.

It also records that the restriction maps of Mathlib's restriction of a sheaf along an open
embedding, `Topology.IsOpenEmbedding.sheafPullback`, are restriction maps of the original sheaf
between the image opens.

## Main results

* `TopCat.Presheaf.isSheaf_iff_of_iso_pushforward`: the sheaf condition transfers along an
  isomorphism with a pushforward along a homeomorphism, in both directions.
* `Topology.IsOpenEmbedding.sheafPullback_obj_obj_map`: the restriction maps of the restriction of
  a sheaf along an open embedding.
-/

public section

universe w v u

open CategoryTheory TopologicalSpace

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X Y : TopCat.{w}}

/-- **The sheaf condition transfers along a homeomorphism.** If `F` is isomorphic to the pushforward
of `G` along a homeomorphism `h`, then `F` is a sheaf exactly when `G` is. -/
theorem isSheaf_iff_of_iso_pushforward (h : Y ≅ X) {F : X.Presheaf C} {G : Y.Presheaf C}
    (α : F ≅ (pushforward C h.hom).obj G) : F.IsSheaf ↔ G.IsSheaf := by
  refine ⟨fun hF ↦ ?_, fun hG ↦ isSheaf_of_iso α.symm (Sheaf.pushforward_sheaf_of_sheaf _ hG)⟩
  -- `G` is the pushforward of `F` along the inverse homeomorphism
  exact isSheaf_of_iso ((pushforward C h.inv).mapIso α ≪≫ (Pushforward.comp h.hom h.inv G).symm ≪≫
      pushforwardEq h.hom_inv_id G ≪≫ Pushforward.id G)
    (Sheaf.pushforward_sheaf_of_sheaf h.inv hF)

end TopCat.Presheaf

namespace Topology.IsOpenEmbedding

open TopCat

/-- The restriction maps of the restriction of a sheaf along an open embedding are restriction maps
of the original sheaf between the image opens. -/
theorem sheafPullback_obj_obj_map {C : Type u} [Category.{w} C] {X Y : TopCat.{w}} {f : Y ⟶ X}
    (hf : IsOpenEmbedding f) (F : Sheaf C X) {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    ((hf.sheafPullback C).obj F).obj.map i = F.obj.map (hf.functor.map i.unop).op :=
  rfl

end Topology.IsOpenEmbedding

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Products of covering maps

Products of evenly covered neighborhoods give evenly covered neighborhoods of the product map.
Consequently products of covering maps are covering maps, including nonsurjective coverings.
-/

public section

open Set Topology

variable {E X F Y A B : Type*}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace F] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B] {f : E → X} {g : F → Y} {x : X} {y : Y}

/-- A product of evenly covered points is evenly covered, with the product of the sheet spaces. -/
theorem IsEvenlyCovered.prodMap (hf : IsEvenlyCovered f x A) (hg : IsEvenlyCovered g y B) :
    IsEvenlyCovered (Prod.map f g) (x, y) (A × B) := by
  rcases hf with ⟨hA, U, hx, hU, hfU, H, hH⟩
  rcases hg with ⟨hB, V, hy, hV, hgV, K, hK⟩
  let := hA
  let := hB
  refine ⟨inferInstance, U ×ˢ V, ⟨hx, hy⟩, hU.prod hV, hfU.prod hgV, ?_, ?_⟩
  · exact (Homeomorph.Set.prod (f ⁻¹' U) (g ⁻¹' V)).trans
      ((H.prodCongr K).trans ((Homeomorph.prodProdProdComm U A V B).trans
        ((Homeomorph.Set.prod U V).symm.prodCongr (Homeomorph.refl (A × B)))))
  · intro z
    exact Prod.ext (hH ⟨z.1.1, z.2.1⟩) (hK ⟨z.1.2, z.2.2⟩)

/-- Products of covering maps are covering maps. Surjectivity of the factors is not required. -/
theorem IsCoveringMap.prodMap (hf : IsCoveringMap f) (hg : IsCoveringMap g) :
    IsCoveringMap (Prod.map f g) :=
  fun z ↦ ((hf z.1).prodMap (hg z.2)).to_isEvenlyCovered_preimage

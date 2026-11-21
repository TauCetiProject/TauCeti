/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.CoordinateHom
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Equivalence

/-!
# Fibrewise bijectivity isomorphism criterion for variable-rank vector bundles

Over a complete scalar field `[CompleteSpace 𝕜]`, a morphism in `TauCeti.FiniteRankVectorBundle 𝕜 X`
is a categorical isomorphism if and only if it is bijective on every fibre
(`FiniteRankVectorBundle.isIso_iff_bijective`), deduced via `toAtlasFunctor` from
`FiniteRankAtlas.isIso_iff_bijective`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankVectorBundle

universe u v w

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]
  {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}

/-- Over a complete scalar field `𝕜`, a morphism of variable-rank vector bundles is an isomorphism
if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective [CompleteSpace 𝕜] (f : V ⟶ W) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  have hIso : IsIso f ↔ IsIso ((toAtlasFunctor.{u, v, w} 𝕜 X).map f) :=
    ⟨fun _ ↦ (toAtlasFunctor.{u, v, w} 𝕜 X).map_isIso f,
      fun _ ↦ isIso_of_fully_faithful (toAtlasFunctor.{u, v, w} 𝕜 X) f⟩
  rw [hIso, FiniteRankAtlas.isIso_iff_bijective]
  refine forall_congr' fun x ↦ ?_
  rw [coe_fiberMap_toAtlasFunctor_map, (W.preferredChartEquiv x).bijective.of_comp_iff',
    (V.preferredChartEquiv x).symm.bijective.of_comp_iff]

end TauCeti.FiniteRankVectorBundle

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Link.Basic
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Sphere

/-!
# Disjoint solid-torus neighbourhoods of links in the three-sphere

A finite family of pairwise disjoint `C²` embedded circles in the unit three-sphere has solid-torus
neighbourhoods with pairwise disjoint images. Each component has a solid-torus neighbourhood
inside any prescribed neighbourhood of its image (`TauCeti.exists_isSolidTorusNeighborhood_sphere`),
so the general construction `TauCeti.exists_isSolidTorusLinkNeighborhood_of_forall_nhdsSet`
applies.

These neighbourhoods are the input for the exterior of a link in `S³`
(`TauCeti.linkExterior`) and for the Dehn surgeries on it (`TauCeti.LinkDehnFilling`), for
instance on the Whitehead link `TauCeti.whiteheadLink`.

## Main results

* `TauCeti.exists_isSolidTorusLinkNeighborhood_sphere`: disjoint solid-torus neighbourhoods of a
  finite family of pairwise disjoint `C²` embedded circles in `S³`.
* `TauCeti.SmoothLinkEmbedding.exists_isSolidTorusLinkNeighborhood_sphere`: the same for a smooth
  link presentation in `S³`.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Sections 2E and 9F.
-/

public section

open Function Manifold Metric Module Set
open scoped Manifold

namespace TauCeti

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 3 + 1)]

/-- A finite family of pairwise disjoint `C²` embedded circles in a unit three-sphere has pairwise
disjoint solid-torus neighbourhoods. -/
theorem exists_isSolidTorusLinkNeighborhood_sphere [Finite ι]
    {f : ι → Circle → sphere (0 : E) 1} (hf : ∀ i, ContMDiff (𝓡 1) (𝓡 3) 2 (f i))
    (himm : ∀ i z, Injective (mfderiv (𝓡 1) (𝓡 3) (f i) z)) (hinj : ∀ i, Injective (f i))
    (hdisj : Pairwise (Disjoint on fun i => range (f i))) :
    ∃ Φ : ι → SolidTorus → sphere (0 : E) 1, IsSolidTorusLinkNeighborhood f Φ :=
  exists_isSolidTorusLinkNeighborhood_of_forall_nhdsSet hdisj fun i _ hU =>
    exists_isSolidTorusNeighborhood_sphere (hf i) (himm i) (hinj i) hU

/-- A smooth link presentation in a unit three-sphere admits pairwise disjoint solid-torus
neighbourhoods of all its labeled components. -/
theorem SmoothLinkEmbedding.exists_isSolidTorusLinkNeighborhood_sphere {n : ℕ}
    (L : SmoothLinkEmbedding (𝓡 3) (sphere (0 : E) 1) n) :
    ∃ Φ : Fin n → SolidTorus → sphere (0 : E) 1,
      IsSolidTorusLinkNeighborhood (fun i => L i) Φ :=
  TauCeti.exists_isSolidTorusLinkNeighborhood_sphere
    (fun i => (L i).contMDiff.of_le (by simp))
    (fun i z => (L i).isImmersion.mfderiv_injective (by simp) z)
    (fun i => (L i).isEmbedding.injective) L.pairwiseDisjoint_range

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Link.Sphere
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Orientation

/-!
# Orientation-preserving solid torus neighbourhoods of links in the three-sphere

A finite family of pairwise disjoint `C²` embedded circles in the unit three-sphere of a
four-dimensional real inner product space `E` has solid torus neighbourhoods with pairwise disjoint
images, each preserving a given orientation of `E` at its core point
(`TauCeti.IsOrientationPreservingAtCore`). Each component has such a neighbourhood inside any
prescribed neighbourhood of its image
(`TauCeti.exists_isSolidTorusNeighborhood_isOrientationPreservingAtCore`), so the general
construction `TauCeti.exists_isSolidTorusLinkNeighborhood_of_forall_nhdsSet` applies. These are
the neighbourhoods in which surgery coefficients on a link in `S³` have their usual orientation
conventions.

## Main results

* `TauCeti.exists_isSolidTorusLinkNeighborhood_isOrientationPreservingAtCore`: disjoint
  orientation-preserving solid torus neighbourhoods of a finite family of pairwise disjoint `C²`
  embedded circles in `S³`.
* `TauCeti.SmoothLinkEmbedding.exists_isSolidTorusLinkNeighborhood_isOrientationPreservingAtCore`:
  the same for a smooth link presentation in `S³`.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Sections 2E, 9F and 9G.
-/

public section

open Function Manifold Metric Module Set
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 4)]

/-- A finite family of pairwise disjoint `C²` embedded circles in the unit three-sphere of `E` has
solid torus neighbourhoods with pairwise disjoint images, each preserving a given orientation of `E`
at its core point. -/
theorem exists_isSolidTorusLinkNeighborhood_isOrientationPreservingAtCore {ι : Type*} [Finite ι]
    {f : ι → Circle → sphere (0 : E) 1} (hf : ∀ i, ContMDiff (𝓡 1) (𝓡 3) 2 (f i))
    (himm : ∀ i z, Injective (mfderiv (𝓡 1) (𝓡 3) (f i) z)) (hinj : ∀ i, Injective (f i))
    (hdisj : Pairwise (Disjoint on fun i => range (f i))) (o : Orientation ℝ E (Fin 4)) :
    ∃ Φ : ι → SolidTorus → sphere (0 : E) 1,
      IsSolidTorusLinkNeighborhood f Φ ∧ ∀ i, IsOrientationPreservingAtCore (Φ i) o :=
  exists_isSolidTorusLinkNeighborhood_of_forall_nhdsSet hdisj fun i _ hU =>
    (exists_isSolidTorusNeighborhood_isOrientationPreservingAtCore (hf i) (himm i) (hinj i) hU
      o).imp fun _ h => ⟨h.1, h.2.2, h.2.1⟩

/-- A smooth link presentation in the unit three-sphere of `E` has solid torus neighbourhoods of
its components with pairwise disjoint images, each preserving a given orientation of `E` at its
core point. -/
theorem SmoothLinkEmbedding.exists_isSolidTorusLinkNeighborhood_isOrientationPreservingAtCore
    {n : ℕ} (L : SmoothLinkEmbedding (𝓡 3) (sphere (0 : E) 1) n) (o : Orientation ℝ E (Fin 4)) :
    ∃ Φ : Fin n → SolidTorus → sphere (0 : E) 1,
      IsSolidTorusLinkNeighborhood (fun i => L i) Φ ∧ ∀ i, IsOrientationPreservingAtCore (Φ i) o :=
  TauCeti.exists_isSolidTorusLinkNeighborhood_isOrientationPreservingAtCore
    (fun i => (L i).contMDiff.of_le (by simp))
    (fun i z => (L i).isImmersion.mfderiv_injective (by simp) z)
    (fun i => (L i).isEmbedding.injective) L.pairwiseDisjoint_range o

end TauCeti

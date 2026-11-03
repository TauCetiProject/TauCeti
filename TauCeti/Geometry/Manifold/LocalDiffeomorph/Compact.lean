/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Topology.Covering.Compact

/-!
# Local diffeomorphisms out of closed manifolds

A local diffeomorphism `f : M → N` from a compact connected Hausdorff manifold, real or complex, to
a simply connected Hausdorff manifold is bijective, so by Mathlib's
`IsLocalDiffeomorph.diffeomorphOfBijective` it is a diffeomorphism, whose forward map is `f` by
`TauCeti.coe_diffeomorphOfBijective`. This is the topological statement
`IsLocalHomeomorph.bijective_of_compactSpace`, which applies because a manifold modelled on a real
normed space is locally path-connected, so a connected one is path-connected.

The unit sphere `Sⁿ` is simply connected for `n ≥ 2`, so every local diffeomorphism from a compact
connected manifold to `Sⁿ`, `n ≥ 2`, is a diffeomorphism. This is the step of the
Schoen–Yau argument which turns the developing map of a compact simply connected locally
conformally flat manifold, a conformal local diffeomorphism into `Sⁿ`, into a conformal
diffeomorphism with the round sphere: no injectivity of the developing map has to be established
beforehand. Neither the simple connectivity of `M` nor any conformal structure is used here.

## Main declarations

* `IsLocalDiffeomorph.bijective_of_compactSpace`: a local diffeomorphism from a compact connected
  manifold to a simply connected Hausdorff manifold is bijective.
* `IsLocalDiffeomorph.bijective_of_compactSpace_sphere`: a local diffeomorphism from a compact
  connected manifold to the unit sphere `Sⁿ`, `n ≥ 2`, is bijective.

## References

* R. Schoen and S.-T. Yau, *Conformally flat manifolds, Kleinian groups and scalar curvature*,
  Invent. Math. 92 (1988), 47–71.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 5.
-/

public section

open Function Metric Module
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [ConnectedSpace M] [T2Space M]
  {k : WithTop ℕ∞}

/-- **A local diffeomorphism from a closed connected manifold to a simply connected manifold is
bijective**, hence a diffeomorphism by `IsLocalDiffeomorph.diffeomorphOfBijective`. Both manifolds
are Hausdorff, and the source is compact and connected. The source model `E` also carries a real
normed-space structure, which makes the manifold locally path-connected and hence, being
connected, path-connected; this covers real and complex manifolds. -/
theorem _root_.IsLocalDiffeomorph.bijective_of_compactSpace {I : ModelWithCorners 𝕜 E H}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
    [SimplyConnectedSpace N]
    {f : M → N} (hf : IsLocalDiffeomorph I J k f) : Bijective f := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace (H := H) (M := M)
  have := pathConnectedSpace_iff_connectedSpace.mpr ‹ConnectedSpace M›
  exact hf.isLocalHomeomorph.bijective_of_compactSpace

/-- **A local diffeomorphism from a closed connected manifold to the unit sphere `Sⁿ`, `n ≥ 2`, is
bijective**, hence a diffeomorphism by `IsLocalDiffeomorph.diffeomorphOfBijective`. The sphere
carries Mathlib's stereographic atlas, and the source is compact, connected and Hausdorff. -/
theorem _root_.IsLocalDiffeomorph.bijective_of_compactSpace_sphere {I : ModelWithCorners ℝ E H}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ} [Fact (finrank ℝ F = n + 1)]
    (hn : 2 ≤ n) {f : M → sphere (0 : F) 1} (hf : IsLocalDiffeomorph I (𝓡 n) k f) :
    Bijective f :=
  have h2 : 2 < finrank ℝ F := by rw [(Fact.out : finrank ℝ F = n + 1)]; omega
  have : SimplyConnectedSpace (sphere (0 : F) 1) :=
    simplyConnectedSpace_sphere (by exact_mod_cast lt_rank_of_lt_finrank h2) 0 zero_le_one
  IsLocalDiffeomorph.bijective_of_compactSpace hf

end TauCeti

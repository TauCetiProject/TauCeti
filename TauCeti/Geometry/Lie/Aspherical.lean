/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Connectivity
public import TauCeti.Geometry.Lie.Interior

/-!
# Simply connected aspherical compact Lie groups

A compact Lie group is a compact manifold without boundary
(`ContMDiffMul.boundarylessManifold`), so it cannot be weakly contractible unless it is a single
point (`TauCeti.IsAspherical.subsingleton_of_boundarylessManifold`). Hence a compact Lie group that
is simply connected and aspherical is trivial
(`TauCeti.IsAspherical.subsingleton_of_contMDiffMul`).

For a compact connected Lie group `G` with a finite covering `T × K → G` by the product of a torus
`T` and a simply connected compact Lie group `K`, the covering and the torus change no homotopy
group in degree at least two. So if `G` is aspherical, then so is `K`, and `K` is trivial.

## Main results

* `TauCeti.IsAspherical.subsingleton_of_contMDiffMul`: a simply connected aspherical compact Lie
  group is trivial.
-/

public section

open scoped Manifold

universe w

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **A simply connected aspherical compact Lie group is trivial.** A compact Hausdorff group with
`Cⁿ` multiplication, `n ≥ 1`, modelled with corners on a finite-dimensional real normed space,
which is simply connected and aspherical has a single element. -/
theorem IsAspherical.subsingleton_of_contMDiffMul {G : Type w} [TopologicalSpace G] [T2Space G]
    [ChartedSpace H G] [Group G] {n : WithTop ℕ∞} [ContMDiffMul I n G] (hn : 1 ≤ n)
    [CompactSpace G] [SimplyConnectedSpace G] (hG : IsAspherical G 1) : Subsingleton G := by
  have := ContMDiffMul.of_le (I := I) (G := G) hn
  have := ContMDiffMul.boundarylessManifold (I := I) (G := G)
  exact hG.subsingleton_of_boundarylessManifold (I := I)

end TauCeti

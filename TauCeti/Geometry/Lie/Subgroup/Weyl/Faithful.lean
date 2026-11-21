/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
public import TauCeti.Geometry.Lie.Subgroup.Weyl.Group
import TauCeti.Geometry.Lie.Subgroup.Torus.Centralizer

/-!
# Faithful Weyl group actions

The Weyl group of a maximal torus in a compact connected finite-dimensional real Lie group
acts faithfully on the torus and on its Lie algebra. These are the existing conjugation and
adjoint actions of the normalizer quotient. The statements apply to arbitrary models with corners.

## Main results

* `TauCeti.Lie.IsMaximalTorus.normalizerQuotientMulAut_injective`: faithful action on the torus.
* `TauCeti.Lie.IsMaximalTorus.weylAdjointRepresentation_injective`: faithful adjoint action
  on the Lie algebra of the torus.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Corollary 4.52,
  p.206, and Section 6 (Analytic Weyl Group), p.207.
-/

public section

open scoped ContDiff Manifold
noncomputable section
namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [ConnectedSpace G]

include I in
/-- The normalizer quotient of a maximal torus acts faithfully on the torus. -/
theorem IsMaximalTorus.normalizerQuotientMulAut_injective {T : Subgroup G}
    (hT : IsMaximalTorus T) :
    let _ := hT.isTorus.isMulCommutative
    Function.Injective T.normalizerQuotientMulAut := by
  let _ := hT.isTorus.isMulCommutative
  exact T.normalizerQuotientMulAut_injective_iff.mpr (hT.centralizer_eq I).le

/-- The Weyl adjoint representation of a maximal torus is faithful on its Lie algebra. -/
theorem IsMaximalTorus.weylAdjointRepresentation_injective {T : Subgroup G}
    (hT : IsMaximalTorus T) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    let _ := hT.isTorus.isMulCommutative
    Function.Injective (T.weylAdjointRepresentation (I := I)) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ := hT.isTorus.isMulCommutative
  exact (T.weylAdjointRepresentation_injective_iff hT.isTorus.isClosed
    hT.isTorus.isConnected.isPreconnected).mpr (hT.centralizer_eq I).le

end TauCeti.Lie

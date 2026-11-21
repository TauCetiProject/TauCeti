/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
import TauCeti.Geometry.Lie.Adjoint.Representation.Stabilizer
import TauCeti.Geometry.Lie.Subgroup.OneParameter
import TauCeti.Geometry.Lie.Subgroup.Torus.Centralizer

/-!
# Connected adjoint and coadjoint stabilizers of compact connected Lie groups

Let `G` be a compact connected finite-dimensional real Lie group with Lie algebra `𝔤`. This file
proves that the stabilizer `Z_G(ξ) = {g | Ad_g ξ = ξ}` of every `ξ ∈ 𝔤` under the adjoint
representation is connected, and so is the stabilizer `G_ν = {g | Ad*_g ν = ν}` of every `ν ∈ 𝔤*`
under the coadjoint representation. These are the isotropy groups of the adjoint and coadjoint
orbits, which are therefore homogeneous spaces `G / Z_G(ξ)` and `G / G_ν` with connected isotropy.

For any Lie group, `Z_G(ξ)` is the centralizer of the closure `T_ξ` of the one-parameter subgroup
`t ↦ exp (t ξ)` (`TauCeti.Lie.closedOneParameterSubgroup`): an element commuting with every
`exp (t ξ)` commutes with their closure, since centralizers are closed
(`TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup`, in
`TauCeti.Geometry.Lie.Adjoint.Representation.Stabilizer`). In a compact group `T_ξ` is a torus,
and the centralizer of a torus in a compact connected Lie group is connected
(`TauCeti.Lie.IsTorus.isConnected_centralizer`).

For the coadjoint stabilizer, an `Ad`-invariant inner product `b` on `𝔤` identifies `𝔤` with `𝔤*`
equivariantly, so that `G_ν` is the adjoint stabilizer of the element `X` with `ν = b(X, ·)`
(`TauCeti.Lie.stabilizer_coadjointRepresentation_eq_stabilizer_adjointRepresentation`,
`TauCeti.Lie.exists_stabilizer_coadjointRepresentation_eq`, both in
`TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer`).

Connectedness of `G` is needed: in `O(2)` the stabilizer of `0 ∈ 𝔰𝔬(2)` is all of `O(2)`. The
statement is special to elements of the Lie algebra: in `SO(3)` the centralizer of the group
element `diag(1, -1, -1)` is a copy of `O(2)`, which is disconnected.

## Main results

* `TauCeti.Lie.isConnected_stabilizer_adjointRepresentation`: `Z_G(ξ)` is connected.
* `TauCeti.Lie.isConnected_stabilizer_coadjointRepresentation`: `G_ν` is connected.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter IV, § 2.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable [CompactSpace G]

omit [T2Space G] in
/-- **Adjoint stabilizers are connected.** In a compact connected finite-dimensional real Lie
group, the stabilizer `{g | Ad_g ξ = ξ}` of each `ξ` in the Lie algebra is connected. -/
theorem isConnected_stabilizer_adjointRepresentation [ConnectedSpace G]
    (ξ : GroupLieAlgebra I G) :
    IsConnected ((adjointRepresentation ℝ I G).stabilizer ξ : Set G) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  rw [stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup]
  exact (isTorus_closedOneParameterSubgroup ξ).isConnected_centralizer I

omit [T2Space G] in
/-- **Coadjoint stabilizers are connected.** In a compact connected finite-dimensional real Lie
group, the coadjoint stabilizer `G_ν = {g | Ad*_g ν = ν}` of each `ν` in the dual of the Lie
algebra is connected. -/
theorem isConnected_stabilizer_coadjointRepresentation [ConnectedSpace G]
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    IsConnected ((coadjointRepresentation ℝ I G).stabilizer ν : Set G) := by
  obtain ⟨X, hX⟩ := exists_stabilizer_coadjointRepresentation_eq ν
  rw [hX]
  exact isConnected_stabilizer_adjointRepresentation X

end TauCeti.Lie

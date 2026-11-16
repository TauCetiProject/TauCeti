/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.Geometry.Lie.Subgroup.Commutative
import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The adjoint stabilizer

For `Y` in the Lie algebra of a Lie group `G`, the **adjoint stabilizer**
`Z_G(Y) = {g ∈ G | Ad_g Y = Y}` is Mathlib's `Representation.stabilizer` of `Y` for
`TauCeti.Lie.continuousAdjointRepresentation`. This file identifies it with the centralizer of the
one-parameter subgroup `t ↦ exp (t Y)`, so it is a closed subgroup, and shows that a commutative
subgroup lies in the adjoint stabilizer of each element of its Lie algebra. The analogous facts
for the coadjoint representation are in
`TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer`.

## Main results

* `TauCeti.Lie.mem_stabilizer_continuousAdjointRepresentation_iff`: `g ∈ Z_G(Y)` exactly when
  `Ad_g Y = Y`.
* `TauCeti.Lie.stabilizer_continuousAdjointRepresentation_eq_centralizer`: `Z_G(Y)` is the
  centralizer of the one-parameter subgroup of `Y`.
* `TauCeti.Lie.isClosed_stabilizer_continuousAdjointRepresentation`: `Z_G(Y)` is closed.
* `TauCeti.Lie.le_stabilizer_continuousAdjointRepresentation`: a commutative subgroup lies in the
  adjoint stabilizer of each element of its Lie algebra.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- An element lies in the adjoint stabilizer `Z_G(Y)` of `Y` exactly when it fixes `Y`. -/
theorem mem_stabilizer_continuousAdjointRepresentation_iff {Y : LeftInvariantDerivation I G}
    {g : G} :
    g ∈ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y ↔
      Ad (I := I) g Y = Y := by
  rw [Representation.mem_stabilizer, ContRepresentation.toRepresentation_apply,
    continuousAdjointRepresentation_apply]

/-- **The adjoint stabilizer of `Y` is the centralizer of its one-parameter subgroup.** -/
theorem stabilizer_continuousAdjointRepresentation_eq_centralizer
    (Y : LeftInvariantDerivation I G) :
    (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y =
      Subgroup.centralizer (Set.range fun t : ℝ ↦ lieExp (I := I) (t • Y)) := by
  ext g
  rw [mem_stabilizer_continuousAdjointRepresentation_iff, Subgroup.mem_centralizer_iff,
    Set.forall_mem_range]
  refine ⟨fun h t ↦ ?_, fun h ↦ Ad_apply_eq_self_of_forall_commute fun t ↦ (h t).symm⟩
  rw [eq_comm, ← mul_inv_eq_iff_eq_mul, conj_lieExp, map_smul, h]

/-- **The adjoint stabilizer `Z_G(Y)` is a closed subgroup.** -/
theorem isClosed_stabilizer_continuousAdjointRepresentation (Y : LeftInvariantDerivation I G) :
    IsClosed ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y :
      Set G) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  rw [stabilizer_continuousAdjointRepresentation_eq_centralizer]
  exact Set.isClosed_centralizer _

/-- A commutative subgroup fixes every element of its Lie algebra, so it lies in the adjoint
stabilizer of each of them. -/
theorem le_stabilizer_continuousAdjointRepresentation {K : Subgroup G} [IsMulCommutative K]
    {Y : LeftInvariantDerivation I G} (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) K) :
    K ≤ (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y :=
  fun _ hg ↦ mem_stabilizer_continuousAdjointRepresentation_iff.mpr
    (Ad_apply_eq_self_of_mem_lieSubalgebraOfSubgroup hg hY)

end TauCeti.Lie

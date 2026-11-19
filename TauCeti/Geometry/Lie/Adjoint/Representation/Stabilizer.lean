/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import TauCeti.Geometry.Lie.Subgroup.OneParameter
import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
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

The same holds on the tangent Lie algebra `𝔤 = GroupLieAlgebra I G`, for the stabilizer of
`μ ∈ 𝔤` under `TauCeti.Lie.adjointRepresentation`. Conjugation by `g` carries `exp (t μ)` to
`exp (t Ad_g μ)`, so `Ad_g μ = μ` exactly when `g` commutes with every `exp (t μ)`; the converse
direction compares the initial velocities of the two lines. Since the centralizer of `g` is
closed, `g` then commutes with the whole closed one-parameter subgroup `T_μ`, the closure of
`{exp (t μ) | t ∈ ℝ}` (`TauCeti.Lie.closedOneParameterSubgroup`).

## Main results

* `TauCeti.Lie.mem_stabilizer_continuousAdjointRepresentation_iff`: `g ∈ Z_G(Y)` exactly when
  `Ad_g Y = Y`.
* `TauCeti.Lie.stabilizer_continuousAdjointRepresentation_eq_centralizer`: `Z_G(Y)` is the
  centralizer of the one-parameter subgroup of `Y`.
* `TauCeti.Lie.isClosed_stabilizer_continuousAdjointRepresentation`: `Z_G(Y)` is closed.
* `TauCeti.Lie.le_stabilizer_continuousAdjointRepresentation`: a commutative subgroup lies in the
  adjoint stabilizer of each element of its Lie algebra.
* `TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer`: on the tangent Lie algebra, the
  stabilizer of `μ` is the centralizer of `{exp (t μ) | t ∈ ℝ}`.
* `TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup`: it is
  the centralizer of the closed one-parameter subgroup `T_μ`.
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

/-! ### The adjoint stabilizer on the tangent Lie algebra -/

/-- **The adjoint stabilizer of `μ` is the centralizer of its one-parameter subgroup.** An element
`g` satisfies `Ad_g μ = μ` exactly when it commutes with every `exp (t μ)`. -/
theorem stabilizer_adjointRepresentation_eq_centralizer (μ : GroupLieAlgebra I G) :
    (adjointRepresentation ℝ I G).stabilizer μ =
      Subgroup.centralizer (Set.range fun t : ℝ ↦ mulInvariantExp (I := I) (t • μ)) := by
  ext g
  rw [Representation.mem_stabilizer, adjointRepresentation_apply, Subgroup.mem_centralizer_iff,
    Set.forall_mem_range]
  -- Conjugation by `g` carries the line `exp (t μ)` to the line `exp (t Ad_g μ)`.
  have hconj (t : ℝ) : g * mulInvariantExp (I := I) (t • μ) * g⁻¹ =
      mulInvariantExp (I := I) (t • adjointContinuousLinearMap (I := I) g μ) := by
    rw [conj_mulInvariantExp, tangentAd_apply, map_smul]
  refine ⟨fun h t ↦ ?_, fun h ↦ ?_⟩
  · rw [eq_comm, ← mul_inv_eq_iff_eq_mul, hconj, h]
  · -- Both lines agree, so their initial velocities `Ad_g μ` and `μ` agree.
    have hline : (fun t : ℝ ↦ mulInvariantExp (I := I) (t • adjointContinuousLinearMap
        (I := I) g μ)) = fun t : ℝ ↦ mulInvariantExp (I := I) (G := G) (t • μ) := by
      funext t
      rw [← hconj, ← h t, mul_inv_cancel_right]
    have h1 := DFunLike.congr_fun (hasMFDerivAt_unique
      (hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G)
        (adjointContinuousLinearMap (I := I) g μ))
      (hline ▸ hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) μ)) (1 : ℝ)
    -- `smulRight 1 X` sends `1` to `1 • X` by definition; as in
    -- `forall_mulInvariantExp_smul_eq_one_iff`, the rewriting lemmas do not fire through the
    -- tangent-space types, so the evaluation is read off definitionally.
    have h2 : (1 : ℝ) • adjointContinuousLinearMap (I := I) g μ = (1 : ℝ) • μ := h1
    rwa [one_smul, one_smul] at h2

section TopologicalGroup

variable [IsTopologicalGroup G]

/-- **The adjoint stabilizer of `μ` is the centralizer of its closed one-parameter subgroup**
`T_μ`, the closure of `{exp (t μ) | t ∈ ℝ}`. -/
theorem stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup
    (μ : GroupLieAlgebra I G) :
    (adjointRepresentation ℝ I G).stabilizer μ =
      Subgroup.centralizer (closedOneParameterSubgroup μ : Set G) := by
  rw [stabilizer_adjointRepresentation_eq_centralizer]
  refine le_antisymm (fun g hg ↦ ?_) (Subgroup.centralizer_le ?_)
  · -- The centralizer of `g` is a closed subgroup containing every `exp (t μ)`, hence `T_μ`.
    have hle : closedOneParameterSubgroup μ ≤ Subgroup.centralizer {g} :=
      (closedOneParameterSubgroup_le (Set.isClosed_centralizer {g})).2 fun t ↦
        Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hg _ (Set.mem_range_self t))
    exact Subgroup.mem_centralizer_iff.2 fun h hh ↦
      Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  · rintro _ ⟨t, rfl⟩
    exact mulInvariantExp_smul_mem_closedOneParameterSubgroup μ t

end TopologicalGroup

end TauCeti.Lie

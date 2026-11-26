/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import TauCeti.Geometry.Lie.Subgroup.OneParameter
import TauCeti.Geometry.Lie.Adjoint.Derivation
import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The adjoint stabilizer

For `Y` in the Lie algebra of a Lie group `G`, the **adjoint stabilizer**
`Z_G(Y) = {g ∈ G | Ad_g Y = Y}` is Mathlib's `Representation.stabilizer` of `Y` for
`TauCeti.Lie.continuousAdjointRepresentation`. This file identifies it with the centralizer of the
one-parameter subgroup `t ↦ exp (t Y)`, so it is a closed subgroup, and shows that a commutative
subgroup lies in the adjoint stabilizer of each element of its Lie algebra. The Lie algebra of
`Z_G(Y)` is the centralizer `{X | ⁅X, Y⁆ = 0}` of `Y`: the one-parameter subgroup of `X` fixes `Y`
exactly when `⁅X, Y⁆ = 0`, the derivative of `t ↦ Ad_(exp (t X)) Y` at `0`. The analogous facts
for the coadjoint representation are in
`TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer`.

The same holds on the tangent Lie algebra `𝔤 = GroupLieAlgebra I G`, for the stabilizer of
`μ ∈ 𝔤` under `TauCeti.Lie.adjointRepresentation`. Conjugation by `g` carries `exp (t μ)` to
`exp (t Ad_g μ)`, so `Ad_g μ = μ` exactly when `g` commutes with every `exp (t μ)`; this is
`TauCeti.Lie.stabilizer_continuousAdjointRepresentation_eq_centralizer`, read through evaluation at
the identity. Since the centralizer of `g` is closed, `g` then commutes with the whole closed
one-parameter subgroup `T_μ`, the closure of `{exp (t μ) | t ∈ ℝ}`
(`TauCeti.Lie.closedOneParameterSubgroup`).

## Main results

* `TauCeti.Lie.mem_stabilizer_continuousAdjointRepresentation_iff`: `g ∈ Z_G(Y)` exactly when
  `Ad_g Y = Y`.
* `TauCeti.Lie.stabilizer_continuousAdjointRepresentation_eq_centralizer`: `Z_G(Y)` is the
  centralizer of the one-parameter subgroup of `Y`.
* `TauCeti.Lie.isClosed_stabilizer_continuousAdjointRepresentation`: `Z_G(Y)` is closed.
* `TauCeti.Lie.lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation`: the Lie algebra
  of `Z_G(Y)` is the centralizer of `Y`.
* `TauCeti.Lie.le_stabilizer_continuousAdjointRepresentation`: a commutative subgroup lies in the
  adjoint stabilizer of each element of its Lie algebra.
* `TauCeti.Lie.stabilizer_continuousAdjointRepresentation_eq_stabilizer_adjointRepresentation`:
  `Z_G(Y)` is the stabilizer of the value of `Y` at the identity in the tangent Lie algebra.
* `TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer`: on the tangent Lie algebra, the
  stabilizer of `μ` is the centralizer of `{exp (t μ) | t ∈ ℝ}`.
* `TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup`: it is
  the centralizer of the closed one-parameter subgroup `T_μ`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, § 1.
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

/-- **The Lie algebra of the adjoint stabilizer is the centralizer.** A left-invariant derivation
`X` lies in the Lie algebra of `Z_G(Y) = {g | Ad_g Y = Y}` exactly when `⁅X, Y⁆ = 0`. -/
theorem lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation
    (Y : LeftInvariantDerivation I G) :
    lieSubalgebraOfSubgroup (I := I)
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y) =
      lieAnnihilator ℝ (LeftInvariantDerivation I G) Y := by
  ext X
  rw [mem_lieSubalgebraOfSubgroup (isClosed_stabilizer_continuousAdjointRepresentation Y),
    mem_lieAnnihilator]
  simp only [mem_stabilizer_continuousAdjointRepresentation_iff]
  refine ⟨fun h ↦ ?_, fun h t ↦ Ad_lieExp_smul_apply_eq_self_of_lie_eq_zero h t⟩
  -- Read at the identity, the curve `t ↦ Ad_(exp (t X)) Y` is constant, and its derivative at `0`
  -- is `⁅X, Y⁆`.
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  have hconst : (fun t : ℝ ↦ show E from
      tangentAd (I := I) (mulInvariantExp (I := I) (G := G) (t • e X)) (e Y)) =
        fun _ ↦ show E from e Y := by
    funext t
    have ht := congrArg e (h t)
    rwa [leftInvariantDerivationLieEquivGroupLieAlgebra_Ad, lieExp_eq_mulInvariantExp, map_smul,
      ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply] at ht
  have hderiv := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) (G := G) (e X) (e Y)
  dsimp only at hderiv
  rw [hconst] at hderiv
  have hzero : e ⁅X, Y⁆ = 0 := by
    rw [LieEquiv.map_lie, ← LieAlgebra.ad_apply ℝ]
    exact hderiv.unique (hasDerivAt_const 0 _)
  exact e.injective (hzero.trans (map_zero e).symm)

/-! ### The adjoint stabilizer on the tangent Lie algebra -/

/-- Evaluation at the identity identifies the adjoint stabilizer `Z_G(Y)` of a left-invariant
derivation with the stabilizer of its value `Y(1)` in the tangent Lie algebra. -/
theorem stabilizer_continuousAdjointRepresentation_eq_stabilizer_adjointRepresentation
    (Y : LeftInvariantDerivation I G) :
    (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer Y =
      (adjointRepresentation ℝ I G).stabilizer
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)) Y) := by
  ext g
  rw [mem_stabilizer_continuousAdjointRepresentation_iff, Representation.mem_stabilizer,
    adjointRepresentation_apply, ← tangentAd_apply,
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_Ad, EmbeddingLike.apply_eq_iff_eq]

/-- **The adjoint stabilizer of `μ` is the centralizer of its one-parameter subgroup.** An element
`g` satisfies `Ad_g μ = μ` exactly when it commutes with every `exp (t μ)`. -/
theorem stabilizer_adjointRepresentation_eq_centralizer (μ : GroupLieAlgebra I G) :
    (adjointRepresentation ℝ I G).stabilizer μ =
      Subgroup.centralizer (Set.range fun t : ℝ ↦ mulInvariantExp (I := I) (t • μ)) := by
  -- Transport `stabilizer_continuousAdjointRepresentation_eq_centralizer` along evaluation at
  -- the identity.
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  have hexp (t : ℝ) : lieExp (I := I) (t • e.symm μ) = mulInvariantExp (I := I) (t • μ) := by
    rw [lieExp_eq_mulInvariantExp, map_smul,
      ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply, e.apply_symm_apply]
  simp_rw [← hexp, ← stabilizer_continuousAdjointRepresentation_eq_centralizer]
  ext g
  rw [Representation.mem_stabilizer, adjointRepresentation_apply,
    mem_stabilizer_continuousAdjointRepresentation_iff, ← EquivLike.apply_eq_iff_eq e,
    leftInvariantDerivationLieEquivGroupLieAlgebra_Ad, e.apply_symm_apply, tangentAd_apply]

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

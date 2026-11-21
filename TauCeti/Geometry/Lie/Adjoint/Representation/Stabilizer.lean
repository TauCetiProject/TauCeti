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
import TauCeti.Geometry.Lie.Adjoint.Derivation
import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The adjoint stabilizer

For `Y` in the Lie algebra of a Lie group `G`, the **adjoint stabilizer**
`Z_G(Y) = {g ∈ G | Ad_g Y = Y}` is Mathlib's `Representation.stabilizer` of `Y` for
`TauCeti.Lie.continuousAdjointRepresentation`. This file identifies it with the centralizer of the
one-parameter subgroup `t ↦ exp (t Y)`, so it is a closed subgroup. For the adjoint
representation `TauCeti.Lie.adjointRepresentation` on `GroupLieAlgebra I G`, it identifies the
stabilizer of `ξ` with the centralizer of the closure `TauCeti.Lie.closedOneParameterSubgroup ξ`
of the one-parameter subgroup of `ξ`. It also shows that a commutative
subgroup lies in the adjoint stabilizer of each element of its Lie algebra. The analogous facts
for the coadjoint representation are in
`TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer`.

## Main results

* `TauCeti.Lie.mem_stabilizer_continuousAdjointRepresentation_iff`: `g ∈ Z_G(Y)` exactly when
  `Ad_g Y = Y`.
* `TauCeti.Lie.stabilizer_continuousAdjointRepresentation_eq_centralizer`: `Z_G(Y)` is the
  centralizer of the one-parameter subgroup of `Y`.
* `TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup`: the
  adjoint stabilizer `Z_G(ξ)` is the centralizer of the closure `T_ξ` of `t ↦ exp (t ξ)`.
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

/-- **The adjoint stabilizer is the centralizer of a closed one-parameter subgroup.** An element
`g` fixes `ξ` under the adjoint representation exactly when it commutes with the closure `T_ξ` of
the one-parameter subgroup `t ↦ exp (t ξ)`. -/
theorem stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup
    [IsTopologicalGroup G] (ξ : GroupLieAlgebra I G) :
    (adjointRepresentation ℝ I G).stabilizer ξ =
      Subgroup.centralizer (closedOneParameterSubgroup ξ : Set G) := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  have hexp (t : ℝ) : lieExp (I := I) (t • e.symm ξ) = mulInvariantExp (t • ξ) := by
    rw [lieExp_eq_mulInvariantExp, map_smul, ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
      LieEquiv.apply_symm_apply]
  have he (g : G) (D : LeftInvariantDerivation I G) :
      e (Ad (I := I) g D) = tangentAd (I := I) g (e D) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_Ad g D
  -- Through the identification of the Lie algebra with left-invariant derivations, this is the
  -- centralizer of the one-parameter subgroup itself; a centralizer is closed, so it is also the
  -- centralizer of the closure.
  have hstab : (adjointRepresentation ℝ I G).stabilizer ξ =
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (e.symm ξ) := by
    ext g
    rw [Representation.mem_stabilizer, adjointRepresentation_apply,
      mem_stabilizer_continuousAdjointRepresentation_iff, ← EmbeddingLike.apply_eq_iff_eq e, he,
      LieEquiv.apply_symm_apply, tangentAd_apply]
  rw [hstab, stabilizer_continuousAdjointRepresentation_eq_centralizer]
  refine le_antisymm (fun g hg ↦ ?_) (Subgroup.centralizer_le ?_)
  · have hle : closedOneParameterSubgroup ξ ≤ Subgroup.centralizer {g} :=
      (closedOneParameterSubgroup_le (Set.isClosed_centralizer _)).2 fun t ↦ by
        have h : lieExp (I := I) (t • e.symm ξ) * g = g * lieExp (I := I) (t • e.symm ξ) :=
          Subgroup.mem_centralizer_iff.1 hg _ ⟨t, rfl⟩
        rw [hexp] at h
        exact Subgroup.mem_centralizer_singleton_iff.2 h
    exact Subgroup.mem_centralizer_iff.2 fun k hk ↦
      Subgroup.mem_centralizer_singleton_iff.1 (hle hk)
  · rintro _ ⟨t, rfl⟩
    simp only [SetLike.mem_coe, hexp, mulInvariantExp_smul_mem_closedOneParameterSubgroup]

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

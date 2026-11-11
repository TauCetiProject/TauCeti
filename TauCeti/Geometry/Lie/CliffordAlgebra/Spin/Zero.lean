/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Topology.Algebra.CliffordAlgebra.Normed
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Zero

/-!
# The geometric rank-zero Spin group as an embedded Lie group

The even unitary group of `CliffordAlgebra (realCliffordForm 0 0)` is the two-element
scalar subgroup `μ₂`. Unlike native `Spin(0)`, which is trivial, this is the structure
group for rank-zero geometric spin lifts. We give this same subgroup of Clifford units
the smooth structure furnished by the closed-subgroup theorem, retaining its induced
topology. Its model and its Lie algebra are zero, and its inclusion in Clifford units
is a smooth embedding.

The carrier of the existing algebraic identification with `Multiplicative (ZMod 2)`
and double cover of the trivial special orthogonal group now has a discrete,
zero-dimensional Lie-group structure.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Q₀" => realCliffordForm 0 0
local notation "μ₂" => evenUnitaryGroup Q₀

/-- The geometric rank-zero Spin group is finite. -/
instance instFiniteEvenUnitaryGroupZero : Finite μ₂ := by
  have : Subsingleton (Fin (0 + 0) → ℝ) := by
    rw [Nat.add_zero]
    exact (Pi.uniqueOfIsEmpty _).instSubsingleton
  infer_instance

/-- The ambient one-parameter-subgroup model for the geometric rank-zero Spin group.
It is the zero subspace, as `evenUnitaryGroupZero_lieSubalgebra_eq_bot` proves. -/
abbrev evenUnitaryGroupZeroLieModel :=
  (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, CliffordAlgebra Q₀)) μ₂).toSubmodule

/-- The geometric rank-zero Spin subgroup is closed in Clifford units. -/
theorem isClosed_evenUnitaryGroupZero : IsClosed (μ₂ : Set (CliffordAlgebra Q₀)ˣ) :=
  (Set.finite_coe_iff.mp (inferInstanceAs (Finite μ₂))).isClosed

/-- The canonical ambient Lie algebra of the geometric rank-zero Spin group is zero. -/
@[simp]
theorem evenUnitaryGroupZero_lieSubalgebra_eq_bot :
    TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, CliffordAlgebra Q₀)) μ₂ = ⊥ :=
  (TauCeti.Lie.discreteTopology_iff_lieSubalgebraOfSubgroup_eq_bot
    (I := 𝓘(ℝ, CliffordAlgebra Q₀)) isClosed_evenUnitaryGroupZero).mp inferInstance

/-- The zero-dimensional model of the geometric rank-zero Spin group has just one vector. -/
instance instSubsingletonEvenUnitaryGroupZeroLieModel :
    Subsingleton evenUnitaryGroupZeroLieModel := by
  unfold evenUnitaryGroupZeroLieModel
  rw [evenUnitaryGroupZero_lieSubalgebra_eq_bot, LieSubalgebra.bot_toSubmodule]
  infer_instance

/-- The embedded smooth structure on the actual rank-zero even unitary subgroup of
Clifford units, selected by the closed-subgroup theorem. -/
def evenUnitaryGroupZeroEmbeddedLieSubgroupData :
    TauCeti.Lie.EmbeddedLieSubgroupData 𝓘(ℝ, CliffordAlgebra Q₀) μ₂
      evenUnitaryGroupZeroLieModel :=
  TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed isClosed_evenUnitaryGroupZero

/-- Charts on the geometric rank-zero Spin group, retaining its induced topology. -/
instance instChartedSpaceEvenUnitaryGroupZero : ChartedSpace evenUnitaryGroupZeroLieModel μ₂ :=
  evenUnitaryGroupZeroEmbeddedLieSubgroupData.chartedSpace

/-- The geometric rank-zero Spin group is a zero-dimensional real Lie group. -/
instance instLieGroupEvenUnitaryGroupZero : LieGroup 𝓘(ℝ, evenUnitaryGroupZeroLieModel) ∞ μ₂ :=
  evenUnitaryGroupZeroEmbeddedLieSubgroupData.lieGroup

/-- The actual Lie algebra of the geometric rank-zero Spin group is trivial. -/
instance instSubsingletonEvenUnitaryGroupZeroLieAlgebra :
    Subsingleton (LeftInvariantDerivation 𝓘(ℝ, evenUnitaryGroupZeroLieModel) μ₂) := by
  have : Subsingleton (TauCeti.Lie.lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, CliffordAlgebra Q₀)) μ₂) := by
    rw [evenUnitaryGroupZero_lieSubalgebra_eq_bot]
    exact LieSubalgebra.subsingleton_bot
  exact evenUnitaryGroupZeroEmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup.injective
    |>.subsingleton

/-- The inclusion of the geometric rank-zero Spin group in Clifford units is a smooth
embedding for the chosen closed-subgroup structure. -/
theorem isSmoothEmbedding_evenUnitaryGroupZero_subtypeVal :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, evenUnitaryGroupZeroLieModel) 𝓘(ℝ, CliffordAlgebra Q₀) ∞
      (fun g : μ₂ ↦ (g : (CliffordAlgebra Q₀)ˣ)) :=
  evenUnitaryGroupZeroEmbeddedLieSubgroupData.isSmoothEmbedding_subtypeVal

end TauCeti.CliffordAlgebra

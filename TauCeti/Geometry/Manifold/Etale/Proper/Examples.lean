/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Proper.Basic
public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid.Basic
public import TauCeti.Geometry.Manifold.Groupoid.Examples
import TauCeti.Topology.Algebra.ProperAction.Basic
import TauCeti.Topology.CategoryTheory.Groupoid.Constructions

/-!
# Proper étale presentations from manifolds and group actions

Unit groupoids present their underlying manifolds. For a smooth action of a discrete countable
group, properness of the action characterizes proper étaleness of its action groupoid. In
particular, smooth finite-group actions give proper étale presentations.
-/

public section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

namespace UnitGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- A manifold presents itself through its unit groupoid. -/
instance isProperEtaleGroupoid : IsProperEtaleGroupoid I I (Discrete M) where
  toIsLieGroupoid := inferInstance
  isLocalDiffeomorph_source := isLocalDiffeomorph_source
  isProperMap_source_target := isProperMap_source_target M

end UnitGroupoid

namespace ActionGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (G X : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] [MulAction G X]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [SecondCountableTopology X] [ContMDiffConstSMul I ∞ G X]

/-- A proper smooth action of a discrete countable group gives a proper étale presentation
with the source-pulled arrow atlas. -/
instance isProperEtaleGroupoid [Countable G] [ProperSMul G X] :
    IsProperEtaleGroupoid I I (ActionCategory G X) := by
  exact .of_isTopologicalGroupoid (isLocalDiffeomorph_source I ∞ G X)
    (isLocalDiffeomorph_target I ∞ G X) ((isProperMap_source_target_iff G X).2 inferInstance)

/-- The action groupoid of a smooth discrete countable group action is proper étale exactly
when the action is proper. -/
theorem isProperEtaleGroupoid_iff [Countable G] :
    IsProperEtaleGroupoid I I (ActionCategory G X) ↔ ProperSMul G X := by
  constructor
  · intro h
    exact (isProperMap_source_target_iff G X).1 h.isProperMap_source_target
  · intro h
    exact isProperEtaleGroupoid I G X

/-- A smooth action of a finite discrete group on a Hausdorff second-countable manifold gives
a proper étale presentation. -/
theorem isProperEtaleGroupoid_of_finite [Finite G] :
    IsProperEtaleGroupoid I I (ActionCategory G X) := by
  have := ContMDiffConstSMul.continuousConstSMul (I := I) ∞ (Γ := G) (M := X)
  have : ContinuousSMul G X := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  have := properSMul_of_compactSpace G X
  exact isProperEtaleGroupoid I G X

end ActionGroupoid

end TauCeti

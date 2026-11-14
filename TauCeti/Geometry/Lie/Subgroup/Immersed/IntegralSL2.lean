/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Countable.Examples
public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
public import TauCeti.Geometry.Manifold.Immersion.ZeroDimensional
public import TauCeti.Geometry.Manifold.Instances.Discrete
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The disconnected integral special-linear immersion

With its original discrete topology, `SL₂(ℤ)` has zero-dimensional smooth charts. Its usual
inclusion into `SL₂(ℝ)`, with the native real special-linear charts, is a smooth immersion.
Its injectivity is `SpecialLinearGroup.map_intCast_injective`, and
`mem_integralSL2Subgroup` identifies its image. The source is disconnected. The existing
`lieSubalgebraOfSubgroup_integralSL2Subgroup_eq_bot` and
`not_isImmersedLieSubgroup_integralSL2Subgroup` from `Countable/Examples.lean` compute the
image's canonical Lie algebra as zero and exclude a connected immersed presentation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Example 7.3(m) and Proposition 7.17.
-/

public section

open Matrix TauCeti.Lie
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie.IntegralSL2

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

local notation "E" => SpecialLinearGroup.Model (Fin 2) ℝ
local notation "G" => SpecialLinearGroup (Fin 2) ℝ

local notation "X" => SpecialLinearGroup (Fin 2) ℤ

/-- The discrete zero-dimensional charts on the integral special-linear group. -/
@[expose, instance_reducible]
def chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 0)) X := ChartedSpace.ofDiscreteTopology

attribute [local instance] chartedSpace

/-- The integral special-linear group is a zero-dimensional analytic manifold. -/
instance instIsManifold : IsManifold (𝓡 0) ω X := IsManifold.of_discreteTopology ω

/-- The integral special-linear group is a discrete zero-dimensional analytic Lie group. -/
instance instLieGroup : LieGroup (𝓡 0) ω X := LieGroup.of_discreteTopology ω

/-- With its discrete topology, the nontrivial group SL₂(ℤ) is not connected. -/
theorem not_connectedSpace : ¬ ConnectedSpace X := by
  intro h
  let _ : ConnectedSpace X := h
  let _ : Subsingleton X := subsingleton_of_preconnected_totallyDisconnected
  apply integralSL2Subgroup_ne_bot
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨γ, hγ⟩ := (mem_integralSL2Subgroup g).mp hg
  simpa [Subsingleton.elim γ 1] using hγ.symm

/-- The usual integral-matrix inclusion into native SL₂(ℝ) is an immersion at every order. -/
theorem isImmersion_map_intCast {m : ℕ∞ω} : Manifold.IsImmersion (𝓡 0) 𝓘(ℝ, E) m
    (SpecialLinearGroup.map (Int.castRingHom ℝ) : X →* G) := by
  suffices h : Manifold.IsImmersion (𝓡 0) 𝓘(ℝ, E) ω
      (SpecialLinearGroup.map (Int.castRingHom ℝ) : X →* G) from h.of_le le_top
  have hs : ContMDiff (𝓡 0) 𝓘(ℝ, E) ω
      (SpecialLinearGroup.map (Int.castRingHom ℝ) : X → G) := contMDiff_of_discreteTopology
  exact hs.isImmersion_of_subsingleton (by simp)

end TauCeti.Lie.IntegralSL2

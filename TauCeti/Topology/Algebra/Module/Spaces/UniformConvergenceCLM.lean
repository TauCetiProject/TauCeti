/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Scalar restriction for uniform-convergence spaces of linear maps

Restricting the scalar field preserves the topology of uniform convergence on any prescribed
family of subsets: `UniformConvergenceCLM.isEmbedding_restrictScalars`. No boundedness or
compactness condition on that family is needed. In particular, this applies to the compact
convergence topology by taking the family of compact sets. The compatibility hypothesis is the
one used by native `ContinuousLinearMap.restrictScalars`, with no normed-algebra assumption.
-/

public section

open scoped UniformConvergenceCLM

namespace UniformConvergenceCLM

variable {𝕜 𝕜' E F : Type*} [NormedField 𝕜] [NormedField 𝕜']
  [AddCommGroup E] [Module 𝕜 E] [Module 𝕜' E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module 𝕜' F] [TopologicalSpace F]
  [LinearMap.CompatibleSMul E F 𝕜' 𝕜]

variable (𝕜') in
/-- Restrict scalars on the native space with its prescribed uniform-convergence topology.
The underlying continuous function is unchanged. -/
def restrictScalars (𝔖 : Set (Set E)) (f : E →Lᵤ[𝕜, 𝔖] F) : E →Lᵤ[𝕜', 𝔖] F :=
  ofFun (RingHom.id 𝕜') F 𝔖 (((ofFun (RingHom.id 𝕜) F 𝔖).symm f).restrictScalars 𝕜')

/-- Scalar restriction evaluates by the original function, through the native type copies. -/
@[simp] theorem restrictScalars_apply (𝔖 : Set (Set E)) (f : E →Lᵤ[𝕜, 𝔖] F) (x : E) :
    restrictScalars 𝕜' 𝔖 f x = f x := by
  -- `ofFun` changes the space topology and native scalar restriction changes only linearity.
  rfl

variable (𝕜') in
/-- Restricting scalars is an embedding for uniform convergence on the same arbitrary family.
Both spaces have the topology induced from exactly the same uniform function space. -/
theorem isEmbedding_restrictScalars [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    Topology.IsEmbedding (restrictScalars 𝕜' 𝔖 : (E →Lᵤ[𝕜, 𝔖] F) → E →Lᵤ[𝕜', 𝔖] F) := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  apply (isEmbedding_coeFn (RingHom.id 𝕜') F 𝔖).of_comp_iff.mp
  exact isEmbedding_coeFn (RingHom.id 𝕜) F 𝔖

end UniformConvergenceCLM

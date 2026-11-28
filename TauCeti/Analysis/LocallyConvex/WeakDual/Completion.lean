/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual
import TauCeti.Topology.Algebra.LinearMapCompletion

/-!
# Weak dual of a uniform completion

This file characterizes pullbacks of weak-star continuous linear functionals along the canonical
completion embedding `UniformSpace.Completion.toComplL`: restricting a functional `ψ` on
`UniformSpace.Completion E` to `E` gives `φ` if and only if `ψ` is the unique extension
`StrongDual.toWeakDual ((WeakDual.toStrongDual φ).fromCompletion)`
(`WeakDual.pullbackFunctional_toComplL_eq_iff`).
-/

public section

namespace WeakDual

/-- Restricting a weak-star continuous functional `ψ` on `UniformSpace.Completion E` along
`UniformSpace.Completion.toComplL` equals `φ` if and only if `ψ` is the continuous linear
extension of `φ`. -/
theorem pullbackFunctional_toComplL_eq_iff
    {𝕜 E : Type*} [CommRing 𝕜] [UniformSpace 𝕜] [IsUniformAddGroup 𝕜]
    [UniformContinuousConstSMul 𝕜 𝕜] [T0Space 𝕜] [CompleteSpace 𝕜]
    [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E] [Module 𝕜 E]
    [UniformContinuousConstSMul 𝕜 E]
    (φ : WeakDual 𝕜 E) (ψ : WeakDual 𝕜 (UniformSpace.Completion E)) :
    (UniformSpace.Completion.toComplL (S := 𝕜) (α := E)).pullbackFunctional ψ = φ ↔
      ψ = StrongDual.toWeakDual ((toStrongDual φ).fromCompletion) := by
  rw [← toStrongDual_inj, ContinuousLinearMap.toStrongDual_pullbackFunctional,
    ContinuousLinearMap.comp_toComplL_eq_iff,
    ← toStrongDual_inj ψ (StrongDual.toWeakDual ((toStrongDual φ).fromCompletion)),
    StrongDual.toStrongDual_toWeakDual]

end WeakDual

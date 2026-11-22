/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
public import TauCeti.Topology.Algebra.Module.Spaces.UniformConvergenceCLM

/-!
# Evaluation of precomposition and postcomposition for compact convergence

The native pre/postcomposition operators preserve the topology of uniform convergence on compact
sets. Their generated application rules return a continuous semilinear map through a native type
copy; the pointwise rules here evaluate that map without unfolding those copies at call sites.
They are intended for explicit rewriting: the generated map-valued rules fire first under `simp`.
-/

public section

open scoped CompactConvergenceCLM

namespace ContinuousLinearMap

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ]
  {E F G : Type*} [AddCommGroup E] [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]

/-- Native compact-convergence precomposition evaluates by ordinary function composition. -/
theorem precompCompactConvergenceCLM_apply_apply
    (L : E →SL[σ] F) (f : F →SL_c[τ] G) (x : E) :
    (L.precompCompactConvergenceCLM G f) x = f (L x) := by
  rw [precompCompactConvergenceCLM_apply]
  -- The generated rule returns composition through the native uniform-convergence type copy.
  rfl

/-- Native compact-convergence postcomposition evaluates by ordinary function composition. -/
theorem postcompCompactConvergenceCLM_apply_apply
    [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
    (L : F →SL[τ] G) (f : E →SL_c[σ] F) (x : E) :
    (L.postcompCompactConvergenceCLM E f) x = L (f x) := by
  rw [postcompCompactConvergenceCLM_apply]
  -- The same type-copy reduction evaluates composition and leaves both map topologies intact.
  rfl

end ContinuousLinearMap

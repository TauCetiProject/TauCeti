/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Exact sequences of continuous linear maps

Elementary topological consequences of algebraic exactness `Function.Exact f g` for continuous
semilinear maps, below the snake-sequence and splitting theories.

## Main results

* `Function.Exact.isClosed_range`: if `E₁ --f--> E₂ --g--> E₃` is exact for continuous semilinear
  maps and `E₃` is `T₁`, then `Set.range f` is closed in `E₂`.
-/

public section

/-- If `E₁ --f--> E₂ --g--> E₃` is algebraically exact for continuous semilinear maps and `E₃` is
`T₁`, then `Set.range f` is closed in `E₂`, being equal to the closed kernel of `g`. -/
theorem Function.Exact.isClosed_range {R₁ R₂ R₃ E₁ E₂ E₃ : Type*}
    [Semiring R₁] [Semiring R₂] [Semiring R₃]
    {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃}
    [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R₁ E₁]
    [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R₂ E₂]
    [TopologicalSpace E₃] [AddCommMonoid E₃] [Module R₃ E₃] [T1Space E₃]
    {f : E₁ →SL[σ₁₂] E₂} {g : E₂ →SL[σ₂₃] E₃} (hfg : Function.Exact f g) :
    IsClosed (Set.range f) :=
  (Set.ext fun y ↦ by simpa using (hfg y).symm : Set.range f = (g.ker : Set E₂)) ▸
    g.isClosed_ker

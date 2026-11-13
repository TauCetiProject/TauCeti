/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Functions with a prescribed limit form a closed subspace

For any filter `l` on the domain `α` and any continuous assignment `g` of a prospective limit
to each function, the functions `f` tending to `g f` along `l` form a closed subset of the space
`α →ᵤ β` of functions with the topology of uniform convergence. Taking `g` constant, the
functions tending to a fixed value form a closed subset.

This is Mathlib's `Equicontinuous.isClosed_setOfPred_tendsto` applied to the evaluation maps
`f ↦ f a`, which form an equicontinuous family on `α →ᵤ β`.
-/

public section

open Filter Topology UniformConvergence

namespace UniformFun

variable {α β : Type*} [UniformSpace β] {l : Filter α} {g : (α →ᵤ β) → β}

/-- For a continuous `g : (α →ᵤ β) → β`, the functions `f` tending to `g f` along a filter form
a closed subset for uniform convergence. In particular (`g` constant) so do the functions with a
prescribed limit. No separation or completeness assumption on the codomain is needed. -/
theorem isClosed_setOfPred_tendsto (hg : Continuous g) :
    IsClosed {f : α →ᵤ β | Tendsto (toFun f) l (𝓝 (g f))} := by
  -- The evaluation maps are equicontinuous: by `equicontinuous_iff_continuous` this says that
  -- `ofFun ∘ Function.swap (fun a f ↦ toFun f a)`, which unfolds to the identity of `α →ᵤ β`,
  -- is continuous.
  have h : Equicontinuous fun (a : α) (f : α →ᵤ β) ↦ toFun f a :=
    equicontinuous_iff_continuous.mpr continuous_id
  exact h.isClosed_setOfPred_tendsto hg

end UniformFun

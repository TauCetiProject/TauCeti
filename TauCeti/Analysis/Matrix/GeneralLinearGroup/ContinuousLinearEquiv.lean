/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Invertible matrices as continuous linear automorphisms

Over a complete nontrivially normed field `𝕜`, an invertible square matrix `g` acts on `ι → 𝕜` by
`Matrix.mulVec` as a continuous linear automorphism
(`Matrix.GeneralLinearGroup.toContinuousLinearEquiv`). This is `Matrix.GeneralLinearGroup.toLin`
with the continuity that every linear map of the finite-dimensional space `ι → 𝕜` has. Products of
matrices act by composition, the first factor acting last. This is how the general linear group
acts on frames `𝕜ⁿ ≃ V` by precomposition.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace Matrix.GeneralLinearGroup

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- The continuous linear automorphism of `ι → 𝕜` given by an invertible matrix, acting by
`Matrix.mulVec`. -/
def toContinuousLinearEquiv (g : GL ι 𝕜) : (ι → 𝕜) ≃L[𝕜] (ι → 𝕜) :=
  (toLin g).toLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem toContinuousLinearEquiv_apply (g : GL ι 𝕜) (w : ι → 𝕜) :
    g.toContinuousLinearEquiv w = (g : Matrix ι ι 𝕜) *ᵥ w :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_one :
    (1 : GL ι 𝕜).toContinuousLinearEquiv = ContinuousLinearEquiv.refl 𝕜 (ι → 𝕜) :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ by simp

/-- The product `g * h` acts by applying `h` first and then `g`. -/
@[simp]
theorem toContinuousLinearEquiv_mul (g h : GL ι 𝕜) :
    (g * h).toContinuousLinearEquiv = h.toContinuousLinearEquiv.trans g.toContinuousLinearEquiv :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ by simp [Matrix.mulVec_mulVec]

end Matrix.GeneralLinearGroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Gram matrices of arbitrary families

Mathlib's `Matrix.posSemidef_gram` states that the Gram matrix `(i, j) ↦ ⟪v i, v j⟫` of a family
of vectors indexed by a finite type is positive semidefinite. Mathlib's `Matrix.PosSemidef` is
defined for matrices indexed by arbitrary types, by testing against finitely supported vectors,
and the Gram matrix of every family is positive semidefinite in this sense. Infinite Gram matrices
arise, for instance, as the kernels `(g, h) ↦ ⟪π g ξ, π h ξ⟫` of orbits of unitary group
representations.
-/

public section

open Matrix
open scoped ComplexOrder

namespace TauCeti

variable {𝕜 E n : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The Gram matrix of a family of vectors indexed by an arbitrary type is positive semidefinite.
This drops the finiteness hypothesis of Mathlib's `Matrix.posSemidef_gram`. -/
theorem posSemidef_gram (v : n → E) : (gram 𝕜 v).PosSemidef := by
  -- Test finite subfamilies in `Type`: each is a finite Gram matrix, covered by Mathlib's theorem.
  refine posSemidef_iff_finite_sum.{_, _, 0}.mpr
    ⟨fun a b ↦ (isHermitian_gram 𝕜 v).apply b a, fun {ι} _ w x ↦ ?_⟩
  simpa only [dotProduct, mulVec, gram_apply, Function.comp_apply, Pi.star_apply,
    Finset.mul_sum, mul_assoc] using
      (Matrix.posSemidef_gram 𝕜 (v ∘ w)).dotProduct_mulVec_nonneg x

end TauCeti

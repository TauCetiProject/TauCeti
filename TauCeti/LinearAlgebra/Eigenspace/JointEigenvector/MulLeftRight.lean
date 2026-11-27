/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Algebra.Bilinear
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Joint eigenvectors of two-sided multiplications

Let `P y` and `Q y`, for `y` in some index type, be endomorphisms of a vector space `M`. An
endomorphism `A` with `P y * A * Q y = e y • A` for every `y` is a joint eigenvector, with
eigenvalue function `e`, of the maps `A ↦ P y * A * Q y` on `Module.End K M`. Joint eigenvectors
with distinct eigenvalue functions are linearly independent
(`linearIndependent_of_forall_mul_mul_eq_smul`). With `P y = U y⁻¹` and `Q y = U y` for
a projective representation `U`, this is the independence of operators on which conjugation acts by
distinct characters, as for the translations in a Heisenberg group.
-/

public section

open Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- **Joint eigenvectors of two-sided multiplications are independent.** Nonzero endomorphisms
`A i` with `P y * A i * Q y = e i y • A i` for all `y`, for pairwise distinct functions `e i`, are
linearly independent. -/
theorem linearIndependent_of_forall_mul_mul_eq_smul {ι Y : Type*} {A : ι → End K M}
    {P Q : Y → End K M} {e : ι → Y → K} (he : Function.Injective e) (hA : ∀ i, A i ≠ 0)
    (h : ∀ i y, P y * A i * Q y = e i y • A i) : LinearIndependent K A := by
  let cj (y : Y) : End K (End K M) := LinearMap.mulLeftRight K (P y, Q y)
  have eigen (i : ι) : A i ∈ ⨅ y, (cj y).eigenspace (e i y) := by
    simp only [Submodule.mem_iInf, End.mem_eigenspace_iff]
    intro y
    rw [LinearMap.mulLeftRight_apply, h]
  exact ((TauCeti.iSupIndep_iInf_eigenspace cj).comp he).linearIndependent _ eigen hA

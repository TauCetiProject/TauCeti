/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Separating two vectors by a nondegenerate form

For a nondegenerate matrix `M` over a field, the linear forms `w ↦ v ⬝ᵥ M *ᵥ w` determine `v`.
This file records the two-vector form of that statement: if `x` is not a multiple of `u`, then
some `w` is orthogonal to `u` but not to `x`. Otherwise the form of `x` would vanish on the kernel
of the form of `u`, making it a multiple of that form, and nondegeneracy would make `x` the same
multiple of `u`. This complements Mathlib's `Matrix.Nondegenerate.exists_not_ortho_of_ne_zero`,
the case `u = 0`, and is the basic tool for moving vectors by transvections in the classical
groups.

## Main results

* `Matrix.Nondegenerate.exists_ortho_and_not_ortho_of_notMem_span`: a vector orthogonal to `u` but
  not to `x`, when `x` is not a multiple of `u`.
-/

public section

namespace Matrix.Nondegenerate

variable {m n K : Type*} [Fintype m] [Fintype n] [Field K] {M : Matrix m n K}

/-- **A vector orthogonal to `u` but not to `x`**, for a nondegenerate matrix `M`, when `x` is not
a multiple of `u`. -/
theorem exists_ortho_and_not_ortho_of_notMem_span (hM : M.Nondegenerate) {u x : m → K}
    (hx : x ∉ K ∙ u) : ∃ w, u ⬝ᵥ M *ᵥ w = 0 ∧ x ⬝ᵥ M *ᵥ w ≠ 0 := by
  by_contra! h
  apply hx
  by_cases hu : u = 0
  · subst hu
    rw [hM.eq_zero_of_ortho fun w ↦ h w (by simp)]
    exact Submodule.zero_mem _
  obtain ⟨w₀, hw₀⟩ := hM.exists_not_ortho_of_ne_zero hu
  refine Submodule.mem_span_singleton.mpr
    ⟨x ⬝ᵥ M *ᵥ w₀ / u ⬝ᵥ M *ᵥ w₀, (sub_eq_zero.mp ?_).symm⟩
  refine hM.eq_zero_of_ortho fun w ↦ ?_
  -- Correct `w` along `w₀` into the kernel of the form of `u`, where the form of `x` vanishes.
  have hw := h (w - (u ⬝ᵥ M *ᵥ w / u ⬝ᵥ M *ᵥ w₀) • w₀) (by
    simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    ring)
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    sub_dotProduct, smul_dotProduct] at hw ⊢
  linear_combination hw

end Matrix.Nondegenerate

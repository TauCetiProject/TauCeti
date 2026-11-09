/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Independent families split by a linear map

If a linear map `D` sends a family `u` to a linearly independent family, and `v` is a linearly
independent family in the kernel of `D`, then `u` and `v` together are linearly independent
(`TauCeti.linearIndependent_sumElim_of_map`). This is how a frame of a regular level set
`D⁻¹(c)` is completed by normal vectors to a basis of the ambient space: the tangent vectors lie
in the kernel of the derivative `D`, and the normals are detected by `D`.
-/

public section

namespace TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A family `u` whose image under a linear map `D` is linearly independent, together with a
linearly independent family `v` in the kernel of `D`, is linearly independent. -/
theorem linearIndependent_sumElim_of_map (D : M →ₗ[R] N) {ι κ : Type*} {u : ι → M}
    {v : κ → M} (hu : LinearIndependent R (D ∘ u)) (hv : LinearIndependent R v)
    (hDv : ∀ i, D (v i) = 0) : LinearIndependent R (Sum.elim u v) := by
  refine (hu.of_comp D).sum_type hv (Submodule.disjoint_def.2 fun x hxu hxv ↦ ?_)
  -- A vector in both spans is killed by `D`, so its coefficients along `u` vanish.
  have hDx : D x = 0 :=
    (Submodule.span_le (p := LinearMap.ker D)).2 (Set.range_subset_iff.2 hDv) hxv
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hxu
  rw [map_finsuppSum] at hDx
  simp only [map_smul] at hDx
  rw [linearIndependent_iff.1 hu c hDx, Finsupp.sum_zero_index]

end TauCeti

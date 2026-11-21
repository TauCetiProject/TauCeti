/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# The least singular value

The last singular value indexed by the dimension of the source is the attained minimum
of the norm of the image over the unit sphere. In particular, this value includes zero
when the linear map has a nontrivial kernel.
-/

public section

open Metric Set Module

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The least source-indexed singular value is the attained minimum of `‖A x‖` on the unit
sphere in a nonzero finite-dimensional source. -/
theorem isLeast_norm_image_sphere (A : E →ₗ[𝕜] F) [Nontrivial E] :
    IsLeast ((fun x ↦ ‖A x‖) '' sphere (0 : E) 1)
      (A.singularValues (finrank 𝕜 E - 1)) := by
  have hp : 0 < finrank 𝕜 E := finrank_pos
  let i : Fin (finrank 𝕜 E) := ⟨finrank 𝕜 E - 1, by omega⟩
  refine ⟨⟨A.rightSingularBasis i,
    mem_sphere_zero_iff_norm.mpr (A.rightSingularBasis.norm_eq_one i),
    A.norm_apply_rightSingularBasis i⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have htop : A.rightSingularBasis.spanIndices {j | (j : ℕ) ≤ finrank 𝕜 E - 1} = ⊤ := by
    have hs : {j : Fin (finrank 𝕜 E) | (j : ℕ) ≤ finrank 𝕜 E - 1} = univ := by
      ext j
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact Nat.le_sub_one_of_lt j.isLt
    rw [hs, OrthonormalBasis.spanIndices_eq_span, image_univ,
      ← OrthonormalBasis.coe_toBasis, Module.Basis.span_eq]
  have h := A.singularValues_mul_norm_le_norm_apply (x := x)
    ((htop ▸ Submodule.mem_top : x ∈ A.rightSingularBasis.spanIndices
      {j | (j : ℕ) ≤ finrank 𝕜 E - 1}))
  simpa only [mem_sphere_zero_iff_norm.mp hx, mul_one] using h

end LinearMap

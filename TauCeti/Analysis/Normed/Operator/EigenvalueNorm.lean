/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Excluding eigenvalues by norm bounds

Let `f` be an endomorphism of a normed space `E` over a normed field `𝕜`. An eigenvector `v` for
`μ` has `‖f v‖ = ‖μ‖ ‖v‖`, so norm inequalities between `f v` and `v` exclude eigenvalues:

* if `f` strictly decreases the norm of every nonzero vector, it has no eigenvalue `μ` with
  `1 ≤ ‖μ‖` (`Module.End.not_hasEigenvalue_of_norm_apply_lt`);
* if `f` strictly increases the norm of every nonzero vector, it has no eigenvalue `μ` with
  `‖μ‖ ≤ 1` (`Module.End.not_hasEigenvalue_of_lt_norm_apply`).

Over `ℝ` these are the norm criteria for the eigenvalue hypotheses of
`LinearMap.sign_det_one_sub_prodMap_of_not_hasEigenvalue`: a strict contraction has no real
eigenvalue `μ ≥ 1`, and a strict expansion has none in `[0, 1]`.
-/

public section

namespace Module.End

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : Module.End 𝕜 E}

/-- A map that strictly decreases the norm of every nonzero vector has no eigenvalue of norm at
least `1`. -/
theorem not_hasEigenvalue_of_norm_apply_lt (hf : ∀ v, v ≠ 0 → ‖f v‖ < ‖v‖) {μ : 𝕜}
    (hμ : 1 ≤ ‖μ‖) : ¬ f.HasEigenvalue μ := fun h ↦ by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hlt := hf v hv.2
  rw [mem_eigenspace_iff.mp hv.1, norm_smul] at hlt
  nlinarith [norm_nonneg v]

/-- A map that strictly increases the norm of every nonzero vector has no eigenvalue of norm at
most `1`. -/
theorem not_hasEigenvalue_of_lt_norm_apply (hf : ∀ v, v ≠ 0 → ‖v‖ < ‖f v‖) {μ : 𝕜}
    (hμ : ‖μ‖ ≤ 1) : ¬ f.HasEigenvalue μ := fun h ↦ by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hlt := hf v hv.2
  rw [mem_eigenspace_iff.mp hv.1, norm_smul] at hlt
  nlinarith [norm_nonneg v]

end Module.End

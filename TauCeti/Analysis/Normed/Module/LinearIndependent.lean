/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.LinearAlgebra.LinearIndependent.Basic

/-!
# Coefficients of a linearly independent subfamily are bounded by the norm

Let `g k`, for `k` in a finite type `κ`, be vectors in a normed space over a complete field, and
let the subfamily indexed by `s` be linearly independent. Then the coefficients of a combination
`∑ k, a k • g k` with `a` vanishing off `s` are bounded by a fixed multiple of its norm
(`LinearIndepOn.exists_norm_le_mul_norm_sum_smul`): the combination map is injective on the
finite-dimensional space `Pi.spanSubset 𝕜 s` of such coefficient functions, hence antilipschitz.
-/

public section

variable {κ 𝕜 E : Type*} [Fintype κ] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Coefficients on a linearly independent subfamily are bounded by the norm.** If the vectors
`g k` with `k ∈ s` are linearly independent, there is a constant `K ≥ 0` such that every
coefficient function `a` vanishing off `s` satisfies `‖a‖ ≤ K ‖∑ k, a k • g k‖`. -/
theorem LinearIndepOn.exists_norm_le_mul_norm_sum_smul {g : κ → E} {s : Set κ}
    (hs : LinearIndepOn 𝕜 g s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : κ → 𝕜, (∀ k ∉ s, a k = 0) → ‖a‖ ≤ K * ‖∑ k, a k • g k‖ := by
  let f := (Fintype.linearCombination 𝕜 g).comp (Pi.spanSubset 𝕜 s).subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact Subtype.ext <| funext <| Fintype.linearIndepOn_iff.1 hs a
      (Pi.mem_spanSubset_iff.1 a.property) (by simpa [f, Fintype.linearCombination_apply] using ha)
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz f).1 hf
  refine ⟨K, K.property, fun a ha ↦ ?_⟩
  simpa [dist_eq_norm, f, Fintype.linearCombination_apply] using
    hK.le_mul_dist ⟨a, Pi.mem_spanSubset_iff.2 ha⟩ 0

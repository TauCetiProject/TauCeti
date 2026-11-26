/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Embedding a space onto the hyperplane orthogonal to a vector

Let `E` be an inner product space of dimension `n + 1` and `v` a nonzero vector of `E`. Its
orthogonal hyperplane `(𝕜 ∙ v)ᗮ` has dimension `n`, so every space `W` of dimension `n` maps
isomorphically onto it. Composing with the inclusion and the orthogonal projection gives a
continuous linear map `L : W → E` with values orthogonal to `v` and a left inverse `P` of `L`
that kills `v`.

The orthogonal projection onto `(𝕜 ∙ v)ᗮ` takes values orthogonal to `v`, and for a unit vector
`e` every `z` is `⟪e, z⟫ e` plus its projection onto `(𝕜 ∙ e)ᗮ`.

## Main results

* `TauCeti.exists_leftInverse_inner_eq_zero_of_finrank_eq`: maps `L : W → E` with values
  orthogonal to `v` and `P : E → W` with `P ∘ L = id` and `P v = 0`.
* `TauCeti.inner_starProjection_orthogonal_singleton_eq_zero`,
  `TauCeti.inner_starProjection_orthogonal_singleton_smul_eq_zero`: the projection onto
  `(𝕜 ∙ v)ᗮ`, or onto `(𝕜 ∙ c v)ᗮ` for `c ≠ 0`, is orthogonal to `v`.
* `TauCeti.inner_smul_add_starProjection_eq`: `⟪e, z⟫ e + P z = z` for a unit vector `e` and the
  projection `P` onto `(𝕜 ∙ e)ᗮ`.
-/

public section

open Module
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 W E : Type*} [RCLike 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [FiniteDimensional 𝕜 W] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- If `E` has dimension `n + 1` and `W` has dimension `n`, then for every nonzero `v : E` there
are a continuous linear map `L : W → E` with values orthogonal to `v` and a left inverse
`P : E → W` of `L` with `P v = 0`: `L` is an isomorphism of `W` onto `(𝕜 ∙ v)ᗮ` followed by the
inclusion, and `P` is its inverse after the orthogonal projection. -/
theorem exists_leftInverse_inner_eq_zero_of_finrank_eq {n : ℕ} [Fact (finrank 𝕜 E = n + 1)]
    (hW : finrank 𝕜 W = n) {v : E} (hv : v ≠ 0) :
    ∃ (L : W →L[𝕜] E) (P : E →L[𝕜] W),
      (∀ w, P (L w) = w) ∧ P v = 0 ∧ ∀ w, ⟪L w, v⟫_𝕜 = 0 := by
  have : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ n
  set K := (𝕜 ∙ v)ᗮ
  let A : W ≃L[𝕜] K := ContinuousLinearEquiv.ofFinrankEq
    (hW.trans (Submodule.finrank_orthogonal_span_singleton hv).symm)
  refine ⟨K.subtypeL ∘L (A : W →L[𝕜] K), (A.symm : K →L[𝕜] W) ∘L K.orthogonalProjectionOnto,
    fun w ↦ ?_, ?_, fun w ↦ ?_⟩
  · simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  · simp [K, Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
  · exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self v)
      (A w).property

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜)

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` is orthogonal to `v`. -/
theorem inner_starProjection_orthogonal_singleton_eq_zero (v z : E) :
    ⟪(𝕜 ∙ v)ᗮ.starProjection z, v⟫_𝕜 = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.starProjection_apply_mem _ z)

/-- For `c ≠ 0`, the orthogonal projection onto `(𝕜 ∙ c v)ᗮ` is orthogonal to `v`. -/
theorem inner_starProjection_orthogonal_singleton_smul_eq_zero {c : 𝕜} (hc : c ≠ 0) (v z : E) :
    ⟪(𝕜 ∙ (c • v))ᗮ.starProjection z, v⟫_𝕜 = 0 := by
  have h := inner_starProjection_orthogonal_singleton_eq_zero 𝕜 (c • v) z
  rw [inner_smul_right, mul_eq_zero] at h
  exact h.resolve_left hc

/-- For a unit vector `e`, every `z` is `⟪e, z⟫ e` plus its projection onto `(𝕜 ∙ e)ᗮ`. -/
theorem inner_smul_add_starProjection_eq {e : E} (he : ‖e‖ = 1) (z : E) :
    ⟪e, z⟫_𝕜 • e + (𝕜 ∙ e)ᗮ.starProjection z = z := by
  rw [← Submodule.starProjection_unit_singleton 𝕜 he,
    Submodule.starProjection_add_starProjection_orthogonal]

end Projection

end TauCeti

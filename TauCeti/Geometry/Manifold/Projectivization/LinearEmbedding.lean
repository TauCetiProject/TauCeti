/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Projectivization.Map

/-!
# Linear subspaces of projective space are analytic submanifolds

An injective linear map `f : 𝕜ᵐ⁺¹ → 𝕜ⁿ⁺¹` induces the map `Projectivization.map f` sending the line
`[v]` to `[f v]`, which is analytic (`Projectivization.contMDiff_map`). Over `ℝ` or `ℂ` it is
moreover an analytic embedding (`Projectivization.isSmoothEmbedding_map`), so the image of
`ℙᵐ`, the projectivization of the range of `f`, is an analytic submanifold of `ℙⁿ`. For
instance the coordinate hyperplanes `{vᵢ = 0}` of `ℙⁿ` are copies of `ℙⁿ⁻¹`.

A linear left inverse `g` of `f` induces the map `[w] ↦ [g w]`, which is analytic on the open set
where `g` does not vanish (`Projectivization.contMDiffOn_linearProjection`). This open set contains
the image of `map f`, and `[w] ↦ [g w]` is a left inverse of `map f` there, so the differential of
`map f` is injective (`Projectivization.isImmersion_map`). Since projective space is compact and
`map f` is injective, it is a topological embedding.

## Main results

* `Projectivization.isImmersion_map`: the map induced by an injective linear map is an immersion.
* `Projectivization.isSmoothEmbedding_map`: it is a `C^r` embedding for every `r ≥ 1`,
  including the analytic order `ω`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
-/

public section

open Set Function Topology Manifold
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Projectivization

open TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- **Linear inclusions of projective spaces are immersions.** The map `[v] ↦ [f v]` induced by an
injective linear map `f` is a `C^r` immersion for every `r ≥ 1`. It has the analytic left inverse
`[w] ↦ [g w]` for a linear left inverse `g` of `f`. -/
theorem isImmersion_map (f : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f)
    {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsImmersion 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf) := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  have hgf (v : Fin (m + 1) → 𝕜) : g (f v) = v := LinearMap.congr_fun hg v
  -- The image of `map f` lies in the open set where `g` does not vanish.
  have hdom (x : ℙ 𝕜 (Fin (m + 1) → 𝕜)) : map f hf x ∈ linearProjectionDomain g := by
    induction x using ind with | h v hv =>
    rw [map_mk, mk_mem_linearProjectionDomain_iff, hgf]
    exact hv
  have hleft (x : ℙ 𝕜 (Fin (m + 1) → 𝕜)) : linearProjection g (map f hf x) = x := by
    induction x using ind with | h v hv =>
    rw [map_mk, linearProjection_mk g _ (by rwa [hgf])]
    simp only [hgf]
  rw [isImmersion_iff_forall_isImmersionAt]
  intro x
  exact ((contMDiff_map f hf r).contMDiffOn (s := univ)).isImmersionAt_of_comp_eventuallyEq_id
    isOpen_univ (mem_univ x) hr
    (((contMDiffOn_linearProjection g r _ (hdom x)).contMDiffAt
      ((isOpen_linearProjectionDomain (LinearMap.continuous_on_pi g)).mem_nhds
        (hdom x))).mdifferentiableAt hr0)
    (Filter.Eventually.of_forall hleft)

/-- **Linear inclusions of projective spaces are analytic embeddings.** The map
`[v] ↦ [f v]` induced by an injective linear map `f` is a `C^r` embedding for every `r ≥ 1`,
including the analytic order `ω`. It is a topological embedding since projective space is compact.
Over `ℂ` it is a holomorphic embedding. -/
theorem isSmoothEmbedding_map (f : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f)
    {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsSmoothEmbedding 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf) :=
  ⟨isImmersion_map f hf hr, ((contMDiff_map f hf r).continuous.isClosedEmbedding
    (map_injective f hf)).isEmbedding⟩

end Projectivization

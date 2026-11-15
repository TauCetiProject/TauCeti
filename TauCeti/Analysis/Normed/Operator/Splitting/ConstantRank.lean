/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Splitting.Family

/-!
# Kernels and ranges in continuous families of constant rank

Let `A x : E →L[𝕜] F` be a family of operators between finite-dimensional spaces over a complete
field, continuous on an open set `s` of a topological space, whose rank is the same at every
point of `s`. Near each point `x₀ ∈ s` the kernels and the ranges of the family then move
continuously: there are continuous families of injective operators, defined on a fixed model
space, whose ranges are exactly `ker (A x)` (`exists_continuousOn_ker_parametrization`), and
exactly `range (A x)` (`exists_continuousOn_range_parametrization`). The model spaces are the
kernel and the range of `A x₀`.

Both parametrizations come from one splitting. Choose a continuous projection `p` of `F` onto
`range (A x₀)` and a continuous projection `q` of `E` onto `ker (A x₀)`. The pair
`(p ∘ A x, q) : E → range (A x₀) × ker (A x₀)` is invertible at `x₀`, hence near `x₀`, with an
inverse depending continuously on `x`
(`ContinuousLinearMap.exists_isOpen_continuousOn_inverse_prod_comp`). Its inverse
restricted to the second factor is the kernel section `ContinuousLinearMap.kerSection`, which
parametrizes `ker (p ∘ A x)`; restricted to the first factor and followed by `A x`, it
parametrizes a subspace of `range (A x)`. Constancy of the rank says exactly that these
subspaces are `ker (A x)` and `range (A x)`, by counting dimensions. Without it the kernels may
jump: the scalar family `x ↦ x` on `𝕜` has rank one except at the origin.

These local parametrizations are the matrix computations behind the kernel and image bundles of a
bundle map of constant rank, `TauCeti/Topology/VectorBundle/ConstantRank.lean`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 10.34,
  for the corresponding statement on smooth bundle homomorphisms of constant rank.
-/

public section

open Function Module Set

namespace ContinuousLinearMap

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [TopologicalSpace X] {A : X → E →L[𝕜] F} {s : Set X} {x₀ : X}

/-- **Kernels of a constant-rank family move continuously.** If `A` is continuous on an open set
`s` and has the same rank at every point of `s`, then near each `x₀ ∈ s` there is a family of
injective operators `κ x : ker (A x₀) →L[𝕜] E`, continuous in `x`, whose range is `ker (A x)`. -/
theorem exists_continuousOn_ker_parametrization (hA : ContinuousOn A s) (hs : IsOpen s)
    (hx₀ : x₀ ∈ s) (hrank : ∀ x ∈ s, finrank 𝕜 (A x).range = finrank 𝕜 (A x₀).range) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ κ : X → (A x₀).ker →L[𝕜] E, ContinuousOn κ U ∧
      ∀ x ∈ U, Injective (κ x) ∧ (κ x).range = (A x).ker := by
  obtain ⟨p, -, q, -, U, hUs, hU, hx₀U, hinv, hcont⟩ :=
    exists_isOpen_continuousOn_inverse_prod_comp hA hs hx₀
  refine ⟨U, hUs, hU, hx₀U, fun x ↦ (p ∘L A x).kerSection q, ?_, fun x hx ↦
    ⟨kerSection_injective (hinv x hx), ?_⟩⟩
  · simp_rw [kerSection_def]
    exact hcont.clm_comp continuousOn_const
  -- `ker (A x) ≤ ker (p ∘ A x)`, and both have the dimension of `ker (A x₀)`.
  rw [range_kerSection (hinv x hx)]
  refine (Submodule.eq_of_le_of_finrank_eq (fun v hv ↦ ?_) ?_).symm
  · simp only [LinearMap.mem_ker, coe_coe, comp_apply] at hv ⊢
    rw [hv, map_zero]
  · rw [← (kerEquivOfProd _ q (hinv x hx)).toLinearEquiv.finrank_eq]
    have h₁ := LinearMap.finrank_range_add_finrank_ker (A x : E →ₗ[𝕜] F)
    have h₀ := LinearMap.finrank_range_add_finrank_ker (A x₀ : E →ₗ[𝕜] F)
    have h := hrank x (hUs hx)
    omega

/-- **Ranges of a constant-rank family move continuously.** If `A` is continuous on an open set
`s` and has the same rank at every point of `s`, then near each `x₀ ∈ s` there is a family of
injective operators `ρ x : range (A x₀) →L[𝕜] F`, continuous in `x`, whose range is
`range (A x)`. -/
theorem exists_continuousOn_range_parametrization (hA : ContinuousOn A s) (hs : IsOpen s)
    (hx₀ : x₀ ∈ s) (hrank : ∀ x ∈ s, finrank 𝕜 (A x).range = finrank 𝕜 (A x₀).range) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ ρ : X → (A x₀).range →L[𝕜] F, ContinuousOn ρ U ∧
      ∀ x ∈ U, Injective (ρ x) ∧ (ρ x).range = (A x).range := by
  obtain ⟨p, -, q, -, U, hUs, hU, hx₀U, hinv, hcont⟩ :=
    exists_isOpen_continuousOn_inverse_prod_comp hA hs hx₀
  -- The section `σ x` of `p ∘ A x` with values in `ker q`, followed by `A x`.
  let σ : X → (A x₀).range →L[𝕜] E := fun x ↦
    ((p ∘L A x).prod q).inverse ∘L inl 𝕜 (A x₀).range (A x₀).ker
  have hσ : ∀ x ∈ U, ∀ w, p (A x (σ x w)) = w := by
    intro x hx w
    obtain ⟨e, he⟩ := hinv x hx
    have h : (p ∘L A x).prod q (σ x w) = (w, 0) := by
      simp only [σ, ← he, inverse_equiv, comp_apply, inl_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg Prod.fst h
  have hinjρ : ∀ x ∈ U, Injective (A x ∘L σ x) := fun x hx ↦
    LeftInverse.injective (g := p) (hσ x hx)
  refine ⟨U, hUs, hU, hx₀U, fun x ↦ A x ∘L σ x,
    (hA.mono hUs).clm_comp (hcont.clm_comp continuousOn_const), fun x hx ↦ ⟨hinjρ x hx, ?_⟩⟩
  -- `range (A x ∘ σ x) ≤ range (A x)`, and both have the dimension of `range (A x₀)`.
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact LinearMap.mem_range_self _ _
  · rw [LinearMap.finrank_range_of_inj (hinjρ x hx), hrank x (hUs hx)]

end ContinuousLinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothly varying left inverses

Let `A x` be a continuous linear map from a Banach space `G` to a normed space `F`, depending
`C^n` on a point `x` of a manifold. If `A x₀` has a continuous left inverse `P`, then the
compression `P ∘ A x` is the identity at `x₀`, hence invertible near `x₀`, and
`(P ∘ A x)⁻¹ ∘ P` is a left inverse of `A x` for `x` near `x₀`. Operator inversion is analytic on
the invertible operators, so this left inverse is again `C^n` at `x₀`. This is the smooth
counterpart of `ContinuousAt.exists_continuousAt_leftInverse`.

For `G = 𝕜ᵏ` and `A x` the operator `c ↦ ∑ i, c i • X i x` of a family of linearly independent
vectors depending smoothly on `x`, the left inverse sends a vector of the span of the `X i x` to
its coordinates. So coordinates in a smoothly moving basis depend smoothly on the base point,
which is what makes the local trivializations of a subbundle spanned by smooth local frames
smoothly compatible.

## Main results

* `ContMDiffAt.exists_contMDiffAt_leftInverse`: `C^n` varying left inverses of a `C^n` family of
  operators whose member at `x₀` has a continuous left inverse.
-/

public section

noncomputable section

open Filter Function Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}

/-- **Left inverses vary smoothly.** Let `A x` be a continuous linear map into a normed space from
a Banach space, depending `C^n` on a manifold point `x` at `x₀`. If `A x₀` has a continuous left
inverse, then there are continuous linear maps `L x`, depending `C^n` on `x` at `x₀`, such that
`L x` is a left inverse of `A x` for all `x` near `x₀`. -/
theorem ContMDiffAt.exists_contMDiffAt_leftInverse {A : M → G →L[𝕜] F} {x₀ : M}
    (hA : ContMDiffAt I 𝓘(𝕜, G →L[𝕜] F) n A x₀) (h : (A x₀).HasLeftInverse) :
    ∃ L : M → F →L[𝕜] G, ContMDiffAt I 𝓘(𝕜, F →L[𝕜] G) n L x₀ ∧
      ∀ᶠ x in 𝓝 x₀, LeftInverse (L x) (A x) := by
  obtain ⟨P, hP⟩ := h
  -- The compression `P ∘ A x` is the identity at `x₀`, hence invertible near `x₀`.
  have hQ : ContMDiffAt I 𝓘(𝕜, G →L[𝕜] G) n (fun x ↦ P ∘L A x) x₀ :=
    contMDiffAt_const.clm_comp hA
  have hQ₀ : P ∘L A x₀ = ((1 : (G →L[𝕜] G)ˣ) : G →L[𝕜] G) := ContinuousLinearMap.ext hP
  have hinv : ContDiffAt 𝕜 n Ring.inverse (P ∘L A x₀) := by
    rw [hQ₀]
    exact contDiffAt_ringInverse 𝕜 1
  refine ⟨fun x ↦ Ring.inverse (P ∘L A x) ∘L P,
    (hinv.comp_contMDiffAt (f := fun x ↦ P ∘L A x) hQ).clm_comp contMDiffAt_const, ?_⟩
  filter_upwards [hQ.continuousAt.preimage_mem_nhds (hQ₀ ▸ Units.nhds 1)] with x hx v
  have := congrArg (fun T : G →L[𝕜] G ↦ T v) (Ring.inverse_mul_cancel _ hx)
  simpa using this

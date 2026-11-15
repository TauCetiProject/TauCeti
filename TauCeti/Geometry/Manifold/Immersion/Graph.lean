/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Immersion
import TauCeti.Analysis.Calculus.ContDiff.Shear

/-!
# Immersion normal forms for graphs

The graph of a `Cⁿ` map on an open subset of a normed space has an immersion normal form
with the target space as complement. The shear `(u, w) ↦ (u, w - g u)` straightens the graph
to `u ↦ (u, 0)`. This works at every regularity over any nontrivially normed field, without
finite-dimensionality or completeness assumptions.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω}

/-- In model spaces, the graph of a `Cⁿ` map on an open set is an immersion with complement
`F` at every point of that set, straightened by the shear `(u, w) ↦ (u, w - g u)`. -/
theorem ContDiffOn.isImmersionAtOfComplement_graph {g : E → F} {s : Set E}
    (hg : ContDiffOn 𝕜 n g s) (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    Manifold.IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E × F) n (fun u ↦ (u, g u)) x := by
  obtain ⟨ψ, hψ₁, hψ₂, hψsrc, hψapp⟩ :=
    (ContinuousLinearEquiv.refl 𝕜 (E × F)).exists_contDiffOn_shear 0 hs hg
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E × F) n (E × F) :=
    ψ.mem_maximalAtlas_of_contMDiffOn (contMDiffOn_iff_contDiffOn.mpr hψ₁)
      (contMDiffOn_iff_contDiffOn.mpr hψ₂)
  let φ := (OpenPartialHomeomorph.refl E).restrOpen s hs
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts (ContinuousLinearEquiv.refl 𝕜 (E × F))
    φ ψ (by simpa [φ] using hx) (by simpa [hψsrc] using hx)
    (φ.mem_maximalAtlas_of_contMDiffOn contMDiffOn_id contMDiffOn_id) hψ
    (fun _ hy ↦ by simpa [φ, hψsrc] using hy) ?_
  intro u _
  simp [φ, hψapp]

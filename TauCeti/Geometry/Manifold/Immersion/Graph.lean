/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Immersion

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
  have ht : IsOpen (Prod.fst ⁻¹' s : Set (E × F)) := hs.preimage continuous_fst
  have hg' : ContDiffOn 𝕜 n (fun p : E × F ↦ g p.1) (Prod.fst ⁻¹' s) :=
    hg.comp contDiff_fst.contDiffOn fun _ hp ↦ hp
  let ψ : OpenPartialHomeomorph (E × F) (E × F) :=
    { toFun := fun p ↦ (p.1, p.2 - g p.1)
      invFun := fun p ↦ (p.1, p.2 + g p.1)
      source := Prod.fst ⁻¹' s
      target := Prod.fst ⁻¹' s
      map_source' := fun _ hp ↦ hp
      map_target' := fun _ hp ↦ hp
      left_inv' := fun p _ ↦ by simp
      right_inv' := fun p _ ↦ by simp
      open_source := ht
      open_target := ht
      continuousOn_toFun :=
        continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.sub hg'.continuousOn)
      continuousOn_invFun :=
        continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.add hg'.continuousOn) }
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E × F) n (E × F) :=
    ψ.mem_maximalAtlas_of_contMDiffOn
      (contMDiffOn_iff_contDiffOn.mpr
        (contDiff_fst.contDiffOn.prodMk (contDiff_snd.contDiffOn.sub hg')))
      (contMDiffOn_iff_contDiffOn.mpr
        (contDiff_fst.contDiffOn.prodMk (contDiff_snd.contDiffOn.add hg')))
  let φ := (OpenPartialHomeomorph.refl E).restrOpen s hs
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts (ContinuousLinearEquiv.refl 𝕜 (E × F))
    φ ψ (by simpa [φ] using hx) hx
    (φ.mem_maximalAtlas_of_contMDiffOn contMDiffOn_id contMDiffOn_id) hψ
    (fun _ hy ↦ by simpa [φ, ψ] using hy) ?_
  intro u _
  simp [φ, ψ]

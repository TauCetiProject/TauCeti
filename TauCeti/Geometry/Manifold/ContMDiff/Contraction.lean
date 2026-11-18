/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth contractions of star-convex chart domains

Let `e` be a chart in the maximal smooth atlas of a manifold `M` modelled on `I`, and let `U` be a
nonempty open subset of its source whose image under the extended chart `e.extend I` is
star-convex. Then `U` is smoothly contractible: some smooth map `F : ℝ × U → U` satisfies
`F (0, y) = y` and `F (1, y) = c'` for a point `c' ∈ U`
(`TauCeti.exists_contMDiff_contraction_of_starConvex`). This holds over every model with corners,
so boundary and corners are allowed, and no `IsManifold` instance is needed.

Such contractions are the base case of comparisons of smooth with continuous invariants over
coordinate domains, for instance of smooth with continuous singular homology.

## Main results

* `TauCeti.exists_contMDiff_contraction_of_starConvex`: a nonempty star-convex chart domain is
  smoothly contractible.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **A star-convex chart domain is smoothly contractible.** Let `U` be a nonempty open subset of
the source of a chart `e` in the maximal smooth atlas of `M`, whose image under the extended chart
`e.extend I` is star-convex. Then some smooth map `F : ℝ × U → U` joins the identity
`F (0, ·) = id` to a constant map `F (1, ·) = c'`. The model `I` may have boundary or corners. -/
theorem exists_contMDiff_contraction_of_starConvex {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {U : TopologicalSpace.Opens M} [Nonempty U]
    (hUe : (U : Set M) ⊆ e.source) {c : E} (hUc : StarConvex ℝ c (e.extend I '' U)) :
    ∃ (F : ℝ × U → U) (c' : U), ContMDiff (𝓘(ℝ).prod I) I ∞ F ∧ (∀ y, F (0, y) = y) ∧
      ∀ y, F (1, y) = c' := by
  -- The contraction is the straight line `(t, y) ↦ c + (1 - ψ t) • (e.extend I y - c)` towards
  -- `c`, read back through the chart, where `ψ` is the smooth transition function from `0` to `1`.
  -- It stays in the image of the extended chart, which lies in `range I`.
  let G : ℝ × U → E := fun p ↦ c + (1 - Real.smoothTransition p.1) • (e.extend I p.2 - c)
  have hG : ∀ p, ∃ u ∈ (U : Set M), e.extend I u = G p := fun p ↦
    hUc.add_smul_sub_mem (mem_image_of_mem _ p.2.2) (by linarith [Real.smoothTransition.le_one p.1])
      (by linarith [Real.smoothTransition.nonneg p.1])
  have hGU : ∀ p, (e.extend I).symm (G p) ∈ (U : Set M) := fun p ↦ by
    obtain ⟨u, hu, hGu⟩ := hG p
    rwa [← hGu, e.extend_left_inv (I := I) (hUe hu)]
  have hGt : ∀ p, G p ∈ I '' e.target := fun p ↦ by
    obtain ⟨u, hu, hGu⟩ := hG p
    rw [← hGu, ← e.extend_target' (I := I)]
    exact (e.extend I).map_source (by rw [e.extend_source]; exact hUe hu)
  refine ⟨fun p ↦ ⟨(e.extend I).symm (G p), hGU p⟩, ⟨(e.extend I).symm c, ?_⟩, ?_,
    fun y ↦ Subtype.ext ?_, fun y ↦ Subtype.ext ?_⟩
  · simpa [G, Real.smoothTransition.one] using hGU (1, Classical.arbitrary U)
  · rw [← ContMDiff.subtypeVal_comp_iff]
    have hφ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ fun p : ℝ × U ↦ e.extend I p.2 :=
      (e.contMDiffOn_extend he).comp_contMDiff (contMDiff_subtype_val.comp contMDiff_snd)
        fun p ↦ hUe p.2.2
    have hψ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ fun p : ℝ × U ↦ Real.smoothTransition p.1 :=
      Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
    exact (contMDiffOn_extend_symm he).comp_contMDiff
      (contMDiff_const.add ((contMDiff_const.sub hψ).smul (hφ.sub contMDiff_const))) hGt
  · simp only [G, Real.smoothTransition.zero, sub_zero, one_smul, add_sub_cancel]
    exact e.extend_left_inv (I := I) (hUe y.2)
  · simp [G, Real.smoothTransition.one]

end TauCeti

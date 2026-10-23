/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Euclidean

/-!
# The disc theorem in a manifold

Let `M` be a boundaryless smooth manifold modelled on a finite-dimensional real normed space `E`.
Two smooth embeddings `f g : E → M` with the same centre `f 0 = g 0`, whose derivatives at `0` have
the same orientation, are smoothly isotopic through embeddings, relative to the centre
(`TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_det_chartAt_mul_pos`). The orientations are
compared in the chart at the centre, by asking that the product of the two derivative
determinants be positive.

This is the disc theorem in the form of Hirsch, Chapter 4, Theorem 6.6, for open discs `E ≅ ℝⁿ`: the
condition there, `Det (D(g⁻¹ ∘ f)(0)) > 0`, is the positivity of the product of determinants
above. The ambient form of Palais's disc theorem, used to show that connected sums are well
defined, follows from it by the isotopy extension theorem, and on a connected manifold the
centres can first be made to agree by a compactly supported diffeotopy
(`TauCeti.exists_diffeotopy_final_apply_eq`). Neither of these steps is taken here.

The Euclidean case is `TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_det_mul_pos`. To reduce to
it, both embeddings are first shrunk by precomposing with a radial contraction of `E` onto a small
Euclidean ball about `0` (`TauCeti.SmoothEmbedding.compRadialContractionIsotopy`), so that they land
in a Euclidean ball `B` inside the chart at the centre. Read in the chart
(`TauCeti.SmoothEmbedding.transChart`), they are embeddings `E → E` with values in `B`, and the
Euclidean disc theorem confined to `B` (`TauCeti.SmoothEmbedding.exists_smoothIsotopy_mapsTo_ball`)
connects them. Since the motion stays in `B`, the inverse chart carries it back to `M`
(`TauCeti.SmoothIsotopy.postcomp`).

## Main results

* `TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_det_chartAt_mul_pos`: the disc theorem in a
  manifold, for embeddings with a common centre.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6, Theorem 6.6, p. 117.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
-/

public section

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The disc theorem in a manifold.** Two smooth embeddings of `E` into a boundaryless manifold
modelled on `E`, with the same centre `f 0 = g 0` and derivatives at `0` of the same orientation,
are smoothly isotopic relative to that centre. The orientations are compared in the chart at the
centre: the product of the derivative determinants there is positive. This condition does not
depend on the chart, since a change of chart multiplies both determinants by the same nonzero
number. For `M = E` it is the hypothesis of the Euclidean disc theorem
`TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_det_mul_pos`. -/
theorem exists_smoothIsotopy_of_det_chartAt_mul_pos
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hcentre : f 0 = g 0)
    (hdet : 0 < (fderiv ℝ (chartAt E (f 0) ∘ f) 0).det *
      (fderiv ℝ (chartAt E (f 0) ∘ g) 0).det) :
    ∃ G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap,
      ∀ t : unitInterval, G (t, 0) = f 0 := by
  set p := f 0 with hp
  set φ := chartAt E p
  have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  set c := φ p
  have hpφ : p ∈ φ.source := mem_chart_source E p
  -- A Euclidean ball about the centre of the chart, and one about `0` that `f` and `g` map into it.
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Euclidean.ball c r ⊆ φ.target :=
    Euclidean.nhds_basis_ball.mem_iff.1 (φ.open_target.mem_nhds (φ.map_source hpφ))
  set U := φ.source ∩ φ ⁻¹' Euclidean.ball c r
  have hU : U ∈ 𝓝 p :=
    (φ.isOpen_inter_preimage Euclidean.isOpen_ball).mem_nhds
      ⟨hpφ, mem_preimage.2 (Euclidean.mem_ball_self (x := c) hr)⟩
  obtain ⟨δ, hδ, hδU⟩ : ∃ δ > 0, Euclidean.ball (0 : E) δ ⊆ f ⁻¹' U ∩ g ⁻¹' U :=
    Euclidean.nhds_basis_ball.mem_iff.1 (Filter.inter_mem
      (f.contMDiff.continuous.continuousAt.preimage_mem_nhds hU)
      (g.contMDiff.continuous.continuousAt.preimage_mem_nhds (hcentre ▸ hU)))
  -- Step 1: shrink the source, so that both embeddings land in `U`.
  have ha : (0 : ℝ) ≤ δ⁻¹ ^ 2 := sq_nonneg _
  set f₁ := f.compRadialContraction ha
  set g₁ := g.compRadialContraction ha
  have hf₁U (x : E) : f₁ x ∈ U := by
    rw [compRadialContraction_apply]
    exact (hδU (radialContraction_mem_ball 0 x hδ)).1
  have hg₁U (x : E) : g₁ x ∈ U := by
    rw [compRadialContraction_apply]
    exact (hδU (radialContraction_mem_ball 0 x hδ)).2
  have hf₁φ : range f₁ ⊆ φ.source := range_subset_iff.2 fun x => (hf₁U x).1
  have hg₁φ : range g₁ ⊆ φ.source := range_subset_iff.2 fun x => (hg₁U x).1
  -- Step 2: read the shrunken embeddings in the chart.
  set F₁ := f₁.transChart hφ hf₁φ
  set G₁ := g₁.transChart hφ hg₁φ
  have hF₁ (x : E) : F₁ x = φ (f₁ x) := transChart_apply ..
  have hG₁ (x : E) : G₁ x = φ (g₁ x) := transChart_apply ..
  have hF₁0 : F₁ 0 = c := by
    rw [hF₁, compRadialContraction_apply, radialContraction_self]
  have hG₁0 : G₁ 0 = c := by
    rw [hG₁, compRadialContraction_apply, radialContraction_self, ← hcentre]
  -- The shrinking has derivative the identity at `0`, so the orientations are unchanged.
  have hfderiv (k : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hk : k 0 = p)
      (hkφ : range (k.compRadialContraction ha) ⊆ φ.source) :
      fderiv ℝ ((k.compRadialContraction ha).transChart hφ hkφ) 0 = fderiv ℝ (φ ∘ k) 0 := by
    rw [coe_transChart, coe_compRadialContraction, ← Function.comp_assoc]
    refine fderiv_comp_radialContraction_self 0 _ ?_
    simpa only [hk] using
      (k.contMDiff.mdifferentiableAt (by simp) (x := 0)).differentiableAt_chartAt_comp
  have hdet₁ : 0 < (fderiv ℝ F₁ 0).det * (fderiv ℝ G₁ 0).det := by
    rwa [hfderiv f rfl hf₁φ, hfderiv g hcentre.symm hg₁φ]
  -- Step 3: the Euclidean disc theorem in the chart, confined to the ball.
  obtain ⟨L, hLball, hL0⟩ :=
    F₁.exists_smoothIsotopy_mapsTo_ball hr G₁ hF₁0 hG₁0 (fun x => hF₁ x ▸ (hf₁U x).2)
      (fun x => hG₁ x ▸ (hg₁U x).2) hdet₁
  -- Step 4: carry the confined motion back to `M` through the chart.
  let L' := L.postcomp φ.symm (s := φ.target) (fun q => hball (hLball q))
    (fun y hy => φ.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas hφ hy)
    φ.symm.isOpenEmbedding_restrict.isEmbedding f₁.toContMDiffMap g₁.toContMDiffMap
    (fun x => by simp [hF₁, φ.left_inv (hf₁U x).1])
    (fun x => by simp [hG₁, φ.left_inv (hg₁U x).1])
  have hL' (q : unitInterval × E) : L' q = φ.symm (L q) := SmoothIsotopy.postcomp_apply ..
  -- Step 5: undo the shrinking of the sources.
  refine ⟨((f.compRadialContractionIsotopy ha).trans L' le_rfl).trans
    (g.compRadialContractionIsotopy ha).symm le_rfl, fun t => ?_⟩
  refine SmoothIsotopy.trans_apply_mem (s := {p}) _ _ _ (fun t => ?_) (fun t => ?_) t
  · refine SmoothIsotopy.trans_apply_mem (s := {p}) _ _ _ (fun t => ?_) (fun t => ?_) t
    · rw [mem_singleton_iff, compRadialContractionIsotopy_apply, radialContraction_self]
    · rw [mem_singleton_iff, hL', hL0, φ.left_inv hpφ]
  · rw [mem_singleton_iff, SmoothIsotopy.symm_apply, compRadialContractionIsotopy_apply,
      radialContraction_self, hcentre]

end TauCeti.SmoothEmbedding

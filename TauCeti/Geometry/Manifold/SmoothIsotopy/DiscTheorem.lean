/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Euclidean
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Extension

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
above.

The isotopy extension theorem (`TauCeti.SmoothIsotopy.exists_diffeotopy_final_apply_eq`) turns
this into the ambient form of Palais's disc theorem, used to show that connected sums are well
defined: on every compact subset of `E`, `g` is `f` followed by the final diffeomorphism of a
compactly supported diffeotopy of `M`
(`TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_det_chartAt_mul_pos`). On a connected
oriented manifold the centres can first be made to agree by a compactly supported diffeotopy
(`TauCeti.exists_diffeotopy_final_apply_eq`), which gives the ambient disc theorem for embeddings
with different centres
(`TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_isOrientationPreservingAt`).

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
* `TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_det_chartAt_mul_pos`: the ambient disc
  theorem, for embeddings with a common centre, on compact subsets of `E`.

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

/-- The disc theorem for embeddings that land in a Euclidean ball inside the chart at the centre:
if `f` and `g` both have centre `p`, map into the preimage of a Euclidean ball about `chartAt E p p`
that lies in the target of the chart, and their derivatives read in the chart have determinants of
positive product, then they are smoothly isotopic relative to the centre. -/
private theorem exists_smoothIsotopy_of_mapsTo_chart {p : M} {r : ℝ}
    (hball : Euclidean.ball (chartAt E p p) r ⊆ (chartAt E p).target)
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hf0 : f 0 = p) (hg0 : g 0 = p)
    (hf : ∀ x, f x ∈ (chartAt E p).source ∩ chartAt E p ⁻¹' Euclidean.ball (chartAt E p p) r)
    (hg : ∀ x, g x ∈ (chartAt E p).source ∩ chartAt E p ⁻¹' Euclidean.ball (chartAt E p p) r)
    (hdet : 0 < (fderiv ℝ (chartAt E p ∘ f) 0).det * (fderiv ℝ (chartAt E p ∘ g) 0).det) :
    ∃ G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap, ∀ t : unitInterval, G (t, 0) = p := by
  set φ := chartAt E p
  have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hfφ : range f ⊆ φ.source := range_subset_iff.2 fun x => (hf x).1
  have hgφ : range g ⊆ φ.source := range_subset_iff.2 fun x => (hg x).1
  set F := f.transChart hφ hfφ
  set G := g.transChart hφ hgφ
  have hF (x : E) : F x = φ (f x) := transChart_apply ..
  have hG (x : E) : G x = φ (g x) := transChart_apply ..
  obtain ⟨L, hLball, hL0⟩ := F.exists_smoothIsotopy_mapsTo_ball (c := φ p) (r := r) G
    (by rw [hF, hf0]) (by rw [hG, hg0]) (fun x => hF x ▸ (hf x).2) (fun x => hG x ▸ (hg x).2)
    (by rwa [coe_transChart, coe_transChart])
  let L' := L.postcomp φ.symm (s := φ.target) (fun q => hball (hLball q))
    (fun y hy => φ.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas hφ hy)
    φ.symm.isOpenEmbedding_restrict.isEmbedding f.toContMDiffMap g.toContMDiffMap
    (fun x => by simp [hF, φ.left_inv (hf x).1])
    (fun x => by simp [hG, φ.left_inv (hg x).1])
  refine ⟨L', fun t => ?_⟩
  have hL' : L' (t, 0) = φ.symm (L (t, 0)) := SmoothIsotopy.postcomp_apply ..
  rw [hL', hL0, φ.left_inv (mem_chart_source E p)]

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
  set p := f 0
  set φ := chartAt E p
  have hpφ : p ∈ φ.source := mem_chart_source E p
  -- A Euclidean ball about the centre of the chart, and one about `0` that `f` and `g` map into it.
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Euclidean.ball (φ p) r ⊆ φ.target :=
    Euclidean.nhds_basis_ball.mem_iff.1 (φ.open_target.mem_nhds (φ.map_source hpφ))
  set U := φ.source ∩ φ ⁻¹' Euclidean.ball (φ p) r
  have hU : U ∈ 𝓝 p :=
    (φ.isOpen_inter_preimage Euclidean.isOpen_ball).mem_nhds
      ⟨hpφ, mem_preimage.2 (Euclidean.mem_ball_self (x := φ p) hr)⟩
  obtain ⟨δ, hδ, hδU⟩ : ∃ δ > 0, Euclidean.ball (0 : E) δ ⊆ f ⁻¹' U ∩ g ⁻¹' U :=
    Euclidean.nhds_basis_ball.mem_iff.1 (Filter.inter_mem
      (f.contMDiff.continuous.continuousAt.preimage_mem_nhds hU)
      (g.contMDiff.continuous.continuousAt.preimage_mem_nhds (hcentre ▸ hU)))
  -- Step 1: shrink the source, so that both embeddings land in `U`.
  have ha : (0 : ℝ) ≤ δ⁻¹ ^ 2 := sq_nonneg _
  have hU₁ (k : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hk : ∀ x ∈ Euclidean.ball 0 δ, k x ∈ U)
      (x : E) : k.compRadialContraction le_rfl ha x ∈ U := by
    rw [compRadialContraction_apply]
    exact hk _ (radialContraction_mem_ball 0 x hδ)
  -- The shrinking has derivative the identity at `0`, so the orientations are unchanged.
  have hd (k : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hk : k 0 = p) :
      fderiv ℝ (φ ∘ k.compRadialContraction le_rfl ha) 0 = fderiv ℝ (φ ∘ k) 0 := by
    rw [coe_compRadialContraction, ← Function.comp_assoc]
    refine fderiv_comp_radialContraction_self 0 _ ?_
    simpa only [hk] using
      (k.contMDiff.mdifferentiableAt (by simp) (x := 0)).differentiableAt_chartAt_comp
  -- Step 2: the disc theorem in the chart, for the shrunken embeddings.
  obtain ⟨L, hL0⟩ := exists_smoothIsotopy_of_mapsTo_chart hball
    (f.compRadialContraction le_rfl ha) (g.compRadialContraction le_rfl ha)
    (by rw [compRadialContraction_apply, radialContraction_self])
    (by rw [compRadialContraction_apply, radialContraction_self, ← hcentre])
    (hU₁ f fun x hx => (hδU hx).1) (hU₁ g fun x hx => (hδU hx).2)
    (by rwa [hd f rfl, hd g hcentre.symm])
  -- Step 3: undo the shrinking of the sources.
  refine ⟨((f.compRadialContractionIsotopy le_rfl ha).trans L le_rfl).trans
    (g.compRadialContractionIsotopy le_rfl ha).symm le_rfl, fun t => ?_⟩
  refine SmoothIsotopy.trans_apply_mem (s := {p}) _ _ _ (fun t => ?_) (fun t => ?_) t
  · refine SmoothIsotopy.trans_apply_mem (s := {p}) _ _ _ (fun t => ?_) (fun t => hL0 t) t
    rw [mem_singleton_iff, compRadialContractionIsotopy_apply, radialContraction_self]
  · rw [mem_singleton_iff, SmoothIsotopy.symm_apply, compRadialContractionIsotopy_apply,
      radialContraction_self, hcentre]

/-- **The ambient disc theorem in a manifold.** Let `f` and `g` be smooth embeddings of `E` into a
Hausdorff, σ-compact boundaryless manifold modelled on `E`, with the same centre `f 0 = g 0` and
derivatives at `0` of the same orientation, compared in the chart at the centre. On every compact
subset `A` of `E`, `g` is `f` followed by the final diffeomorphism of a smooth diffeotopy of `M`
fixing every point outside a compact set. -/
theorem exists_diffeotopy_eqOn_of_det_chartAt_mul_pos [T2Space M] [SigmaCompactSpace M]
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hcentre : f 0 = g 0)
    (hdet : 0 < (fderiv ℝ (chartAt E (f 0) ∘ f) 0).det *
      (fderiv ℝ (chartAt E (f 0) ∘ g) 0).det) {A : Set E} (hA : IsCompact A) :
    ∃ Φ : Diffeotopy 𝓘(ℝ, E) ∞ M, ∃ K : Set M, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      EqOn (Φ.final ∘ f) g A := by
  obtain ⟨G, -⟩ := exists_smoothIsotopy_of_det_chartAt_mul_pos f g hcentre hdet
  obtain ⟨Φ, K, hK, hΦK, hΦ⟩ := G.exists_diffeotopy_final_apply_eq (m := ⊤) hA le_top le_top
  exact ⟨Φ, K, hK, hΦK, fun x hx => hΦ x hx⟩

end TauCeti.SmoothEmbedding

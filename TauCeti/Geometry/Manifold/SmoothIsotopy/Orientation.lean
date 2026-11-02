/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.DiscTheorem
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Orientation

/-!
# The disc theorem for oriented embeddings

Two orientation-preserving smooth embeddings of a real normed space into an oriented manifold
of the same dimension, with the same centre, are smoothly isotopic relative to that centre.
Only orientation preservation at the centre is needed. Giving the target the opposite orientation
also covers two orientation-reversing embeddings.

This connects the intrinsic tangent-orientation condition to the chart determinant condition in
`SmoothEmbedding.exists_smoothIsotopy_of_det_chartAt_mul_pos`.

On a connected manifold the centres need not agree: this is the ambient disc theorem of Palais
(`TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_isOrientationPreservingAt`). On every compact
subset of `E`, one orientation-preserving embedding is the other followed by the final
diffeomorphism of a compactly supported diffeotopy. The homogeneity lemma
(`TauCeti.exists_diffeotopy_final_apply_eq`) first moves the centre of the first embedding to the
centre of the second by a compactly supported diffeotopy, whose final diffeomorphism preserves
the orientation (`TauCeti.Diffeotopy.isOrientationPreservingAt_final`); the ambient disc theorem
at a common centre (`TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_det_chartAt_mul_pos`) then
finishes. This is what makes a connected sum independent of its balls.

## Main results

* `TauCeti.SmoothEmbedding.exists_smoothIsotopy_of_isOrientationPreservingAt`: two
  orientation-preserving embeddings with a common centre are isotopic relative to the centre.
* `TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_isOrientationPreservingAt`: on a connected
  manifold, two orientation-preserving embeddings agree on any compact set after an ambient
  compactly supported diffeotopy.
* `TauCeti.SmoothEmbedding.exists_diffeomorph_comp_eventuallyEq`: on a connected manifold, two
  orientation-preserving embeddings agree near the origin after a diffeomorphism.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6, Theorem 6.6.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
-/

public noncomputable section

open Set Metric Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

/-- Two smooth embeddings with a common centre which preserve the chosen orientations at the
origin have derivatives of the same orientation in the chart at the centre. -/
private theorem det_mul_pos_of_isOrientationPreservingAt
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hcentre : f 0 = g 0)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (hf : o.IsOrientationPreservingAt oM f 0)
    (hg : o.IsOrientationPreservingAt oM g 0) :
    0 < (fderiv ℝ (chartAt E (f 0) ∘ f) 0).det * (fderiv ℝ (chartAt E (f 0) ∘ g) 0).det := by
  obtain ⟨ef, hef, hfo⟩ :=
    (Manifold.Orientation.isOrientationPreservingAt_iff o oM f 0).mp hf
  obtain ⟨eg, heg, hgo⟩ :=
    (Manifold.Orientation.isOrientationPreservingAt_iff o oM g 0).mp hg
  have ho : oM.orientationAt (f 0) = oM.orientationAt (g 0) := by rw [hcentre]
  -- Both tangent spaces are represented by the common model E. In that representation,
  -- transport of the source orientation agrees exactly when the determinants have the same sign.
  have hprod := (_root_.Orientation.map_eq_map_iff_det_mul_pos
    (o.orientationAt 0) ef.toLinearEquiv eg.toLinearEquiv o.card_eq).mp
      (hfo.trans (ho.trans hgo.symm))
  rw [← hcentre] at heg
  have hdf := (f.contMDiff.mdifferentiableAt (by simp) (x := 0)).fderiv_chartAt_comp
  have hdg := (g.contMDiff.mdifferentiableAt (by simp) (x := 0)).fderiv_chartAt_comp
  rw [← hcentre] at hdg
  rw [hdf, hdg]
  simpa only [← hef, ← heg] using! hprod

/-- **The oriented common-centre disc theorem.** Two smooth embeddings that preserve the chosen
orientations at the origin and have the same centre are smoothly isotopic relative to that centre.
No orientation condition away from the origin is required. -/
theorem exists_smoothIsotopy_of_isOrientationPreservingAt
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hcentre : f 0 = g 0)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (hf : o.IsOrientationPreservingAt oM f 0)
    (hg : o.IsOrientationPreservingAt oM g 0) :
    ∃ G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap,
      ∀ t : unitInterval, G (t, 0) = f 0 :=
  f.exists_smoothIsotopy_of_det_chartAt_mul_pos g hcentre
    (det_mul_pos_of_isOrientationPreservingAt f g hcentre o oM hf hg)

/-- **The ambient disc theorem for oriented embeddings** (Palais). Let `f` and `g` be smooth
embeddings of `E` into a connected, Hausdorff, σ-compact boundaryless manifold `M` modelled on
`E`, which preserve the orientations `o` of `E` and `oM` of `M` at the origin; their centres
`f 0` and `g 0` may differ. On every compact subset `A` of `E`, `g` is `f` followed by the final
diffeomorphism of a smooth diffeotopy of `M` fixing every point outside a compact set. -/
theorem exists_diffeotopy_eqOn_of_isOrientationPreservingAt [T2Space M] [SigmaCompactSpace M]
    [PreconnectedSpace M] (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (hf : o.IsOrientationPreservingAt oM f 0) (hg : o.IsOrientationPreservingAt oM g 0)
    {A : Set E} (hA : IsCompact A) :
    ∃ Φ : Diffeotopy 𝓘(ℝ, E) ∞ M, ∃ K : Set M, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      EqOn (Φ.final ∘ f) g A := by
  -- Move the centre of `f` to the centre of `g`, by the homogeneity lemma.
  obtain ⟨Ψ, L, hL, hΨL, hΨ⟩ := exists_diffeotopy_final_apply_eq (I := 𝓘(ℝ, E)) (n := ∞)
    (m := ⊤) le_top le_rfl (f 0) (g 0)
  set f' := f.transDiffeomorph Ψ.final
  have hcentre : f' 0 = g 0 := by rw [transDiffeomorph_apply, hΨ]
  -- The moved embedding still preserves the orientations, as the final diffeomorphism does.
  have hf' : o.IsOrientationPreservingAt oM f' 0 := by
    rw [coe_transDiffeomorph]
    exact (Ψ.isOrientationPreservingAt_final (by simp) oM (f 0)).comp hf
  -- The ambient disc theorem at the common centre.
  obtain ⟨Θ, K, hK, hΘK, hΘ⟩ := f'.exists_diffeotopy_eqOn_of_det_chartAt_mul_pos g hcentre
    (det_mul_pos_of_isOrientationPreservingAt f' g hcentre o oM hf' hg) hA
  refine ⟨Ψ.trans Θ, L ∪ K, hL.union hK, fun t y hy => ?_, fun x hx => ?_⟩
  · rw [mem_union, not_or] at hy
    simp [hΨL t hy.1, hΘK t y hy.2]
  · simpa [f'] using hΘ hx

/-- On a connected oriented manifold, two smooth embeddings of `E` which preserve the orientations
`o` of `E` and `oM` of `M` at the origin agree near the origin after a diffeomorphism of `M`. -/
theorem exists_diffeomorph_comp_eventuallyEq [T2Space M] [SigmaCompactSpace M]
    [PreconnectedSpace M] (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (hf : o.IsOrientationPreservingAt oM f 0) (hg : o.IsOrientationPreservingAt oM g 0) :
    ∃ φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M, φ ∘ f =ᶠ[𝓝 0] g := by
  obtain ⟨Φ, -, -, -, hΦ⟩ := f.exists_diffeotopy_eqOn_of_isOrientationPreservingAt g o oM hf hg
    (isCompact_closedBall (0 : E) 1)
  exact ⟨Φ.final, hΦ.eventuallyEq_of_mem (closedBall_mem_nhds 0 one_pos)⟩

end TauCeti.SmoothEmbedding

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.DiscTheorem
public import TauCeti.Geometry.Manifold.Orientation.Preserving

/-!
# The disc theorem for oriented embeddings

Two orientation-preserving smooth embeddings of a real normed space into an oriented manifold
of the same dimension, with the same centre, are smoothly isotopic relative to that centre.
Only orientation preservation at the centre is needed. Giving the target the opposite orientation
also covers two orientation-reversing embeddings.

This connects the intrinsic tangent-orientation condition to the chart determinant condition in
`SmoothEmbedding.exists_smoothIsotopy_of_det_chartAt_mul_pos`. It supplies the oriented
common-centre comparison of open discs used before extending their isotopy to the ambient manifold.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6, Theorem 6.6.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

/-- **The oriented common-centre disc theorem.** Two smooth embeddings that preserve the chosen
orientations at the origin and have the same centre are smoothly isotopic relative to that centre.
No orientation condition away from the origin is required. -/
theorem exists_smoothIsotopy_of_isOrientationPreservingAt
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M) (hcentre : f 0 = g 0)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (hf : o.IsOrientationPreservingAt oM f 0)
    (hg : o.IsOrientationPreservingAt oM g 0) :
    ∃ G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap,
      ∀ t : unitInterval, G (t, 0) = f 0 := by
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
  apply f.exists_smoothIsotopy_of_det_chartAt_mul_pos g hcentre
  rw [← hcentre] at heg
  have hdf := (f.contMDiff.mdifferentiableAt (by simp) (x := 0)).fderiv_chartAt_comp
  have hdg := (g.contMDiff.mdifferentiableAt (by simp) (x := 0)).fderiv_chartAt_comp
  rw [← hcentre] at hdg
  rw [hdf, hdg]
  simpa only [← hef, ← heg] using! hprod

end TauCeti.SmoothEmbedding

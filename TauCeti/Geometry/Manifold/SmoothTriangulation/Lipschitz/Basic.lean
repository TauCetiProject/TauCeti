/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Approximation
public import TauCeti.Analysis.Calculus.MeanValue

import TauCeti.Analysis.Convex.StdSimplex

/-!
# Lipschitz control of secant errors on edgewise faces

On every face of a sufficiently fine edgewise subdivision, the error between a `C¹` map
and its affine interpolant has an arbitrarily small Lipschitz bound, measured in the original
simplex coordinates. The constant is uniform over all subdivided faces, including their
boundaries. No immersion or injectivity hypothesis is needed.

The first-order estimate in `SmoothTriangulation.Approximation` compares derivatives on
geometric directions. Here the directional mean value inequality integrates that estimate
along chords of each face. This supplies the facewise bounds needed to glue a Lipschitz
estimate across a finite closed simplex cover; simplexwise immersion alone does not give
such an estimate.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9 (secant approximation)
  and Theorems 10.5–10.6 (uniqueness and existence of smooth triangulations).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Finset AbstractSimplicialComplex PreAbstractSimplicialComplex Filter
open TauCeti

namespace ContDiffOn

/-- The error of affine interpolation on each face of a sufficiently fine edgewise subdivision
is Lipschitz with arbitrarily small constant in the original simplex coordinates. In the
conclusion, `A` places barycentric coordinates in the original simplex and `B` interpolates
the values of `F` at its vertices. The estimate is uniform over faces and pairs of points,
including boundary points, and does not lose a factor depending on the subdivision scale. -/
theorem eventually_norm_linearCombination_sub_comp_sub_le_edgewiseSubdivision
    {ι E : Type*} [LinearOrder ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {σ : Finset ι} {F : (σ → ℝ) → E}
    (hF : ContDiffOn ℝ 1 F (range fun x : Convexity.StdSimplex ℝ σ => ⇑x.weights))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (K : PreAbstractSimplicialComplex ι)
      (ρ : Finset (K.EdgewiseVertex k)), ρ ∈ K.edgewiseSubdivision k →
      ∀ p : ρ → StandardSimplex σ,
      (∀ a, (p a : ι →₀ ℝ) = edgewisePoint a.1.1) →
      let A := Fintype.linearCombination ℝ (fun (a : ρ) (i : σ) => (p a).1 i)
      let B := Fintype.linearCombination ℝ (fun a : ρ => F (fun i : σ => (p a).1 i))
      ∀ x y : Convexity.StdSimplex ℝ ρ,
        ‖(B ⇑y.weights - F (A ⇑y.weights)) - (B ⇑x.weights - F (A ⇑x.weights))‖ ≤
          ε * ‖A (⇑y.weights - ⇑x.weights)‖ := by
  obtain ⟨F', hFd, _, happrox⟩ :=
    hF.exists_eventually_norm_linearCombination_sub_le_edgewiseSubdivision
  filter_upwards [happrox ε hε] with k hk K ρ hρ p hp
  dsimp only
  intro x y
  let S := range fun z : Convexity.StdSimplex ℝ ρ => ⇑z.weights
  let T := range fun z : Convexity.StdSimplex ℝ σ => ⇑z.weights
  let A : (ρ → ℝ) →L[ℝ] (σ → ℝ) :=
    (Fintype.linearCombination ℝ (fun (a : ρ) (i : σ) => (p a).1 i)).toContinuousLinearMap
  let B : (ρ → ℝ) →L[ℝ] E :=
    (Fintype.linearCombination ℝ (fun a : ρ => F (fun i : σ => (p a).1 i))).toContinuousLinearMap
  have hvertex (a : ρ) : (fun i : σ => (p a).1 i) ∈ T :=
    ⟨Finset.standardSimplexHomeomorph σ (p a),
      funext fun i => Finset.standardSimplexHomeomorph_weights σ (p a) i⟩
  have hconv := Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ
  have hAhull : ∀ z ∈ S, A z ∈ convexHull ℝ (range fun a : ρ => fun i : σ => (p a).1 i) := by
    rintro _ ⟨z, rfl⟩
    exact (convex_convexHull ℝ _).sum_mem (fun a _ => z.weights_nonneg a)
      z.total_of_fintype (fun a _ => subset_convexHull ℝ _ (mem_range_self a))
  have hmap : MapsTo A S T := fun z hz =>
    convexHull_min (range_subset_iff.mpr hvertex) hconv (hAhull z hz)
  have hd : ∀ z ∈ S, HasFDerivWithinAt (fun w => B w - F (A w))
      (B - (F' (A z)).comp A) S z := by
    intro z hz
    exact B.hasFDerivWithinAt.sub
      ((hFd _ (hmap hz)).comp z A.hasFDerivWithinAt hmap)
  have hsum : ∑ a : ρ, (y.weights a - x.weights a) = 0 := by
    rw [Finset.sum_sub_distrib, y.total_of_fintype, x.total_of_fintype, sub_self]
  have hbound : ∀ z ∈ segment ℝ (⇑x.weights) (⇑y.weights),
      ‖(B - (F' (A z)).comp A) (⇑y.weights - ⇑x.weights)‖ ≤
        ε * ‖A (⇑y.weights - ⇑x.weights)‖ := by
    intro z hz
    have hzS := (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ ρ).segment_subset
      (mem_range_self x) (mem_range_self y) hz
    simpa only [A, B, sub_apply, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', Fintype.linearCombination_apply, Pi.sub_apply] using
      hk K ρ hρ p hp (A z) (hAhull z hzS) (⇑y.weights - ⇑x.weights) hsum
  simpa only [A, B, LinearMap.coe_toContinuousLinearMap'] using
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_apply_le
      (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ ρ) hd hbound
        (mem_range_self x) (mem_range_self y)

end ContDiffOn

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Approximation
public import TauCeti.Analysis.Calculus.MeanValue
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Edgewise

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

## Main results

* `ContDiffOn.eventually_norm_linearCombination_sub_comp_sub_le_edgewiseSubdivision`: the
  estimate for a single `C¹` map on a simplex, over all faces of fine edgewise subdivisions.
* `TauCeti.eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision_faceInclusion`: for a map of
  a complex on a finite vertex type which is `C¹` on every closed simplex, the difference between
  its secant map on a fine edgewise subdivision and the map itself is `ε`-Lipschitz on every
  closed simplex of the subdivision, in the original coordinates.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9 (secant approximation)
  and Theorems 10.5–10.6 (uniqueness and existence of smooth triangulations).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Finset AbstractSimplicialComplex PreAbstractSimplicialComplex Filter TauCeti.SetLike
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

namespace TauCeti

variable {ι E : Type*} [LinearOrder ι] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {f : Realization K → E}

/-- On the closed simplices of every sufficiently fine edgewise subdivision, the secant error
`s - f ∘ φ` of a map `f` which is `C¹` on every closed simplex is `ε`-Lipschitz in the original
coordinates. Here `s` is the secant map of `f` on the subdivision, `φ` is the canonical map onto
`|K|`, and being `C¹` on a closed simplex means being, in barycentric coordinates, the restriction
of a map which is `C¹` within the standard simplex. -/
theorem eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision_faceInclusion
    (hf : ∀ σ : Face K, ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (ρ : Face (K.edgewiseSubdivision k)) (x y : StandardSimplex ρ.1),
      ‖((K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)
              (faceInclusion _ ρ y) -
            f (edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ y))) -
          ((K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)
              (faceInclusion _ ρ x) -
            f (edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ x)))‖ ≤
        ε * ‖((edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ y)).1 : ι → ℝ) -
          (edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ x)).1‖ := by
  have : Finite (Face K) := (Set.toFinite K.faces).to_subtype
  choose F hFg hF using hf
  filter_upwards [eventually_all.mpr fun σ : Face K =>
    (hF σ).eventually_norm_linearCombination_sub_comp_sub_le_edgewiseSubdivision hε]
    with k hk ρ x y
  -- The simplex `ρ` lies in the face `σ` of `K` spanned by the entries of its vertices.
  let σ : Face K := ⟨_, biUnion_image_mem_of_mem_edgewiseSubdivision ρ.2⟩
  have hρσ : ∀ u ∈ ρ.1, ∀ l, u.1 l ∈ σ.1 := fun u hu l =>
    Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩
  let w (t : StandardSimplex ρ.1) := ⇑(Finset.standardSimplexHomeomorph ρ.1 t).weights
  have hφ (t : StandardSimplex ρ.1) :
      edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ t) =
        faceInclusion K σ (edgewiseSubdivisionFaceMap hρσ t) :=
    congrFun (edgewiseSubdivisionRealizationMap_comp_faceInclusion ρ σ hρσ) t
  -- In the coordinates of `σ`, the vertices of `ρ` combine to the image of `t`.
  have hA (t : StandardSimplex ρ.1) :
      Fintype.linearCombination ℝ (fun (a : ρ.1) (i : σ.1) => (edgewiseVertexPoint hρσ a).1 i)
        (w t) = fun i : σ.1 => (edgewiseSubdivisionFaceMap hρσ t).1 i := by
    funext i
    rw [Fintype.linearCombination_apply, edgewiseSubdivisionFaceMap_apply, Finset.sum_apply,
      ← Finset.sum_coe_sort ρ.1]
    simp [w, Finset.standardSimplexHomeomorph_weights]
  have hB (t : StandardSimplex ρ.1) :
      Fintype.linearCombination ℝ
          (fun a : ρ.1 => F σ fun i : σ.1 => (edgewiseVertexPoint hρσ a).1 i) (w t) -
        F σ (Fintype.linearCombination ℝ
          (fun (a : ρ.1) (i : σ.1) => (edgewiseVertexPoint hρσ a).1 i) (w t)) =
        (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)
            (faceInclusion _ ρ t) -
          f (edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ t)) := by
    rw [hA, hFg, secantMap_faceInclusion_edgewiseSubdivision f ρ σ hρσ, hφ,
      Fintype.linearCombination_apply]
    simp only [hFg, w, Finset.standardSimplexHomeomorph_weights, Function.comp_apply]
  have h := hk σ K.toPreAbstractSimplicialComplex ρ.1 ρ.2 (edgewiseVertexPoint hρσ)
    (coe_edgewiseVertexPoint hρσ) (Finset.standardSimplexHomeomorph ρ.1 x)
    (Finset.standardSimplexHomeomorph ρ.1 y)
  rw [hB, hB, map_sub, hA, hA] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hε.le)
  rw [hφ, hφ, faceInclusion_val, faceInclusion_val]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact norm_le_pi_norm (((edgewiseSubdivisionFaceMap hρσ y).1 : ι → ℝ) -
    ((edgewiseSubdivisionFaceMap hρσ x).1 : ι → ℝ)) i.1

end TauCeti

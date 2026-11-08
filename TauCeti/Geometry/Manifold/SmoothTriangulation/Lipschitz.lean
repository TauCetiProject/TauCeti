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
import TauCeti.Analysis.Convex.Lipschitz
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates

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
* `TauCeti.eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision`: the same difference is
  `ε`-Lipschitz on the whole subdivision, also between points of different simplices.

## Implementation notes

The cross-face bound glues the facewise bounds across the simplices of the subdivision on each
closed simplex of `K`. It then passes between two closed simplices of `K` through a common
nearby point given by `AbstractSimplicialComplex.exists_mem_inter_range_standardSimplex_coe`;
distant pairs are handled by the uniform convergence of the secant maps.

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

/-- The secant error of `f` on the `k`-th edgewise subdivision: the difference between the secant
map of `f` and `f`, read on the subdivision through the canonical map onto `|K|`. -/
private noncomputable def secantError (f : Realization K → E) (k : ℕ)
    (x : Realization (K.edgewiseSubdivision k)) : E :=
  (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) x -
    f (edgewiseSubdivisionRealizationMap K k x)

omit [Fintype ι] in
/-- Unfolding the secant error, used to fold the public statements into `secantError`. -/
private theorem secantError_apply (f : Realization K → E) (k : ℕ)
    (x : Realization (K.edgewiseSubdivision k)) :
    secantError f k x =
      (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) x -
        f (edgewiseSubdivisionRealizationMap K k x) :=
  rfl

/-- The secant error, read as a function of the original coordinates `ι → ℝ` (and extended by
zero off the realization). -/
private noncomputable def secantErrorCoord (f : Realization K → E) (k : ℕ) : (ι → ℝ) → E :=
  Function.extend
    (fun x : Realization (K.edgewiseSubdivision k) =>
      ((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ))
    (secantError f k) 0

omit [Fintype ι] in
/-- The secant error read in the original coordinates is the secant error. -/
private theorem secantErrorCoord_apply (f : Realization K → E) (k : ℕ)
    (x : Realization (K.edgewiseSubdivision k)) :
    secantErrorCoord f k ((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ) =
      secantError f k x :=
  Function.Injective.extend_apply (fun _ _ h => edgewiseSubdivisionRealizationMap_injective
    (Subtype.ext (DFunLike.coe_injective h))) _ _ x

/-- A Lipschitz bound for the secant error on the closed simplices of the edgewise subdivision
holds on every closed simplex of `K`, in the original coordinates. -/
private theorem lipschitzOnWith_secantErrorCoord {k : ℕ} (hk : k ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hface : ∀ (ρ : Face (K.edgewiseSubdivision k)) (x y : StandardSimplex ρ.1),
      ‖secantError f k (faceInclusion _ ρ y) - secantError f k (faceInclusion _ ρ x)‖ ≤
        ε * ‖((edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ y)).1 : ι → ℝ) -
          (edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ x)).1‖)
    (σ : Face K) :
    LipschitzOnWith (Real.toNNReal ε) (secantErrorCoord f k)
      (range fun x : StandardSimplex σ.1 => (x.1 : ι → ℝ)) := by
  have : Finite (K.EdgewiseVertex k) := Finite.of_injective Subtype.val Subtype.val_injective
  have : Finite (Face (K.edgewiseSubdivision k)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  refine (convex_range_standardSimplex_coe σ.1).lipschitzOnWith_of_finite_closed_cover
    (fun ρ : Face (K.edgewiseSubdivision k) =>
      convexHull ℝ (range fun a : ρ.1 => (edgewisePoint a.1.1 : ι → ℝ)))
    (fun ρ => ((finite_range _).isCompact_convexHull (𝕜 := ℝ)).isClosed) (fun z hz => ?_)
    (fun ρ => LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_)
  · obtain ⟨t, rfl⟩ := hz
    rw [iUnion_convexHull_range_edgewisePoint K hk]
    exact ⟨faceInclusion K σ t, congrArg DFunLike.coe (faceInclusion_val K σ t)⟩
  · rw [← range_edgewiseSubdivisionRealizationMap_faceInclusion] at hz hz'
    obtain ⟨t, rfl⟩ := hz.2
    obtain ⟨t', rfl⟩ := hz'.2
    rw [dist_eq_norm, dist_eq_norm, secantErrorCoord_apply, secantErrorCoord_apply,
      Real.coe_toNNReal _ hε]
    exact hface ρ t' t

/-- On every sufficiently fine edgewise subdivision, the secant error `s - f ∘ φ` of a
map `f` which is `C¹` on every closed simplex is `ε`-Lipschitz in the original coordinates, also
between points of different simplices. Here `s` is the secant map of `f` on the subdivision, `φ`
is the canonical map onto `|K|`, and being `C¹` on a closed simplex means being, in barycentric
coordinates, the restriction of a map which is `C¹` within the standard simplex. -/
theorem eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision
    (hf : ∀ σ : Face K, ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x y : Realization (K.edgewiseSubdivision k),
      ‖((K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) x -
            f (edgewiseSubdivisionRealizationMap K k x)) -
          ((K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) y -
            f (edgewiseSubdivisionRealizationMap K k y))‖ ≤
        ε * ‖((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ) -
          (edgewiseSubdivisionRealizationMap K k y).1‖ := by
  have hfc : Continuous f := continuous_iff_faceInclusion.2 fun σ => by
    obtain ⟨F, hFg, hF⟩ := hf σ
    exact Finset.continuous_of_continuousOn_coordinates hFg hF.continuousOn
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  filter_upwards [eventually_ne_atTop 0,
    eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision_faceInclusion hf
      (ε := ε / (2 * N + 1)) (by positivity),
    hfc.eventually_norm_secantMap_sub_lt_edgewiseSubdivision (Set.toFinite K.faces)
      (ε := ε / (2 * (N + 1))) (by positivity)] with k hk hface hclose x y
  rw [← secantError_apply, ← secantError_apply]
  set c := fun x : Realization (K.edgewiseSubdivision k) =>
    ((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ)
  have hmem (x : Realization (K.edgewiseSubdivision k)) :
      c x ∈ range fun t : StandardSimplex (carrier K (edgewiseSubdivisionRealizationMap K k x)).1 =>
        (t.1 : ι → ℝ) :=
    ⟨⟨_, mem_convexHull_carrier K _⟩, rfl⟩
  by_cases hnear : N * ‖c x - c y‖ < 1
  · -- Nearby points: pass through a common point `z` of the two closed simplices of `K`.
    obtain ⟨z, hz, -, -, hyz, -⟩ := exists_mem_inter_range_standardSimplex_coe (hmem x) (hmem y)
      hnear
    have hx := (lipschitzOnWith_secantErrorCoord hk (by positivity) hface _).dist_le_mul
      (c x) (hmem x) z hz.1
    have hy := (lipschitzOnWith_secantErrorCoord hk (by positivity) hface _).dist_le_mul
      z hz.2 (c y) (hmem y)
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm] at hx hy
    rw [secantErrorCoord_apply] at hx hy
    have hxz : ‖c x - z‖ ≤ ‖c x - c y‖ + ‖c y - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hzy : ‖z - c y‖ = ‖c y - z‖ := norm_sub_rev _ _
    have hε' : ε / (2 * N + 1) * (2 * N + 1) = ε := div_mul_cancel₀ _ (by positivity)
    calc ‖secantError f k x - secantError f k y‖
        ≤ ‖secantError f k x - secantErrorCoord f k z‖ +
          ‖secantErrorCoord f k z - secantError f k y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε / (2 * N + 1) * (‖c x - c y‖ + 2 * ‖c y - z‖) := by nlinarith
      _ ≤ ε / (2 * N + 1) * ((2 * N + 1) * ‖c x - c y‖) := by gcongr; nlinarith
      _ = ε * ‖c x - c y‖ := by rw [← mul_assoc, hε']
  · -- Distant points: both secant errors are uniformly small.
    have hfar : 1 ≤ (N + 1) * ‖c x - c y‖ := by nlinarith [norm_nonneg (c x - c y)]
    calc ‖secantError f k x - secantError f k y‖
        ≤ ‖secantError f k x‖ + ‖secantError f k y‖ := norm_sub_le _ _
      _ ≤ ε / (2 * (N + 1)) + ε / (2 * (N + 1)) := add_le_add (hclose x).le (hclose y).le
      _ = ε / (N + 1) * 1 := by field_simp; ring
      _ ≤ ε / (N + 1) * ((N + 1) * ‖c x - c y‖) := by gcongr
      _ = ε * ‖c x - c y‖ := by field_simp

end TauCeti

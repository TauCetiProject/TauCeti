/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Lipschitz.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Lipschitz
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Secant
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite

/-!
# Global secant-error bounds on a simplex

For a map which is `C¹` within a closed simplex, the error of its secant interpolant on
fine edgewise subdivisions has arbitrarily small Lipschitz constant on the entire original
simplex. The estimate compares points in different subdivided faces as well as points in
one face, using distances in the original barycentric coordinates.

The facewise derivative estimate is integrated in `Lipschitz.Basic`. Here the geometric
closed-cover theorem combines those estimates without increasing the constant. This is the
error bound used to preserve separation of embedded simplices under secant approximation.
No immersion, injectivity, or completeness assumption is needed for the error estimate.

The construction combines
`ContDiffOn.eventually_norm_linearCombination_sub_comp_sub_le_edgewiseSubdivision` with
`TauCeti.lipschitzOnWith_stdSimplex_of_edgewiseSubdivision`. The embedding consequence uses
Mathlib's `AntilipschitzWith.add_sub_lipschitzWith` to preserve the original separation bound.

## Main results

* `ContDiffOn.eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision`: the global error bound.
* `ContDiffOn.eventually_isClosedEmbedding_secantMap_edgewiseSubdivision`: secant embeddings
  for maps with a quantitative separation bound on the original simplex.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9.
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public noncomputable section

open Set Finset Function Filter AbstractSimplicialComplex PreAbstractSimplicialComplex
open TauCeti TauCeti.SetLike
open scoped NNReal

namespace ContDiffOn

variable {ι E : Type*} [LinearOrder ι] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Both estimates use the original barycentric metric, rather than the metric on the
-- increasingly large set of subdivision vertices.
private def subdivisionCoordinates {k : ℕ} (hk : k ≠ 0) :
    Realization ((⊤ : AbstractSimplicialComplex ι).edgewiseSubdivision k) ≃ₜ
      range (fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights) :=
  (edgewiseSubdivisionRealizationHomeomorph ⊤ hk).trans
    (((⊤ : AbstractSimplicialComplex ι).realizationHomeomorphRange (Set.toFinite _)).trans
      (Homeomorph.setCongr range_realization_coe_top))

private theorem subdivisionCoordinates_apply_val {k : ℕ} (hk : k ≠ 0)
    (x : Realization ((⊤ : AbstractSimplicialComplex ι).edgewiseSubdivision k)) :
    (subdivisionCoordinates hk x).1 =
      ((edgewiseSubdivisionRealizationMap ⊤ k x).1 : ι → ℝ) := by
  -- `setCongr` changes only the subtype proof, so the transported coordinate is unchanged.
  have hcast : ∀ z, ((Homeomorph.setCongr
      (range_realization_coe_top (ι := ι))) z).1 = z.1 := fun _ => rfl
  simp only [subdivisionCoordinates, Homeomorph.trans_apply, hcast,
    coe_realizationHomeomorphRange_apply, edgewiseSubdivisionRealizationHomeomorph_apply]

private theorem subdivisionCoordinates_symm_apply_val {k : ℕ} (hk : k ≠ 0)
    (z : range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights) :
    ((edgewiseSubdivisionRealizationMap ⊤ k ((subdivisionCoordinates hk).symm z)).1 :
      ι → ℝ) = z.1 :=
  (subdivisionCoordinates_apply_val hk _).symm.trans
    (congrArg Subtype.val ((subdivisionCoordinates hk).apply_symm_apply z))

-- Reindex the existing finite-face estimate along the full vertex set. This keeps the
-- auxiliary finset subtype out of the global estimate's interface.
private theorem eventually_norm_error_sub_le
    (K : AbstractSimplicialComplex ι) {F : (ι → ℝ) → E}
    (hF : ContDiffOn ℝ 1 F (range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ ρ : Face (K.edgewiseSubdivision k),
      let A := Fintype.linearCombination ℝ
        (fun a : ρ.1 => (edgewisePoint a.1.1 : ι → ℝ))
      let B := Fintype.linearCombination ℝ
        (fun a : ρ.1 => F (edgewisePoint a.1.1 : ι → ℝ))
      ∀ x y : Convexity.StdSimplex ℝ ρ.1,
        ‖(B ⇑y.weights - F (A ⇑y.weights)) - (B ⇑x.weights - F (A ⇑x.weights))‖ ≤
          ε * ‖A (⇑y.weights - ⇑x.weights)‖ := by
  let σ : Finset ι := univ
  let e : σ ≃ ι := Equiv.subtypeUnivEquiv mem_univ
  let L := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : ι => ℝ) e
  have hL_apply (v : σ → ℝ) (i : ι) : L v i = v ⟨i, mem_univ i⟩ :=
    Equiv.piCongrLeft_apply_apply (fun _ : ι => ℝ) e v ⟨i, mem_univ i⟩
  have hmap : MapsTo L (range fun x : Convexity.StdSimplex ℝ σ => ⇑x.weights)
      (range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights) := by
    rintro _ ⟨x, rfl⟩
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    refine ⟨mem_iInter.mpr fun i => ?_, ?_⟩
    · exact x.weights_nonneg ⟨i, mem_univ i⟩
    · simpa [hL_apply, σ] using x.total_of_fintype
  have hFL := hF.comp L.contDiff.contDiffOn hmap
  filter_upwards [hFL.eventually_norm_linearCombination_sub_comp_sub_le_edgewiseSubdivision hε]
    with k hk ρ
  dsimp only
  intro x y
  let p : ρ.1 → StandardSimplex σ := fun a => ⟨edgewisePoint a.1.1,
    by
      simpa only [Finset.coe_image] using edgewisePoint_mem_convexHull
        (a.1.ne_zero) (fun _ => mem_univ _)⟩
  have hnorm (v : σ → ℝ) : ‖v‖ = ‖L v‖ := by
    -- The linear and isometric versions share the same underlying `Equiv.piCongrLeft`.
    exact ((IsometryEquiv.piCongrLeft (Y := fun _ : ι => ℝ) e).isometry.norm_map_of_map_zero
      (by ext; rfl) v).symm
  have h := hk K.toPreAbstractSimplicialComplex ρ.1 ρ.2 p (fun _ => rfl) x y
  have hL (v : ρ.1 → ℝ) :
      L (∑ a : ρ.1, v a • fun i : σ => (p a).1 i) =
        ∑ a : ρ.1, v a • (edgewisePoint a.1.1 : ι → ℝ) := by
    ext i
    simp [hL_apply, p]
  have hLp (a : ρ.1) : L (fun i : σ => (p a).1 i) =
      (edgewisePoint a.1.1 : ι → ℝ) := by
    ext i
    simp [hL_apply, p]
  have herror (v : ρ.1 → ℝ) :
      (∑ a : ρ.1, v a • (F ∘ L) (fun i : σ => (p a).1 i)) -
        (F ∘ L) (∑ a : ρ.1, v a • fun i : σ => (p a).1 i) =
      (∑ a : ρ.1, v a • F (edgewisePoint a.1.1 : ι → ℝ)) -
        F (∑ a : ρ.1, v a • (edgewisePoint a.1.1 : ι → ℝ)) := by
    simp only [Function.comp_apply, hL, hLp]
  simpa only [Fintype.linearCombination_apply, herror, hnorm, hL] using h

/-- The error of the secant interpolant on fine edgewise subdivisions of a closed simplex
has arbitrarily small Lipschitz constant on the whole original simplex. The two points may
lie in different subdivided faces. Distances are measured in the original barycentric
coordinates, and no immersion or injectivity assumption is needed. -/
theorem eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision
    {F : (ι → ℝ) → E}
    (hF : ContDiffOn ℝ 1 F (range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      let K : AbstractSimplicialComplex ι := ⊤
      let f : Realization K → E := fun x => F (x.1 : ι → ℝ)
      let q := edgewiseSubdivisionRealizationMap K k
      let s := (K.edgewiseSubdivision k).secantMap (f ∘ q)
      ∀ x y, ‖(s x - f (q x)) - (s y - f (q y))‖ ≤
        ε * ‖((q x).1 : ι → ℝ) - ((q y).1 : ι → ℝ)‖ := by
  classical
  filter_upwards [eventually_ne_atTop 0,
    eventually_norm_error_sub_le (⊤ : AbstractSimplicialComplex ι) hF hε]
    with k hk hface
  dsimp only
  let f : Realization (⊤ : AbstractSimplicialComplex ι) → E := fun x => F (x.1 : ι → ℝ)
  let q := edgewiseSubdivisionRealizationMap (⊤ : AbstractSimplicialComplex ι) k
  let s := ((⊤ : AbstractSimplicialComplex ι).edgewiseSubdivision k).secantMap (f ∘ q)
  let d := subdivisionCoordinates (ι := ι) hk
  let S := range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights
  -- Transport the secant map to the original simplex before gluing the facewise bounds.
  let g : (ι → ℝ) → E := fun z => if hz : z ∈ S then s (d.symm ⟨z, hz⟩) else 0
  have hmem (z : Realization ((⊤ : AbstractSimplicialComplex ι).edgewiseSubdivision k)) :
      ((q z).1 : ι → ℝ) ∈ S := by
    dsimp only [S]
    rw [← range_realization_coe_top]
    exact mem_range_self (q z)
  have hg (z : Realization ((⊤ : AbstractSimplicialComplex ι).edgewiseSubdivision k)) :
      g ((q z).1 : ι → ℝ) = s z := by
    have hz : (⟨((q z).1 : ι → ℝ), hmem z⟩ : S) = d z :=
      Subtype.ext (subdivisionCoordinates_apply_val hk z).symm
    simp only [g, dite_eq_left (hmem z), hz, Homeomorph.symm_apply_apply]
  have hLip : LipschitzOnWith (NNReal.mk ε hε.le) (fun z => g z - F z)
      (range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights) := by
    apply lipschitzOnWith_stdSimplex_of_edgewiseSubdivision hk
    intro ρ
    rw [← range_edgewiseSubdivisionRealizationMap_faceInclusion ρ]
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    -- Identify the geometric coordinates and the secant values separately on this face.
    have hcoords (z : StandardSimplex ρ.1) :
        (∑ a : ρ.1, z.1 a • (edgewisePoint a.1.1 : ι → ℝ)) =
          ((q (faceInclusion _ ρ z)).1 : ι → ℝ) := by
      ext i
      have hsupp : z.1 ∈ Finsupp.supported ℝ ℝ
          (↑ρ.1 : Set ((⊤ : AbstractSimplicialComplex ι).EdgewiseVertex k)) :=
        (Finsupp.mem_supported ℝ z.1).mpr (StandardSimplex.support_subset z)
      simp only [q, edgewiseSubdivisionRealizationMap_val, faceInclusion_val,
        Finsupp.linearCombination_apply_of_mem_supported ℝ hsupp,
        Finset.sum_apply', Finset.sum_apply, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_coe_sort ρ.1 fun a => z.1 a * edgewisePoint a.1 i
    have hsecant (z : StandardSimplex ρ.1) :
        (∑ a : ρ.1, z.1 a • F (edgewisePoint a.1.1 : ι → ℝ)) =
          s (faceInclusion _ ρ z) := by
      simp [s, secantMap_faceInclusion, f, q]
    have herror (z : StandardSimplex ρ.1) :
        (∑ a : ρ.1, z.1 a • F (edgewisePoint a.1.1 : ι → ℝ)) -
          F (∑ a : ρ.1, z.1 a • (edgewisePoint a.1.1 : ι → ℝ)) =
        g ((q (faceInclusion _ ρ z)).1 : ι → ℝ) -
          F ((q (faceInclusion _ ρ z)).1 : ι → ℝ) := by
      rw [hcoords, hsecant, hg]
    have h := hface ρ (Finset.standardSimplexHomeomorph ρ.1 y)
      (Finset.standardSimplexHomeomorph ρ.1 x)
    rw [map_sub] at h
    simp only [Fintype.linearCombination_apply, Finset.standardSimplexHomeomorph_weights] at h
    rw [herror, herror, hcoords, hcoords] at h
    simpa only [dist_eq_norm, NNReal.coe_mk] using h
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_mk, hg, s, f, q] using
    hLip.dist_le_mul _ (hmem x) _ (hmem y)

/-- An anti-Lipschitz `C¹` map on a closed simplex has closed embedded secant interpolants
on every sufficiently fine edgewise subdivision. The separation assumption is on the
whole original simplex, and the conclusion rules out collisions across subdivided faces. -/
theorem eventually_isClosedEmbedding_secantMap_edgewiseSubdivision
    {F : (ι → ℝ) → E} {C : ℝ≥0}
    (hF : ContDiffOn ℝ 1 F (range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights))
    (hsep : AntilipschitzWith C
      ((range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights).domRestrict F)) :
    ∀ᶠ k in atTop,
      let K : AbstractSimplicialComplex ι := ⊤
      let f : Realization K → E := fun x => F (x.1 : ι → ℝ)
      Topology.IsClosedEmbedding ((K.edgewiseSubdivision k).secantMap
        (f ∘ edgewiseSubdivisionRealizationMap K k)) := by
  have hsep' : AntilipschitzWith (C + 1)
      ((range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights).domRestrict F) := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => (hsep.le_mul_dist x y).trans ?_
    exact mul_le_mul_of_nonneg_right (by simp) dist_nonneg
  have hC : 0 < C + 1 := by positivity
  let δ : ℝ≥0 := (C + 1)⁻¹ / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : δ < (C + 1)⁻¹ := by dsimp [δ]; exact half_lt_self (inv_pos.mpr hC)
  filter_upwards [eventually_ne_atTop 0,
    hF.eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision (NNReal.coe_pos.mpr hδ)]
    with k hk herror
  dsimp only at herror ⊢
  let K : AbstractSimplicialComplex ι := ⊤
  let q := edgewiseSubdivisionRealizationMap K k
  let f : Realization K → E := fun x => F (x.1 : ι → ℝ)
  let s := (K.edgewiseSubdivision k).secantMap (f ∘ q)
  let e := edgewiseSubdivisionRealizationHomeomorph K hk
  let d := subdivisionCoordinates (ι := ι) hk
  let A := (range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights).domRestrict F
  let B := s ∘ d.symm
  have hcoords (x) : ((q (d.symm x)).1 : ι → ℝ) = x.1 :=
    subdivisionCoordinates_symm_apply_val hk x
  have herror_coords (x) : s (d.symm x) - f (q (d.symm x)) = (B - A) x := by
    simp only [Pi.sub_apply, B, A, Function.comp_apply, Set.domRestrict_apply, f, hcoords]
  have hLip : LipschitzWith δ (B - A) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := herror (d.symm x) (d.symm y)
    rw [herror_coords, herror_coords, hcoords, hcoords] at h
    simpa only [dist_eq_norm, Subtype.dist_eq] using h
  have hB : Injective B := (hsep'.add_sub_lipschitzWith hLip hsmall).injective
  have hs : Injective s := by
    intro x y hxy
    apply d.injective
    apply hB
    simpa only [B, Function.comp_apply, Homeomorph.symm_apply_apply] using hxy
  let : CompactSpace (Realization K) := K.compactSpace_realization_of_finite_faces (Set.toFinite _)
  let : CompactSpace (Realization (K.edgewiseSubdivision k)) := e.symm.compactSpace
  exact (continuous_secantMap _).isClosedEmbedding hs

end ContDiffOn

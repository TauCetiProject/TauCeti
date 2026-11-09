/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Lipschitz.Basic
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Secant
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite

/-!
# Secant embeddings from quantitative separation

A `C¹` map on a closed simplex with a quantitative separation bound has closed embedded
secant interpolants on every sufficiently fine edgewise subdivision. The separation assumption
uses the original barycentric metric and rules out collisions across subdivided faces.

The global secant-error estimate is provided by
`TauCeti.eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision` in `Lipschitz.Basic`,
which also applies to arbitrary complexes on finite vertex types. Here its hypotheses are
obtained by restricting the original map to each face. Mathlib's
`AntilipschitzWith.add_sub_lipschitzWith` preserves separation under the resulting small error.
No immersion or completeness assumption is needed.

## Main results

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
  classical
  let f₀ : Realization (⊤ : AbstractSimplicialComplex ι) → E := fun x => F (x.1 : ι → ℝ)
  -- Extend face coordinates by zero to restrict the original map to every closed face.
  have hC1 (σ : Face (⊤ : AbstractSimplicialComplex ι)) :
      ∃ G : (σ.1 → ℝ) → E,
        (∀ x : StandardSimplex σ.1, G (fun a => x.1 a) = f₀ (faceInclusion ⊤ σ x)) ∧
          ContDiffOn ℝ 1 G (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights) := by
    let L := (Function.ExtendByZero.linearMap ℝ ℝ (Subtype.val : σ.1 → ι)).toContinuousLinearMap
    have hL (x : StandardSimplex σ.1) : L (fun a => x.1 a) = (x.1 : ι → ℝ) := by
      ext i
      by_cases hi : i ∈ σ.1
      · exact Subtype.val_injective.extend_apply (fun a : σ.1 => x.1 a) 0 ⟨i, hi⟩
      · rw [show L (fun a => x.1 a) i = 0 from
          Function.extend_apply' _ _ _ (by simpa using hi)]
        exact (Finsupp.notMem_support_iff.mp
          (fun h => hi (StandardSimplex.support_subset x h))).symm
    have hmap : MapsTo L (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights)
        (range fun t : Convexity.StdSimplex ℝ ι => ⇑t.weights) := by
      rw [← Finset.range_standardSimplex_coordinates]
      rintro _ ⟨x, rfl⟩
      rw [hL, ← range_realization_coe_top]
      exact ⟨faceInclusion ⊤ σ x, rfl⟩
    exact ⟨F ∘ L, fun x => congrArg F (hL x), hF.comp L.contDiff.contDiffOn hmap⟩
  have hsep' : AntilipschitzWith (C + 1)
      ((range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights).domRestrict F) := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => (hsep.le_mul_dist x y).trans ?_
    exact mul_le_mul_of_nonneg_right (by simp) dist_nonneg
  have hC : 0 < C + 1 := by positivity
  let δ : ℝ≥0 := (C + 1)⁻¹ / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : δ < (C + 1)⁻¹ := by dsimp [δ]; exact half_lt_self (inv_pos.mpr hC)
  filter_upwards [eventually_ne_atTop 0,
    TauCeti.eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision hC1
      (NNReal.coe_pos.mpr hδ)]
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Lipschitz.Basic
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Secant
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite

/-!
# Secant embeddings from quantitative separation

A map of a complex on a finite vertex type which is `C¹` on every closed simplex and satisfies a
quantitative separation bound in barycentric coordinates has closed embedded secant
interpolants on every sufficiently fine edgewise subdivision. The separation assumption uses the
original barycentric metric and rules out collisions across subdivided faces.

The global secant-error estimate is provided by
`TauCeti.eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision` in `Lipschitz.Basic`.
Mathlib's `AntilipschitzWith.add_sub_lipschitzWith` preserves separation under the resulting
small error. No immersion or completeness assumption is needed.

## Main results

* `TauCeti.exists_pos_eventually_norm_sub_le_mul_norm_secantMap_sub_of_antilipschitzWith`: the
  secant maps of an anti-Lipschitz map on fine edgewise subdivisions are anti-Lipschitz, with a
  constant independent of the subdivision.
* `TauCeti.eventually_isClosedEmbedding_secantMap_edgewiseSubdivision_of_antilipschitzWith`:
  these secant maps are closed embeddings.
* `ContDiffOn.eventually_isClosedEmbedding_secantMap_edgewiseSubdivision`: secant embeddings
  for `C¹` maps with a quantitative separation bound on the original simplex.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9.
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public noncomputable section

open Set Finset Function Filter AbstractSimplicialComplex PreAbstractSimplicialComplex
open TauCeti TauCeti.SetLike
open scoped NNReal

namespace TauCeti

variable {ι E : Type*} [LinearOrder ι] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {f : Realization K → E}

/-- **Secant maps of anti-Lipschitz maps are uniformly anti-Lipschitz.** Let `f` be a map of the
realization of a complex on a finite vertex type which is `C¹` on every closed simplex and
anti-Lipschitz in barycentric coordinates. There is a constant `C'` such that for all
sufficiently large `k`, the secant map `s` of `f` on the `k`-th edgewise subdivision satisfies
`‖x - y‖ ≤ C' * ‖s x - s y‖` for all points `x` and `y` of the subdivision, where `‖x - y‖` is
the distance of their images in the barycentric coordinates of `|K|`. The constant does not
depend on `k`. -/
theorem exists_pos_eventually_norm_sub_le_mul_norm_secantMap_sub_of_antilipschitzWith
    (hf : ∀ σ : Face K, ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights))
    {C : ℝ≥0}
    (hanti : AntilipschitzWith C (f ∘ (K.realizationHomeomorphRange (Set.toFinite K.faces)).symm)) :
    ∃ C' > 0, ∀ᶠ k in atTop, ∀ x y : Realization (K.edgewiseSubdivision k),
      ‖((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ) -
          (edgewiseSubdivisionRealizationMap K k y).1‖ ≤
        C' * ‖(K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) x -
          (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) y‖ := by
  set e := K.realizationHomeomorphRange (Set.toFinite K.faces)
  -- Raise the separation constant to a positive one, so that its inverse is a positive margin.
  set C₁ : ℝ≥0 := C + 1
  have hC : 0 < C₁ := by positivity
  have hanti₁ : AntilipschitzWith C₁ (f ∘ e.symm) :=
    AntilipschitzWith.of_le_mul_dist fun p q => (hanti.le_mul_dist p q).trans <|
      mul_le_mul_of_nonneg_right (by simp [C₁]) dist_nonneg
  have hlt : (2 * C₁)⁻¹ < C₁⁻¹ := inv_strictAnti₀ hC (lt_two_mul_self hC)
  refine ⟨((C₁⁻¹ - (2 * C₁)⁻¹)⁻¹ : NNReal), NNReal.coe_pos.2 (inv_pos.2 (tsub_pos_of_lt hlt)), ?_⟩
  filter_upwards [eventually_ne_atTop 0, eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision
    hf (ε := ((2 * C₁)⁻¹ : NNReal)) (NNReal.coe_pos.2 (inv_pos.2 (by positivity)))]
    with k hk0 hk x y
  -- Move the secant map to the coordinate image of `|K|` and perturb `f` there.
  set Ψ := (edgewiseSubdivisionRealizationHomeomorph K hk0).trans e
  set s := (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)
  have hΨ (x : Realization (K.edgewiseSubdivision k)) :
      e.symm (Ψ x) = edgewiseSubdivisionRealizationMap K k x := by
    rw [Homeomorph.trans_apply, e.symm_apply_apply, edgewiseSubdivisionRealizationHomeomorph_apply]
  have hdist (x y : Realization (K.edgewiseSubdivision k)) : dist (Ψ x) (Ψ y) =
      ‖((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ) -
        (edgewiseSubdivisionRealizationMap K k y).1‖ := by
    rw [dist_eq_norm_realizationHomeomorphRange_symm _ (Set.toFinite _), hΨ, hΨ]
  have hlip : LipschitzWith (2 * C₁)⁻¹ (s ∘ Ψ.symm - f ∘ e.symm) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      obtain ⟨x, rfl⟩ := Ψ.surjective p
      obtain ⟨y, rfl⟩ := Ψ.surjective q
      simpa only [hdist, dist_eq_norm, Pi.sub_apply, comp_apply, Homeomorph.symm_apply_apply,
        hΨ] using hk x y
  simpa only [hdist, dist_eq_norm, comp_apply, Homeomorph.symm_apply_apply] using
    (hanti₁.add_sub_lipschitzWith hlip hlt).le_mul_dist (Ψ x) (Ψ y)

/-- **Secant maps of anti-Lipschitz maps are closed embeddings.** Let `f` be a map of the
realization of a complex on a finite vertex type which is `C¹` on every closed simplex and
anti-Lipschitz in barycentric coordinates. For all sufficiently large `k`, the secant map of `f`
on the `k`-th edgewise subdivision is a closed embedding. -/
theorem eventually_isClosedEmbedding_secantMap_edgewiseSubdivision_of_antilipschitzWith
    (hf : ∀ σ : Face K, ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights))
    {C : ℝ≥0}
    (hanti : AntilipschitzWith C (f ∘ (K.realizationHomeomorphRange (Set.toFinite K.faces)).symm)) :
    ∀ᶠ k in atTop, Topology.IsClosedEmbedding
      ((K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)) := by
  obtain ⟨C', -, hC'⟩ :=
    exists_pos_eventually_norm_sub_le_mul_norm_secantMap_sub_of_antilipschitzWith hf hanti
  filter_upwards [hC', eventually_ne_atTop 0] with k hk hk0
  have : CompactSpace (Realization K) := K.compactSpace_realization_of_finite_faces
    (Set.toFinite K.faces)
  have : CompactSpace (Realization (K.edgewiseSubdivision k)) :=
    (edgewiseSubdivisionRealizationHomeomorph K hk0).symm.compactSpace
  refine (continuous_secantMap _).isClosedEmbedding fun x y hxy => ?_
  have hle := hk x y
  rw [hxy, sub_self, norm_zero, mul_zero] at hle
  exact edgewiseSubdivisionRealizationMap_injective
    (Subtype.ext (DFunLike.coe_injective (sub_eq_zero.mp (norm_le_zero_iff.mp hle))))

end TauCeti

namespace ContDiffOn

variable {ι E : Type*} [LinearOrder ι] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

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
      rw [LinearMap.coe_toContinuousLinearMap', Function.ExtendByZero.linearMap_apply,
        extend_val_standardSimplex]
    have hmap : MapsTo L (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights)
        (range fun t : Convexity.StdSimplex ℝ ι => ⇑t.weights) := by
      rw [← Finset.range_standardSimplex_coordinates]
      rintro _ ⟨x, rfl⟩
      rw [hL, ← range_realization_coe_top]
      exact ⟨faceInclusion ⊤ σ x, congrArg DFunLike.coe (faceInclusion_val ⊤ σ x)⟩
    refine ⟨F ∘ L, ?_, hF.comp L.contDiff.contDiffOn hmap⟩
    intro x
    simpa only [Function.comp_apply, f₀, faceInclusion_val] using congrArg F (hL x)
  -- The barycentric image of the realization is the original simplex, so `hsep` transports.
  have hanti : AntilipschitzWith C
      (f₀ ∘ ((⊤ : AbstractSimplicialComplex ι).realizationHomeomorphRange (Set.toFinite _)).symm) :=
    AntilipschitzWith.of_le_mul_dist fun p q => by
      have hp : (p : ι → ℝ) ∈ range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights :=
        range_realization_coe_top (ι := ι) ▸ p.2
      have hq : (q : ι → ℝ) ∈ range fun x : Convexity.StdSimplex ℝ ι => ⇑x.weights :=
        range_realization_coe_top (ι := ι) ▸ q.2
      simpa only [Subtype.dist_eq, Function.comp_apply, f₀,
        coe_realizationHomeomorphRange_symm_apply, Set.domRestrict_apply] using
        hsep.le_mul_dist ⟨p, hp⟩ ⟨q, hq⟩
  exact eventually_isClosedEmbedding_secantMap_edgewiseSubdivision_of_antilipschitzWith hC1 hanti

end ContDiffOn

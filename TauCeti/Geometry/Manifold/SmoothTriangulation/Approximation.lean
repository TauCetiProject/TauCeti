/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SecantEstimate
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Fatness
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic
import TauCeti.Analysis.Convex.StdSimplex

/-!
# First-order secant approximation on edgewise subdivisions

For a map which is `C¹` within a closed simplex, the derivatives of its secants on fine
edgewise subdivisions approximate its derivative uniformly. The comparison uses the original
barycentric directions: its error is at most `ε` times the norm of the direction, independently
of the number or shape of the subdivided simplex. The derivative is compared at every point of
that simplex, including its boundary.

Unlike the immersion criterion in `SmoothTriangulation.Edgewise`, this estimate controls the
size of the derivative perturbation, and does not require the original map to be an immersion.
It is the first-order control needed when fitting together triangulations by secant perturbations.
The continuous derivative within the simplex is chosen once, before the approximation tolerance.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9 (secant approximation)
  and Theorems 10.5–10.6 (uniqueness and existence of smooth triangulations).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582 (the uniformly fat subdivisions).
-/

public section

open Set Finset AbstractSimplicialComplex PreAbstractSimplicialComplex Filter
open TauCeti

namespace ContDiffOn

/-- On edgewise subdivisions of a fixed simplex, a `C¹` map has secant derivatives converging
uniformly to a single continuous choice of derivative within the simplex. The comparison holds
on all geometric directions of each subdivided face, at every point in its convex hull. No
injectivity assumption on the original derivative or finiteness of the ambient complex is needed.
The linear combination of vertex values is the derivative of the affine secant parametrization. -/
theorem exists_eventually_norm_linearCombination_sub_le_edgewiseSubdivision
    {ι E : Type*} [LinearOrder ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {σ : Finset ι} {F : (σ → ℝ) → E}
    (hF : ContDiffOn ℝ 1 F (range fun x : Convexity.StdSimplex ℝ σ => ⇑x.weights)) :
    ∃ F' : (σ → ℝ) → (σ → ℝ) →L[ℝ] E,
      (∀ y ∈ range fun x : Convexity.StdSimplex ℝ σ => ⇑x.weights,
        HasFDerivWithinAt F (F' y) (range fun x : Convexity.StdSimplex ℝ σ => ⇑x.weights) y) ∧
      ContinuousOn F' (range fun x : Convexity.StdSimplex ℝ σ => ⇑x.weights) ∧
      ∀ ε > 0, ∀ᶠ k in atTop, ∀ (K : PreAbstractSimplicialComplex ι)
        (ρ : Finset (K.EdgewiseVertex k)), ρ ∈ K.edgewiseSubdivision k →
        ∀ p : ρ → StandardSimplex σ,
        (∀ a, (p a : ι →₀ ℝ) = edgewisePoint a.1.1) →
        ∀ y ∈ convexHull ℝ (range fun a : ρ => fun i : σ => (p a).1 i),
        ∀ v : ρ → ℝ, ∑ a, v a = 0 →
          ‖(∑ a, v a • F (fun i : σ => (p a).1 i)) -
            F' y (∑ a, v a • fun i : σ => (p a).1 i)‖ ≤
              ε * ‖∑ a, v a • fun i : σ => (p a).1 i‖ := by
  obtain ⟨F', hFd, hFc⟩ := hF.exists_continuousOn_hasFDerivWithinAt_stdSimplex
  refine ⟨F', hFd, hFc, fun ε hε => ?_⟩
  rcases σ.eq_empty_or_nonempty with rfl | hσ
  · refine Eventually.of_forall fun k K ρ hρ p _ => ?_
    obtain ⟨a, ha⟩ := (mem_edgewiseSubdivision_iff.mp hρ).1
    have hmem := (p ⟨a, ha⟩).2
    simp at hmem
  have hS : IsCompact (range fun x : Convexity.StdSimplex ℝ σ => ⇑x.weights) :=
    isCompact_range
      (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights (R := ℝ) σ).continuous
  obtain ⟨δ, hδ, happrox⟩ := hS.exists_pos_norm_linearCombination_sub_le
    (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ) hFd hFc
    (t := ((2 : ℝ) * #σ ^ 2)⁻¹) (by positivity) hε
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  filter_upwards [eventually_ge_atTop N] with k hk K ρ hρ p hp
  have hkδ : δ⁻¹ < k := hN.trans_le (Nat.cast_le.mpr hk)
  have hmem (a : ρ) :
      (fun i : σ => (p a).1 i) ∈ range fun x : Convexity.StdSimplex ℝ σ => ⇑x.weights :=
    ⟨Finset.standardSimplexHomeomorph σ (p a),
      funext fun i => Finset.standardSimplexHomeomorph_weights σ (p a) i⟩
  have hentries : ∀ u ∈ ρ, ∀ l, u.1 l ∈ σ := by
    intro u hu l
    have hsupp := StandardSimplex.support_subset (p ⟨u, hu⟩)
    rw [hp, support_edgewisePoint] at hsupp
    exact hsupp (mem_image_of_mem _ (mem_univ l))
  simpa only [Fintype.linearCombination_apply] using
    happrox (fun a i => (p a).1 i) k⁻¹ hmem (inv_lt_of_inv_lt₀ hδ hkδ)
      (fun a b => by simpa only [hp] using
        norm_edgewisePoint_sub_edgewisePoint_le hρ a.2 b.2 σ)
      (fun v hv => by simpa only [Fintype.linearCombination_apply, hp] using
        mul_sum_abs_le_norm_sum_smul_edgewisePoint hρ hentries v hv)

end ContDiffOn

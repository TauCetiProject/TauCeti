/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.CoefficientApproximateUnit

/-!
# Nondegeneracy of the canonical coefficient map

The canonical map `i_A : A → M(A ⋊ G)` is nondegenerate: the linear span of `i_A(a) x` is
dense in the full crossed product. More precisely, an increasing approximate unit `e` of `A`
satisfies `i_A(e) x → x` and `x i_A(e) → x` in norm for every `x`. Thus coefficient approximate
units converge strictly to the identity multiplier, even for nonunital coefficients.

No faithful representation, separability, or global σ-finiteness is needed.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for nondegeneracy of the canonical
coefficient map. We use the canonical multipliers and dense compact-support inclusion of
`FullCrossedProduct`, and the compact-range approximation
`ConvolutionAlgebra.tendsto_coefficientMul`.
-/

public section

open Filter MeasureTheory Topology
open scoped CStarAlgebra MultiplierAlgebra

namespace TauCeti.CStarAction.FullCrossedProduct

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

/-- Coefficient approximate units act as the identity in norm on the left of the full crossed
product, equivalently their canonical multiplier images converge left-strictly to one. -/
theorem tendsto_coefficientMultiplier_fst [PartialOrder A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (x : FullCrossedProduct α μ) :
    Tendsto (fun e => (coefficientMultiplier α μ e).fst x) l (𝓝 x) := by
  have hd (f : ConvolutionAlgebra α μ) :
      Tendsto (fun e => (coefficientMultiplier α μ e).fst (of α μ f)) l (𝓝 (of α μ f)) := by
    simpa only [coefficientMultiplier_fst_of, Function.comp_def] using
      (continuous_of.tendsto f).comp (ConvolutionAlgebra.tendsto_coefficientMul hl f)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨f, hf⟩ := (denseRange_of (α := α) (μ := μ)).exists_dist_lt x (by positivity : 0 < ε / 3)
  filter_upwards [hl.eventually_norm, Metric.tendsto_nhds.1 (hd f) (ε / 3) (by positivity)]
    with e he hconv
  have hnorm : ‖(coefficientMultiplier α μ e).fst‖ ≤ 1 := by
    rw [DoubleCentralizer.norm_fst]
    exact (NonUnitalStarAlgHom.norm_apply_le _ e).trans he
  have hdist : dist ((coefficientMultiplier α μ e).fst x)
      ((coefficientMultiplier α μ e).fst (of α μ f)) ≤ dist x (of α μ f) := by
    simp only [dist_eq_norm, ← map_sub]
    exact ((coefficientMultiplier α μ e).fst.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  calc
    dist ((coefficientMultiplier α μ e).fst x) x
        ≤ dist ((coefficientMultiplier α μ e).fst x)
            ((coefficientMultiplier α μ e).fst (of α μ f)) +
          dist ((coefficientMultiplier α μ e).fst (of α μ f)) (of α μ f) +
          dist (of α μ f) x := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact hdist.trans_lt hf
      · rwa [dist_comm]
    _ = ε := by ring

/-- Coefficient approximate units act as the identity in norm on the right of the full crossed
product. Together with `tendsto_coefficientMultiplier_fst`, this is strict convergence to one. -/
theorem tendsto_coefficientMultiplier_snd [PartialOrder A] [StarOrderedRing A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (x : FullCrossedProduct α μ) :
    Tendsto (fun e => (coefficientMultiplier α μ e).snd x) l (𝓝 x) := by
  have h := (tendsto_coefficientMultiplier_fst hl (star x)).star
  simp only [star_star] at h
  refine h.congr' ?_
  filter_upwards [hl.eventually_star_eq] with e he
  have hm : star (coefficientMultiplier α μ e) = coefficientMultiplier α μ e := by
    rw [← map_star, he]
  simpa only [hm, star_star] using
    (DoubleCentralizer.star_snd (coefficientMultiplier α μ e) x).symm

/-- The canonical coefficient map into crossed-product multipliers is nondegenerate:
the vectors `i_A(a) x` linearly span a dense subspace of the full crossed product. -/
theorem dense_span_range_coefficientMultiplier_fst :
    Dense (Submodule.span ℂ (⋃ a : A, Set.range (coefficientMultiplier α μ a).fst) :
      Set (FullCrossedProduct α μ)) := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  intro x
  exact mem_closure_of_tendsto (tendsto_coefficientMultiplier_fst hl x) <|
    .of_forall fun e => Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, x, rfl⟩

end TauCeti.CStarAction.FullCrossedProduct

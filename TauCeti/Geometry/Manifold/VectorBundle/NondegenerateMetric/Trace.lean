/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Variation
public import TauCeti.Topology.Algebra.Module.Trace
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Variation of an inverse-metric contraction

The trace uses the fixed model of each tangent fibre, so both factors can be differentiated
with ordinary one-variable calculus. The inverse derivative is the native nondegenerate-metric
variation formula.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006), §2.3.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Differentiating the contraction of a bilinear form with the inverse metric gives the
trace of its derivative minus the contribution from the moving inverse metric. -/
theorem ContMDiffNondegenerateMetric.hasDerivAt_trace_inverse_comp
    {g : ℝ → ContMDiffNondegenerateMetric (I := I) (M := M)} {x : M}
    {B : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {h K : E →L[ℝ] E →L[ℝ] ℝ} {t : ℝ}
    (hg : ∀ v w, HasDerivAt (fun s ↦ g s x v w) (h v w) t)
    (hB : ∀ v w, HasDerivAt (fun s ↦ B s v w) (K v w) t) :
    HasDerivAt (fun s ↦ traceCLM ℝ (E) ((g s x).inverse ∘L B s))
      (traceCLM ℝ (E) ((g t x).inverse ∘L K) -
        traceCLM ℝ (E) (((g t x).inverse ∘L (h ∘L (g t x).inverse)) ∘L B t)) t := by
  set G : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E := fun s ↦ (g s x).inverse
  set B' : ℝ → E →L[ℝ] E →L[ℝ] ℝ := B
  have hdB : HasDerivAt B' K t := hasDerivAt_clm_apply₂.mpr hB
  have hdG : HasDerivAt G (-((g t x).inverse ∘L (h ∘L (g t x).inverse))) t :=
    ContMDiffNondegenerateMetric.hasDerivAt_inverse hg
  have hd := hdG.clm_comp hdB
  have ht := (traceCLM ℝ (E)).hasFDerivAt.comp_hasDerivAt t hd
  refine ht.congr_deriv ?_
  -- Read every fixed-fibre operation on the model space before normalizing compositions.
  change (traceCLM ℝ E) ((-(G t ∘L (h ∘L G t))) ∘L B' t + G t ∘L K) =
    (traceCLM ℝ E) (G t ∘L K) - (traceCLM ℝ E) ((G t ∘L (h ∘L G t)) ∘L B' t)
  simp only [map_add, ContinuousLinearMap.neg_comp, map_neg, sub_eq_add_neg]
  exact add_comm _ _

end TauCeti.Manifold

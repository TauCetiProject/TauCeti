/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import TauCeti.Probability.Distributions.Gamma.Support
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of the Dirichlet distribution

A Dirichlet law with positive concentrations has support equal to the whole closed standard
simplex in Euclidean coordinates. Although every coordinate is almost surely strictly positive,
every neighbourhood of a boundary point, including a vertex, has positive mass. The statement
includes a single coordinate, where the simplex is a singleton. Invalid parameters and an empty
coordinate type give the zero measure and hence empty support.

The normalized-Gamma construction gives this directly: each nonnegative vector belongs to the
support of the Gamma product, and normalization is continuous at every vector of total one.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

open Convexity MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- At positive concentrations, the exact topological support is the closed standard simplex,
including all its faces and vertices. -/
@[simp]
theorem support_dirichletMeasure {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    (dirichletMeasure a).support =
      (EuclideanSpace.equiv ι ℝ) ⁻¹'
        Set.range (fun p : StdSimplex ℝ ι ↦ (p.weights : ι → ℝ)) := by
  apply Set.Subset.antisymm
  · exact Measure.support_subset_of_isClosed
      ((StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ ι).isClosed_range.preimage
        (EuclideanSpace.equiv ι ℝ).continuous)
      ae_mem_stdSimplex_dirichletMeasure
  · rintro x ⟨p, hp⟩
    have := p.nonempty
    have hsum : ∑ i, p.weights i = 1 := p.total_of_fintype
    have hx : dirichletNormalize (fun i ↦ p.weights i) = x := by
      apply (EuclideanSpace.equiv ι ℝ).injective
      ext i
      simpa [dirichletNormalize_apply, hsum] using congrFun hp i
    rw [dirichletMeasure_of_pos ha, ← hx]
    apply Measure.mem_support_map_of_continuousAt measurable_dirichletNormalize.aemeasurable
      (continuousAt_dirichletNormalize (hsum ▸ one_ne_zero))
    simp only [Measure.support_pi, mem_univ_pi, support_gammaMeasure (ha _) zero_lt_one,
      mem_Ici]
    exact fun i ↦ p.nonneg i

open Classical in
/-- The totalized Dirichlet law has closed-simplex support exactly in its valid nonempty,
positive-concentration range, and empty support otherwise. -/
theorem support_dirichletMeasure_eq_if (a : ι → ℝ) :
    (dirichletMeasure a).support =
      if Nonempty ι ∧ ∀ i, 0 < a i then
        (EuclideanSpace.equiv ι ℝ) ⁻¹'
          Set.range (fun p : StdSimplex ℝ ι ↦ (p.weights : ι → ℝ))
      else ∅ := by
  classical
  split_ifs with h
  · exact support_dirichletMeasure h.2
  · rw [dirichletMeasure_eq_zero_of_invalid h, Measure.support_zero]

end TauCeti.Probability

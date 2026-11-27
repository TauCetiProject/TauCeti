/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import TauCeti.Probability.Distributions.Gamma.Support
public import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Support and ambient singularity of the Dirichlet distribution

A Dirichlet law with positive concentrations has support equal to the whole closed standard
simplex in Euclidean coordinates. Although every coordinate is almost surely strictly positive,
every neighbourhood of a boundary point, including a vertex, has positive mass. The statement
includes a single coordinate, where the simplex is a singleton. Invalid parameters and an empty
coordinate type give the zero measure and hence empty support.

For every concentration vector, the Dirichlet law is mutually singular with respect to ambient
Euclidean volume. In the valid case it is carried by the affine hyperplane on which the coordinates
sum to one; in the invalid cases the law is zero.

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

/-- A Dirichlet law is mutually singular with respect to ambient Euclidean volume. -/
theorem mutuallySingular_dirichletMeasure_volume (a : ι → ℝ) :
    dirichletMeasure a ⟂ₘ (volume : Measure (EuclideanSpace ℝ ι)) := by
  cases isEmpty_or_nonempty ι
  · rw [dirichletMeasure_of_isEmpty]
    exact Measure.MutuallySingular.zero_left
  · let u : EuclideanSpace ℝ ι := WithLp.toLp 2 fun _ ↦ 1
    have hu : u ≠ 0 := by
      intro h
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hi : (1 : ℝ) = 0 := congrFun (congrArg WithLp.ofLp h) i
      exact one_ne_zero hi
    have hvolume : volume {x : EuclideanSpace ℝ ι | ∑ i, x i = 1} = 0 := by
      simpa only [u, PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial,
        mul_one, one_mul] using
        Measure.addHaar_setOf_inner_eq
          (volume : Measure (EuclideanSpace ℝ ι)) hu 1
    refine ⟨{x | ∑ i, x i = 1}ᶜ, ?_, ?_, by simpa only [compl_compl] using hvolume⟩
    · exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl
    · exact mem_ae_iff.mp ae_sum_eq_one_dirichletMeasure

end TauCeti.Probability

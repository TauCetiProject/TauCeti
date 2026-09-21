/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.Distributions.Dirichlet.Basic

/-!
# Aggregation of Dirichlet coordinates

Merging the coordinates of a Dirichlet vector along a surjection `f : ι → κ`, by replacing the
coordinates in each fibre of `f` by their total, again gives a Dirichlet vector: the
concentration parameters are merged the same way.  Surjectivity is what keeps every merged
parameter positive.  If `ι` is empty then so is `κ`, and the statement degenerates to an identity
between two zero measures, since `dirichletMeasure` has no probability law to offer on an empty
index type.

Aggregation is how a Dirichlet model is coarsened, and it is the source of the laws of the blocks
of a Dirichlet vector: the law of the total mass carried by a set of coordinates is the
two-coordinate case of the aggregation law, and the covariance of two coordinates is read off the
variance of their total, which is again a case of it.

## Main results

* `TauCeti.Probability.map_euclideanFiberSum_dirichletMeasure` is the aggregation law.

Its random-variable form is `MeasureTheory.MeasurePreserving.fun_comp_hasLaw` applied to the
aggregation law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Summing over a fibre commutes with dividing by the grand total: aggregating a normalized
vector is the same as normalizing the aggregated vector. -/
@[simp]
theorem euclideanFiberSum_dirichletNormalize (f : ι → κ) (x : ι → ℝ) :
    euclideanFiberSum f (dirichletNormalize x) = dirichletNormalize (FunOnFinite.map f x) := by
  classical
  have hsum : ∑ j, ∑ i with f i = j, x i = ∑ i, x i := Finset.sum_fiberwise Finset.univ f x
  ext j
  simp only [euclideanFiberSum_apply, dirichletNormalize_apply, FunOnFinite.map_apply_apply,
    hsum, ← Finset.sum_div]

/-! ### The aggregation law -/

/-- **Aggregation law for the Dirichlet distribution.** Replacing the coordinates in each fibre
of a surjection `f` by their total gives the Dirichlet law whose concentration parameters are the
fibre totals of the original ones.  On an empty index type, where `dirichletMeasure` is the zero
measure, this is the identity between two zero measures. -/
theorem map_euclideanFiberSum_dirichletMeasure [DecidableEq κ] {f : ι → κ}
    (hf : Function.Surjective f) {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    (dirichletMeasure a).map (euclideanFiberSum f) =
      dirichletMeasure fun j ↦ ∑ i with f i = j, a i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hκ : IsEmpty κ := ⟨fun j ↦ (hf j).elim fun i _ ↦ isEmptyElim i⟩
    rw [dirichletMeasure_eq_zero_of_invalid fun h ↦ (not_nonempty_iff.mpr hι) h.1,
      dirichletMeasure_eq_zero_of_invalid fun h ↦ (not_nonempty_iff.mpr hκ) h.1,
      Measure.map_zero]
  · have : Nonempty κ := ⟨f (Classical.arbitrary ι)⟩
    have hpos (j : κ) : 0 < ∑ i with f i = j, a i := by
      obtain ⟨i₀, hi₀⟩ := hf j
      exact Finset.sum_pos (fun i _ ↦ ha i) ⟨i₀, by simp [hi₀]⟩
    have hmap : Measurable (FunOnFinite.map (M := ℝ) f) :=
      (FunOnFinite.continuous_map ℝ f).measurable
    have hcompose : euclideanFiberSum f ∘ dirichletNormalize =
        dirichletNormalize ∘ FunOnFinite.map (M := ℝ) f :=
      funext (euclideanFiberSum_dirichletNormalize f)
    rw [dirichletMeasure_of_pos ha, dirichletMeasure_of_pos hpos,
      Measure.map_map (measurable_euclideanFiberSum f) measurable_dirichletNormalize, hcompose,
      ← Measure.map_map measurable_dirichletNormalize hmap,
      map_funOnFinite_map_pi_gammaMeasure hf ha one_pos]

end Probability

end TauCeti

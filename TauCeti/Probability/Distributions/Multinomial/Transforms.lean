/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Directional exponential transforms of the multinomial distribution

A count vector `k : ι → ℕ` is cast into `EuclideanSpace ℝ ι` by `multinomialToEuclidean`. For
the pushforward of `multinomialMeasure n p` along that cast and a direction `θ`, the directional
moment generating function is finite everywhere and equals
`(∑ i, p i * exp (t * θ i)) ^ n`: the multinomial theorem, with the cell weights tilted by
`exp (t * θ i)`. The cumulant generating function is its real logarithm.

Every statement holds for `n = 0` (the law is a Dirac mass at zero, and the formula is `1`) and
for probability vectors with zero cells, which contribute nothing to the tilted sum.

## Main results

* `TauCeti.Probability.multinomialToEuclidean` — the cast of count vectors into Euclidean space;
* `TauCeti.Probability.integrableExpSet_inner_multinomial` — every direction has full exponential
  integrability domain;
* `TauCeti.Probability.mgf_inner_multinomial` — the directional moment generating function;
* `TauCeti.Probability.cgf_inner_multinomial` — the directional cumulant generating function.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997,
  Chapter 35.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

/-- The count vector cast into Euclidean space. -/
def multinomialToEuclidean (k : ι → ℕ) : EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm fun i => (k i : ℝ)

omit [Fintype ι] in
/-- The coordinates of the cast are the counts, as reals. -/
@[simp]
theorem multinomialToEuclidean_apply (k : ι → ℕ) (i : ι) :
    multinomialToEuclidean k i = (k i : ℝ) := (rfl)

/-- The pointwise identity behind the moment generating function: a multinomial weight times the
exponential of a directional sum is the multinomial weight of the tilted cells `pᵢ exp (t θᵢ)`. -/
private theorem multinomialWeightReal_mul_exp (p : ι → NNReal) (θ : ι → ℝ) (t : ℝ)
    (k : ι → ℕ) :
    multinomialWeightReal p k * exp (t * ∑ i, θ i * (k i : ℝ)) =
      (Nat.multinomial Finset.univ k : ℝ) * ∏ i, ((p i : ℝ) * exp (t * θ i)) ^ k i := by
  rw [multinomialWeightReal_def, Finset.mul_sum, exp_sum, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_pow, ← exp_nat_mul]
  ring_nf

omit [Fintype ι] in
/-- The cast of count vectors into Euclidean space is measurable. -/
theorem measurable_multinomialToEuclidean [Finite ι] :
    Measurable (multinomialToEuclidean (ι := ι)) := by
  have := Fintype.ofFinite ι
  refine (EuclideanSpace.equiv ι ℝ).symm.continuous.measurable.comp ?_
  exact Measurable.of_eval fun i => measurable_from_nat.comp (measurable_pi_apply i)

/-- The cell weights tilted by `exp (t * θ i)`, as a nonnegative family. -/
private def tiltedWeights (p : ι → NNReal) (θ : ι → ℝ) (t : ℝ) (i : ι) : NNReal :=
  p i * ⟨exp (t * θ i), (exp_pos _).le⟩

omit [Fintype ι] in
/-- The real value of a tilted weight. -/
private theorem coe_tiltedWeights (p : ι → NNReal) (θ : ι → ℝ) (t : ℝ) (i : ι) :
    (tiltedWeights p θ t i : ℝ) = (p i : ℝ) * exp (t * θ i) := rfl

/-- **Directional moment generating function of the multinomial law**: for every direction `θ`
and every `t`, it is `(∑ i, pᵢ exp (t θᵢ)) ^ n`. -/
theorem mgf_inner_multinomial (n : ℕ) (p : StdSimplex NNReal ι) (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    mgf (fun x => inner ℝ θ x) ((multinomialMeasure n p).map multinomialToEuclidean) t =
      (∑ i, (p.weights i : ℝ) * exp (t * θ i)) ^ n := by
  classical
  rw [mgf, integral_map measurable_multinomialToEuclidean.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι => exp (t * inner ℝ θ x)) _),
    integral_multinomialMeasure]
  have hdot : ∀ k : ι → ℕ, inner ℝ θ (multinomialToEuclidean k) = ∑ i, θ i * (k i : ℝ) := by
    intro k
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      multinomialToEuclidean_apply, mul_comm]
  simp_rw [smul_eq_mul, hdot, multinomialWeightReal_mul_exp]
  simp_rw [← coe_tiltedWeights p.weights θ t]
  exact (sum_multinomialWeightReal n (tiltedWeights p.weights θ t)).symm ▸
    Finset.sum_congr rfl fun k _ => (multinomialWeightReal_def _ k).symm

/-- Every direction has full exponential-integrability domain: the law has finite support. -/
theorem integrableExpSet_inner_multinomial (n : ℕ) (p : StdSimplex NNReal ι)
    (θ : EuclideanSpace ℝ ι) :
    integrableExpSet (fun x => inner ℝ θ x) ((multinomialMeasure n p).map multinomialToEuclidean)
      = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rw [integrable_map_measure (by fun_prop) measurable_multinomialToEuclidean.aemeasurable]
  exact integrable_multinomialMeasure _ n p

/-- **Directional cumulant generating function of the multinomial law**: the real logarithm of
the moment generating function. -/
theorem cgf_inner_multinomial (n : ℕ) (p : StdSimplex NNReal ι) (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    cgf (fun x => inner ℝ θ x) ((multinomialMeasure n p).map multinomialToEuclidean) t =
      Real.log ((∑ i, (p.weights i : ℝ) * exp (t * θ i)) ^ n) := by
  rw [cgf, mgf_inner_multinomial]

end Probability

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.DirichletMultinomial.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Transforms of Dirichlet-multinomial laws

The Euclidean cast of a Dirichlet-multinomial count vector has every exponential moment.
Its directional moment-generating function and vector characteristic function are finite
sums of the Gamma-ratio masses on the count antidiagonal. The cumulant-generating function
is the logarithm of the positive exponential sum. These formulas include zero trials and
one category; integrability also holds at invalid concentrations, whose measure is zero.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 40.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Every real observable of the Euclidean Dirichlet-multinomial count vector has exponential
integrability domain all of `ℝ`, including invalid concentration parameters. -/
@[simp]
theorem integrableExpSet_map_multinomialToEuclidean_dirichletMultinomialMeasure
    (n : ℕ) (a : ι → ℝ) (f : EuclideanSpace ℝ ι → ℝ) :
    integrableExpSet f
      ((dirichletMultinomialMeasure n a).map multinomialToEuclidean) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦
    integrable_map_multinomialToEuclidean_dirichletMultinomialMeasure _ n a

open Classical in
/-- The directional mgf is the finite exponential sum of the Gamma-ratio masses. -/
theorem mgf_inner_dirichletMultinomialMeasure {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (n : ℕ) (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    mgf (fun x ↦ ⟪θ, x⟫)
      ((dirichletMultinomialMeasure n a).map multinomialToEuclidean) t =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        (((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
          (Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + n) *
            ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i))) *
          Real.exp (t * ∑ i, θ i * (k i : ℝ)) := by
  rw [mgf, integral_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
  simp only [inner_multinomialToEuclidean, smul_eq_mul]

open Classical in
/-- The directional cgf is the logarithm of the finite Gamma-ratio exponential sum,
on its full domain `ℝ`. -/
theorem cgf_inner_dirichletMultinomialMeasure {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (n : ℕ) (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    cgf (fun x ↦ ⟪θ, x⟫)
      ((dirichletMultinomialMeasure n a).map multinomialToEuclidean) t =
      Real.log (∑ k ∈ Finset.piAntidiag Finset.univ n,
        (((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
          (Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + n) *
            ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i))) *
          Real.exp (t * ∑ i, θ i * (k i : ℝ))) := by
  rw [cgf, mgf_inner_dirichletMultinomialMeasure ha]

open Classical in
/-- The vector characteristic function is the finite Fourier sum of the Gamma-ratio masses. -/
theorem charFun_map_multinomialToEuclidean_dirichletMultinomialMeasure
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) (t : EuclideanSpace ℝ ι) :
    charFun ((dirichletMultinomialMeasure n a).map multinomialToEuclidean) t =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        (((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
          (Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + n) *
            ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i))) •
          Complex.exp ((∑ i, (t i : ℂ) * (k i : ℂ)) * Complex.I) := by
  rw [charFun_apply, integral_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [real_inner_comm, inner_multinomialToEuclidean]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]

end TauCeti.Probability

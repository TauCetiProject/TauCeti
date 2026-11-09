/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.DirichletMultinomial.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of Dirichlet-multinomial laws

Positive concentrations give positive mass to every count vector with the prescribed total.
Consequently the native topological support is the finite count antidiagonal, and the support
of the Euclidean cast is its image. The Euclidean membership criterion below describes this
image intrinsically: each coordinate is a natural number and the coordinate sum is the trial
count. These statements include zero trials and a single category; invalid concentrations give
empty support.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 40.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The native topological support is exactly the count antidiagonal for positive
concentrations, and is empty for invalid concentrations. -/
@[simp]
theorem support_dirichletMultinomialMeasure (n : ℕ) (a : ι → ℝ) :
    (dirichletMultinomialMeasure n a).support =
      if ∀ i, 0 < a i then {k | ∑ i, k i = n} else ∅ := by
  classical
  by_cases ha : ∀ i, 0 < a i
  · rw [ite_eq_left ha, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    exact dirichletMultinomialMeasure_singleton_ne_zero_iff ha n k
  · simp [ha]

/-- The Euclidean topological support is the finite image of all natural count vectors
with the prescribed total. No additional limit points occur. -/
@[simp]
theorem support_map_multinomialToEuclidean_dirichletMultinomialMeasure
    (n : ℕ) (a : ι → ℝ) :
    ((dirichletMultinomialMeasure n a).map multinomialToEuclidean).support =
      if ∀ i, 0 < a i then
        multinomialToEuclidean '' {k : ι → ℕ | ∑ i, k i = n} else ∅ := by
  classical
  by_cases ha : ∀ i, 0 < a i
  · have hfinite : ({k : ι → ℕ | ∑ i, k i = n} : Set (ι → ℕ)).Finite := by
      exact (Finset.piAntidiag Finset.univ n).finite_toSet.subset fun k hk ↦ by
        exact Finset.mem_piAntidiag.mpr ⟨hk, fun i _ ↦ Finset.mem_univ i⟩
    rw [ite_eq_left ha, Measure.support_map_eq_closure_image _ Measure.support_mem_ae
      (continuous_of_discreteTopology : Continuous (multinomialToEuclidean (ι := ι))),
      support_dirichletMultinomialMeasure, ite_eq_left ha,
      (hfinite.image multinomialToEuclidean).isClosed.closure_eq]
  · simp [ha]

/-- A Euclidean vector belongs to the support precisely when the concentrations are positive,
its coordinates are natural numbers, and their sum is the trial count. -/
theorem mem_support_map_multinomialToEuclidean_dirichletMultinomialMeasure_iff
    (n : ℕ) (a : ι → ℝ) (x : EuclideanSpace ℝ ι) :
    x ∈ ((dirichletMultinomialMeasure n a).map multinomialToEuclidean).support ↔
      (∀ i, 0 < a i) ∧ (∀ i, ∃ k : ℕ, x i = k) ∧ ∑ i, x i = n := by
  classical
  rw [support_map_multinomialToEuclidean_dirichletMultinomialMeasure]
  by_cases ha : ∀ i, 0 < a i
  · rw [ite_eq_left ha]
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨ha, ?_, ?_⟩
      · intro i
        exact ⟨k i, multinomialToEuclidean_apply k i⟩
      · simpa only [multinomialToEuclidean_apply, ← Nat.cast_sum] using
          congrArg (Nat.cast : ℕ → ℝ) hk
    · rintro ⟨_, hx, hsum⟩
      choose k hk using hx
      have hxk : multinomialToEuclidean k = x := by
        ext i
        exact (multinomialToEuclidean_apply k i).trans (hk i).symm
      refine ⟨k, ?_, hxk⟩
      have hcast : ((∑ i, k i : ℕ) : ℝ) = n := by
        simpa only [Nat.cast_sum, ← hk] using hsum
      exact_mod_cast hcast
  · simp [ha]

end TauCeti.Probability

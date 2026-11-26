/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Finitely many elements of a Bernoulli random set

Under Mathlib's `setBer(u, p)`, each element of `u` belongs to the random set with probability
`p`, independently of the others. For a finite set `F ⊆ u` this file computes the probability
that every element of `F` belongs to the random set, `p ^ #F`, and the probability that none of
them does, `(1 - p) ^ #F`. These are the cylinder events read off finitely many coordinates of the
product measure behind `setBer(u, p)`.

## Main results

* `ProbabilityTheory.setBernoulli_setOf_subset` — every element of `F` belongs to the random set
  with probability `p ^ #F`;
* `ProbabilityTheory.setBernoulli_setOf_disjoint` — no element of `F` belongs to the random set
  with probability `(1 - p) ^ #F`.
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal Finset

namespace ProbabilityTheory

variable {ι : Type*} {u : Set ι} {F : Finset ι}

/-- Every element of a finite set `F ⊆ u` belongs to the random set of `setBer(u, p)` with
probability `p ^ #F`. -/
theorem setBernoulli_setOf_subset (p : I) (hF : (F : Set ι) ⊆ u) :
    setBer(u, p) {s | (F : Set ι) ⊆ s} = (toNNReal p : ℝ≥0∞) ^ #F := by
  have : (fun P : ι → Prop ↦ {i | P i}) ⁻¹' {s | (F : Set ι) ⊆ s} =
      Set.pi F fun _ ↦ {True} := by
    ext P
    simp [Set.subset_def]
  rw [setBernoulli_apply', this, ← Finset.prod_const]
  refine (infinitePi_pi _ fun _ _ ↦ MeasurableSet.singleton _).trans <|
    Finset.prod_congr rfl fun i hi ↦ ?_
  exact bernoulliMeasure_apply_of_mem_of_notMem p (.singleton _) (by simpa using hF hi) (by simp)

/-- Every element of a finite set `F ⊆ u` belongs to the random set of `setBer(u, p)` with
probability `p ^ #F`. -/
theorem setBernoulli_real_setOf_subset (p : I) (hF : (F : Set ι) ⊆ u) :
    setBer(u, p).real {s | (F : Set ι) ⊆ s} = (p : ℝ) ^ #F := by
  simp [measureReal_def, setBernoulli_setOf_subset p hF]

/-- No element of a finite set `F ⊆ u` belongs to the random set of `setBer(u, p)` with
probability `(1 - p) ^ #F`. -/
theorem setBernoulli_setOf_disjoint (p : I) (hF : (F : Set ι) ⊆ u) :
    setBer(u, p) {s | Disjoint (F : Set ι) s} = (toNNReal (σ p) : ℝ≥0∞) ^ #F := by
  have : (fun P : ι → Prop ↦ {i | P i}) ⁻¹' {s | Disjoint (F : Set ι) s} =
      Set.pi F fun _ ↦ {False} := by
    ext P
    simp [Set.disjoint_left]
  rw [setBernoulli_apply', this, ← Finset.prod_const]
  refine (infinitePi_pi _ fun _ _ ↦ MeasurableSet.singleton _).trans <|
    Finset.prod_congr rfl fun i hi ↦ ?_
  exact bernoulliMeasure_apply_of_notMem_of_mem p (.singleton _) (by simpa using hF hi) (by simp)

/-- No element of a finite set `F ⊆ u` belongs to the random set of `setBer(u, p)` with
probability `(1 - p) ^ #F`. -/
theorem setBernoulli_real_setOf_disjoint (p : I) (hF : (F : Set ι) ⊆ u) :
    setBer(u, p).real {s | Disjoint (F : Set ι) s} = (1 - p : ℝ) ^ #F := by
  simp [measureReal_def, setBernoulli_setOf_disjoint p hF]

end ProbabilityTheory

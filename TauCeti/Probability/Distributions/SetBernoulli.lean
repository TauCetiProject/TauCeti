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

/-- The elements of a finite set `F ⊆ u` all have membership `b` in the random set of
`setBer(u, p)` with probability `Ber(True, False, p) {b} ^ #F`: the event is the cylinder over
`F` of the product measure, and each of its factors is the same Bernoulli mass. -/
private theorem setBernoulli_setOf_forall_mem_iff (p : I) (hF : (F : Set ι) ⊆ u) (b : Prop) :
    setBer(u, p) {s | ∀ i ∈ F, (i ∈ s ↔ b)} = Ber(True, False, p) {b} ^ #F := by
  have : (fun P : ι → Prop ↦ {i | P i}) ⁻¹' {s | ∀ i ∈ F, (i ∈ s ↔ b)} =
      Set.pi F fun _ ↦ {b} := by
    ext P
    simp
  rw [setBernoulli_apply', this, ← Finset.prod_const]
  refine (infinitePi_pi _ fun _ _ ↦ MeasurableSet.singleton _).trans <|
    Finset.prod_congr rfl fun i hi ↦ ?_
  rw [eq_true (hF hi)]

/-- Every element of a finite set `F ⊆ u` belongs to the random set of `setBer(u, p)` with
probability `p ^ #F`. -/
theorem setBernoulli_setOf_subset (p : I) (hF : (F : Set ι) ⊆ u) :
    setBer(u, p) {s | (F : Set ι) ⊆ s} = (toNNReal p : ℝ≥0∞) ^ #F := by
  simpa [Set.subset_def] using setBernoulli_setOf_forall_mem_iff p hF True

/-- Every element of a finite set `F ⊆ u` belongs to the random set of `setBer(u, p)` with
probability `p ^ #F`. -/
theorem setBernoulli_real_setOf_subset (p : I) (hF : (F : Set ι) ⊆ u) :
    setBer(u, p).real {s | (F : Set ι) ⊆ s} = (p : ℝ) ^ #F := by
  simp [measureReal_def, setBernoulli_setOf_subset p hF]

/-- No element of a finite set `F ⊆ u` belongs to the random set of `setBer(u, p)` with
probability `(1 - p) ^ #F`. -/
theorem setBernoulli_setOf_disjoint (p : I) (hF : (F : Set ι) ⊆ u) :
    setBer(u, p) {s | Disjoint (F : Set ι) s} = (toNNReal (σ p) : ℝ≥0∞) ^ #F := by
  simpa [Set.disjoint_left] using setBernoulli_setOf_forall_mem_iff p hF False

/-- No element of a finite set `F ⊆ u` belongs to the random set of `setBer(u, p)` with
probability `(1 - p) ^ #F`. -/
theorem setBernoulli_real_setOf_disjoint (p : I) (hF : (F : Set ι) ⊆ u) :
    setBer(u, p).real {s | Disjoint (F : Set ι) s} = (1 - p : ℝ) ^ #F := by
  simp [measureReal_def, setBernoulli_setOf_disjoint p hF]

end ProbabilityTheory

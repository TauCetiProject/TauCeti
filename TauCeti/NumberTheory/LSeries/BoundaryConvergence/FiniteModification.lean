/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.LSeries.Linearity
public import TauCeti.Topology.Algebra.Group.FiniteModification

/-!
# Finite changes of Dirichlet coefficients

Changing coefficients on a finite set adds a finite Dirichlet polynomial to an analytic
continuation, and adds its value at `1` to the limit of ordered harmonic sums. This file
gives both corrections explicitly. In particular, the boundary statements concern limits
of finite sums and do not require absolute summability at the boundary. The lemma
`LSeries.differentiable_sum_term` in `TauCeti.NumberTheory.LSeries.Deriv` shows that the
correction is entire; combine its
`.differentiableOn` with `DifferentiableOn.add` to correct a continuation.

The coefficient at `0` is immaterial throughout. The finite set of changes may contain `0`,
and agreement outside it is required only at positive indices.

## Main declarations

* `LSeriesHasSum.congr_finset`: transport a native Dirichlet-series sum through finite changes.
* `Finset.eventually_sum_Icc_div_sub_eq_sum`: the exact eventual finite correction.
* `Finset.tendsto_sum_Icc_div_congr_finset_iff`: the corresponding equivalence of
  ordered boundary limits.
-/

public section

namespace LSeriesHasSum

/-- Finite changes of coefficients add the corresponding finite Dirichlet polynomial to
the sum. No agreement at index `0` is needed. -/
theorem congr_finset {a b : ℕ → ℂ} {s A : ℂ} (ha : LSeriesHasSum a s A)
    (S : Finset ℕ) (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) :
    LSeriesHasSum b s (A + ∑ n ∈ S, LSeries.term (b - a) s n) := by
  have hfinite : HasSum (LSeries.term (b - a) s)
      (∑ n ∈ S, LSeries.term (b - a) s n) :=
    hasSum_sum_of_ne_finset_zero fun n hn ↦ by
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · simp [LSeries.term_of_ne_zero hn0, hab n hn0 hn]
  have h := ha.add hfinite
  simpa only [add_sub_cancel] using h

end LSeriesHasSum

open Filter
open scoped Topology

namespace Finset

variable {K : Type*} [DivisionRing K] {a b : ℕ → K} {L : K}

/-- Once the cutoff contains every positive changed index, the difference of the ordered
harmonic sums is exactly the finite correction. Changes at index `0` contribute zero. -/
theorem sum_Icc_div_sub_eq_sum (S : Finset ℕ)
    (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) {N : ℕ} (hN : S.sup id ≤ N) :
    (∑ n ∈ Icc 1 N, b n / (n : K)) - (∑ n ∈ Icc 1 N, a n / (n : K)) =
      ∑ n ∈ S, (b n - a n) / (n : K) := by
  classical
  simpa only [← sub_div,
    sum_erase (a := 0) (f := fun n ↦ (b n - a n) / (n : K)) S (by simp)] using
    sum_Icc_sub_eq_sum S (fun n hn hnS ↦ congrArg (· / (n : K)) (hab n hn hnS)) hN

/-- The exact correction formula for finite changes holds eventually in the natural cutoff. -/
theorem eventually_sum_Icc_div_sub_eq_sum (S : Finset ℕ)
    (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Icc 1 N, b n / (n : K)) - (∑ n ∈ Icc 1 N, a n / (n : K)) =
        ∑ n ∈ S, (b n - a n) / (n : K) := by
  filter_upwards [eventually_ge_atTop (S.sup id)] with N hN
  exact sum_Icc_div_sub_eq_sum S hab hN

/-- Finite changes preserve convergence of ordered harmonic sums, with the explicit finite
correction to the limit. This does not assert an unconditional sum at `1`. -/
theorem tendsto_sum_Icc_div_congr_finset_iff [TopologicalSpace K]
    [IsTopologicalAddGroup K] (S : Finset ℕ)
    (hab : ∀ n, n ≠ 0 → n ∉ S → a n = b n) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, b n / (n : K)) atTop
        (𝓝 (L + ∑ n ∈ S, (b n - a n) / (n : K))) ↔
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n / (n : K)) atTop (𝓝 L) := by
  classical
  simpa only [← sub_div,
    sum_erase (a := 0) (f := fun n ↦ (b n - a n) / (n : K)) S (by simp)] using
    tendsto_sum_Icc_congr_finset_iff (L := L) S
      (fun n hn hnS ↦ congrArg (· / (n : K)) (hab n hn hnS))

end Finset

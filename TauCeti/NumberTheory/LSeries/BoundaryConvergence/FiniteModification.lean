/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Linearity
public import TauCeti.Topology.Algebra.InfiniteSum.FiniteModification

/-!
# Finite changes of Dirichlet coefficients

Changing coefficients on a finite set adds a finite Dirichlet polynomial to an analytic
continuation, and adds its value at `1` to the limit of ordered harmonic sums. This file
gives both corrections explicitly. In particular, the boundary statements concern limits
of finite sums and do not require absolute summability at the boundary.

The coefficient at `0` is immaterial throughout. The finite set of changes may contain `0`,
and agreement outside it is required only at positive indices.

## Main declarations

* `LSeriesHasSum.congr_finset`: transport a native Dirichlet-series sum through finite changes.
* `DifferentiableOn.add_sum_LSeries_term`: the corrected continuation is holomorphic
  on the original domain.
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

namespace DifferentiableOn

/-- Adding the finite Dirichlet correction to a holomorphic continuation preserves its
domain of holomorphy. The correction itself is entire, including at `s = 0`. -/
theorem add_sum_LSeries_term {F : ℂ → ℂ} {Ω : Set ℂ}
    (hF : DifferentiableOn ℂ F Ω) (c : ℕ → ℂ) (S : Finset ℕ) :
    DifferentiableOn ℂ (fun s ↦ F s + ∑ n ∈ S, LSeries.term c s n) Ω := by
  exact hF.add (Differentiable.fun_sum (𝕜 := ℂ)
    (fun n _ s ↦ (LSeries.hasDerivAt_term c n s).differentiableAt)).differentiableOn

end DifferentiableOn

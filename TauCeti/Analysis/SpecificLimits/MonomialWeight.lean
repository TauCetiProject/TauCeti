/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finsupp.Weight
import TauCeti.Data.Finsupp.Weight

/-!
# Monomial weights tend to zero

Over finitely many variables, there are only finitely many exponents `t : σ →₀ ℕ` of bounded
degree. Hence, for polyradii `w` with `0 ≤ wᵢ < 1`, the monomial weight `∏ wᵢ ^ tᵢ`, which is at
most `(maxᵢ wᵢ) ^ degree t`, tends to zero along the cofinite filter of exponents.

## Main results

* `Finsupp.tendsto_prod_pow_cofinite_nhds_zero`: over finitely many variables, the monomial
  weights `∏ wᵢ ^ tᵢ` with `0 ≤ wᵢ < 1` tend to zero along the cofinite filter of exponents.
-/

public section

open Filter Topology

namespace Finsupp

/-- Over finitely many variables, the monomial weights `∏ wᵢ ^ tᵢ` of polyradii `w` with
`0 ≤ wᵢ < 1` tend to zero along the cofinite filter of exponents. -/
theorem tendsto_prod_pow_cofinite_nhds_zero {σ : Type*} [Finite σ] {w : σ → ℝ}
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∀ i, w i < 1) :
    Tendsto (fun t : σ →₀ ℕ ↦ t.prod (w · ^ ·)) cofinite (𝓝 0) := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · simp [cofinite_eq_bot]
  have := Fintype.ofFinite σ
  -- Every weight is bounded by `q ^ degree t`, where `q < 1` is the largest `wᵢ`.
  set q := Finset.univ.sup' Finset.univ_nonempty w
  have hwq (i : σ) : w i ≤ q := Finset.le_sup' w (Finset.mem_univ i)
  have hq1 : q < 1 := (Finset.sup'_lt_iff _).2 fun i _ ↦ h1 i
  have hdeg : Tendsto (fun t : σ →₀ ℕ ↦ t.degree) cofinite atTop :=
    tendsto_atTop.2 fun N ↦ (finite_of_degree_lt N).eventually_cofinite_notMem.mono
      fun _ ht ↦ not_lt.1 ht
  refine squeeze_zero (fun t ↦ Finset.prod_nonneg fun i _ ↦ pow_nonneg (h0 i) _) (fun t ↦ ?_)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one ((h0 _).trans (hwq hσ.some)) hq1).comp hdeg)
  rw [Function.comp_apply, ← prod_pow_eq_pow_degree]
  exact Finset.prod_le_prod₀ (fun i _ ↦ pow_nonneg (h0 i) _) fun i _ ↦
    pow_le_pow_left₀ (h0 i) (hwq i) _

end Finsupp

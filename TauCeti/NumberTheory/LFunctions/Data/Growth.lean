/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Comparison
public import TauCeti.NumberTheory.LSeries.CoefficientGrowth

/-!
# Average coefficient growth of analytic L-function cards

`HasAverageCoefficientGrowth` requires `∑_{1 ≤ k ≤ n} ‖a(k)‖ = O(n ^ t)` for
every `t > 1`, the usual `O(n ^ (1 + ε))` bound. This is an average absolute bound,
not cancellation of coefficient sums or a pointwise Ramanujan bound. It is
independent of the coefficient at zero and is equivalent to the abscissa of
absolute convergence being at most one. Thus it supplies absolute convergence
on the half-plane used by `HasDirichletAgreement`, without imposing any
continuation or functional equation.

Duality and `EqOffZero` preserve this predicate. Uniformly bounded positive-index
coefficients provide a sufficient criterion, as for zeta and Dirichlet characters.
-/

public section

open Asymptotics Filter Finset
open scoped Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- The absolute coefficient sums have growth `O(n ^ (1 + ε))` for every `ε > 0`.
No condition is imposed on the coefficient at zero. -/
def HasAverageCoefficientGrowth (d : AnalyticLFunctionData) : Prop :=
  ∀ t : ℝ, 1 < t →
    (fun n ↦ ∑ k ∈ Icc 1 n, ‖d.coeff k‖) =O[atTop] fun n ↦ (n : ℝ) ^ t

variable {d e : AnalyticLFunctionData}

/-- The defining bound on positive-index absolute coefficient sums. -/
theorem hasAverageCoefficientGrowth_def :
    d.HasAverageCoefficientGrowth ↔ ∀ t : ℝ, 1 < t →
      (fun n ↦ ∑ k ∈ Icc 1 n, ‖d.coeff k‖) =O[atTop] fun n ↦ (n : ℝ) ^ t := (Iff.rfl)

/-- Average absolute coefficient growth is exactly an upper bound of one on the
abscissa of absolute convergence. -/
theorem hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le :
    d.HasAverageCoefficientGrowth ↔ LSeries.abscissaOfAbsConv d.coeff ≤ 1 := by
  exact (TauCeti.LSeries.abscissaOfAbsConv_le_iff_sum_norm_isBigO zero_le_one).symm

/-- The growth bound supplies the absolute convergence required on `Re s > 1`. -/
theorem HasAverageCoefficientGrowth.LSeriesSummable (h : d.HasAverageCoefficientGrowth)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable d.coeff s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le.mp h).trans_lt (by exact_mod_cast hs))

/-- Coefficient growth is unchanged by conjugating the card. -/
theorem HasAverageCoefficientGrowth.dual (h : d.HasAverageCoefficientGrowth) :
    d.dual.HasAverageCoefficientGrowth := by
  intro t ht
  simpa only [dual_coeff, Complex.norm_conj] using h t ht

@[simp]
theorem hasAverageCoefficientGrowth_dual_iff :
    d.dual.HasAverageCoefficientGrowth ↔ d.HasAverageCoefficientGrowth :=
  ⟨fun h ↦ by simpa using h.dual, HasAverageCoefficientGrowth.dual⟩

/-- Comparison away from coefficient zero preserves the average growth bound. -/
theorem EqOffZero.hasAverageCoefficientGrowth (h : d.EqOffZero e)
    (hd : d.HasAverageCoefficientGrowth) : e.HasAverageCoefficientGrowth := by
  intro t ht
  have heq : (fun n ↦ ∑ k ∈ Icc 1 n, ‖d.coeff k‖) =
      (fun n ↦ ∑ k ∈ Icc 1 n, ‖e.coeff k‖) := by
    funext n
    apply sum_congr rfl
    intro k hk
    rw [h.coeff_eq k (by have := (mem_Icc.mp hk).1; omega)]
  rw [← heq]
  exact hd t ht

/-- Average growth is an invariant of cards compared by `EqOffZero`. -/
theorem EqOffZero.hasAverageCoefficientGrowth_iff (h : d.EqOffZero e) :
    d.HasAverageCoefficientGrowth ↔ e.HasAverageCoefficientGrowth :=
  ⟨h.hasAverageCoefficientGrowth, h.symm.hasAverageCoefficientGrowth⟩

/-- A uniform bound on the positive-index coefficients implies average growth.
The unused coefficient at zero need not obey this bound. -/
theorem hasAverageCoefficientGrowth_of_norm_coeff_le (h : ∃ C : ℝ,
    ∀ n : ℕ, n ≠ 0 → ‖d.coeff n‖ ≤ C) : d.HasAverageCoefficientGrowth :=
  hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le.mpr
    (LSeries.abscissaOfAbsConv_le_of_le_const h)

end TauCeti.LFunctions.AnalyticLFunctionData

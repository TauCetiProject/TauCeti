/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LSeries.SumCoeff
public import TauCeti.NumberTheory.DirichletCharacter.PartialSum
import Mathlib.Analysis.Complex.Convex

/-!
# A level-dependent bound for continued Dirichlet L-functions

Cancellation over a full period bounds the partial sums of a nonprincipal character of level
`N` by `N`. Partial summation then represents its continued L-function on `Re(s) > 0` by an
absolutely convergent integral and gives `‖L(s, χ)‖ ≤ N ‖s‖ / Re(s)`. In particular this is a
linear growth bound on each vertical line in the right half-plane, with explicit dependence
on the level. For a primitive character the level is its conductor.

The function being bounded is the native analytic continuation, not the Dirichlet series
(which need not converge absolutely in this half-plane). No zero-free hypothesis is required.

## References

* H. Davenport, *Multiplicative Number Theory*, the partial-summation construction and bounds
  for Dirichlet L-functions.
-/

public section

open Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

private theorem sum_isBigO_one (hχ : χ ≠ 1) :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
  refine isBigO_iff.mpr ⟨N, Eventually.of_forall fun n ↦ ?_⟩
  simpa using χ.norm_sum_Icc_le_level hχ n

/-- Partial summation represents the continued L-function of a nonprincipal character on the
whole half-plane `Re(s) > 0`. -/
theorem LFunction_eq_mul_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    χ.LFunction s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hF := TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO _ (χ.sum_isBigO_one hχ)
  have heq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)]
      fun z ↦ z * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) *
        (t : ℂ) ^ (-(z + 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    rw [LFunction_eq_LSeries χ hz]
    exact LSeries_eq_mul_integral _ le_rfl (lt_trans zero_lt_one hz)
      (χ.LSeriesSummable_of_one_lt_re hz) (χ.sum_isBigO_one hχ)
  have hL := (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hopen
  exact (hL.eqOn_of_preconnected_of_eventuallyEq
    (hF.analyticOnNhd hopen) (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq) hs

/-- On the right half-plane, the continued L-function of a nonprincipal character satisfies
`‖L(s, χ)‖ ≤ N ‖s‖ / Re(s)`. For a primitive character, `N` is the conductor. -/
theorem norm_LFunction_le_level_mul_norm_div_re (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ (N : ℝ) * ‖s‖ / s.re := by
  rw [χ.LFunction_eq_mul_integral hχ hs]
  exact TauCeti.LSeries.norm_mul_integral_le_of_bound _ (χ.norm_sum_Icc_le_level hχ) hs

end DirichletCharacter

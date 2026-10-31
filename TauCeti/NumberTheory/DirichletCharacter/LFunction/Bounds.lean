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

/-- The partial-summation integral of a nonprincipal character converges absolutely whenever
`Re(s) > 0`. -/
theorem integrableOn_sum_mul_cpow (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) := by
  have hloc : LocallyIntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ (-(s + 1)) * (∑ k ∈ Icc 1 ⌊t⌋₊, χ k)) (Set.Ici 1) := by
    refine locallyIntegrableOn_mul_sum_Icc (fun k : ℕ ↦ χ k) zero_le_one
      (g := fun t : ℝ ↦ (t : ℂ) ^ (-(s + 1))) ?_
    refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
    exact (continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  refine ((integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1)
    zero_lt_one).const_mul (N : ℝ)).mono'
      (by simpa only [mul_comm] using
        (hloc.mono_set Set.Ioi_subset_Ici_self).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
  simp only [neg_re, add_re, one_re]
  exact mul_le_mul_of_nonneg_right (χ.norm_sum_Icc_le_level hχ _) (Real.rpow_nonneg
    (zero_lt_one.trans ht).le _)

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
  rw [χ.LFunction_eq_mul_integral hχ hs, norm_mul]
  have hbound : ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) *
      (t : ℂ) ^ (-(s + 1))‖ ≤ (N : ℝ) / s.re := by
    calc
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), (N : ℝ) * t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le
          ((integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1)
            zero_lt_one).const_mul (N : ℝ)) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
        simp only [neg_re, add_re, one_re]
        exact mul_le_mul_of_nonneg_right (χ.norm_sum_Icc_le_level hχ _) (Real.rpow_nonneg
          (zero_lt_one.trans ht).le _)
      _ = (N : ℝ) / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
          Real.one_rpow]
        congr 1
        ring
  calc
    _ ≤ ‖s‖ * ((N : ℝ) / s.re) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = (N : ℝ) * ‖s‖ / s.re := by ring

end DirichletCharacter

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

At `s = 1` the same integral is `∫_{t > 1} S(t) / t²`, where `S(t)` is the sum of `χ k` over
`1 ≤ k ≤ t`. Using `‖S(t)‖ ≤ t` on `(1, N]` and `‖S(t)‖ ≤ N` beyond gives
`‖L(1, χ)‖ ≤ 1 + log N`. No primitivity is assumed, so this bound also holds for imprimitive
characters such as the product of two characters taken at the least common multiple of their
levels.

The function being bounded is the native analytic continuation, not the Dirichlet series
(which need not converge absolutely in this half-plane). No zero-free hypothesis is required.

## References

* H. Davenport, *Multiplicative Number Theory*, the partial-summation construction and bounds
  for Dirichlet L-functions, and the chapter on Siegel's theorem for the bound at `s = 1`.
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

/-- **A logarithmic bound for `L(1, χ)`.** The continued L-function of a nonprincipal character
of level `N` satisfies `‖L(1, χ)‖ ≤ 1 + log N`. Primitivity is not assumed; for a primitive
character, `N` is the conductor. -/
theorem norm_LFunction_one_le_one_add_log (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ 1 + Real.log N := by
  set f : ℝ → ℂ := fun t ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-((1 : ℂ) + 1)) with hf
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hnorm {t : ℝ} (ht : 0 < t) : ‖f t‖ = ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ * t ^ (-2 : ℝ) := by
    rw [hf, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
    norm_num
  have hint : IntegrableOn (fun t ↦ ‖f t‖) (Set.Ioi 1) :=
    (TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO _ (χ.sum_isBigO_one hχ)
      (s := 1) (by simp)).norm
  -- Split the integral at `N`: bound the partial sums by `t` below `N` and by `N` above it.
  have hlow : ∫ t in Set.Ioc 1 (N : ℝ), ‖f t‖ ≤ Real.log N := by
    have hinv : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Set.Ioc 1 N) :=
      (continuousOn_inv₀.mono fun t (ht : t ∈ Set.Icc 1 (N : ℝ)) ↦
        (zero_lt_one.trans_le ht.1).ne').integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    calc
      _ ≤ ∫ t in Set.Ioc 1 (N : ℝ), t⁻¹ := by
        refine setIntegral_mono_on (hint.mono_set Set.Ioc_subset_Ioi_self) hinv measurableSet_Ioc
          fun t ht ↦ ?_
        have ht0 : 0 < t := zero_lt_one.trans ht.1
        -- Termwise, the partial sum up to `t` has norm at most `⌊t⌋₊ ≤ t`.
        have hsum : ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ ≤ t :=
          calc
            _ ≤ ∑ _k ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) :=
              (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ χ.norm_le_one k)
            _ ≤ t := by simpa using Nat.floor_le ht0.le
        rw [hnorm ht0]
        calc
          _ ≤ t * t ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg ht0.le _)
          _ = t⁻¹ := by
            rw [Real.rpow_neg ht0.le, Real.rpow_two]
            field_simp
      _ = Real.log N := by
        rw [← intervalIntegral.integral_of_le hN, integral_inv_of_pos one_pos (by linarith),
          div_one]
  have hhigh : ∫ t in Set.Ioi (N : ℝ), ‖f t‖ ≤ 1 := by
    have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
    calc
      _ ≤ ∫ t in Set.Ioi (N : ℝ), (N : ℝ) * t ^ (-2 : ℝ) := by
        refine setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi hN))
          ((integrableOn_Ioi_rpow_of_lt (by norm_num) hN0).const_mul _) measurableSet_Ioi
          fun t ht ↦ ?_
        have ht0 : 0 < t := hN0.trans ht
        rw [hnorm ht0]
        exact mul_le_mul_of_nonneg_right (χ.norm_sum_Icc_le_level hχ _)
          (Real.rpow_nonneg ht0.le _)
      _ = 1 := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hN0]
        norm_num [Real.rpow_neg_one, hN0.ne']
  rw [χ.LFunction_eq_mul_integral hχ (by simp), one_mul]
  calc
    _ ≤ ∫ t in Set.Ioi 1, ‖f t‖ := norm_integral_le_integral_norm _
    _ = (∫ t in Set.Ioc 1 (N : ℝ), ‖f t‖) + ∫ t in Set.Ioi (N : ℝ), ‖f t‖ := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN)),
        Set.Ioc_union_Ioi_eq_Ioi hN]
    _ ≤ 1 + Real.log N := by linarith

end DirichletCharacter

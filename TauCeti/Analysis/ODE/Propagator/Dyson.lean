/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
public import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Dyson expansion of the propagator

For a coefficient `P : ℝ → E →L[𝕜] E` integrable on `[a, b]` and `s ∈ [a, b]`, the Dyson terms
`D₀(t) = 1`, `Dₙ₊₁(t) = ∫ r in s..t, P r ∘L Dₙ(r)` (`TauCeti.propagatorDysonTerm`) are the
iterated integrals `∫_{s<r₁<⋯<rₙ<t} P(rₙ) ⋯ P(r₁)` for `s ≤ t`. Their norms are at most
`|∫ r in s..t, ‖P r‖| ^ n / n!` (`TauCeti.norm_propagatorDysonTerm_le`), and their sum converges
to the propagator `N_P(t, s)` (`TauCeti.hasSum_propagatorDysonTerm`).

For a continuous coefficient on `ℝ`, the propagator from `0` is Tau Ceti's left Dyson series
`TauCeti.dysonSeriesLeft` (`TauCeti.propagator_zero_eq_dysonSeriesLeft`).

## Main definitions and results

* `TauCeti.propagatorDysonTerm P s n t`: the `n`-th Dyson term `Dₙ(t)` based at `s`.
* `TauCeti.norm_propagatorDysonTerm_le`: `‖Dₙ(t)‖ ≤ |∫ r in s..t, ‖P r‖| ^ n / n!`.
* `TauCeti.norm_propagatorDysonTerm_le_of_norm_le`: `‖Dₙ(t)‖ ≤ |∫ r in s..t, m r| ^ n / n!` when
  `‖P r‖ ≤ m r` between `s` and `t`.
* `TauCeti.hasSum_propagatorDysonTerm`: `∑ₙ Dₙ(t) = N_P(t, s)`.
* `TauCeti.propagator_zero_eq_dysonSeriesLeft`: `N_P(t, 0) = dysonSeriesLeft P t` for continuous
  `P`.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set intervalIntegral Real
open scoped Nat

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The `n`-th **Dyson term** of the coefficient `P` based at `s`: `D₀(t) = 1` and
`Dₙ₊₁(t) = ∫ r in s..t, P r ∘L Dₙ(r)`. For `s ≤ t` it is the iterated integral of
`P(rₙ) ⋯ P(r₁)` over `s < r₁ < ⋯ < rₙ < t`. -/
noncomputable def propagatorDysonTerm (P : ℝ → E →L[𝕜] E) (s : ℝ) : ℕ → ℝ → E →L[𝕜] E
  | 0 => fun _ ↦ 1
  | n + 1 => fun t ↦ ∫ r in s..t, P r ∘L propagatorDysonTerm P s n r

variable {P : ℝ → E →L[𝕜] E} {a b s t : ℝ}

@[simp]
theorem propagatorDysonTerm_zero (P : ℝ → E →L[𝕜] E) (s t : ℝ) :
    propagatorDysonTerm P s 0 t = 1 := by
  simp [propagatorDysonTerm]

theorem propagatorDysonTerm_succ (P : ℝ → E →L[𝕜] E) (s : ℝ) (n : ℕ) (t : ℝ) :
    propagatorDysonTerm P s (n + 1) t = ∫ r in s..t, P r ∘L propagatorDysonTerm P s n r := by
  simp [propagatorDysonTerm]

/-- Every Dyson term after the first vanishes at the base point. -/
@[simp]
theorem propagatorDysonTerm_succ_self (P : ℝ → E →L[𝕜] E) (s : ℝ) (n : ℕ) :
    propagatorDysonTerm P s (n + 1) s = 0 := by
  rw [propagatorDysonTerm_succ, integral_same]

/-- The Dyson terms are continuous on `[a, b]`. -/
theorem continuousOn_propagatorDysonTerm (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (n : ℕ) : ContinuousOn (propagatorDysonTerm P s n) (Icc a b) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    have hab := hs.1.trans hs.2
    have hI : IntervalIntegrable (fun r ↦ P r ∘L propagatorDysonTerm P s n r) volume a b :=
      hP.intervalIntegrable_clm_comp ih ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    have h := continuousOn_primitive_interval' hI (by rwa [uIcc_of_le hab])
    rwa [uIcc_of_le hab] at h

/-- **The factorial bound on the Dyson terms.**
`‖Dₙ(t)‖ ≤ |∫ r in s..t, ‖P r‖| ^ n / n!` for `s, t ∈ [a, b]`. -/
theorem norm_propagatorDysonTerm_le (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (n : ℕ) (ht : t ∈ Icc a b) :
    ‖propagatorDysonTerm P s n t‖ ≤ |∫ r in s..t, ‖P r‖| ^ n / n ! := by
  induction n generalizing t with
  | zero =>
    simp only [propagatorDysonTerm_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    have hsub := uIcc_subset_Icc hs ht
    have hPi : IntervalIntegrable (fun r ↦ ‖P r‖) volume s t :=
      IntegrableOn.intervalIntegrable (hP.mono_set hsub).norm
    rw [propagatorDysonTerm_succ, ← mul_one (_ / _)]
    refine norm_integral_le_abs_integral_norm_pow_div_factorial_mul zero_le_one hPi
      ((ae_restrict_mem measurableSet_uIoc).mono fun r hr ↦ ?_)
    rw [mul_one]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
      (ih (hsub (uIoc_subset_uIcc hr))) (norm_nonneg _))

open scoped Interval in
/-- **The factorial bound on the Dyson terms under a domination.** If `m` is integrable between
`s` and `t` and `‖P r‖ ≤ m r` for almost every `r` there, then
`‖Dₙ(t)‖ ≤ |∫ r in s..t, m r| ^ n / n!` for `s, t ∈ [a, b]`. -/
theorem norm_propagatorDysonTerm_le_of_norm_le {m : ℝ → ℝ} (hP : IntegrableOn P (Icc a b))
    (hm : IntervalIntegrable m volume s t) (hPm : ∀ᵐ r, r ∈ Ι s t → ‖P r‖ ≤ m r)
    (hs : s ∈ Icc a b) (n : ℕ) (ht : t ∈ Icc a b) :
    ‖propagatorDysonTerm P s n t‖ ≤ |∫ r in s..t, m r| ^ n / n ! := by
  refine (norm_propagatorDysonTerm_le hP hs n ht).trans ?_
  gcongr ?_ ^ _ / _
  exact intervalIntegral.abs_integral_norm_le_abs_integral_of_norm_le hm hPm

/-- **The Dyson expansion of the propagator.** For `s, t ∈ [a, b]`, the Dyson terms sum to
`N_P(t, s)`. -/
theorem hasSum_propagatorDysonTerm [CompleteSpace E] (hP : IntegrableOn P (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    HasSum (fun n ↦ propagatorDysonTerm P s n t) (propagator P t s) := by
  set D := propagatorDysonTerm P s
  set C := ∫ r in a..b, ‖P r‖
  -- On `[a, b]` the terms are dominated by the exponential series of `C`.
  have hD (n : ℕ) {r : ℝ} (hr : r ∈ Icc a b) : ‖D n r‖ ≤ C ^ n / n ! :=
    (norm_propagatorDysonTerm_le hP hs n hr).trans (by
      gcongr
      exact intervalIntegral.abs_integral_norm_le hP hs hr)
  have hsum := Real.summable_pow_div_factorial C
  let S : ℝ → E →L[𝕜] E := fun r ↦ ∑' n, D n r
  have hS {r : ℝ} (hr : r ∈ Icc a b) : HasSum (fun n ↦ D n r) (S r) :=
    (hsum.of_norm_bounded fun n ↦ hD n hr).hasSum
  have hSc : ContinuousOn S (Icc a b) :=
    continuousOn_tsum (continuousOn_propagatorDysonTerm hP hs) hsum fun n r hr ↦ hD n hr
  have hSeq (r : ℝ) (hr : r ∈ Icc a b) : S r = 1 + ∫ u in s..r, P u ∘L S u := by
    have hsub := uIcc_subset_Icc hs hr
    have hPi : IntervalIntegrable (fun u ↦ ‖P u‖) volume s r :=
      IntegrableOn.intervalIntegrable (hP.mono_set hsub).norm
    have hI : HasSum (fun n ↦ ∫ u in s..r, P u ∘L D n u) (∫ u in s..r, P u ∘L S u) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence
        (fun n u ↦ ‖P u‖ * (C ^ n / n !)) (fun n ↦ ?_) (fun n ↦ ?_)
        (ae_of_all _ fun u _ ↦ hsum.mul_left _) ?_ (ae_of_all _ fun u hu ↦ ?_)
      · exact (hP.intervalIntegrable_clm_comp (continuousOn_propagatorDysonTerm hP hs n) hs
          hr).def'.aestronglyMeasurable
      · exact ae_of_all _ fun u hu ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (hD n (hsub (uIoc_subset_uIcc hu))) (norm_nonneg _))
      · simp_rw [tsum_mul_left]
        exact hPi.mul_const _
      · exact (hS (hsub (uIoc_subset_uIcc hu))).mapL (ContinuousLinearMap.compL 𝕜 E E E (P u))
    have h1 := (hasSum_nat_add_iff' 1).2 (hS hr)
    simp only [Finset.range_one, Finset.sum_singleton] at h1
    rw [funext fun n ↦ propagatorDysonTerm_succ P s n r] at h1
    rw [← h1.unique hI]
    simp [D]
  rw [propagator_eq_of_forall_mem_Icc hP hs ht hSc hSeq]
  exact hS ht

omit [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] in
/-- **Agreement with the left Dyson series.** For a continuous coefficient
`P : ℝ → E →L[ℝ] E`, `N_P(t, 0) = dysonSeriesLeft P t`. -/
theorem propagator_zero_eq_dysonSeriesLeft [CompleteSpace E] {P : ℝ → E →L[ℝ] E}
    (hP : Continuous P) (t : ℝ) : propagator P t 0 = dysonSeriesLeft P t :=
  propagator_eq_of_hasDerivAt (a := min 0 t) (b := max 0 t) hP.continuousOn.integrableOn_Icc
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
    (fun r _ ↦ by simpa [ContinuousLinearMap.mul_def] using hasDerivAt_dysonSeriesLeft hP r)
    (dysonSeriesLeft_zero P)

end TauCeti

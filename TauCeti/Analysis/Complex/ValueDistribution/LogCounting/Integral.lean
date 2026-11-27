/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.PosLog
import TauCeti.Analysis.SpecialFunctions.Log.PosLog

/-!
# The logarithmic counting function as an integral of the counting function

For `D : E → ℤ` with locally finite support on a proper normed group, write
`n(t) = ∑ᶠ z ∈ closedBall 0 t, D z` for its unintegrated counting function. Mathlib's logarithmic
counting function `Function.locallyFinsuppWithin.logCounting D` is the log-weighted integral of `n`:
for `0 ≤ r`,
`logCounting D r = ∫ t in 0..r, (n(t) - D 0) / t + D 0 * log r`
(`Function.locallyFinsuppWithin.logCounting_eq_integral`). The proof goes through the finite-sum
form `logCounting D r = ∑ z, D z * log⁺ (r / ‖z‖) + D 0 * log r`
(`Function.locallyFinsuppWithin.logCounting_eq_sum_posLog`), in which a point `z ≠ 0` of the support
contributes `log⁺ (r / ‖z‖) = ∫ t in 0..r, 1_{‖z‖ ≤ t} t⁻¹` (`TauCeti.integral_indicator_Ici_inv`).
The same finite-sum form compares the counting function with the increments of the logarithmic
counting function: if `D` is nonnegative on the closed ball of radius `max r R`, then
`n(r) * log (R / r) ≤ logCounting D R - logCounting D r` for all positive radii `r` and `R`
(`Function.locallyFinsuppWithin.finsum_mem_closedBall_mul_log_le_logCounting_sub`).

For a function `f` on a proper nontrivially normed field,
`TauCeti.zeroCount f univ (closedBall 0 r)` is the unintegrated count `n(r)` of the zeros of `f` in
the closed disc of radius `r`, with multiplicity. Its log-weighted integral is
`ValueDistribution.logCounting f 0`, the logarithmic counting function of the positive part of the
divisor of `f`, and not the signed
`Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f univ)`, in which poles count
negatively:

* `TauCeti.logCounting_zero_eq_integral_zeroCount`: for `0 ≤ r`,
  `ValueDistribution.logCounting f 0 r = ∫ t in 0..r, (n(t) - n(0)) / t + n(0) * log r`;
* `TauCeti.zeroCount_mul_log_le_logCounting_sub`: for all positive radii `r` and `R`,
  `n(r) * log (R / r) ≤ ValueDistribution.logCounting f 0 R - ValueDistribution.logCounting f 0 r`.

## References

* S. Lang, *Introduction to Complex Hyperbolic Spaces*, Springer, 1987, §VI.1.
* J. Noguchi, J. Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
  Approximation*, Springer, 2014, §1.1.
-/

public section

open Filter MeasureTheory Metric Set

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- For `0 ≤ ρ`, some finite subset of the closed ball of radius `ρ` contains the origin and every
point of that ball at which `D` is nonzero. -/
private theorem exists_finset_cover (D : locallyFinsupp E ℤ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ T : Finset E, 0 ∈ T ∧ (∀ z ∈ T, ‖z‖ ≤ ρ) ∧ ∀ z, ‖z‖ ≤ ρ → D z ≠ 0 → z ∈ T := by
  classical
  have hball (z : E) : z ∈ closedBall (0 : E) |ρ| ↔ ‖z‖ ≤ ρ := by
    rw [mem_closedBall_zero_iff, abs_of_nonneg hρ]
  have hfin : (toClosedBall ρ D).support.Finite :=
    (toClosedBall ρ D).finiteSupport (isCompact_closedBall 0 |ρ|)
  refine ⟨insert 0 hfin.toFinset, Finset.mem_insert_self 0 _, fun z hz ↦ ?_, fun z hz hD ↦ ?_⟩
  · rcases Finset.mem_insert.1 hz with rfl | hz
    · simpa using hρ
    · exact (hball z).1 (toClosedBall_support_subset_closedBall D (hfin.mem_toFinset.1 hz))
  · refine Finset.mem_insert_of_mem (hfin.mem_toFinset.2 ?_)
    rwa [Function.mem_support, toClosedBall_eval_within _ ((hball z).2 hz)]

omit [ProperSpace E] in
/-- On the closed ball of radius `x`, the counting function of `D` is a finite sum over any finite
set `T` containing the points of the ball at which `D` is nonzero. -/
private theorem finsum_mem_closedBall_eq_sum (D : locallyFinsupp E ℤ) {x : ℝ} {T : Finset E}
    (hT : ∀ z, ‖z‖ ≤ x → D z ≠ 0 → z ∈ T) :
    ∑ᶠ z ∈ closedBall (0 : E) x, (D z : ℝ) = ∑ z ∈ T, if ‖z‖ ≤ x then (D z : ℝ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply finsum_mem_eq_sum_of_inter_support_eq
  ext z
  simp only [mem_inter_iff, mem_closedBall_zero_iff, mem_support, ne_eq, Int.cast_eq_zero,
    Finset.coe_filter, mem_ofPred_eq]
  exact ⟨fun ⟨hz, hD⟩ ↦ ⟨⟨hT z hz hD, hz⟩, hD⟩, fun ⟨⟨_, hz⟩, hD⟩ ↦ ⟨hz, hD⟩⟩

/-- **The logarithmic counting function as a finite sum of positive logarithms.** For `0 ≤ x` and
any finite set `T` containing every point of norm at most `x` at which `D` is nonzero,
`logCounting D x = ∑ z ∈ T, D z * log⁺ (x / ‖z‖) + D 0 * log x`. Points of norm greater than `x`
contribute `log⁺ (x / ‖z‖) = 0`, and so does the origin, whose weight is the separate term
`D 0 * log x`. -/
theorem logCounting_eq_sum_posLog (D : locallyFinsupp E ℤ) {x : ℝ} (hx : 0 ≤ x) {T : Finset E}
    (hT : ∀ z, ‖z‖ ≤ x → D z ≠ 0 → z ∈ T) :
    D.logCounting x = ∑ z ∈ T, (D z : ℝ) * Real.posLog (x / ‖z‖) + D 0 * Real.log x := by
  have hball (z : E) : z ∈ closedBall (0 : E) |x| ↔ ‖z‖ ≤ x := by
    rw [mem_closedBall_zero_iff, abs_of_nonneg hx]
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := T) fun z hz ↦ ?_]
  · refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hz : ‖z‖ ≤ x
    · have hzx : |‖z‖| ≤ |x| := by rwa [abs_norm, abs_of_nonneg hx]
      rw [toClosedBall_eval_within _ ((hball z).2 hz), Real.posLog_div_eq_log_of_abs_le_abs hzx,
        div_eq_mul_inv]
    · have hxz : |x| ≤ |‖z‖| := by
        rw [abs_norm, abs_of_nonneg hx]
        exact (not_le.1 hz).le
      rw [apply_eq_zero_of_notMem _ (mt (hball z).1 hz),
        Real.posLog_div_eq_zero_of_abs_le_abs hxz]
      simp
  · have h1 : toClosedBall x D z ≠ 0 := fun h ↦ hz (by simp [h])
    have h2 : z ∈ closedBall (0 : E) |x| := by
      by_contra h
      exact h1 (apply_eq_zero_of_notMem _ h)
    rw [toClosedBall_eval_within _ h2] at h1
    exact hT z ((hball z).1 h2) h1

/-- **The logarithmic counting function is the log-weighted integral of the counting function.**
With `n(t) = ∑ᶠ z ∈ closedBall 0 t, D z`, for every `0 ≤ r`,
`logCounting D r = ∫ t in 0..r, (n(t) - D 0) / t + D 0 * log r`.
The integrand vanishes near `0`, and the weight of the origin enters only through `D 0 * log r`. -/
theorem logCounting_eq_integral (D : locallyFinsupp E ℤ) {r : ℝ} (hr : 0 ≤ r) :
    D.logCounting r = (∫ t in (0 : ℝ)..r,
      ((∑ᶠ z ∈ closedBall (0 : E) t, (D z : ℝ)) - D 0) / t) + D 0 * Real.log r := by
  classical
  obtain ⟨T, hT0, -, hT⟩ := exists_finset_cover D hr
  have hpos : ∀ z ∈ T.erase 0, 0 < ‖z‖ := fun z hz ↦ norm_pos_iff.2 (Finset.ne_of_mem_erase hz)
  have hn : ∀ t ∈ uIcc 0 r, ((∑ᶠ z ∈ closedBall (0 : E) t, (D z : ℝ)) - D 0) / t =
      ∑ z ∈ T.erase 0, (D z : ℝ) * (Ici ‖z‖).indicator (fun t : ℝ ↦ t⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hr] at ht
    rw [finsum_mem_closedBall_eq_sum D fun z hz hD ↦ hT z (hz.trans ht.2) hD,
      ← Finset.add_sum_erase T _ hT0, norm_zero, ite_eq_left ht.1, add_sub_cancel_left,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hzt : ‖z‖ ≤ t
    · rw [ite_eq_left hzt, indicator_of_mem (mem_Ici.2 hzt), div_eq_mul_inv]
    · rw [ite_eq_right hzt, indicator_of_notMem (by simpa using hzt), zero_div, mul_zero]
  rw [intervalIntegral.integral_congr hn, intervalIntegral.integral_finsetSum fun z hz ↦
      (TauCeti.intervalIntegrable_indicator_Ici_inv (hpos z hz) 0 r).const_mul _,
    logCounting_eq_sum_posLog D hr hT, ← Finset.add_sum_erase T _ hT0]
  simp only [intervalIntegral.integral_const_mul, norm_zero, div_zero, Real.posLog_zero, mul_zero,
    zero_add]
  exact congrArg (· + _) (Finset.sum_congr rfl fun z hz ↦ by
    rw [TauCeti.integral_indicator_Ici_inv (hpos z hz) hr])

/-- For `0 < a` and positive radii `r` and `R`, the weight `log⁺ (· / a)` increases from `r` to `R`
by at least `log (R / r)` when `a ≤ r`, and by at least `0` otherwise. -/
private theorem ite_le_posLog_div_sub_posLog_div {a r R : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hR : 0 < R) :
    (if a ≤ r then Real.log (R / r) else 0) ≤ Real.posLog (R / a) - Real.posLog (r / a) := by
  split_ifs with h
  · have hlog : Real.log (R / r) = Real.log (R / a) - Real.log (r / a) := by
      rw [Real.log_div hR.ne' hr.ne', Real.log_div hR.ne' ha.ne', Real.log_div hr.ne' ha.ne']
      ring
    have hle : Real.log (R / a) ≤ Real.posLog (R / a) := by
      rw [Real.posLog_apply]
      exact le_max_right _ _
    rw [Real.posLog_div_eq_log_of_abs_le_abs (abs_le_abs_of_nonneg ha.le h)]
    linarith
  · rw [Real.posLog_div_eq_zero_of_abs_le_abs (abs_le_abs_of_nonneg hr.le (not_le.1 h).le),
      sub_zero]
    exact Real.posLog_nonneg

/-- **The counting function against the logarithmic counting function.** If `D` is nonnegative on
the closed ball of radius `max r R`, then for positive radii `r` and `R`, with
`n(r) = ∑ᶠ z ∈ closedBall 0 r, D z`, `n(r) * log (R / r) ≤ logCounting D R - logCounting D r`.
For `r ≤ R` this bounds the increment of the logarithmic counting function from below; for
`R < r` it reads `logCounting D r - logCounting D R ≤ n(r) * log (r / R)`, an upper bound. -/
theorem finsum_mem_closedBall_mul_log_le_logCounting_sub (D : locallyFinsupp E ℤ) {r R : ℝ}
    (hD : ∀ z, ‖z‖ ≤ max r R → 0 ≤ D z) (hr : 0 < r) (hR : 0 < R) :
    (∑ᶠ z ∈ closedBall (0 : E) r, (D z : ℝ)) * Real.log (R / r) ≤
      D.logCounting R - D.logCounting r := by
  classical
  obtain ⟨T, hT0, hTball, hT⟩ := exists_finset_cover D (hr.le.trans (le_max_left r R))
  have hTr : ∀ z, ‖z‖ ≤ r → D z ≠ 0 → z ∈ T := fun z hz ↦ hT z (hz.trans (le_max_left r R))
  rw [logCounting_eq_sum_posLog D hR.le fun z hz ↦ hT z (hz.trans (le_max_right r R)),
    logCounting_eq_sum_posLog D hr.le hTr, finsum_mem_closedBall_eq_sum D hTr, Finset.sum_mul]
  have key : ∀ z ∈ T, (if ‖z‖ ≤ r then (D z : ℝ) else 0) * Real.log (R / r) ≤
      (D z : ℝ) * (Real.posLog (R / ‖z‖) - Real.posLog (r / ‖z‖)) +
        if z = 0 then (D 0 : ℝ) * Real.log (R / r) else 0 := by
    intro z hzT
    by_cases hz : z = 0
    · subst hz
      simp [hr.le]
    · rw [ite_eq_right hz, add_zero]
      calc (if ‖z‖ ≤ r then (D z : ℝ) else 0) * Real.log (R / r)
          = (D z : ℝ) * (if ‖z‖ ≤ r then Real.log (R / r) else 0) := by
            split_ifs <;> simp
        _ ≤ (D z : ℝ) * (Real.posLog (R / ‖z‖) - Real.posLog (r / ‖z‖)) :=
            mul_le_mul_of_nonneg_left
              (ite_le_posLog_div_sub_posLog_div (norm_pos_iff.2 hz) hr hR)
              (by exact_mod_cast hD z (hTball z hzT))
  refine (Finset.sum_le_sum key).trans_eq ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' T 0, ite_eq_left hT0,
    Real.log_div hR.ne' hr.ne']
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end Function.locallyFinsuppWithin

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The logarithmic counting function of the zeros is the log-weighted integral of the zero
count.** With `n(t) = zeroCount f univ (closedBall 0 t)`, for every `0 ≤ r`,
`ValueDistribution.logCounting f 0 r = ∫ t in 0..r, (n(t) - n(0)) / t + n(0) * log r`. -/
theorem logCounting_zero_eq_integral_zeroCount (f : 𝕜 → F) {r : ℝ} (hr : 0 ≤ r) :
    ValueDistribution.logCounting f 0 r =
      (∫ t in (0 : ℝ)..r, ((zeroCount f univ (closedBall 0 t) : ℝ) -
        zeroCount f univ (closedBall 0 0)) / t) +
        zeroCount f univ (closedBall 0 0) * Real.log r := by
  have h0 : (zeroCount f univ (closedBall 0 0) : ℝ) = ((MeromorphicOn.divisor f univ)⁺ 0 : ℝ) := by
    rw [zeroCount_eq_finsum_posPart, closedBall_zero, finsum_mem_singleton]
  rw [ValueDistribution.logCounting_zero, h0]
  simp only [zeroCount_eq_finsum_posPart]
  exact Function.locallyFinsuppWithin.logCounting_eq_integral _ hr

/-- **The zero count against the logarithmic counting function.** For positive radii `r` and `R`,
the zero count `n(r) = zeroCount f univ (closedBall 0 r)` satisfies
`n(r) * log (R / r) ≤ ValueDistribution.logCounting f 0 R - ValueDistribution.logCounting f 0 r`.
For `r ≤ R` this bounds the increment of the logarithmic counting function from below; for
`R < r` it reads `N(r) - N(R) ≤ n(r) * log (r / R)`, an upper bound. -/
theorem zeroCount_mul_log_le_logCounting_sub (f : 𝕜 → F) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (zeroCount f univ (closedBall 0 r) : ℝ) * Real.log (R / r) ≤
      ValueDistribution.logCounting f 0 R - ValueDistribution.logCounting f 0 r := by
  rw [ValueDistribution.logCounting_zero, zeroCount_eq_finsum_posPart]
  refine Function.locallyFinsuppWithin.finsum_mem_closedBall_mul_log_le_logCounting_sub _
    (fun z _ ↦ ?_) hr hR
  rw [Function.locallyFinsuppWithin.posPart_apply]
  exact posPart_nonneg _

end TauCeti

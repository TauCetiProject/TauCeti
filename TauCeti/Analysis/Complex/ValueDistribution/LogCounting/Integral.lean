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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
contributes `log⁺ (r / ‖z‖) = ∫ t in 0..r, 1_{‖z‖ ≤ t} t⁻¹`.

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

/-- The reciprocal function cut off below `a > 0` is interval integrable on every interval: on
`Ici a` it agrees with the continuous function `t ↦ (max t a)⁻¹`. -/
private theorem intervalIntegrable_indicator_Ici_inv {a : ℝ} (ha : 0 < a) (b c : ℝ) :
    IntervalIntegrable ((Ici a).indicator fun t : ℝ ↦ t⁻¹) volume b c := by
  have heq : (Ici a).indicator (fun t : ℝ ↦ t⁻¹) = (Ici a).indicator fun t ↦ (max t a)⁻¹ :=
    indicator_congr fun t ht ↦ by rw [max_eq_left (mem_Ici.1 ht)]
  have hcont : Continuous fun t : ℝ ↦ (max t a)⁻¹ :=
    (continuous_id.max continuous_const).inv₀ fun t ↦ (ha.trans_le (le_max_right t a)).ne'
  rw [heq, intervalIntegrable_iff]
  exact (intervalIntegrable_iff.1 (hcont.intervalIntegrable b c)).indicator measurableSet_Ici

/-- For `0 < a` and `0 ≤ x`, `∫ t in 0..x, 1_{a ≤ t} t⁻¹ = log⁺ (x / a)`. -/
private theorem integral_indicator_Ici_inv {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    ∫ t in (0 : ℝ)..x, (Ici a).indicator (fun t : ℝ ↦ t⁻¹) t = Real.posLog (x / a) := by
  rw [intervalIntegral.integral_of_le hx, setIntegral_indicator measurableSet_Ici]
  rcases le_or_gt a x with hax | hxa
  · have hset : Ioc 0 x ∩ Ici a = Icc a x := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      exact ⟨fun ⟨⟨_, htx⟩, hat⟩ ↦ ⟨hat, htx⟩, fun ⟨hat, htx⟩ ↦ ⟨⟨ha.trans_le hat, htx⟩, hat⟩⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hax,
      integral_inv_of_pos ha (ha.trans_le hax), Real.posLog_eq_log]
    rw [abs_of_pos (div_pos (ha.trans_le hax) ha), one_le_div ha]
    exact hax
  · have hset : Ioc 0 x ∩ Ici a = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_empty_iff_false, iff_false]
      exact fun ⟨⟨_, htx⟩, hat⟩ ↦ (hat.trans htx).not_gt hxa
    rw [hset, Measure.restrict_empty, integral_zero_measure, eq_comm, Real.posLog_eq_zero_iff,
      abs_of_nonneg (div_nonneg hx ha.le)]
    exact (div_le_one ha).2 hxa.le

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
    · rw [toClosedBall_eval_within _ ((hball z).2 hz)]
      rcases (norm_nonneg z).eq_or_lt with h0 | hpos
      · simp [← h0]
      · have hxz : 1 ≤ |x / ‖z‖| := by
          rw [abs_of_pos (div_pos (hpos.trans_le hz) hpos)]
          exact (one_le_div hpos).2 hz
        rw [Real.posLog_eq_log hxz, div_eq_mul_inv]
    · have hxz : |x / ‖z‖| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg hx (norm_nonneg z))]
        exact (div_le_one (hx.trans_lt (not_le.1 hz))).2 (not_le.1 hz).le
      rw [apply_eq_zero_of_notMem _ (mt (hball z).1 hz), (Real.posLog_eq_zero_iff _).2 hxz]
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
  have hfin : (toClosedBall r D).support.Finite :=
    (toClosedBall r D).finiteSupport (isCompact_closedBall 0 |r|)
  set T : Finset E := insert 0 hfin.toFinset
  have hT : ∀ z, ‖z‖ ≤ r → D z ≠ 0 → z ∈ T := fun z hz hD ↦ by
    refine Finset.mem_insert_of_mem (hfin.mem_toFinset.2 ?_)
    rwa [mem_support, toClosedBall_eval_within _
      (by rwa [mem_closedBall_zero_iff, abs_of_nonneg hr])]
  have hpos : ∀ z ∈ T.erase 0, 0 < ‖z‖ := fun z hz ↦ norm_pos_iff.2 (Finset.ne_of_mem_erase hz)
  have hn : ∀ t ∈ uIcc 0 r, ((∑ᶠ z ∈ closedBall (0 : E) t, (D z : ℝ)) - D 0) / t =
      ∑ z ∈ T.erase 0, (D z : ℝ) * (Ici ‖z‖).indicator (fun t : ℝ ↦ t⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hr] at ht
    rw [finsum_mem_closedBall_eq_sum D fun z hz hD ↦ hT z (hz.trans ht.2) hD,
      ← Finset.add_sum_erase T _ (Finset.mem_insert_self 0 _), norm_zero, ite_eq_left ht.1,
      add_sub_cancel_left, Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hzt : ‖z‖ ≤ t
    · rw [ite_eq_left hzt, indicator_of_mem (mem_Ici.2 hzt), div_eq_mul_inv]
    · rw [ite_eq_right hzt, indicator_of_notMem (by simpa using hzt), zero_div, mul_zero]
  rw [intervalIntegral.integral_congr hn, intervalIntegral.integral_finsetSum fun z hz ↦
      (intervalIntegrable_indicator_Ici_inv (hpos z hz) 0 r).const_mul _,
    logCounting_eq_sum_posLog D hr hT, ← Finset.add_sum_erase T _ (Finset.mem_insert_self 0 _)]
  simp only [intervalIntegral.integral_const_mul, norm_zero, div_zero, Real.posLog_zero, mul_zero,
    zero_add]
  exact congrArg (· + _) (Finset.sum_congr rfl fun z hz ↦ by
    rw [integral_indicator_Ici_inv (hpos z hz) hr])

end Function.locallyFinsuppWithin

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

omit [ProperSpace 𝕜] in
/-- The zero count in a closed ball is the counting function of the positive part of the
divisor. -/
private theorem zeroCount_closedBall_eq_finsum (f : 𝕜 → F) (t : ℝ) :
    (zeroCount f univ (closedBall 0 t) : ℝ) =
      ∑ᶠ z ∈ closedBall (0 : 𝕜) t, ((MeromorphicOn.divisor f univ)⁺ z : ℝ) := by
  have hcast := (Nat.castAddMonoidHom ℝ).map_finsum_of_injective Nat.cast_injective
    (fun z ↦ ∑ᶠ _ : z ∈ closedBall (0 : 𝕜) t, (MeromorphicOn.divisor f univ z).toNat)
  simp only [AddMonoidHom.map_finsum_Prop, Nat.coe_castAddMonoidHom] at hcast
  rw [zeroCount_def, hcast]
  refine finsum_congr fun z ↦ finsum_congr fun _ ↦ ?_
  rw [Function.locallyFinsuppWithin.posPart_apply, posPart_def, ← Int.toNat_eq_max,
    Int.cast_natCast]

/-- **The logarithmic counting function of the zeros is the log-weighted integral of the zero
count.** With `n(t) = zeroCount f univ (closedBall 0 t)`, for every `0 ≤ r`,
`ValueDistribution.logCounting f 0 r = ∫ t in 0..r, (n(t) - n(0)) / t + n(0) * log r`. -/
theorem logCounting_zero_eq_integral_zeroCount (f : 𝕜 → F) {r : ℝ} (hr : 0 ≤ r) :
    ValueDistribution.logCounting f 0 r =
      (∫ t in (0 : ℝ)..r, ((zeroCount f univ (closedBall 0 t) : ℝ) -
        zeroCount f univ (closedBall 0 0)) / t) +
        zeroCount f univ (closedBall 0 0) * Real.log r := by
  have h0 : (zeroCount f univ (closedBall 0 0) : ℝ) = ((MeromorphicOn.divisor f univ)⁺ 0 : ℝ) := by
    rw [zeroCount_closedBall_eq_finsum, closedBall_zero, finsum_mem_singleton]
  rw [ValueDistribution.logCounting_zero, h0]
  simp only [zeroCount_closedBall_eq_finsum]
  exact Function.locallyFinsuppWithin.logCounting_eq_integral _ hr

/-- For `0 < a` and positive radii `r` and `R`, the weight `log⁺ (· / a)` increases from `r` to `R`
by at least `log (R / r)` when `a ≤ r`, and by at least `0` otherwise. -/
private theorem ite_le_posLog_div_sub_posLog_div {a r R : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hR : 0 < R) :
    (if a ≤ r then Real.log (R / r) else 0) ≤ Real.posLog (R / a) - Real.posLog (r / a) := by
  split_ifs with h
  · have hra : 1 ≤ |r / a| := by
      rw [abs_of_pos (div_pos hr ha)]
      exact (one_le_div ha).2 h
    have hlog : Real.log (R / r) = Real.log (R / a) - Real.log (r / a) := by
      rw [Real.log_div hR.ne' hr.ne', Real.log_div hR.ne' ha.ne', Real.log_div hr.ne' ha.ne']
      ring
    have hle : Real.log (R / a) ≤ Real.posLog (R / a) := by
      rw [Real.posLog_apply]
      exact le_max_right _ _
    rw [Real.posLog_eq_log hra]
    linarith
  · have hra : |r / a| ≤ 1 := by
      rw [abs_of_pos (div_pos hr ha)]
      exact (div_le_one ha).2 (not_le.1 h).le
    rw [(Real.posLog_eq_zero_iff _).2 hra, sub_zero]
    exact Real.posLog_nonneg

/-- **The zero count against the logarithmic counting function.** For positive radii `r` and `R`,
the zero count `n(r) = zeroCount f univ (closedBall 0 r)` satisfies
`n(r) * log (R / r) ≤ ValueDistribution.logCounting f 0 R - ValueDistribution.logCounting f 0 r`.
For `r ≤ R` this bounds the increment of the logarithmic counting function from below; for
`R < r` it reads `N(r) - N(R) ≤ n(r) * log (r / R)`, an upper bound. -/
theorem zeroCount_mul_log_le_logCounting_sub (f : 𝕜 → F) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (zeroCount f univ (closedBall 0 r) : ℝ) * Real.log (R / r) ≤
      ValueDistribution.logCounting f 0 R - ValueDistribution.logCounting f 0 r := by
  classical
  set D := (MeromorphicOn.divisor f univ)⁺ with hD_def
  have hD : ∀ z, 0 ≤ D z := fun z ↦ by
    rw [hD_def, Function.locallyFinsuppWithin.posPart_apply]
    exact posPart_nonneg _
  have hM : 0 < max r R := hr.trans_le (le_max_left r R)
  have hfin : (Function.locallyFinsuppWithin.toClosedBall (max r R) D).support.Finite :=
    (Function.locallyFinsuppWithin.toClosedBall (max r R) D).finiteSupport
      (isCompact_closedBall 0 |max r R|)
  set T : Finset 𝕜 := insert 0 hfin.toFinset
  have hT : ∀ x ≤ max r R, ∀ z, ‖z‖ ≤ x → D z ≠ 0 → z ∈ T := fun x hx z hz hDz ↦ by
    refine Finset.mem_insert_of_mem (hfin.mem_toFinset.2 ?_)
    rwa [Function.mem_support, Function.locallyFinsuppWithin.toClosedBall_eval_within _
      (by rw [mem_closedBall_zero_iff, abs_of_pos hM]; exact hz.trans hx)]
  rw [ValueDistribution.logCounting_zero, zeroCount_closedBall_eq_finsum, ← hD_def,
    Function.locallyFinsuppWithin.logCounting_eq_sum_posLog D hR.le (hT R (le_max_right r R)),
    Function.locallyFinsuppWithin.logCounting_eq_sum_posLog D hr.le (hT r (le_max_left r R)),
    Function.locallyFinsuppWithin.finsum_mem_closedBall_eq_sum D (hT r (le_max_left r R)),
    Finset.sum_mul]
  have key : ∀ z ∈ T, (if ‖z‖ ≤ r then (D z : ℝ) else 0) * Real.log (R / r) ≤
      (D z : ℝ) * (Real.posLog (R / ‖z‖) - Real.posLog (r / ‖z‖)) +
        if z = 0 then (D 0 : ℝ) * Real.log (R / r) else 0 := by
    intro z _
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
              (by exact_mod_cast hD z)
  refine (Finset.sum_le_sum key).trans_eq ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' T 0, ite_eq_left (Finset.mem_insert_self 0 _),
    Real.log_div hR.ne' hr.ne']
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end TauCeti

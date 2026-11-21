/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Stretched exponential decay implies rapid power decay

For positive `c` and `α`, the stretched exponential `exp (-c * t ^ α)` decays faster
than every real power of `t` at infinity. Consequently an error bounded by this
exponential satisfies the power-decay hypotheses in `WeakFEPair` and hence in the
Mellin-transform construction of completed zeta and L-functions.

The estimate is obtained from Mathlib's `isLittleO_exp_neg_mul_rpow_atTop` by the
substitution `u = t ^ α`. No regularity of the dominated function is needed, and its
values may lie in any type carrying a norm.

In addition, for any function continuous on a ray `[a, ∞)` with `0 < a ∨ 0 ≤ α`, an eventual
big-O or pointwise bound by `exp (-p * u ^ α)` at infinity upgrades to a uniform bound
`C * exp (-p * u ^ α)` on all of `[a, ∞)`, with `C ≥ 0`. Dividing the argument by a positive
real `N` preserves stretched-exponential asymptotic bounds `f =O[atTop] fun u ↦ exp (-c * u ^ α)`,
rescaling the coefficient from `c` to `c / N ^ α`.

On the complex side, for `c > 0` and the principal fourth root `z^{1/4}`, the real part of
`c z^{1/4}` is at least `c |z|^{1/4} / 2` on the whole plane, so `exp(-c z^{1/4})` decays faster
than every power of `z⁻¹` along `cobounded ℂ`: see `TauCeti.norm_cexp_neg_mul_cpow_quarter_le`
and `TauCeti.isBigO_cexp_neg_mul_cpow_quarter`. These two estimates are adapted from the lean-DLMF
project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`.
-/

public section

open Asymptotics Filter Real Set

namespace TauCeti

/-- A stretched exponential with positive rate and exponent is little-o of every real
power at infinity. The power `r` may be negative. -/
theorem isLittleO_exp_neg_mul_rpow_rpow_atTop {c α : ℝ} (hc : 0 < c) (hα : 0 < α) (r : ℝ) :
    (fun t : ℝ ↦ Real.exp (-c * t ^ α)) =o[atTop] fun t ↦ t ^ r := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (r / α)).comp_tendsto
    (tendsto_rpow_atTop hα)
  refine h.congr' .rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply, ← Real.rpow_mul ht, mul_div_cancel₀ r hα.ne']

/-- Exponential decay supplies the rapid power bounds required by the Mellin principle:
`f = O(exp (-c t^α))` implies `f = O(t^r)` for every real `r`, when `c, α > 0`. -/
theorem isBigO_rpow_of_isBigO_exp_neg {E : Type*} [Norm E] {f : ℝ → E} {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α)
    (hf : f =O[atTop] fun t ↦ Real.exp (-c * t ^ α)) (r : ℝ) :
    f =O[atTop] fun t ↦ t ^ r :=
  (hf.trans_isLittleO (isLittleO_exp_neg_mul_rpow_rpow_atTop hc hα r)).isBigO

/-- Dividing the argument by a positive real `N` preserves stretched-exponential asymptotic bounds,
rescaling the coefficient `c` to `c / N ^ α`. -/
theorem isBigO_comp_div_exp_neg_mul_rpow {E : Type*} [Norm E] {f : ℝ → E} {N c α : ℝ}
    (hN : 0 < N) (hf : f =O[atTop] fun u ↦ exp (-c * u ^ α)) :
    (fun u ↦ f (u / N)) =O[atTop] fun u ↦ exp (-(c / N ^ α) * u ^ α) := by
  refine (hf.comp_tendsto (tendsto_id.atTop_div_const hN)).congr' .rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  simp only [Function.comp_apply, id_eq]
  congr 1
  rw [div_rpow hu hN.le]
  ring

/-- A function continuous on `[a, ∞)` with `0 < a ∨ 0 ≤ α` and an eventual bound
`O(exp (-p u ^ α))` satisfies `‖f u‖ ≤ C exp (-p u ^ α)` for every `u ≥ a`, with `C ≥ 0`.
The condition `0 < a ∨ 0 ≤ α` ensures continuity of `u ↦ u ^ α` on `[a, ∞)`. -/
theorem exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_isBigO {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {a p α : ℝ} (ha : 0 < a ∨ 0 ≤ α) (hf : ContinuousOn f (Ici a))
    (h : f =O[atTop] fun u ↦ exp (-p * u ^ α)) :
    ∃ C ≥ 0, ∀ u ∈ Ici a, ‖f u‖ ≤ C * exp (-p * u ^ α) := by
  have hg : ContinuousOn (fun u : ℝ ↦ exp (-p * u ^ α)) (Ici a) :=
    continuous_exp.comp_continuousOn <| continuousOn_const.mul <|
      continuousOn_id.rpow_const fun u hu ↦ ha.imp (fun ha0 ↦ (ha0.trans_le hu).ne') id
  obtain ⟨C, hC⟩ := isBigO_principal.mp (h.isBigO_principal_Ici_of_continuousOn hf
    hg fun u _ ↦ (exp_pos _).ne')
  refine ⟨max C 0, le_max_right _ _, fun u hu ↦ ?_⟩
  have hCu := hC u hu
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)] at hCu
  exact hCu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le)

/-- Promotes an eventual pointwise stretched-exponential bound at `∞` on a function continuous on
`[a, ∞)` (with `0 < a ∨ 0 ≤ α`) to a uniform bound on all of `[a, ∞)`. -/
theorem exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_eventually {F : Type*} [SeminormedAddGroup F]
    {f : ℝ → F} {a C₀ p α : ℝ} (ha : 0 < a ∨ 0 ≤ α) (hf : ContinuousOn f (Ici a))
    (h : ∀ᶠ u in atTop, ‖f u‖ ≤ C₀ * exp (-p * u ^ α)) :
    ∃ C ≥ 0, ∀ u ∈ Ici a, ‖f u‖ ≤ C * exp (-p * u ^ α) := by
  refine exists_norm_le_mul_exp_neg_mul_rpow_Ici_of_isBigO ha hf (IsBigO.of_bound C₀ ?_)
  filter_upwards [h] with u hu
  rwa [Real.norm_eq_abs, abs_of_pos (exp_pos _)]

section CpowQuarter

open Complex Bornology

/-- For `c > 0`, `‖exp(-c z^{1/4})‖ ≤ (4N)! (2/c)^{4N} |z|⁻ᴺ`. -/
theorem norm_cexp_neg_mul_cpow_quarter_le {c : ℝ} (hc : 0 < c) (N : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖cexp (-(c * z ^ (1 / 4 : ℂ)))‖ ≤ (4 * N).factorial * (2 / c) ^ (4 * N) * (‖z‖ ^ N)⁻¹ := by
  have ht : 0 < ‖z‖ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.2 hz) _
  set t := ‖z‖ ^ (1 / 4 : ℝ) with ht_def
  have h4 : t ^ (4 * N) = ‖z‖ ^ N := by
    rw [pow_mul, ht_def, ← Real.rpow_mul_natCast (norm_nonneg z)]
    norm_num
  have hre := norm_rpow_le_two_mul_re_cpow_quarter (z := z)
  have hexp := Real.pow_div_factorial_le_exp (c / 2 * t) (by positivity) (4 * N)
  rw [Complex.norm_exp, neg_re, re_ofReal_mul]
  calc Real.exp (-(c * (z ^ (1 / 4 : ℂ)).re)) ≤ Real.exp (-(c / 2 * t)) :=
        Real.exp_le_exp.2 (by nlinarith)
    _ = (Real.exp (c / 2 * t))⁻¹ := Real.exp_neg _
    _ ≤ ((c / 2 * t) ^ (4 * N) / (4 * N).factorial)⁻¹ := inv_anti₀ (by positivity) hexp
    _ = _ := by rw [← h4]; field_simp; rw [← mul_pow]; congr 1; field_simp

/-- For `c > 0`, `exp(-c z^{1/4}) = O(z⁻ᴺ)` at infinity for every `N`. -/
theorem isBigO_cexp_neg_mul_cpow_quarter {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (fun z : ℂ => cexp (-(c * z ^ (1 / 4 : ℂ)))) =O[cobounded ℂ] fun z => (z ^ N)⁻¹ := by
  refine Asymptotics.IsBigO.of_bound ((4 * N).factorial * (2 / c) ^ (4 * N)) ?_
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz
  rw [norm_inv, norm_pow]
  exact norm_cexp_neg_mul_cpow_quarter_le hc N (norm_pos_iff.1 hz)

end CpowQuarter

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.Asymptotics.Lemmas

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

end TauCeti

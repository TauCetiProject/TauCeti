/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic
public import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The quadratic correction under power-law bounds on its constants

Gluing constructions at a large parameter, such as Taubes's construction of Seiberg–Witten
solutions from pseudoholomorphic curves, solve a family of equations

`e_h + D_h x + N_h x = 0`,

indexed by a small scale `h > 0` (for the Seiberg–Witten equations at parameter `r`,
`h = (2 r)^(-1/2)`), with the fixed-point argument of
`TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic`. None of its constants is uniform in
`h`: the right inverse `Q_h` of `D_h` has norm `C_h`, the remainder `N_h` is quadratic with
constant `L_h` on the ball of radius `δ_h`, and the residual `e_h` of the approximate solution has
norm at most `ε_h`. The analysis only provides power laws

`C_h = O(h^(-q))`,  `L_h = O(h^(-l))`,  `δ_h⁻¹ = O(h^(-a))`,  `ε_h = O(h^s)`,

where the exponents `q`, `l`, `a` measure the losses of the linear theory and `s` is the order of
the approximate solution (`s = N + 1 - π` for a profile of order `N` whose residual loses `π`
powers of `h` in the norms used). This file proves that the fixed-point argument nevertheless
applies for all small `h` once

`2 q + l < s`  and  `q + a < s`.

Under these inequalities, the quantities `2 C_h² L_h ε_h` and `C_h ε_h / δ_h` that control the
contraction tend to zero. So for all small `h` the equations have solutions `x_h(p)` in the range
of `Q_h(p)`, of norm at most `2 C_h ‖e_h(p)‖`, depending continuously on a parameter `p`, and
these are the only solutions in that range of norm at most `δ_h` with `C_h L_h ‖y‖ < 1`
(`TauCeti.eventually_exists_continuous_forall_add_add_eq_zero`).

The point of the uniqueness region is recovery. A separate a priori argument typically shows that
every actual solution `y` lies within `K_h ε_h` of the approximate solution, for a recovery
constant `K_h = O(h^(-b))`. If moreover

`a + b < s`  and  `q + l + b < s`,

then for all small `h` every such solution in the range of `Q_h(p)` is the constructed one
(`TauCeti.eventually_exists_continuous_forall_add_add_eq_zero_of_norm_le_mul`). The two pairs of
exponent inequalities together say that the residual exponent `s` exceeds `2 q + l` and `q + a`,
and that `s - b` exceeds both `a` and `q + l`. All exponents are real, and the constants hidden
in the `O` may depend on everything except `h`, so a single threshold for `h` serves the
contraction and the recovery comparison simultaneously. When the profile order `N` is free and the
exponents `q`, `l`, `a`, `π`, `b` do not depend on it, all four inequalities hold for every large
`N`.

The bound `δ_h⁻¹ = O(h^(-a))` together with `δ_h > 0` is equivalent to a lower bound
`δ_h ≥ k h^a` with `k > 0`, for small `h`.

## Main results

* `TauCeti.eventually_exists_continuous_forall_add_add_eq_zero`: existence, continuity in the
  parameter and uniqueness of the corrections for all small `h`.
* `TauCeti.eventually_exists_continuous_forall_add_add_eq_zero_of_norm_le_mul`: the same, with
  every solution of norm at most `K_h ε_h` identified with the constructed one.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Proposition A.3.4.
-/

public section

open Asymptotics Filter Metric Set
open scoped NNReal Topology

namespace TauCeti

/-! ### The budgets -/

/-- **The contraction budget.** If `C = O(h^(-q))`, `L = O(h^(-l))`, `δ⁻¹ = O(h^(-a))` and
`ε = O(h^s)` with `2 q + l < s` and `q + a < s`, and `δ > 0` for small `h`, then for small `h`
the residual bound `ε` satisfies both hypotheses `2 C ε ≤ δ` and `2 C² L ε < 1` of the fixed-point
argument. -/
private lemma eventually_contraction_budget {C L δ ε : ℝ → ℝ} {q l a s : ℝ}
    (hC : C =O[𝓝[>] 0] fun h ↦ h ^ (-q)) (hL : L =O[𝓝[>] 0] fun h ↦ h ^ (-l))
    (hδ : (fun h ↦ (δ h)⁻¹) =O[𝓝[>] 0] fun h ↦ h ^ (-a))
    (hε : ε =O[𝓝[>] 0] fun h ↦ h ^ s) (hδ0 : ∀ᶠ h in 𝓝[>] 0, 0 < δ h)
    (hql : 2 * q + l < s) (hqa : q + a < s) :
    ∀ᶠ h in 𝓝[>] 0, 2 * C h * ε h ≤ δ h ∧ 2 * C h ^ 2 * L h * ε h < 1 := by
  have h₁ := eventually_lt_of_isBigO_rpow (sub_pos.2 hql) (((hC.mul_nhdsGT_zero_rpow_of_isBigO_rpow
    hC le_rfl).mul_nhdsGT_zero_rpow_of_isBigO_rpow hL le_rfl).mul_nhdsGT_zero_rpow_of_isBigO_rpow
    hε (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2)
  have h₂ := eventually_lt_of_isBigO_rpow (sub_pos.2 hqa) ((hC.mul_nhdsGT_zero_rpow_of_isBigO_rpow
    hε le_rfl).mul_nhdsGT_zero_rpow_of_isBigO_rpow hδ (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [h₁, h₂, hδ0] with h h₁ h₂ hδ0
  simp only [Pi.mul_apply] at h₁ h₂
  refine ⟨?_, by nlinarith⟩
  rw [mul_inv_lt_iff₀ hδ0] at h₂
  linarith

/-- **The recovery budget.** If moreover `K = O(h^(-b))` with `a + b < s` and `q + l + b < s`,
then for small `h` the recovery radius `K ε` satisfies `K ε ≤ δ` and `C L (K ε) < 1`. -/
private lemma eventually_recovery_budget {C L δ ε K : ℝ → ℝ} {q l a s b : ℝ}
    (hC : C =O[𝓝[>] 0] fun h ↦ h ^ (-q)) (hL : L =O[𝓝[>] 0] fun h ↦ h ^ (-l))
    (hδ : (fun h ↦ (δ h)⁻¹) =O[𝓝[>] 0] fun h ↦ h ^ (-a))
    (hε : ε =O[𝓝[>] 0] fun h ↦ h ^ s) (hK : K =O[𝓝[>] 0] fun h ↦ h ^ (-b))
    (hδ0 : ∀ᶠ h in 𝓝[>] 0, 0 < δ h) (hab : a + b < s) (hqlb : q + l + b < s) :
    ∀ᶠ h in 𝓝[>] 0, K h * ε h ≤ δ h ∧ C h * L h * (K h * ε h) < 1 := by
  have hKε := hK.mul_nhdsGT_zero_rpow_of_isBigO_rpow hε le_rfl
  have h₁ := eventually_lt_of_isBigO_rpow (sub_pos.2 hab)
    (hKε.mul_nhdsGT_zero_rpow_of_isBigO_rpow hδ (by linarith)) one_pos
  have h₂ := eventually_lt_of_isBigO_rpow (sub_pos.2 hqlb) ((hC.mul_nhdsGT_zero_rpow_of_isBigO_rpow
    hL le_rfl).mul_nhdsGT_zero_rpow_of_isBigO_rpow hKε (by linarith)) one_pos
  filter_upwards [h₁, h₂, hδ0] with h h₁ h₂ hδ0
  simp only [Pi.mul_apply] at h₁ h₂
  rw [mul_inv_lt_iff₀ hδ0, one_mul] at h₁
  exact ⟨h₁.le, h₂⟩

/-! ### The corrections for all small `h` -/

variable {P : Type*} [TopologicalSpace P] {E : ℝ → Type*} {F G : ℝ → P → Type*}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, CompleteSpace (E h)]
  [∀ h p, SeminormedAddCommGroup (F h p)] [∀ h p, FunLike (G h p) (F h p) (E h)]
  [∀ h p, AddMonoidHomClass (G h p) (F h p) (E h)]
  {Q : ∀ h p, G h p} {D N : ∀ h p, E h → F h p} {e : ∀ h p, F h p}
  {C L : ℝ → ℝ≥0} {δ ε : ℝ → ℝ} {q l a s : ℝ}

/-- **The quadratic correction for all small `h`.** Let `e_h(p) + D_h(p) x + N_h(p) x = 0` be
equations in a complete space `E_h`, indexed by a scale `h > 0` and a parameter `p`, with additive
right inverses `Q_h(p)` of `D_h(p)` of norm at most `C_h`, and remainders `N_h(p)` vanishing at
the origin and quadratic with constant `L_h` on the ball of radius `δ_h > 0`; all constants are
uniform in `p`, and the target of `D_h(p)` may depend on `p`. Suppose that the residuals are
bounded by `ε_h`, uniformly in `p`, and that `p ↦ Q_h(p) (e_h(p) + N_h(p) z)` is continuous for
each `z` of norm at most `δ_h`. If, as `h → 0⁺`,

`C_h = O(h^(-q))`,  `L_h = O(h^(-l))`,  `δ_h⁻¹ = O(h^(-a))`,  `ε_h = O(h^s)`

with `2 q + l < s` and `q + a < s`, then for all small `h` there is a continuous family of
solutions `x_h(p)` in the range of `Q_h(p)`, with `‖x_h(p)‖ ≤ 2 C_h ‖e_h(p)‖`, and every solution
`y` in the range of `Q_h(p)` with `‖y‖ ≤ δ_h` and `C_h L_h ‖y‖ < 1` equals `x_h(p)`. All hypotheses
need only hold for small `h`. -/
theorem eventually_exists_continuous_forall_add_add_eq_zero
    (hDQ : ∀ᶠ h in 𝓝[>] 0, ∀ p y, D h p (Q h p y) = y)
    (hQ : ∀ᶠ h in 𝓝[>] 0, ∀ p y, ‖Q h p y‖ ≤ C h * ‖y‖)
    (hN : ∀ᶠ h in 𝓝[>] 0, ∀ p, ∀ x ∈ closedBall (0 : E h) (δ h),
      ∀ y ∈ closedBall (0 : E h) (δ h), ‖N h p x - N h p y‖ ≤ L h / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
    (hN0 : ∀ᶠ h in 𝓝[>] 0, ∀ p, N h p 0 = 0) (he : ∀ᶠ h in 𝓝[>] 0, ∀ p, ‖e h p‖ ≤ ε h)
    (hT : ∀ᶠ h in 𝓝[>] 0, ∀ z ∈ closedBall (0 : E h) (δ h),
      Continuous fun p ↦ Q h p (e h p + N h p z))
    (hδ0 : ∀ᶠ h in 𝓝[>] 0, 0 < δ h)
    (hC : (fun h ↦ (C h : ℝ)) =O[𝓝[>] 0] fun h ↦ h ^ (-q))
    (hL : (fun h ↦ (L h : ℝ)) =O[𝓝[>] 0] fun h ↦ h ^ (-l))
    (hδ : (fun h ↦ (δ h)⁻¹) =O[𝓝[>] 0] fun h ↦ h ^ (-a))
    (hε : ε =O[𝓝[>] 0] fun h ↦ h ^ s) (hql : 2 * q + l < s) (hqa : q + a < s) :
    ∀ᶠ h in 𝓝[>] 0, ∃ x : P → E h, Continuous x ∧ ∀ p, x p ∈ range (Q h p) ∧
      ‖x p‖ ≤ 2 * C h * ‖e h p‖ ∧ e h p + D h p (x p) + N h p (x p) = 0 ∧
      ∀ y ∈ range (Q h p), e h p + D h p y + N h p y = 0 → ‖y‖ ≤ δ h →
        C h * L h * ‖y‖ < 1 → y = x p := by
  filter_upwards [hDQ, hQ, hN, hN0, he, hT,
    eventually_contraction_budget hC hL hδ hε hδ0 hql hqa] with h hDQ hQ hN hN0 he hT hbud
  obtain ⟨hεδ, hεL⟩ := hbud
  have hC0 : (0 : ℝ) ≤ C h := (C h).property
  have hL0 : (0 : ℝ) ≤ L h := (L h).property
  -- The radius `r = 2 C ε` is below `δ`, and `C L r = 2 C² L ε < 1`.
  have hr : (C h : ℝ) * L h * (2 * C h * ε h) < 1 := by nlinarith
  have hre (p : P) : 2 * C h * ‖e h p‖ ≤ 2 * C h * ε h := by gcongr; exact he p
  obtain ⟨x, hx, hxsol⟩ := exists_continuous_forall_add_add_eq_zero (P := P) (F := F h)
    hDQ hQ hN hN0 hεδ hr hre fun z hz ↦ hT z (closedBall_subset_closedBall hεδ hz)
  refine ⟨x, hx, fun p ↦ ⟨(hxsol p).1, (hxsol p).2.1, (hxsol p).2.2, ?_⟩⟩
  intro y hyQ hye hyδ hyL
  -- Both solutions have norm at most `max ‖y‖ (2 C ε)`, a radius where uniqueness holds.
  have hxr : ‖x p‖ ≤ 2 * C h * ε h := (hxsol p).2.1.trans (hre p)
  refine eq_of_add_add_eq_zero (hDQ p) (hQ p) (hN p) (max_le hyδ hεδ) ?_ (le_max_left _ _)
    (hxr.trans (le_max_right _ _)) hyQ hye (hxsol p).1 (hxsol p).2.2
  rw [mul_max_of_nonneg _ _ (mul_nonneg hC0 hL0)]
  exact max_lt hyL hr

/-- **Recovery of all solutions for small `h`.** In the situation of
`TauCeti.eventually_exists_continuous_forall_add_add_eq_zero`, let `K_h = O(h^(-b))` be a
recovery constant, and assume in addition `a + b < s` and `q + l + b < s`. Then for all small `h`
the continuous family of solutions `x_h(p)` in the range of `Q_h(p)`, with
`‖x_h(p)‖ ≤ 2 C_h ‖e_h(p)‖`, also contains every solution `y` in the range of `Q_h(p)` with
`‖y‖ ≤ K_h ε_h`. Thus once an a priori estimate places each actual solution within `K_h ε_h` of
the approximate solution, a single threshold for `h` gives both the construction and the
identification of all solutions. -/
theorem eventually_exists_continuous_forall_add_add_eq_zero_of_norm_le_mul {K : ℝ → ℝ} {b : ℝ}
    (hDQ : ∀ᶠ h in 𝓝[>] 0, ∀ p y, D h p (Q h p y) = y)
    (hQ : ∀ᶠ h in 𝓝[>] 0, ∀ p y, ‖Q h p y‖ ≤ C h * ‖y‖)
    (hN : ∀ᶠ h in 𝓝[>] 0, ∀ p, ∀ x ∈ closedBall (0 : E h) (δ h),
      ∀ y ∈ closedBall (0 : E h) (δ h), ‖N h p x - N h p y‖ ≤ L h / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
    (hN0 : ∀ᶠ h in 𝓝[>] 0, ∀ p, N h p 0 = 0) (he : ∀ᶠ h in 𝓝[>] 0, ∀ p, ‖e h p‖ ≤ ε h)
    (hT : ∀ᶠ h in 𝓝[>] 0, ∀ z ∈ closedBall (0 : E h) (δ h),
      Continuous fun p ↦ Q h p (e h p + N h p z))
    (hδ0 : ∀ᶠ h in 𝓝[>] 0, 0 < δ h)
    (hC : (fun h ↦ (C h : ℝ)) =O[𝓝[>] 0] fun h ↦ h ^ (-q))
    (hL : (fun h ↦ (L h : ℝ)) =O[𝓝[>] 0] fun h ↦ h ^ (-l))
    (hδ : (fun h ↦ (δ h)⁻¹) =O[𝓝[>] 0] fun h ↦ h ^ (-a))
    (hε : ε =O[𝓝[>] 0] fun h ↦ h ^ s) (hK : K =O[𝓝[>] 0] fun h ↦ h ^ (-b))
    (hql : 2 * q + l < s) (hqa : q + a < s) (hab : a + b < s) (hqlb : q + l + b < s) :
    ∀ᶠ h in 𝓝[>] 0, ∃ x : P → E h, Continuous x ∧ ∀ p, x p ∈ range (Q h p) ∧
      ‖x p‖ ≤ 2 * C h * ‖e h p‖ ∧ e h p + D h p (x p) + N h p (x p) = 0 ∧
      ∀ y ∈ range (Q h p), e h p + D h p y + N h p y = 0 → ‖y‖ ≤ K h * ε h → y = x p := by
  filter_upwards [eventually_exists_continuous_forall_add_add_eq_zero hDQ hQ hN hN0 he hT hδ0 hC
    hL hδ hε hql hqa, eventually_recovery_budget hC hL hδ hε hK hδ0 hab hqlb]
    with h ⟨x, hx, hxsol⟩ ⟨hKδ, hKL⟩
  refine ⟨x, hx, fun p ↦ ⟨(hxsol p).1, (hxsol p).2.1, (hxsol p).2.2.1, ?_⟩⟩
  intro y hyQ hye hyK
  have hCL : (0 : ℝ) ≤ C h * L h := mul_nonneg (C h).property (L h).property
  exact (hxsol p).2.2.2 y hyQ hye (hyK.trans hKδ)
    ((mul_le_mul_of_nonneg_left hyK hCL).trans_lt hKL)

end TauCeti

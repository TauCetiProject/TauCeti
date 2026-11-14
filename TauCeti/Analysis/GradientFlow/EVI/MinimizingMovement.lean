/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.Analysis.GradientFlow.EVI.Semigroup
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.GradientFlow.EVI.Stability
import TauCeti.Analysis.GradientFlow.MinimizingMovement
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall

/-!
# Convergence of minimizing movements to `EVI_λ` gradient flows

Let `φ : X → EReal` be lower semicontinuous on a complete metric space, coercive
(`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0`, `x₁`), and `PenalizedConvex lam τ φ` for small `τ > 0`
(Ambrosio–Gigli–Savaré, Assumption 4.0.1). From every `x₀` with `φ x₀ ≠ ⊤`, minimizing movements
exist (`TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`) and
`t ↦ J ⌈t / τ⌉₊` converges uniformly on `[0, T]` as `τ → 0` to the unique `EVI_λ`
solution (`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`).

By `λ`-contraction and stability of `EVI_λ` solutions, existence extends to every point `x₀` in
`closure {x | φ x ≠ ⊤}` (`TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex`),
giving `TauCeti.eviDomain lam φ = closure {x | φ x ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_penalizedConvex`). On a complete CAT(0) space, `λ`-geodesically
convex lower semicontinuous energies satisfy both hypotheses automatically.

## Main results

* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`: existence of the `EVI_λ`
  solution and uniform convergence on compact time intervals of all minimizing movement interpolants
  as `τ → 0` (Ambrosio–Gigli–Savaré, Theorem 4.1.2).
* `TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex` and
  `TauCeti.eviDomain_eq_closure_of_penalizedConvex`: existence on `closure {x | φ x ≠ ⊤}` and
  `TauCeti.eviDomain lam φ = closure {x | φ x ≠ ⊤}`
  (Ambrosio–Gigli–Savaré, Theorem 4.0.4).
* `TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn`,
  `TauCeti.GeodesicallyConvex.exists_isEVISolution_of_mem_closure`, and
  `TauCeti.GeodesicallyConvex.eviDomain_eq_closure`: CAT(0) corollaries.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 4, Theorems 4.0.4 and 4.1.2.
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, in *Modelling and Optimisation of
  Flows on Networks*, Lecture Notes in Math. 2062, Springer 2013, Theorem 3.25.
-/

public section

noncomputable section

open Filter Finset Set Topology Real
open scoped NNReal ENNReal

namespace TauCeti

section Helpers

/-- Discrete-to-continuous exponential limit: if `τ j → 0⁺` and `N j * τ j → d`, then
`(1 + m * τ j) ^ N j → exp (m * d)`. -/
private theorem tendsto_one_add_mul_pow {m d : ℝ} {τ : ℕ → ℝ≥0} {N : ℕ → ℕ}
    (hτ0 : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0))
    (hτ_pos : ∀ᶠ j in atTop, 0 < τ j)
    (hN : Tendsto (fun j ↦ (N j : ℝ) * τ j) atTop (𝓝 d)) :
    Tendsto (fun j ↦ (1 + m * (τ j : ℝ)) ^ N j) atTop (𝓝 (Real.exp (m * d))) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have h1 : ∀ᶠ j in atTop, 0 < 1 + m * (τ j : ℝ) := by
    have htend : Tendsto (fun j ↦ 1 + m * (τ j : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add (hτ0.const_mul m))
    exact htend.eventually (lt_mem_nhds one_pos)
  have hslope :
      Tendsto (fun j ↦ slope (fun x : ℝ ↦ Real.log (1 + x)) 0 (m * τ j)) atTop (𝓝 1) := by
    have hd : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x)) 1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)
    have hmτ : Tendsto (fun j ↦ m * (τ j : ℝ)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by simpa using hτ0.const_mul m,
        hτ_pos.mono fun j hj ↦ mul_ne_zero hm (NNReal.coe_pos.2 hj).ne'⟩
    exact ((hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ ({0}ᶜ : Set ℝ))).1
      hd.hasDerivWithinAt).comp hmτ
  have hexp_arg :
      Tendsto (fun j ↦ (N j : ℝ) * Real.log (1 + m * τ j)) atTop (𝓝 (m * d)) := by
    have hprod : Tendsto (fun j ↦ ((N j : ℝ) * τ j * m) *
        slope (fun x : ℝ ↦ Real.log (1 + x)) 0 (m * τ j)) atTop (𝓝 (d * m * 1)) :=
      (hN.mul_const m).mul hslope
    rw [show d * m * 1 = m * d by ring] at hprod
    refine hprod.congr' (hτ_pos.mono fun j hj ↦ ?_)
    have : m * (τ j : ℝ) ≠ 0 := mul_ne_zero hm (NNReal.coe_pos.2 hj).ne'
    simp only [slope_def_field, sub_zero, add_zero, Real.log_one]; field_simp
  refine (Real.continuous_exp.tendsto _ |>.comp hexp_arg).congr' (h1.mono fun j hj ↦ ?_)
  simp only [Function.comp_apply]; rw [Real.exp_nat_mul, Real.exp_log hj]

/-- Discrete-to-continuous integral exponential limit: if `τ j → 0⁺` and `N j * τ j → d`,
then `τ j * ∑ n < N j, (1 + m * τ j) ^ n → ∫ r in 0..d, exp (m * r)`. -/
private theorem tendsto_coe_mul_sum_one_add_mul_pow {m d : ℝ} {τ : ℕ → ℝ≥0}
    {N : ℕ → ℕ} (hτ0 : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0))
    (hτ_pos : ∀ᶠ j in atTop, 0 < τ j)
    (hN : Tendsto (fun j ↦ (N j : ℝ) * τ j) atTop (𝓝 d)) :
    Tendsto (fun j ↦ (τ j : ℝ) * ∑ n ∈ range (N j), (1 + m * (τ j : ℝ)) ^ n) atTop
      (𝓝 (∫ r in (0 : ℝ)..d, Real.exp (m * r))) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa [mul_comm] using hN
  have hint : (∫ r in (0 : ℝ)..d, Real.exp (m * r)) = (Real.exp (m * d) - 1) / m := by
    rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) hm, mul_zero, integral_exp,
      Real.exp_zero, smul_eq_mul, div_eq_inv_mul]
  rw [hint]
  refine (((tendsto_one_add_mul_pow (m := m) (d := d) hτ0 hτ_pos hN).sub_const 1).div_const
    m).congr' (Eventually.of_forall fun j ↦ ?_)
  have hgeom := geom_sum_mul (1 + m * (τ j : ℝ)) (N j)
  rw [show 1 + m * (τ j : ℝ) - 1 = m * τ j by ring] at hgeom
  have hmul : m * ((τ j : ℝ) * ∑ n ∈ range (N j), (1 + m * (τ j : ℝ)) ^ n) =
      (1 + m * (τ j : ℝ)) ^ N j - 1 := by
    rw [show m * ((τ j : ℝ) * ∑ n ∈ range (N j), (1 + m * (τ j : ℝ)) ^ n) =
      (∑ n ∈ range (N j), (1 + m * (τ j : ℝ)) ^ n) * (m * τ j) by ring, hgeom]
  rw [div_eq_iff hm, mul_comm _ m]; exact hmul.symm

/-- Along any metric space with `moreauYosida φ τ₀ x₁ ≠ ⊥`, `φ` avoids `⊥`. -/
private theorem apply_ne_bot_of_moreauYosida_ne_bot {X : Type*} [PseudoMetricSpace X]
    {φ : X → EReal} {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (z : X) : φ z ≠ ⊥ := by
  intro hz
  have hle := moreauYosida_le φ τ₀ (edist_ne_top x₁ z)
  rw [hz, coe_edist_sq_div_eq_coe_dist_sq_div hτ₀, EReal.bot_add, le_bot_iff] at hle
  exact h₀ hle

end Helpers

section DiscreteComparison

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {φ : X → EReal}

private def barrierC (m T : ℝ) (τ' : ℝ≥0) : ℝ := (2 * |m| * (T + τ') + 5 / 4) / (3 / 2)

private def gridBarrier (τ σ : ℝ≥0) (C : ℝ) (i j : ℕ) : ℝ :=
  ((i : ℝ) * τ - (j : ℝ) * σ) ^ 2 + C * (τ + σ) * ((i : ℝ) * τ + (j : ℝ) * σ)

private def cauchyL (T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  A - (E - A) * Real.exp (8 * (T + τ') / τ')

private def cauchyM (m T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  2 * (E - cauchyL T τ' A E) * Real.exp (|m| * (T + τ'))

private def cauchyK (m T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  Real.exp (4 * |m| * (T + τ')) * cauchyM m T τ' A E *
    Real.sqrt (2 * τ' + 2 * barrierC m T τ' * (T + τ'))

/-- **Discrete comparison step** between two minimizing movement sequences `U` (step `τ`) and `V`
(step `σ`): cross-testing eliminates the energies and yields
`((1 + m τ) σ + (1 + m σ) τ) d(U (n + 1), V (k + 1))² ≤
  σ d(U n, V (k + 1))² + τ d(U (n + 1), V k)²`. -/
private theorem discrete_comparison_step {τ σ : ℝ≥0}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    (hUtop : ∀ n, φ (U n) ≠ ⊤) (hUbot : ∀ n, φ (U n) ≠ ⊥)
    (hVtop : ∀ k, φ (V k) ≠ ⊤) (hVbot : ∀ k, φ (V k) ≠ ⊥) (n k : ℕ) :
    ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ)) * dist (U (n + 1)) (V (k + 1)) ^ 2 ≤
      σ * dist (U n) (V (k + 1)) ^ 2 + τ * dist (U (n + 1)) (V k) ^ 2 := by
  have h1 := hPenτ.apply_add_le_of_mem_moreauYosidaResolvent hτ (hU n) (hVtop (k + 1))
  have h2 := hPenσ.apply_add_le_of_mem_moreauYosidaResolvent hσ (hV k) (hUtop (n + 1))
  have ha : φ (U (n + 1)) = (φ (U (n + 1))).toReal :=
    (EReal.coe_toReal (hUtop (n + 1)) (hUbot (n + 1))).symm
  have hb : φ (V (k + 1)) = (φ (V (k + 1))).toReal :=
    (EReal.coe_toReal (hVtop (k + 1)) (hVbot (k + 1))).symm
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
  have h1m := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * (τ : ℝ) * σ)
  have h2m := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * (τ : ℝ) * σ)
  field_simp at h1m h2m
  rw [dist_comm (V (k + 1)) (U (n + 1)), dist_comm (V k) (U (n + 1))] at h2m
  nlinarith [NNReal.coe_nonneg σ, NNReal.coe_nonneg τ,
    mul_nonneg (NNReal.coe_nonneg σ) (sq_nonneg (dist (U n) (U (n + 1)))),
    mul_nonneg (NNReal.coe_nonneg τ) (sq_nonneg (dist (V k) (V (k + 1))))]

/-- Weighted comparison inequality: setting `a n k = (1 + m τ) ^ n (1 + m σ) ^ k d(U n, V k)²`
with weights `p + q = 1`, we have `a (n + 1) (k + 1) ≤ p * a n (k + 1) + q * a (n + 1) k`. -/
private theorem weighted_comparison_step {τ σ : ℝ≥0}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hmτ : 0 < 1 + m * τ) (hmσ : 0 < 1 + m * σ)
    {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    (hUtop : ∀ n, φ (U n) ≠ ⊤) (hUbot : ∀ n, φ (U n) ≠ ⊥)
    (hVtop : ∀ k, φ (V k) ≠ ⊤) (hVbot : ∀ k, φ (V k) ≠ ⊥) (n k : ℕ) :
    (1 + m * τ) ^ (n + 1) * (1 + m * σ) ^ (k + 1) * dist (U (n + 1)) (V (k + 1)) ^ 2 ≤
      ((σ : ℝ) * (1 + m * τ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        ((1 + m * τ) ^ n * (1 + m * σ) ^ (k + 1) * dist (U n) (V (k + 1)) ^ 2) +
      ((τ : ℝ) * (1 + m * σ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        ((1 + m * τ) ^ (n + 1) * (1 + m * σ) ^ k * dist (U (n + 1)) (V k) ^ 2) := by
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  set γ : ℝ := (σ : ℝ) * r₁ + τ * r₂
  have hstep := discrete_comparison_step hPenτ hPenσ hτ hσ hU hV hUtop hUbot hVtop hVbot n k
  have hγ : 0 < γ :=
    add_pos (mul_pos (NNReal.coe_pos.2 hσ) hmτ) (mul_pos (NNReal.coe_pos.2 hτ) hmσ)
  have hmul := mul_le_mul_of_nonneg_left hstep
    (mul_nonneg (pow_nonneg hmτ.le (n + 1)) (pow_nonneg hmσ.le (k + 1)))
  rw [← div_le_div_iff_of_pos_right hγ] at hmul
  change r₁ ^ (n + 1) * r₂ ^ (k + 1) * (γ * dist (U (n + 1)) (V (k + 1)) ^ 2) / γ ≤
    r₁ ^ (n + 1) * r₂ ^ (k + 1) *
      ((σ : ℝ) * dist (U n) (V (k + 1)) ^ 2 + τ * dist (U (n + 1)) (V k) ^ 2) / γ at hmul
  change r₁ ^ (n + 1) * r₂ ^ (k + 1) * dist (U (n + 1)) (V (k + 1)) ^ 2 ≤
    ((σ : ℝ) * r₁ / γ) * (r₁ ^ n * r₂ ^ (k + 1) * dist (U n) (V (k + 1)) ^ 2) +
    ((τ : ℝ) * r₂ / γ) * (r₁ ^ (n + 1) * r₂ ^ k * dist (U (n + 1)) (V k) ^ 2)
  refine le_trans (le_of_eq ?_) (hmul.trans_eq ?_)
  · field_simp [hγ.ne']
  · rw [pow_succ r₁ n, pow_succ r₂ k]; field_simp [hγ.ne']

/-- The discrete heat-equation barrier `gridBarrier` is a supersolution of the `(p, q)` random walk
on the grid `n τ ≤ T + τ'`, `k σ ≤ T + τ'`. -/
private theorem barrier_superharmonic {τ σ τ' : ℝ≥0} {T : ℝ}
    (hmτ : |m| * τ ≤ 1 / 4) (hmσ : |m| * σ ≤ 1 / 4) {n k : ℕ}
    (hn : ((n + 1 : ℕ) : ℝ) * τ ≤ T + τ') (hk : ((k + 1 : ℕ) : ℝ) * σ ≤ T + τ') :
    ((σ : ℝ) * (1 + m * τ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        gridBarrier τ σ (barrierC m T τ') n (k + 1) +
      ((τ : ℝ) * (1 + m * σ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        gridBarrier τ σ (barrierC m T τ') (n + 1) k ≤
      gridBarrier τ σ (barrierC m T τ') (n + 1) (k + 1) := by
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  set γ : ℝ := (σ : ℝ) * r₁ + τ * r₂
  set C : ℝ := barrierC m T τ'
  have hτ0 : (0 : ℝ) ≤ τ := τ.2
  have hσ0 : (0 : ℝ) ≤ σ := σ.2
  have h1 : |m * (τ : ℝ)| = |m| * τ := by rw [abs_mul, abs_of_nonneg hτ0]
  have h2 : |m * (σ : ℝ)| = |m| * σ := by rw [abs_mul, abs_of_nonneg hσ0]
  have hr₁_lo : 3 / 4 ≤ r₁ := by linarith [neg_abs_le (m * (τ : ℝ))]
  have hr₁_hi : r₁ ≤ 5 / 4 := by linarith [(le_abs_self (m * (τ : ℝ))).trans_eq h1]
  have hr₂_lo : 3 / 4 ≤ r₂ := by linarith [neg_abs_le (m * (σ : ℝ))]
  have hr₂_hi : r₂ ≤ 5 / 4 := by linarith [(le_abs_self (m * (σ : ℝ))).trans_eq h2]
  have hTτ' : 0 ≤ T + τ' := le_trans (mul_nonneg (Nat.cast_nonneg _) hτ0) hn
  set x : ℝ := ((n + 1 : ℕ) : ℝ) * τ - ((k + 1 : ℕ) : ℝ) * σ
  have hx : |x| ≤ T + τ' := abs_le.2 ⟨by linarith [mul_nonneg (Nat.cast_nonneg (n + 1)) hτ0],
    by linarith [mul_nonneg (Nat.cast_nonneg (k + 1)) hσ0]⟩
  have hστ : |((σ : ℝ) - τ)| ≤ τ + σ :=
    (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hσ0, abs_of_nonneg hτ0]; ring)
  have hcross : 2 * x * m * ((σ : ℝ) - τ) ≤ 2 * |m| * (T + τ') * (τ + σ) := by
    calc 2 * x * m * ((σ : ℝ) - τ) ≤ |2 * x * m * ((σ : ℝ) - τ)| := le_abs_self _
      _ = 2 * |x| * |m| * |((σ : ℝ) - τ)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg two_pos.le]
      _ ≤ 2 * (T + τ') * |m| * (τ + σ) := by gcongr
      _ = 2 * |m| * (T + τ') * (τ + σ) := by ring
  have hconst : r₁ * τ + r₂ * σ ≤ 5 / 4 * (τ + σ) := by nlinarith
  have hC : (2 * |m| * (T + τ') + 5 / 4) * (τ + σ) ≤ C * (τ + σ) * (r₁ + r₂) := by
    have hC0 : 0 ≤ C * (τ + σ) := by unfold C barrierC; positivity
    calc (2 * |m| * (T + τ') + 5 / 4) * (τ + σ)
        = C * (τ + σ) * (3 / 2) := by unfold C barrierC; field_simp
      _ ≤ C * (τ + σ) * (r₁ + r₂) := by gcongr; linarith
  set rhs : ℝ :=
    2 * x * m * ((σ : ℝ) - τ) + r₁ * τ + r₂ * σ - C * (τ + σ) * (r₁ + r₂)
  have hmain : rhs ≤ 0 := by dsimp [rhs]; linarith
  change ((σ : ℝ) * r₁ / γ) * gridBarrier τ σ C n (k + 1) +
    ((τ : ℝ) * r₂ / γ) * gridBarrier τ σ C (n + 1) k ≤ gridBarrier τ σ C (n + 1) (k + 1)
  rcases eq_or_lt_of_le (show 0 ≤ γ by positivity) with hγ0 | hγpos
  · have hστ0 : (τ : ℝ) = 0 ∧ (σ : ℝ) = 0 := by
      have : 0 ≤ (σ : ℝ) * r₁ := mul_nonneg hσ0 (by linarith)
      have : 0 ≤ (τ : ℝ) * r₂ := mul_nonneg hτ0 (by linarith)
      exact ⟨by nlinarith, by nlinarith⟩
    unfold gridBarrier; rw [hστ0.1, hστ0.2]; norm_num
  have hid : γ * (((σ : ℝ) * r₁ / γ) * gridBarrier τ σ C n (k + 1) +
      ((τ : ℝ) * r₂ / γ) * gridBarrier τ σ C (n + 1) k -
      gridBarrier τ σ C (n + 1) (k + 1)) = (τ : ℝ) * σ * rhs := by
    unfold gridBarrier
    field_simp [hγpos.ne']
    dsimp [rhs, γ, r₁, r₂, x]
    push_cast
    ring
  have hneg : γ * (((σ : ℝ) * r₁ / γ) * gridBarrier τ σ C n (k + 1) +
      ((τ : ℝ) * r₂ / γ) * gridBarrier τ σ C (n + 1) k -
      gridBarrier τ σ C (n + 1) (k + 1)) ≤ 0 :=
    hid ▸ mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hτ0 hσ0) hmain
  nlinarith

/-- Square-root concavity for convex combinations: if `p, q ≥ 0`, `p + q = 1`, `A, B ≥ 0`,
and `p * A + q * B ≤ D`, then `p * √A + q * √B ≤ √D`. -/
private theorem convex_comb_sqrt_le {p q A B D : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q = 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : p * A + q * B ≤ D) :
    p * Real.sqrt A + q * Real.sqrt B ≤ Real.sqrt D := by
  refine Real.le_sqrt_of_sq_le ?_
  have hid : (p * Real.sqrt A + q * Real.sqrt B) ^ 2 =
      p * A + q * B - p * q * (Real.sqrt A - Real.sqrt B) ^ 2 := by
    have hp' : p ^ 2 = p - p * q := by nlinarith
    have hq' : q ^ 2 = q - p * q := by nlinarith
    rw [add_sq, sub_sq, mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB, hp', hq']
    ring
  rw [hid]
  nlinarith [mul_nonneg (mul_nonneg hp hq) (sq_nonneg (Real.sqrt A - Real.sqrt B))]

/-- Boundary estimate at `k = 0`: for `n ≤ ⌈T / τ⌉₊`,
`(1 + m τ) ^ n * d(U n, x₀)² ≤ M * √(gridBarrier τ σ C n 0)`. -/
private theorem boundary_comparison_left {τ σ τ' : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hτ : 0 < τ) (hττ' : 4 * τ ≤ τ') (hmτ : |m| * τ ≤ 1 / 4)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) (hT : 0 ≤ T)
    {U : ℕ → X} (hU0 : U 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {n : ℕ} (hn : n ≤ ⌈T / τ⌉₊) :
    (1 + m * τ) ^ n * dist (U n) x₀ ^ 2 ≤
      cauchyM m T τ' A E * Real.sqrt (gridBarrier τ σ (barrierC m T τ') n 0) := by
  set r₁ : ℝ := 1 + m * τ
  set L : ℝ := cauchyL T τ' A E
  set M : ℝ := cauchyM m T τ' A E
  set C : ℝ := barrierC m T τ'
  have hτr : (0 : ℝ) < τ := hτ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have hτ_le_τ' : (τ : ℝ) ≤ τ' := by linarith
  have hτ'r : (0 : ℝ) < τ' := by linarith
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀
  have hL_le : L ≤ E := by
    have : 0 ≤ (E - A) * Real.exp (8 * (T + τ') / τ') := by positivity
    unfold L cauchyL; linarith
  have hM0 : 0 ≤ M := by
    unfold M cauchyM
    exact mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.2 hL_le)) (Real.exp_pos _).le
  have hr₁0 : 0 ≤ r₁ := by
    have h := neg_abs_le (m * (τ : ℝ))
    rw [abs_mul, abs_of_nonneg hτr.le] at h
    linarith
  rcases Nat.eq_or_lt_of_le (Nat.zero_le n) with rfl | hn0
  · rw [hU0, dist_self]; simpa using mul_nonneg hM0 (Real.sqrt_nonneg _)
  have hmulti := apply_add_edist_sq_div_le_of_forall_mem_moreauYosidaResolvent
    hU (m := 0) (n := n) (Nat.zero_le n)
  rw [Nat.sub_zero, hU0] at hmulti
  have hB : (1 + 8 * (τ : ℝ) / τ') ^ n ≤ Real.exp (8 * (T + τ') / τ') := by
    calc (1 + 8 * (τ : ℝ) / τ') ^ n
        ≤ (1 + 8 / τ' * τ) ^ ⌈T / τ⌉₊ := by
          rw [div_mul_eq_mul_div]
          exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hn
      _ ≤ Real.exp (8 / τ' * (T + τ)) :=
          one_add_mul_pow_ceil_div_le_exp (by positivity) (add_nonneg hT hτr.le)
      _ ≤ Real.exp (8 * (T + τ') / τ') :=
          Real.exp_le_exp.2 (by rw [div_mul_eq_mul_div]; gcongr)
  have hlow_n : (L : EReal) ≤ φ (U n) := by
    have hlo := le_apply_of_forall_mem_moreauYosidaResolvent hU hτ hττ'
      (hU0 ▸ hA) (hU0 ▸ hE) n
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hlo
    unfold L cauchyL; nlinarith [sub_nonneg.2 hAE]
  have htop_n : φ (U n) ≠ ⊤ := by
    have hle := antitone_comp_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le n)
    simp only [Function.comp_apply, hU0, hE] at hle
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  set en : ℝ := (φ (U n)).toReal
  have hen : φ (U n) = en :=
    (EReal.coe_toReal htop_n (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow_n)).symm
  have hL_en : L ≤ en := by exact_mod_cast hen ▸ hlow_n
  have hPne : edist x₀ (U n) ^ 2 / (2 * (n * τ)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (edist_ne_top _ _))
      (mul_ne_zero two_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 hn0.ne')
        (ENNReal.coe_ne_zero.2 hτ.ne')))
  rw [hen, hE, ← EReal.coe_ennreal_toReal hPne, ← EReal.coe_add, EReal.coe_le_coe_iff] at hmulti
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    at hmulti
  have hdist : dist (U n) x₀ ^ 2 ≤ 2 * (E - L) * ((n : ℝ) * τ) := by
    rw [dist_comm]
    have hdiv : dist x₀ (U n) ^ 2 / (2 * (n * τ)) ≤ E - L := by linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n * τ))] at hdiv
    linarith
  have hr₁_exp : r₁ ^ n ≤ Real.exp (|m| * (T + τ')) := by
    have hr₁_le : r₁ ≤ 1 + |m| * τ :=
      by linarith [(le_abs_self (m * (τ : ℝ))).trans_eq (by rw [abs_mul, abs_of_nonneg hτr.le])]
    calc r₁ ^ n ≤ (1 + |m| * τ) ^ n := pow_le_pow_left₀ hr₁0 hr₁_le n
      _ ≤ (1 + |m| * τ) ^ ⌈T / τ⌉₊ :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hn
      _ ≤ Real.exp (|m| * (T + τ)) :=
          one_add_mul_pow_ceil_div_le_exp (abs_nonneg m) (add_nonneg hT hτr.le)
      _ ≤ Real.exp (|m| * (T + τ')) := Real.exp_le_exp.2 (by gcongr)
  have hnτ_sqrt : (n : ℝ) * τ ≤ Real.sqrt (gridBarrier τ σ C n 0) := by
    refine Real.le_sqrt_of_sq_le ?_
    have hC0 : 0 ≤ C := by
      unfold C barrierC
      exact div_nonneg (add_nonneg (mul_nonneg (mul_nonneg two_pos.le (abs_nonneg m))
        (by linarith)) (by norm_num)) (by norm_num)
    have : 0 ≤ C * ((τ : ℝ) + σ) * ((n : ℝ) * τ + 0) :=
      mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity)
    unfold gridBarrier; simp only [Nat.cast_zero, zero_mul, sub_zero, add_zero]; linarith
  calc r₁ ^ n * dist (U n) x₀ ^ 2
      ≤ Real.exp (|m| * (T + τ')) * (2 * (E - L) * ((n : ℝ) * τ)) :=
        mul_le_mul hr₁_exp hdist (sq_nonneg _) (by positivity)
    _ = M * ((n : ℝ) * τ) := by unfold M cauchyM L; ring
    _ ≤ M * Real.sqrt (gridBarrier τ σ C n 0) := mul_le_mul_of_nonneg_left hnτ_sqrt hM0

/-- **Uniform Cauchy comparison between minimizing movement interpolants**
(Ambrosio–Gigli–Savaré, Theorem 4.1.2). For minimizing movement sequences `U`, `V`
started at `x₀` with `φ x₀ = E` and `φ_{τ'}(x₀) = A`, when `4 τ ≤ τ'`, `4 σ ≤ τ'`,
`|m| τ ≤ 1 / 4`, `|m| σ ≤ 1 / 4`, and `t ∈ [0, T]`, we have
`dist (U ⌈t / τ⌉₊) (V ⌈t / σ⌉₊) ^ 2 ≤ cauchyK m T τ' A E * √(τ + σ)`. -/
private theorem dist_ceil_sq_le_of_penalizedConvex {τ σ τ' : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hmτ : |m| * τ ≤ 1 / 4) (hmσ : |m| * σ ≤ 1 / 4)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) (hT : 0 ≤ T)
    {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    dist (U ⌈t / τ⌉₊) (V ⌈t / σ⌉₊) ^ 2 ≤
      cauchyK m T τ' A E * Real.sqrt (τ + σ) := by
  set M : ℝ := cauchyM m T τ' A E
  set C : ℝ := barrierC m T τ'
  set Φ : ℕ → ℕ → ℝ := gridBarrier τ σ C
  have hτr : (0 : ℝ) < τ := hτ
  have hσr : (0 : ℝ) < σ := hσ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  have hτ' : 0 < τ' := lt_of_lt_of_le (by positivity) hττ'
  have hτ_le_τ' : (τ : ℝ) ≤ τ' := by linarith
  have hσ_le_τ' : (σ : ℝ) ≤ τ' := by linarith
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  have hr₁_lo : 3 / 4 ≤ r₁ := by
    linarith [neg_abs_le (m * (τ : ℝ)), show |m * (τ : ℝ)| = |m| * τ by
      rw [abs_mul, abs_of_nonneg hτr.le]]
  have hr₂_lo : 3 / 4 ≤ r₂ := by
    linarith [neg_abs_le (m * (σ : ℝ)), show |m * (σ : ℝ)| = |m| * σ by
      rw [abs_mul, abs_of_nonneg hσr.le]]
  have hr₁_pos : 0 < r₁ := by linarith
  have hr₂_pos : 0 < r₂ := by linarith
  have hfin_seq : ∀ {δ : ℝ≥0} {W : ℕ → X}, W 0 = x₀ →
      (∀ n, W (n + 1) ∈ moreauYosidaResolvent φ δ (W n)) →
      (∀ n, φ (W n) ≠ ⊤) ∧ (∀ n, φ (W n) ≠ ⊥) := fun {δ W} hW0 hW ↦ by
    have hfin_n : ∀ n, ∃ e : ℝ, φ (W n) = e := fun n ↦ by
      have hev := antitone_comp_of_forall_mem_moreauYosidaResolvent hW (Nat.zero_le n)
      simp only [Function.comp_apply, hW0, hE] at hev
      have htop : φ (W n) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top E) hev
      have hm_le : moreauYosida φ τ' x₀ ≤
          φ (W n) + ((dist x₀ (W n) ^ 2 / (2 * τ') : ℝ) : EReal) := by
        rw [← coe_edist_sq_div_eq_coe_dist_sq_div hτ']
        exact moreauYosida_le φ τ' (edist_ne_top _ _)
      have hbot : φ (W n) ≠ ⊥ := fun hbn ↦ by
        rw [hbn, EReal.bot_add, hA, le_bot_iff] at hm_le; exact EReal.coe_ne_bot A hm_le
      exact ⟨(φ (W n)).toReal, (EReal.coe_toReal htop hbot).symm⟩
    exact ⟨fun n ↦ (hfin_n n).choose_spec ▸ EReal.coe_ne_top _,
      fun n ↦ (hfin_n n).choose_spec ▸ EReal.coe_ne_bot _⟩
  obtain ⟨hUtop, hUbot⟩ := hfin_seq hU0 hU
  obtain ⟨hVtop, hVbot⟩ := hfin_seq hV0 hV
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀
  have hM0 : 0 ≤ M := by
    have : cauchyL T τ' A E ≤ E := by
      have : 0 ≤ (E - A) * Real.exp (8 * (T + τ') / τ') := by positivity
      unfold cauchyL; linarith
    unfold M cauchyM
    exact mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.2 this)) (Real.exp_pos _).le
  have hC0 : 0 ≤ C := by unfold C barrierC; positivity
  have hΦ0 : ∀ i j : ℕ, 0 ≤ Φ i j := fun i j ↦ by
    unfold Φ gridBarrier
    exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity))
  have hgrid : ∀ n ≤ ⌈T / τ⌉₊, ∀ k ≤ ⌈T / σ⌉₊,
      r₁ ^ n * r₂ ^ k * dist (U n) (V k) ^ 2 ≤ M * Real.sqrt (Φ n k) := by
    intro n; induction n with
    | zero =>
      intro _ k hk
      have hs := boundary_comparison_left (φ := φ) (x₀ := x₀) (m := m) (τ := σ) (σ := τ)
        hσ hστ' hmσ hA hE hT hV0 hV hk
      rw [hU0, pow_zero, one_mul, dist_comm]
      refine hs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hM0)
      unfold Φ gridBarrier; dsimp only [C]
      simp only [Nat.cast_zero, zero_mul, sub_zero, zero_sub, zero_add, add_zero, neg_sq,
        add_comm (σ : ℝ) τ]; rfl
    | succ n ihn =>
      intro hn k; induction k with
      | zero =>
        intro _; rw [hV0, pow_zero, mul_one]
        exact boundary_comparison_left (φ := φ) (x₀ := x₀) (m := m) (τ := τ) (σ := σ)
          hτ hττ' hmτ hA hE hT hU0 hU hn
      | succ k ihk =>
        intro hk
        have hlt_mul : ∀ {i : ℕ} {δ : ℝ≥0}, 0 < (δ : ℝ) → (δ : ℝ) ≤ τ' →
            i + 1 ≤ ⌈T / δ⌉₊ → ((i + 1 : ℕ) : ℝ) * δ ≤ T + τ' :=
          fun {i δ} hδ hδτ' hi ↦ by
          have hlt : (i : ℝ) < T / δ := by
            by_contra h
            have hceil : ⌈T / (δ : ℝ)⌉₊ ≤ i := Nat.ceil_le.2 (not_lt.1 h)
            omega
          have : (i : ℝ) * δ < T := (lt_div_iff₀ hδ).1 hlt
          push_cast; linarith
        have hn_lt := hlt_mul hτr hτ_le_τ' hn
        have hk_lt := hlt_mul hσr hσ_le_τ' hk
        set γ : ℝ := σ * r₁ + τ * r₂
        set p : ℝ := σ * r₁ / γ
        set q : ℝ := τ * r₂ / γ
        have hγ : 0 < γ := add_pos (mul_pos hσr hr₁_pos) (mul_pos hτr hr₂_pos)
        have hp0 : 0 ≤ p := div_nonneg (mul_nonneg hσr.le hr₁_pos.le) hγ.le
        have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hτr.le hr₂_pos.le) hγ.le
        have hpq : p + q = 1 := by dsimp [p, q, γ]; field_simp
        have hstep := weighted_comparison_step hPenτ hPenσ hτ hσ hr₁_pos hr₂_pos hU hV
          hUtop hUbot hVtop hVbot n k
        have h1 := ihn (Nat.le_of_succ_le hn) (k + 1) hk
        have h2 := ihk (Nat.le_of_succ_le hk)
        have hbar := barrier_superharmonic (τ := τ) (σ := σ) (τ' := τ') (T := T)
          hmτ hmσ hn_lt hk_lt
        have hsqrt := convex_comb_sqrt_le hp0 hq0 hpq (hΦ0 n (k + 1)) (hΦ0 (n + 1) k) hbar
        calc r₁ ^ (n + 1) * r₂ ^ (k + 1) * dist (U (n + 1)) (V (k + 1)) ^ 2
            ≤ p * (r₁ ^ n * r₂ ^ (k + 1) * dist (U n) (V (k + 1)) ^ 2) +
                q * (r₁ ^ (n + 1) * r₂ ^ k * dist (U (n + 1)) (V k) ^ 2) := hstep
          _ ≤ p * (M * Real.sqrt (Φ n (k + 1))) + q * (M * Real.sqrt (Φ (n + 1) k)) := by gcongr
          _ = M * (p * Real.sqrt (Φ n (k + 1)) + q * Real.sqrt (Φ (n + 1) k)) := by ring
          _ ≤ M * Real.sqrt (Φ (n + 1) (k + 1)) := by gcongr
  set n := ⌈t / τ⌉₊
  set k := ⌈t / σ⌉₊
  have hnT : n ≤ ⌈T / τ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right htT hτr.le)
  have hkT : k ≤ ⌈T / σ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right htT hσr.le)
  have hr_inv_exp : ∀ (δ : ℝ≥0) (r : ℝ) (N : ℕ), 0 < δ → (δ : ℝ) ≤ τ' →
      r = 1 + m * δ → 3 / 4 ≤ r → N ≤ ⌈T / δ⌉₊ →
      r⁻¹ ^ N ≤ Real.exp (2 * |m| * (T + τ')) := by
    intro δ r N hδ hδτ' hr hr_lo hN
    have hδr : (0 : ℝ) < δ := hδ
    have hm_bound : -m * (δ : ℝ) ≤ |m| * δ := by
      have hle : -(m * (δ : ℝ)) ≤ |-(m * (δ : ℝ))| := le_abs_self _
      rw [abs_neg, abs_mul, abs_of_nonneg hδr.le] at hle
      rwa [neg_mul]
    have hr_inv_le : r⁻¹ ≤ 1 + 2 * |m| * δ := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      have h1 : 3 / 2 * (|m| * δ) ≤ 2 * |m| * δ * r := by
        nlinarith [mul_nonneg (abs_nonneg m) hδr.le]
      rw [show (1 + 2 * |m| * δ) * r = 1 + (2 * |m| * δ * r + m * δ) by rw [hr]; ring]
      linarith [mul_nonneg (abs_nonneg m) hδr.le]
    calc r⁻¹ ^ N ≤ (1 + 2 * |m| * δ) ^ N :=
          pow_le_pow_left₀ (inv_nonneg.2 (by linarith)) hr_inv_le N
      _ ≤ (1 + 2 * |m| * δ) ^ ⌈T / δ⌉₊ :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hN
      _ ≤ Real.exp ((2 * |m|) * (T + δ)) := by
          simpa only [mul_assoc] using one_add_mul_pow_ceil_div_le_exp
            (a := 2 * |m|) (by positivity) (add_nonneg hT hδr.le)
      _ ≤ Real.exp (2 * |m| * (T + τ')) := Real.exp_le_exp.2 (by gcongr)
  have hn_lo : t ≤ (n : ℝ) * τ := (div_le_iff₀ hτr).1 (Nat.le_ceil _)
  have hn_hi : (n : ℝ) * τ < t + τ := by
    have h2 := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg ht0 hτr.le)) hτr
    rwa [add_mul, div_mul_cancel₀ t hτr.ne', one_mul] at h2
  have hk_lo : t ≤ (k : ℝ) * σ := (div_le_iff₀ hσr).1 (Nat.le_ceil _)
  have hk_hi : (k : ℝ) * σ < t + σ := by
    have h2 := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg ht0 hσr.le)) hσr
    rwa [add_mul, div_mul_cancel₀ t hσr.ne', one_mul] at h2
  have hΦ_le : Φ n k ≤ (2 * τ' + 2 * C * (T + τ')) * (τ + σ) := by
    have hdiff_sq : ((n : ℝ) * τ - (k : ℝ) * σ) ^ 2 ≤ (τ + σ) ^ 2 :=
      sq_le_sq.2 (by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ τ + σ)]
        exact abs_le.2 ⟨by linarith, by linarith⟩)
    have hsum_le : (n : ℝ) * τ + (k : ℝ) * σ ≤ 2 * (T + τ') := by linarith
    have hτσ_sq : ((τ : ℝ) + σ) ^ 2 ≤ 2 * τ' * (τ + σ) := by nlinarith
    unfold Φ gridBarrier
    calc ((n : ℝ) * τ - (k : ℝ) * σ) ^ 2 + C * (τ + σ) * ((n : ℝ) * τ + (k : ℝ) * σ)
        ≤ 2 * τ' * (τ + σ) + C * (τ + σ) * (2 * (T + τ')) := by
          gcongr; exact hdiff_sq.trans hτσ_sq
      _ = (2 * τ' + 2 * C * (T + τ')) * (τ + σ) := by ring
  have hsqrt_le : Real.sqrt (Φ n k) ≤
      Real.sqrt (2 * τ' + 2 * C * (T + τ')) * Real.sqrt (τ + σ) := by
    rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hΦ_le
  have hinv_prod : r₁⁻¹ ^ n * r₂⁻¹ ^ k ≤ Real.exp (4 * |m| * (T + τ')) := by
    calc r₁⁻¹ ^ n * r₂⁻¹ ^ k
        ≤ Real.exp (2 * |m| * (T + τ')) * Real.exp (2 * |m| * (T + τ')) :=
          mul_le_mul (hr_inv_exp τ r₁ n hτ hτ_le_τ' rfl hr₁_lo hnT)
            (hr_inv_exp σ r₂ k hσ hσ_le_τ' rfl hr₂_lo hkT) (by positivity) (by positivity)
      _ = Real.exp (4 * |m| * (T + τ')) := by rw [← Real.exp_add]; ring_nf
  have hdist_eq : dist (U n) (V k) ^ 2 =
      (r₁⁻¹ ^ n * r₂⁻¹ ^ k) * (r₁ ^ n * r₂ ^ k * dist (U n) (V k) ^ 2) := by
    rw [← mul_assoc, mul_mul_mul_comm, ← mul_pow, inv_mul_cancel₀ hr₁_pos.ne', one_pow,
      one_mul, ← mul_pow, inv_mul_cancel₀ hr₂_pos.ne', one_pow, one_mul]
  rw [hdist_eq]
  calc (r₁⁻¹ ^ n * r₂⁻¹ ^ k) * (r₁ ^ n * r₂ ^ k * dist (U n) (V k) ^ 2)
      ≤ Real.exp (4 * |m| * (T + τ')) * (M * Real.sqrt (Φ n k)) :=
        mul_le_mul hinv_prod (hgrid n hnT k hkT) (mul_nonneg (mul_nonneg (pow_nonneg hr₁_pos.le n)
          (pow_nonneg hr₂_pos.le k)) (sq_nonneg _)) (by positivity)
    _ ≤ Real.exp (4 * |m| * (T + τ')) *
          (M * (Real.sqrt (2 * τ' + 2 * C * (T + τ')) * Real.sqrt (τ + σ))) := by gcongr
    _ = cauchyK m T τ' A E * Real.sqrt (τ + σ) := by unfold cauchyK; ring

end DiscreteComparison

section Existence

variable {X : Type*} [MetricSpace X] {lam : ℝ} {φ : X → EReal}

/-- **Existence of `EVI_λ` flows and uniform convergence of minimizing movements**
(Ambrosio–Gigli–Savaré, Theorem 4.1.2; Ambrosio–Gigli, Theorem 3.25). Let `φ : X → EReal`
be lower semicontinuous on a complete metric space, coercive (`φ_{τ₀}(x₁) > -∞` for some
`τ₀ > 0`), and `lam`-penalized convex for all sufficiently small `τ > 0`. Then from every
point `x₀` of finite energy starts an `EVI_λ` solution `u` with `u 0 = x₀`, and the piecewise
constant interpolants `t ↦ J j ⌈t / τ j⌉₊` of every minimizing movement scheme starting at
`x₀` with time steps `τ j → 0⁺` converge to `u` uniformly on `[0, T]` for every `T : ℝ`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ j, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → (∀ j, J j 0 = x₀) →
        (∀ j k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  set τ' : ℝ≥0 := min (τ₀ / 2) (min (τ₁ / 2) ⟨(4 * (|lam| + 1))⁻¹, by positivity⟩)
  have hτ' : 0 < τ' := lt_min (half_pos hτ₀) (lt_min (half_pos hτ₁)
    (Subtype.mk_lt_mk.2 (by positivity)))
  have hτ'τ₀ : τ' < τ₀ := (min_le_left _ _).trans_lt (half_lt_self hτ₀)
  have hτ'τ₁ : τ' < τ₁ :=
    (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hτ₁))
  have hlamτ' : |lam| * (τ' : ℝ) ≤ 1 / 4 := by
    have hτ'le : (τ' : ℝ) ≤ (4 * (|lam| + 1))⁻¹ := by
      exact_mod_cast (min_le_right _ _).trans (min_le_right _ _)
    calc |lam| * (τ' : ℝ) ≤ |lam| * (4 * (|lam| + 1))⁻¹ := by gcongr
      _ ≤ (|lam| + 1) * (4 * (|lam| + 1))⁻¹ := by gcongr; linarith
      _ = 1 / 4 := by field_simp [show |lam| + 1 ≠ 0 by positivity]
  have hAbot : moreauYosida φ τ' x₀ ≠ ⊥ :=
    moreauYosida_ne_bot_of_lt hτ'τ₀ (edist_ne_top x₀ x₁) h₀
  have hAtop : moreauYosida φ τ' x₀ ≠ ⊤ :=
    ne_top_of_le_ne_top hx₀ (moreauYosida_le_self φ τ' x₀)
  set A : ℝ := (moreauYosida φ τ' x₀).toReal
  set E : ℝ := (φ x₀).toReal
  have hA : moreauYosida φ τ' x₀ = A := (EReal.coe_toReal hAtop hAbot).symm
  have hE : φ x₀ = E :=
    (EReal.coe_toReal hx₀ (apply_ne_bot_of_moreauYosida_ne_bot hτ₀ h₀ x₀)).symm
  have hEA : 0 ≤ E - A :=
    sub_nonneg.2 (by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀)
  have hpair : ∀ {τ σ : ℝ≥0} {U V : ℕ → X} {T : ℝ}, 0 ≤ T →
      0 < τ → 0 < σ → 4 * τ ≤ τ' → 4 * σ ≤ τ' → U 0 = x₀ → V 0 = x₀ →
      (∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) →
      (∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k)) →
      ∀ t ∈ Icc 0 T,
        dist (U ⌈t / (τ : ℝ)⌉₊) (V ⌈t / (σ : ℝ)⌉₊) ^ 2 ≤
          cauchyK lam T τ' A E * Real.sqrt ((τ : ℝ) + σ) := by
    intro τ σ U V T hT hτ hσ hττ' hστ' hU0 hV0 hU hV t ht
    have h4_le : ∀ {δ : ℝ≥0}, 4 * δ ≤ τ' → (δ : ℝ) ≤ τ' := fun {δ} h4 ↦ by
      have : (4 : ℝ) * δ ≤ τ' := by exact_mod_cast h4
      linarith [NNReal.coe_nonneg δ]
    have hττ₁ : τ < τ₁ := (NNReal.coe_le_coe.1 (h4_le hττ')).trans_lt hτ'τ₁
    have hστ₁ : σ < τ₁ := (NNReal.coe_le_coe.1 (h4_le hστ')).trans_lt hτ'τ₁
    have hmτ := (mul_le_mul_of_nonneg_left (h4_le hττ') (abs_nonneg _)).trans hlamτ'
    have hmσ := (mul_le_mul_of_nonneg_left (h4_le hστ') (abs_nonneg _)).trans hlamτ'
    exact dist_ceil_sq_le_of_penalizedConvex (hconv τ hτ hττ₁) (hconv σ hσ hστ₁)
      hτ hσ hττ' hστ' hmτ hmσ hA hE hT hU0 hV0 hU hV ht.1 ht.2
  set τc : ℕ → ℝ≥0 := fun j ↦ τ' / (4 * (j + 1)) with hτc_def
  have hτc : ∀ j, 0 < τc j := fun j ↦ by positivity
  have hτcτ' : ∀ j, 4 * τc j ≤ τ' := fun j ↦ by
    rw [← NNReal.coe_le_coe]; push_cast [hτc_def]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j), NNReal.coe_nonneg τ']
  have hτc_le : ∀ j, τc j ≤ τ' := fun j ↦ by
    have h4 : (4 : ℝ) * τc j ≤ τ' := by exact_mod_cast hτcτ' j
    exact_mod_cast (by linarith [NNReal.coe_nonneg (τc j)] : (τc j : ℝ) ≤ τ')
  have hτc0 : Tendsto τc atTop (𝓝 0) := by
    refine NNReal.tendsto_coe.1 ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ((τ' : ℝ) / 4)
    rw [mul_zero] at this
    refine this.congr fun j ↦ ?_
    push_cast [hτc_def]
    have hjp : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hlamτc : ∀ j, 0 < 1 + lam * (τc j : ℝ) := fun j ↦ by
    have habs : |lam| * τc j ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (hτc_le j)) (abs_nonneg _)).trans hlamτ'
    linarith [neg_abs_le (lam * (τc j : ℝ)), show |lam * (τc j : ℝ)| = |lam| * τc j by
      rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg (τc j))]]
  choose Jc hJc0 hJc using fun j ↦
    PenalizedConvex.exists_forall_mem_moreauYosidaResolvent
      hφ (hconv (τc j) (hτc j) ((hτc_le j).trans_lt hτ'τ₁)) (hτc j) (hlamτc j)
      ((hτc_le j).trans_lt hτ'τ₀) h₀ x₀
  have huc : ∀ T ≥ 0,
      UniformCauchySeqOn (fun j (t : ℝ) ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (Icc 0 T) := by
    intro T hT
    set K : ℝ := cauchyK lam T τ' A E
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set δ : ℝ := ε ^ 4 / (2 * (|K| + 1) ^ 2 + 1)
    have hδ : 0 < δ := by positivity
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 ((NNReal.tendsto_coe.2 hτc0).eventually (gt_mem_nhds hδ))
    refine ⟨N, fun i hi j hj t ht ↦ ?_⟩
    have hsum : (τc i : ℝ) + τc j < 2 * δ :=
      (add_lt_add (hN i hi) (hN j hj)).trans_eq (by ring)
    have hK_lt : |K| * Real.sqrt (2 * δ) < ε ^ 2 := by
      have h1 : (|K| * Real.sqrt (2 * δ)) ^ 2 < (ε ^ 2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hlt1 : 2 * |K| ^ 2 / (2 * (|K| + 1) ^ 2 + 1) < 1 := by
          rw [div_lt_one (by positivity)]; nlinarith [abs_nonneg K]
        rw [show |K| ^ 2 * (2 * δ) = (2 * |K| ^ 2 / (2 * (|K| + 1) ^ 2 + 1)) * ε ^ 4 by
          dsimp [δ]; ring, show (ε ^ 2) ^ 2 = 1 * ε ^ 4 by ring]
        exact mul_lt_mul_of_pos_right hlt1 (by positivity)
      exact (pow_lt_pow_iff_left₀ (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
        (sq_nonneg _) two_ne_zero).1 h1
    have hsq :
        dist (Jc i ⌈t / (τc i : ℝ)⌉₊) (Jc j ⌈t / (τc j : ℝ)⌉₊) ^ 2 < ε ^ 2 := by
      calc dist (Jc i ⌈t / (τc i : ℝ)⌉₊) (Jc j ⌈t / (τc j : ℝ)⌉₊) ^ 2
          ≤ K * Real.sqrt ((τc i : ℝ) + τc j) := hpair hT (hτc i) (hτc j)
            (hτcτ' i) (hτcτ' j) (hJc0 i) (hJc0 j) (hJc i) (hJc j) t ht
        _ ≤ |K| * Real.sqrt (2 * δ) := mul_le_mul (le_abs_self _)
            (Real.sqrt_le_sqrt hsum.le) (Real.sqrt_nonneg _) (abs_nonneg _)
        _ < ε ^ 2 := hK_lt
    exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hsq
  have hlim_ex : ∀ t : ℝ,
      ∃ y : X, Tendsto (fun j ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (𝓝 y) := fun t ↦ by
    rcases le_or_gt 0 t with ht | ht
    · exact cauchySeq_tendsto_of_complete ((huc t ht).cauchySeq ⟨ht, le_rfl⟩)
    · refine ⟨x₀, tendsto_const_nhds.congr fun j ↦ ?_⟩
      have h0 : ⌈t / (τc j : ℝ)⌉₊ = 0 :=
        Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg ht.le (NNReal.coe_nonneg _))
      rw [h0, hJc0 j]
  choose u hu_lim using hlim_ex
  have hu0 : u 0 = x₀ := tendsto_nhds_unique (hu_lim 0) (by
    simp only [zero_div, Nat.ceil_zero, hJc0]; exact tendsto_const_nhds)
  have hu_unif : ∀ T ≥ 0,
      TendstoUniformlyOn (fun j (t : ℝ) ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) u atTop (Icc 0 T) :=
    fun T hT ↦ (huc T hT).tendstoUniformlyOn_of_tendsto fun t _ ↦ hu_lim t
  have hmod : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t →
      dist (u s) (u t) ^ 2 ≤ 2 * (t - s) * (E - A) * (1 + Real.exp (8 * (t + τ') / τ')) := by
    intro s t hs hst
    have hlim_r : Tendsto (fun j ↦ 2 * (t - s + τc j) * (E - A) *
        (1 + Real.exp (8 * (t + τ') / τ'))) atTop
        (𝓝 (2 * (t - s) * (E - A) * (1 + Real.exp (8 * (t + τ') / τ')))) := by
      simpa using (((tendsto_const_nhds.sub tendsto_const_nhds).add
        (NNReal.tendsto_coe.2 hτc0)).const_mul 2).mul_const (E - A) |>.mul_const
          (1 + Real.exp (8 * (t + τ') / τ'))
    refine le_of_tendsto_of_tendsto (((hu_lim s).dist (hu_lim t)).pow 2) hlim_r
      (Eventually.of_forall fun j ↦ ?_)
    have hed := edist_ceil_sq_le_of_forall_mem_moreauYosidaResolvent (hJc j) (hτc j) (hτcτ' j)
      (hJc0 j ▸ hA) (hJc0 j ▸ hE) hs hst
    rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hed
    refine hed.trans (mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (mul_nonneg zero_le_two (add_nonneg (sub_nonneg.2 hst) (τc j).2)) hEA))
    linarith [Real.exp_le_exp.2 (show 8 * (t + τc j) / τ' ≤ 8 * (t + τ') / τ' by
      gcongr; exact NNReal.coe_le_coe.2 (hτc_le j))]
  have hu_cont : ContinuousOn u (Ici 0) := by
    rw [Metric.continuousOn_iff]
    intro t ht ε hε
    set C : ℝ := 2 * (E - A) * (1 + Real.exp (8 * ((t + 1) + τ') / τ')) + 1
    have hCpos : 0 < C := by positivity
    refine ⟨min 1 (ε ^ 2 / C), lt_min one_pos (by positivity), fun s hs hst ↦ ?_⟩
    have hst' : |s - t| < min 1 (ε ^ 2 / C) := by rwa [Real.dist_eq] at hst
    have hsT : s ≤ t + 1 := by linarith [(abs_lt.1 (hst'.trans_le (min_le_left _ _))).2]
    have hsq : dist (u s) (u t) ^ 2 ≤ C * |s - t| := by
      rcases le_total s t with h | h
      · have hm := hmod hs h
        have hB : 1 + Real.exp (8 * (t + τ') / τ') ≤
            1 + Real.exp (8 * ((t + 1) + τ') / τ') := by gcongr; linarith
        have : 2 * (E - A) * (1 + Real.exp (8 * (t + τ') / τ')) ≤ C := by
          dsimp [C]; linarith [mul_le_mul_of_nonneg_left hB (mul_nonneg zero_le_two hEA)]
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]; nlinarith [sub_nonneg.2 h]
      · have hm := hmod ht h
        have hB : 1 + Real.exp (8 * (s + τ') / τ') ≤
            1 + Real.exp (8 * ((t + 1) + τ') / τ') := by gcongr
        have : 2 * (E - A) * (1 + Real.exp (8 * (s + τ') / τ')) ≤ C := by
          dsimp [C]; linarith [mul_le_mul_of_nonneg_left hB (mul_nonneg zero_le_two hEA)]
        rw [dist_comm, abs_of_nonneg (sub_nonneg.2 h)]; nlinarith [sub_nonneg.2 h]
    exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 (hsq.trans_lt (by
      have := mul_lt_mul_of_pos_left (hst'.trans_le (min_le_right _ _)) hCpos
      rwa [mul_div_cancel₀ _ hCpos.ne'] at this))
  have hu_reg : ∀ y, φ y ≠ ⊤ → ∀ s t : ℝ, 0 ≤ s → s < t →
      φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - Real.exp (lam * (t - s)) * dist (u t) y ^ 2) /
        (2 * ∫ r in (0 : ℝ)..(t - s), Real.exp (lam * r)) : ℝ) : EReal) := by
    intro y hy s t hs hst
    set n : ℕ → ℕ := fun j ↦ ⌈s / (τc j : ℝ)⌉₊
    set m : ℕ → ℕ := fun j ↦ ⌈t / (τc j : ℝ)⌉₊
    have hτc_real : Tendsto (fun j ↦ (τc j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτc0
    have hev_lt : ∀ᶠ j in atTop, n j < m j := by
      filter_upwards [hτc_real.eventually (gt_mem_nhds (div_pos (sub_pos.2 hst) two_pos))]
        with j hj
      have hτj : (0 : ℝ) < τc j := hτc j
      have h1 : (n j : ℝ) < s / (τc j : ℝ) + 1 := Nat.ceil_lt_add_one (div_nonneg hs hτj.le)
      have h2 : t / (τc j : ℝ) ≤ m j := Nat.le_ceil _
      have h3 : (1 : ℝ) < (t - s) / τc j := (one_lt_div hτj).2 (by linarith)
      exact Nat.cast_lt.1 (by calc (n j : ℝ) < s / τc j + 1 := h1
        _ < s / τc j + (t - s) / τc j := by linarith
        _ = t / τc j := by rw [← add_div, add_sub_cancel]
        _ ≤ m j := h2)
    have hN_lim : Tendsto (fun j ↦ ((m j - n j : ℕ) : ℝ) * τc j) atTop (𝓝 (t - s)) := by
      have hceil_lim : ∀ r : ℝ, 0 ≤ r → Tendsto
          (fun j ↦ (⌈r / (τc j : ℝ)⌉₊ : ℝ) * τc j) atTop (𝓝 r) := fun r hr ↦ by
        refine tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
          (fun j ↦ ?_) hτc_real
        have hτj : (0 : ℝ) < τc j := hτc j
        have hlo : r ≤ (⌈r / (τc j : ℝ)⌉₊ : ℝ) * τc j :=
          (div_le_iff₀ hτj).1 (Nat.le_ceil _)
        have hhi : (⌈r / (τc j : ℝ)⌉₊ : ℝ) * τc j < r + τc j := by
          have := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hr hτj.le)) hτj
          rwa [add_mul, div_mul_cancel₀ r hτj.ne', one_mul] at this
        rw [Real.norm_of_nonneg (sub_nonneg.2 hlo)]; linarith
      exact ((hceil_lim t (hs.trans hst.le)).sub (hceil_lim s hs)).congr'
        (hev_lt.mono fun j hj ↦ by dsimp only [m, n]; rw [Nat.cast_sub hj.le, sub_mul])
    have hrhs_lim : Tendsto (fun j ↦ φ y +
        (((dist (Jc j (n j)) y ^ 2 - (1 + lam * (τc j : ℝ)) ^ (m j - n j) *
            dist (Jc j (m j)) y ^ 2) /
          (2 * (τc j : ℝ) *
            ∑ k ∈ range (m j - n j), (1 + lam * (τc j : ℝ)) ^ k) : ℝ) : EReal))
        atTop (𝓝 (φ y + (((dist (u s) y ^ 2 - Real.exp (lam * (t - s)) * dist (u t) y ^ 2) /
          (2 * ∫ r in (0 : ℝ)..(t - s), Real.exp (lam * r)) : ℝ) : EReal))) := by
      have hnum : Tendsto (fun j ↦ dist (Jc j (n j)) y ^ 2 -
          (1 + lam * (τc j : ℝ)) ^ (m j - n j) * dist (Jc j (m j)) y ^ 2) atTop
          (𝓝 (dist (u s) y ^ 2 - Real.exp (lam * (t - s)) * dist (u t) y ^ 2)) :=
        (((hu_lim s).dist tendsto_const_nhds).pow 2).sub
          ((tendsto_one_add_mul_pow hτc_real (Eventually.of_forall hτc) hN_lim).mul
            (((hu_lim t).dist tendsto_const_nhds).pow 2))
      have hden : Tendsto (fun j ↦ 2 * (τc j : ℝ) *
          ∑ k ∈ range (m j - n j), (1 + lam * (τc j : ℝ)) ^ k) atTop
          (𝓝 (2 * ∫ r in (0 : ℝ)..(t - s), Real.exp (lam * r))) := by
        simpa only [mul_assoc] using (tendsto_coe_mul_sum_one_add_mul_pow hτc_real
          (Eventually.of_forall hτc) hN_lim).const_mul 2
      have hfrac :=
        hnum.div hden (mul_ne_zero two_ne_zero (integral_exp_mul_pos lam (sub_pos.2 hst)).ne')
      lift φ y to ℝ using ⟨hy, apply_ne_bot_of_moreauYosida_ne_bot hτ₀ h₀ y⟩ with py
      exact ((continuous_coe_real_ereal.tendsto _).comp (hfrac.const_add py)).congr
        fun j ↦ by simp
    have hdisc : ∀ᶠ j in atTop, φ (Jc j (m j)) ≤ φ y +
        (((dist (Jc j (n j)) y ^ 2 - (1 + lam * (τc j : ℝ)) ^ (m j - n j) *
            dist (Jc j (m j)) y ^ 2) /
          (2 * (τc j : ℝ) *
            ∑ k ∈ range (m j - n j), (1 + lam * (τc j : ℝ)) ^ k) : ℝ) : EReal) := by
      filter_upwards [hev_lt] with j hj
      have hshift := (hconv (τc j) (hτc j) ((hτc_le j).trans_lt hτ'τ₁)).apply_le
        (hτc j) (hlamτc j).le (U := fun k ↦ Jc j (n j + k)) (fun k ↦ hJc j (n j + k))
        hy (Nat.sub_pos_of_lt hj)
      rwa [Nat.add_zero, Nat.add_sub_cancel' hj.le] at hshift
    exact ((hφ.le_liminf (u t)).trans (hu_lim t).liminf_le_liminf_comp).trans
      ((liminf_le_liminf hdisc).trans_eq hrhs_lim.liminf_eq)
  have hu_evi : IsEVISolution lam φ u := by
    refine isEVISolution_of_apply_le hφ hu_cont ?_
      (fun t _ ↦ apply_ne_bot_of_moreauYosida_ne_bot hτ₀ h₀ (u t)) hu_reg
    exact fun t ht ↦ ne_top_of_le_ne_top (EReal.add_ne_top hx₀ (EReal.coe_ne_top _))
      (hu_reg x₀ hx₀ 0 t le_rfl ht)
  refine ⟨u, hu0, hu_evi, fun τ J hτ hτ0 hJ0 hJ T ↦ ?_⟩
  set T' : ℝ := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  suffices h :
      TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T') from
    h.mono (fun t ht ↦ ⟨ht.1, ht.2.trans (le_max_left _ _)⟩)
  set K : ℝ := cauchyK lam T' τ' A E
  have hdiff : ∀ᶠ j in atTop, ∀ t ∈ Icc 0 T',
      dist (J j ⌈t / (τ j : ℝ)⌉₊) (Jc j ⌈t / (τc j : ℝ)⌉₊) ^ 2 ≤
        K * Real.sqrt ((τ j : ℝ) + τc j) := by
    filter_upwards
      [hτ0.eventually (ge_mem_nhds (by positivity : (0 : ℝ≥0) < τ' / 4))] with j hj
    have h4 : 4 * τ j ≤ τ' := by
      calc 4 * τ j ≤ 4 * (τ' / 4) := by gcongr
        _ = τ' := mul_div_cancel₀ _ (by norm_num)
    exact fun t ht ↦
      hpair hT' (hτ j) (hτc j) h4 (hτcτ' j) (hJ0 j) (hJc0 j) (hJ j) (hJc j) t ht
  have herr0 :
      Tendsto (fun j ↦ Real.sqrt (K * Real.sqrt ((τ j : ℝ) + τc j))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun j ↦ (τ j : ℝ) + τc j) atTop (𝓝 0) := by
      simpa using (NNReal.tendsto_coe.2 hτ0).add (NNReal.tendsto_coe.2 hτc0)
    have h0 : Tendsto (fun j ↦ K * Real.sqrt ((τ j : ℝ) + τc j)) atTop (𝓝 0) :=
      (((Real.continuous_sqrt.tendsto 0).comp hsum).const_mul K).trans_eq (by simp)
    exact ((Real.continuous_sqrt.tendsto 0).comp h0).trans_eq (by simp)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ_unif := Metric.tendstoUniformlyOn_iff.1 (hu_unif T' hT') (ε / 2) (half_pos hε)
  have herr_ev := herr0.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hδ_unif, hdiff, herr_ev] with j hj_unif hj_diff hj_err t ht
  have hd_le : dist (J j ⌈t / (τ j : ℝ)⌉₊) (Jc j ⌈t / (τc j : ℝ)⌉₊) ≤
      Real.sqrt (K * Real.sqrt ((τ j : ℝ) + τc j)) := Real.le_sqrt_of_sq_le (hj_diff t ht)
  have hd_lt : dist (u t) (J j ⌈t / (τ j : ℝ)⌉₊) < ε / 2 + ε / 2 :=
    (dist_triangle _ (Jc j ⌈t / (τc j : ℝ)⌉₊) _).trans_lt
      (add_lt_add (hj_unif t ht) (by rw [dist_comm]; exact hd_le.trans_lt hj_err))
  linarith

/-- **Existence of `EVI_λ` flows on the closure of the effective domain**
(Ambrosio–Gigli–Savaré, Theorem 4.0.4). Under the hypotheses of
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, every point `x₀` in
`closure {x | φ x ≠ ⊤}` is the initial point of an `EVI_λ` solution. -/
theorem exists_isEVISolution_of_mem_closure_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X}
    (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ := by
  obtain ⟨seq, hseq, hseq_lim⟩ := mem_closure_iff_seq_limit.1 hx₀
  choose U hU0 hU using fun k ↦
    exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ (hseq k)
  have hU_evi : ∀ k, IsEVISolution lam φ (U k) := fun k ↦ (hU k).1
  have huc : ∀ T ≥ 0, UniformCauchySeqOn U atTop (Icc 0 T) := by
    intro T _
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set C : ℝ := Real.exp (|lam| * T) + 1
    have hC0 : 0 < C := by positivity
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hseq_lim.cauchySeq (ε / C) (by positivity)
    refine ⟨N, fun i hi j hj t ht ↦ ?_⟩
    have hexp : Real.exp (-(lam * t)) ≤ Real.exp (|lam| * T) := by
      refine Real.exp_le_exp.2 ?_
      have : -(lam * t) ≤ |lam * t| := neg_le_abs _
      rw [abs_mul, abs_of_nonneg ht.1] at this
      exact this.trans (by gcongr; exact ht.2)
    calc dist (U i t) (U j t)
        ≤ Real.exp (-(lam * t)) * dist (U i 0) (U j 0) :=
          (hU_evi i).dist_le (hU_evi j) hφ ht.1
      _ ≤ Real.exp (|lam| * T) * dist (seq i) (seq j) := by
          rw [hU0 i, hU0 j]; gcongr
      _ < C * (ε / C) :=
          mul_lt_mul' (by linarith [Real.exp_pos (|lam| * T)]) (hN i hi j hj)
            dist_nonneg (by positivity)
      _ = ε := mul_div_cancel₀ _ hC0.ne'
  have hlim_ex :
      ∀ t : {r : ℝ // 0 ≤ r}, ∃ y : X, Tendsto (fun k ↦ U k t.1) atTop (𝓝 y) :=
    fun t ↦ cauchySeq_tendsto_of_complete ((huc t.1 t.2).cauchySeq ⟨t.2, le_rfl⟩)
  let u : ℝ → X := fun t ↦ if ht : 0 ≤ t then (hlim_ex ⟨t, ht⟩).choose else x₀
  have hu_lim : ∀ t ≥ 0, Tendsto (fun k ↦ U k t) atTop (𝓝 (u t)) := fun t ht ↦ by
    simp only [u, ht, ↓reduceDIte]
    exact (hlim_ex ⟨t, ht⟩).choose_spec
  have hu0 : u 0 = x₀ := tendsto_nhds_unique (hu_lim 0 le_rfl) (by simpa [hU0] using hseq_lim)
  have hu_unif : ∀ T ≥ 0, TendstoUniformlyOn U u atTop (Icc 0 T) :=
    fun T hT ↦ (huc T hT).tendstoUniformlyOn_of_tendsto fun t ht ↦ hu_lim t ht.1
  have hu_cont : ContinuousOn u (Ici 0) := fun t ht ↦ by
    have hT : ContinuousOn u (Icc 0 (t + 1)) :=
      (hu_unif (t + 1) (by linarith [mem_Ici.1 ht])).continuousOn
        (Eventually.of_forall fun k ↦ (hU_evi k).continuousOn.mono Icc_subset_Ici_self).frequently
    have hnhds : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t :=
      Filter.mem_of_superset (inter_mem_nhdsWithin (Ici 0) (Iio_mem_nhds (lt_add_one t)))
        fun _ hr ↦ ⟨hr.1, hr.2.le⟩
    exact (hT t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hnhds
  refine ⟨u, TendstoGamma.isEVISolution_of_tendsto hφ.tendstoGamma_const (fun _ ↦ hφ) hU_evi
    hu_lim hu_cont ⟨seq 0, hseq 0⟩
    (fun t _ ↦ apply_ne_bot_of_moreauYosida_ne_bot hτ₀ h₀ (u t)), hu0⟩

/-- **Characterization of the `EVI_λ` domain** (Ambrosio–Gigli–Savaré, Theorem 4.0.4). Under
the hypotheses of `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, the set
of initial points of `EVI_λ` solutions equals `closure {x | φ x ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) :
    eviDomain lam φ = closure {x | φ x ≠ ⊤} :=
  Set.Subset.antisymm eviDomain_subset_closure fun _ hx ↦
    mem_eviDomain.2 (exists_isEVISolution_of_mem_closure_of_penalizedConvex
      hφ hτ₀ hτ₁ hconv h₀ hx)

end Existence

section GeodesicallyConvex

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [IsCATZeroSpace X]
  {lam : ℝ} {φ : X → EReal}

omit [CompleteSpace X] [IsCATZeroSpace X] in
private lemma exists_moreauYosida_ne_bot_of_geodesicallyConvex
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    {z : X} (hz : φ z ≠ ⊤) (hzbot : φ z ≠ ⊥) :
    ∃ τ₀ : ℝ≥0, 0 < τ₀ ∧ moreauYosida φ τ₀ z ≠ ⊥ := by
  let τ₀ : ℝ≥0 := ⟨(2 * (|lam| + 1))⁻¹, by positivity⟩
  refine ⟨τ₀, Subtype.mk_lt_mk.2 (by positivity), ?_⟩
  refine hconv.moreauYosida_ne_bot hφ hz hzbot (Subtype.mk_lt_mk.2 (by positivity)) ?_
  have hτ₀ : (τ₀ : ℝ) = (2 * (|lam| + 1))⁻¹ := rfl
  have habs : |lam| * (τ₀ : ℝ) ≤ 1 / 2 := by
    rw [hτ₀]
    calc |lam| * (2 * (|lam| + 1))⁻¹
        ≤ (|lam| + 1) * (2 * (|lam| + 1))⁻¹ := by gcongr; linarith
      _ = 1 / 2 := by field_simp [show |lam| + 1 ≠ 0 by positivity]
  have heq : |lam * (τ₀ : ℝ)| = |lam| * τ₀ := by
    rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg τ₀)]
  linarith [neg_abs_le (lam * (τ₀ : ℝ))]

/-- **Existence and uniform convergence of minimizing movements for geodesically convex energies
on CAT(0) spaces.** Let `φ : X → EReal` be lower semicontinuous and `lam`-geodesically convex on
a complete CAT(0) space. Then from every point `x₀` of finite energy starts an `EVI_λ` solution
`u` with `u 0 = x₀`, and all minimizing movement interpolants starting at `x₀` converge
uniformly to `u` on compact time intervals `[0, T]` as `τ → 0⁺`. -/
theorem GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ j, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → (∀ j, J j 0 = x₀) →
        (∀ j k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, h₀⟩ :=
    exists_moreauYosida_ne_bot_of_geodesicallyConvex hφ hconv hx₀ (hbot x₀)
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ one_pos
    (fun _ _ _ ↦ hconv.penalizedConvex) h₀ hx₀

/-- **Existence of `EVI_λ` flows on `closure {x | φ x ≠ ⊤}` for geodesically convex energies
on CAT(0) spaces.** -/
theorem GeodesicallyConvex.exists_isEVISolution_of_mem_closure
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) {x₀ : X} (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ := by
  obtain ⟨seq, hseq, -⟩ := mem_closure_iff_seq_limit.1 hx₀
  obtain ⟨τ₀, hτ₀, h₀⟩ :=
    exists_moreauYosida_ne_bot_of_geodesicallyConvex hφ hconv (hseq 0) (hbot (seq 0))
  exact exists_isEVISolution_of_mem_closure_of_penalizedConvex hφ hτ₀ one_pos
    (fun _ _ _ ↦ hconv.penalizedConvex) h₀ hx₀

/-- **Characterization of the `EVI_λ` domain for geodesically convex energies on CAT(0)
spaces.** -/
theorem GeodesicallyConvex.eviDomain_eq_closure
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) : eviDomain lam φ = closure {x | φ x ≠ ⊤} :=
  Set.Subset.antisymm eviDomain_subset_closure fun _ hx ↦
    mem_eviDomain.2 (hconv.exists_isEVISolution_of_mem_closure hφ hbot hx)

end GeodesicallyConvex

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Graph
public import TauCeti.Analysis.ODE.LyapunovPerron.Linear

/-!
# Perturbing the nonlinearity in the Lyapunov--Perron construction

Keep the linear part and its exponential dichotomy fixed, and vary the nonlinear remainder.
A uniform bound `d` on the change in the remainder gives a uniform bound
`(2 K d / α) / (1 - 2 K ε / α)` on the change in the bounded forward solution,
and hence on its stable graph. The estimate is uniform in the stable parameter and over the
entire forward half-line. The two remainders may have different Lipschitz constants: only
the first one enters the denominator.

The local versions in `TauCeti.Analysis.ODE.LyapunovPerron.Local` require uniform control
only on the common closed ball of confinement. The radial cutoff sends the whole space into
that ball, so no control of the vector fields outside it is needed. Uniform convergence of the
remainders on that ball gives uniform convergence of the graph maps. These are estimates
for graph values; convergence of their derivatives requires a separate variational estimate.

The perturbation argument is Banach's fixed-point estimate, applied to the integral operator
in the Lyapunov--Perron method; see W. A. Coppel, *Dichotomies in Stability Theory*,
Springer, 1978, Chapter 5. We use Mathlib's
`ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'` for the fixed-point comparison.
-/

public section

open Filter Metric NormedSpace Set Topology
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {A P : X →L[ℝ] X} {K α ε η : ℝ≥0} {N M : X → X}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
    ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
    ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hN : LipschitzWith ε N) (hM : LipschitzWith η M)

/-- Changing a globally Lipschitz remainder by at most `d` changes the Lyapunov--Perron
operator, on every bounded curve and at every stable parameter, by at most `2 K d / α`. -/
theorem dist_lyapunovPerronMap_le_of_norm_sub_le {d : ℝ}
    (hNM : ∀ z, ‖N z - M z‖ ≤ d) (ξ : X) (γ : ℝ≥0 →ᵇ X) :
    dist (lyapunovPerronMap A P N hs hu hα hN ξ γ)
      (lyapunovPerronMap A P M hs hu hα hM ξ γ) ≤ 2 * K * d / α := by
  let I := lyapunovPerronIntegralCLM A P hs hu hα
  have hdiff : lyapunovPerronMap A P N hs hu hα hN ξ γ -
      lyapunovPerronMap A P M hs hu hα hM ξ γ = I (γ.comp N hN - γ.comp M hM) := by
    ext t
    simp only [I, map_sub, _root_.sub_apply,
      lyapunovPerronMap_apply, lyapunovPerronIntegralCLM_apply, add_sub_add_left_eq_sub]
    rfl
  have hbound : ‖γ.comp N hN - γ.comp M hM‖ ≤ d :=
    (BoundedContinuousFunction.norm_le ((norm_nonneg _).trans (hNM 0))).2 fun t ↦ hNM (γ t)
  rw [dist_eq_norm, hdiff]
  calc
    ‖I (γ.comp N hN - γ.comp M hM)‖ ≤ ‖I‖ * ‖γ.comp N hN - γ.comp M hM‖ :=
      I.le_opNorm _
    _ ≤ (2 * K / α) * d := mul_le_mul (norm_lyapunovPerronIntegralCLM_le hs hu hα)
      hbound (norm_nonneg _) (by positivity)
    _ = 2 * K * d / α := by ring

/-- The bounded forward solutions depend uniformly on the nonlinear remainder. The estimate
holds in the sup norm over the entire forward half-line and is independent of `ξ`. -/
theorem dist_lyapunovPerronSolution_le_of_norm_sub_le
    (hsmallN : 2 * K * ε < α) (hsmallM : 2 * K * η < α)
    {d : ℝ} (hNM : ∀ z, ‖N z - M z‖ ≤ d) (ξ : X) :
    dist (lyapunovPerronSolution A P N hs hu hα hN hsmallN ξ)
      (lyapunovPerronSolution A P M hs hu hα hM hsmallM ξ) ≤
        (2 * K * d / α) / (1 - 2 * K * ε / α) := by
  have h := (contractingWith_lyapunovPerronMap hs hu hα hN hsmallN ξ
    ).dist_fixedPoint_fixedPoint_of_dist_le' (lyapunovPerronMap A P M hs hu hα hM ξ)
      (isFixedPt_lyapunovPerronSolution hs hu hα hN hsmallN ξ)
      (isFixedPt_lyapunovPerronSolution hs hu hα hM hsmallM ξ)
      (dist_lyapunovPerronMap_le_of_norm_sub_le hs hu hα hN hM hNM ξ)
  simpa only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat] using h

/-- The stable graph displacement depends uniformly on the nonlinear remainder, with the
same bound as the full bounded trajectory. -/
theorem dist_lyapunovPerronGraphMap_le_of_norm_sub_le
    (hsmallN : 2 * K * ε < α) (hsmallM : 2 * K * η < α)
    {d : ℝ} (hNM : ∀ z, ‖N z - M z‖ ≤ d) (ξ : X) :
    dist (lyapunovPerronGraphMap A P N hs hu hα hN hsmallN ξ)
      (lyapunovPerronGraphMap A P M hs hu hα hM hsmallM ξ) ≤
        (2 * K * d / α) / (1 - 2 * K * ε / α) := by
  rw [← dist_add_left (P ξ),
    ← lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap,
    ← lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap]
  exact (BoundedContinuousFunction.dist_coe_le_dist 0).trans
    (dist_lyapunovPerronSolution_le_of_norm_sub_le hs hu hα hN hM
      hsmallN hsmallM hNM ξ)

end ContinuousLinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Smooth
import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction

/-!
# Perturbing the derivatives of Lyapunov--Perron graphs

Fix a linear exponential dichotomy, and consider two small Lipschitz remainders `N` and `M`.
Their bounded forward solutions have derivatives in the stable parameter that solve the
variational Lyapunov--Perron equation. If the derivatives of the remainders, evaluated along
these two solutions, differ by at most `d`, then the solution derivatives differ in operator
norm by at most

`(2 K / α) d K / ((1 - 2 K ε / α) (1 - 2 K ε' / α))`.

Evaluation at zero gives the same estimate for the graph derivatives. The parameters may be
different: this compares tangent graphs as well as perturbations of one graph. The bound uses
only the derivatives along the actual trajectories, so local smoothness suffices; neither
remainder needs to be differentiable outside its confinement region. In particular, these
estimates can be combined with uniform continuity of the remainder derivative and uniform
convergence of the trajectories to control the tangent spaces of compact graph pieces.

The argument uses the variational equation from
`ContinuousLinearMap.fderiv_lyapunovPerronSolution_apply` and the integral operator from
`ContinuousLinearMap.lyapunovPerronIntegralCLM`.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics 629,
  Springer, 1978, Chapter 5.
-/

public section

open Metric NormedSpace Set Topology
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K α ε ε' : ℝ≥0} {A P : X →L[ℝ] X} {N M : X → X}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hN : LipschitzWith ε N) (hM : LipschitzWith ε' M)
  (hsmall : 2 * K * ε < α) (hsmall' : 2 * K * ε' < α)
  {N' M' : X → X →L[ℝ] X} {s u : Set X} {δ ρ : ℝ} {ξ ζ : X}
  (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s)
  (hMs : ∀ x ∈ u, HasFDerivAt M (M' x) x) (hM' : UniformContinuousOn M' u)
  (hδ : 0 < δ) (hρ : 0 < ρ)
  (hξ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t) δ ⊆ s)
  (hζ : ∀ t, ball (lyapunovPerronSolution A P M hs hu hα hM hsmall' ζ t) ρ ⊆ u)

include hNs hN' hMs hM' hδ hρ hξ hζ

/-- Subtracting two variational equations separates the change of solution from the change of
linearized remainder. -/
private theorem fderiv_solution_sub_eq_integral
    {Φ Ψ : ℝ≥0 →ᵇ (X →L[ℝ] X)}
    (hΦ : ∀ t, Φ t = N' (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t))
    (hΨ : ∀ t, Ψ t = M' (lyapunovPerronSolution A P M hs hu hα hM hsmall' ζ t)) :
    let D := fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ
    let E := fderiv ℝ (lyapunovPerronSolution A P M hs hu hα hM hsmall') ζ
    let I := lyapunovPerronIntegralCLM A P hs hu hα
    D - E = I ∘L BoundedContinuousFunction.applyCLM Φ ∘L (D - E) +
      I ∘L BoundedContinuousFunction.applyCLM (Φ - Ψ) ∘L E := by
  dsimp only
  set D := fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ
  set E := fderiv ℝ (lyapunovPerronSolution A P M hs hu hα hM hsmall') ζ
  set I := lyapunovPerronIntegralCLM A P hs hu hα
  set B := BoundedContinuousFunction.applyCLM Φ
  set C := BoundedContinuousFunction.applyCLM Ψ
  have hres : D - I ∘L B ∘L D = E - I ∘L C ∘L E := by
    ext v t
    simp only [D, E, I, B, C, sub_apply, comp_apply,
      lyapunovPerronIntegralCLM_apply, BoundedContinuousFunction.applyCLM_apply, hΦ, hΨ]
    rw [fderiv_lyapunovPerronSolution_apply hs hu hα hN hsmall hNs hN' hδ hξ,
      fderiv_lyapunovPerronSolution_apply hs hu hα hM hsmall' hMs hM' hρ hζ]
    abel
  simp only [map_sub, comp_sub, sub_comp]
  calc
    D - E = (D - I ∘L B ∘L D) - (E - I ∘L C ∘L E) +
        (I ∘L B ∘L D - I ∘L C ∘L E) := by abel
    _ = _ := by rw [hres]; abel

/-- A uniform comparison of the linearized remainders along two bounded forward trajectories
controls the operator-norm difference of their stable-parameter derivatives. The two small
Lipschitz constants need not coincide. -/
theorem norm_fderiv_lyapunovPerronSolution_sub_le {d : ℝ}
    (hderiv : ∀ t,
      ‖N' (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t) -
        M' (lyapunovPerronSolution A P M hs hu hα hM hsmall' ζ t)‖ ≤ d) :
    ‖fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ -
        fderiv ℝ (lyapunovPerronSolution A P M hs hu hα hM hsmall') ζ‖ ≤
      (2 * K / α * d * (K / (1 - 2 * K * ε' / α))) / (1 - 2 * K * ε / α) := by
  obtain ⟨Φ, hΦ⟩ := BoundedContinuousFunction.exists_eq_comp hN hNs hN'.continuousOn
    fun t ↦ hξ t (mem_ball_self hδ)
  obtain ⟨Ψ, hΨ⟩ := BoundedContinuousFunction.exists_eq_comp hM hMs hM'.continuousOn
    fun t ↦ hζ t (mem_ball_self hρ)
  have hΦnorm : ‖Φ‖ ≤ ε := (BoundedContinuousFunction.norm_le ε.coe_nonneg).2 fun t ↦ by
    rw [hΦ]
    exact (hNs _ (hξ t (mem_ball_self hδ))).le_of_lipschitz hN
  have hd := (norm_nonneg _).trans (hderiv 0)
  have hdiff : ‖Φ - Ψ‖ ≤ d := (BoundedContinuousFunction.norm_le hd).2 fun t ↦ by
    simpa only [_root_.sub_apply, hΦ, hΨ] using hderiv t
  set D := fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ
  set E := fderiv ℝ (lyapunovPerronSolution A P M hs hu hα hM hsmall') ζ
  set I := lyapunovPerronIntegralCLM A P hs hu hα
  set B := BoundedContinuousFunction.applyCLM Φ
  set C := BoundedContinuousFunction.applyCLM Ψ
  have heq : D - E = I ∘L B ∘L (D - E) + I ∘L (B - C) ∘L E := by
    simpa only [map_sub] using
      fderiv_solution_sub_eq_integral hs hu hα hN hM hsmall hsmall'
        hNs hN' hMs hM' hδ hρ hξ hζ hΦ hΨ
  have hInorm : ‖I‖ ≤ 2 * K / α := norm_lyapunovPerronIntegralCLM_le hs hu hα
  have hBnorm : ‖B‖ ≤ ε := (BoundedContinuousFunction.norm_applyCLM_apply_le Φ).trans hΦnorm
  have hBCnorm : ‖B - C‖ ≤ d := by
    rw [← map_sub]
    exact (BoundedContinuousFunction.norm_applyCLM_apply_le (Φ - Ψ)).trans hdiff
  have hEnorm : ‖E‖ ≤ K / (1 - 2 * K * ε' / α) := by
    have hle : 2 * K * ε' / α ≤ 1 := ((div_lt_one hα).2 hsmall').le
    simpa only [E, NNReal.coe_div, NNReal.coe_sub hle, NNReal.coe_one, NNReal.coe_mul,
      NNReal.coe_ofNat] using
      norm_fderiv_le_of_lipschitz (x₀ := ζ) ℝ
        (lipschitzWith_lyapunovPerronSolution hs hu hα hM hsmall')
  have hq : 0 < 1 - 2 * (K : ℝ) * ε / α :=
    sub_pos.mpr ((div_lt_one (by exact_mod_cast hα)).2 (by exact_mod_cast hsmall))
  have hEnonneg := (norm_nonneg E).trans hEnorm
  have hbound : ‖D - E‖ ≤ 2 * K / α * ε * ‖D - E‖ +
      2 * K / α * d * (K / (1 - 2 * K * ε' / α)) := by
    calc
      ‖D - E‖ = ‖I ∘L B ∘L (D - E) + I ∘L (B - C) ∘L E‖ := congrArg norm heq
      _ ≤ ‖I ∘L B ∘L (D - E)‖ + ‖I ∘L (B - C) ∘L E‖ := norm_add_le _ _
      _ ≤ ‖I‖ * ‖B‖ * ‖D - E‖ + ‖I‖ * ‖B - C‖ * ‖E‖ := by
        exact add_le_add
          ((opNorm_comp_le (I ∘L B) (D - E)).trans (mul_le_mul_of_nonneg_right
            (opNorm_comp_le I B) (norm_nonneg (D - E))))
          ((opNorm_comp_le (I ∘L (B - C)) E).trans (mul_le_mul_of_nonneg_right
            (opNorm_comp_le I (B - C)) (norm_nonneg E)))
      _ ≤ _ := by gcongr
  apply (le_div_iff₀ hq).2
  simp only [div_eq_mul_inv] at hbound ⊢
  nlinarith only [hbound]

/-- The tangent graph changes by at most the variational solution bound. The stable projection
cancels, and evaluation at zero has operator norm at most one. -/
theorem norm_fderiv_lyapunovPerronGraphMap_sub_le {d : ℝ}
    (hderiv : ∀ t,
      ‖N' (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ t) -
        M' (lyapunovPerronSolution A P M hs hu hα hM hsmall' ζ t)‖ ≤ d) :
    ‖fderiv ℝ (lyapunovPerronGraphMap A P N hs hu hα hN hsmall) ξ -
        fderiv ℝ (lyapunovPerronGraphMap A P M hs hu hα hM hsmall') ζ‖ ≤
      (2 * K / α * d * (K / (1 - 2 * K * ε' / α))) / (1 - 2 * K * ε / α) := by
  rw [fderiv_lyapunovPerronGraphMap hs hu hα hN hsmall hNs hN' hδ hξ,
    fderiv_lyapunovPerronGraphMap hs hu hα hM hsmall' hMs hM' hρ hζ,
    sub_sub_sub_cancel_right, ← comp_sub]
  let D := fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ -
    fderiv ℝ (lyapunovPerronSolution A P M hs hu hα hM hsmall') ζ
  have hnorm : ‖BoundedContinuousFunction.evalCLM ℝ 0 ∘L D‖ ≤ ‖D‖ :=
    (BoundedContinuousFunction.evalCLM ℝ 0 ∘L D).opNorm_le_bound (norm_nonneg D) fun v ↦
      ((D v).norm_coe_le_norm 0).trans (D.le_opNorm v)
  exact hnorm.trans (norm_fderiv_lyapunovPerronSolution_sub_le hs hu hα hN hM hsmall hsmall'
    hNs hN' hMs hM' hδ hρ hξ hζ hderiv)

end ContinuousLinearMap

end

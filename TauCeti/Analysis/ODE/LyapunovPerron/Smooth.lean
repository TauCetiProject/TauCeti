/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.ODE.LyapunovPerron.Graph
public import TauCeti.Analysis.ODE.LyapunovPerron.Linear
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction

/-!
# Smooth dependence of Lyapunov--Perron solutions on the parameter

Let `A` and `P` be bounded operators on a real Banach space `X` satisfying the forward and
backward exponential estimates of the Lyapunov--Perron construction, with constant `K` and rate
`α`, and let the nonlinearity `N` be `ε`-Lipschitz with `2 K ε < α`. The Lyapunov--Perron
solution `ContinuousLinearMap.lyapunovPerronSolution ξ` is the fixed point of the operator

`T ξ γ = (t ↦ exp (t A) (P ξ)) + I (N ∘ γ)`

on bounded continuous curves on `[0, ∞)`, where `I` is the bounded linear integral operator
`ContinuousLinearMap.lyapunovPerronIntegralCLM`. It is Lipschitz in `ξ`.

This file shows that it is `C¹` in `ξ` wherever the nonlinearity is `C¹` along the solution.
Suppose that `N` has derivative `N' x` at every point `x` of a set `s`, that `N'` is uniformly
continuous on `s`, and that the values of the solution with parameter `ξ₀` stay a fixed distance
`δ > 0` inside `s`. The superposition operator `γ ↦ N ∘ γ` is then `C¹` near that solution
(`BoundedContinuousFunction.contDiffAt_comp`), with derivative pointwise multiplication by
`N' (γ t)`, of operator norm at most `ε`. So the partial derivative in `γ` of the equation
`γ - T ξ γ = 0` is the identity minus an operator of norm at most `2 K ε / α < 1`, hence
invertible, and the implicit function theorem (`ContDiffAt.implicitFunction`) gives a `C¹`
solution of the equation near `ξ₀`. Uniqueness of fixed points of the contraction `T ξ`
identifies it with the Lyapunov--Perron solution.

Differentiating the fixed-point equation then shows that the derivative `η` in the direction `v`
solves the *variational* Lyapunov--Perron equation, the linearization of the integral equation
along the solution `γ₀`:

`η t = exp (t A) (P v) + lyapunovPerronIntegral A P (s ↦ N' (γ₀ s) (η s)) t`.

The Lyapunov--Perron graph map, the value at time `0` minus `P ξ`, is therefore `C¹` as well.
After a cutoff, the graph map describes the local stable manifold at a hyperbolic equilibrium
(`TauCeti/Analysis/ODE/LyapunovPerron/Local.lean`), so these results upgrade that Lipschitz graph
to a `C¹` one.

## Main declarations

* `ContinuousLinearMap.contDiffAt_lyapunovPerronSolution`: the Lyapunov--Perron solution is `C¹`
  in its parameter at every parameter whose solution stays a positive distance inside the region
  where the nonlinearity is `C¹` with uniformly continuous derivative.
* `ContinuousLinearMap.fderiv_lyapunovPerronSolution_apply`: its derivative solves the
  variational Lyapunov--Perron equation.
* `ContinuousLinearMap.contDiffAt_lyapunovPerronGraphMap`: the Lyapunov--Perron graph map is `C¹`
  at such parameters.

## References

* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  Section 4.3 (smoothness of the stable manifold via the fixed-point equation).
* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics 629, Springer,
  1978, Chapter 5.
-/

public section

open Metric NormedSpace Set Topology
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K α ε : ℝ≥0} {A P : X →L[ℝ] X} {N : X → X}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hN : LipschitzWith ε N) (hsmall : 2 * K * ε < α)

omit [CompleteSpace X] in
include hs in
/-- The homogeneous term of the Lyapunov--Perron equation is bounded by `K ‖ξ‖` in forward
time. -/
private theorem norm_exp_smul_apply_le (ξ : X) (t : ℝ≥0) :
    ‖exp ((t : ℝ) • A) (P ξ)‖ ≤ K * ‖ξ‖ :=
  calc ‖exp ((t : ℝ) • A) (P ξ)‖ ≤ K * Real.exp (-α * t) * ‖ξ‖ := hs t t.2 ξ
    _ ≤ K * 1 * ‖ξ‖ := by
      gcongr
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.2 α.coe_nonneg) t.2)
    _ = K * ‖ξ‖ := by ring

/-- The homogeneous term `ξ ↦ (t ↦ exp (t A) (P ξ))` of the Lyapunov--Perron equation, as a
bounded linear map into bounded continuous curves on `[0, ∞)`. -/
private def lyapunovPerronHomogeneousCLM : X →L[ℝ] (ℝ≥0 →ᵇ X) :=
  LinearMap.mkContinuous
    { toFun := fun ξ ↦ BoundedContinuousFunction.ofNormedAddCommGroup
        (fun t : ℝ≥0 ↦ exp ((t : ℝ) • A) (P ξ))
        (((differentiable_exp_smul_const ℝ A).continuous.comp NNReal.continuous_coe).clm_apply
          continuous_const)
        (K * ‖ξ‖) (norm_exp_smul_apply_le hs ξ)
      map_add' := fun ξ ζ ↦ by ext t; simp
      map_smul' := fun c ξ ↦ by ext t; simp }
    K fun ξ ↦ BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity)
      (norm_exp_smul_apply_le hs ξ)

private theorem lyapunovPerronHomogeneousCLM_apply (ξ : X) (t : ℝ≥0) :
    lyapunovPerronHomogeneousCLM hs ξ t = exp ((t : ℝ) • A) (P ξ) :=
  (rfl)

/-- The Lyapunov--Perron operator splits as the homogeneous term plus the integral operator
applied to the superposition `N ∘ γ`. -/
private theorem lyapunovPerronMap_eq_add (ξ : X) (γ : ℝ≥0 →ᵇ X) :
    lyapunovPerronMap A P N hs hu hα hN ξ γ =
      lyapunovPerronHomogeneousCLM hs ξ +
        lyapunovPerronIntegralCLM A P hs hu hα (γ.comp N hN) := by
  ext t
  simp [lyapunovPerronHomogeneousCLM_apply]

/-- The Lyapunov--Perron solution is the homogeneous term plus the integral operator applied to
the superposition of the nonlinearity with the solution. -/
private theorem lyapunovPerronSolution_eq_add (ξ : X) :
    lyapunovPerronSolution A P N hs hu hα hN hsmall ξ =
      lyapunovPerronHomogeneousCLM hs ξ + lyapunovPerronIntegralCLM A P hs hu hα
        ((lyapunovPerronSolution A P N hs hu hα hN hsmall ξ).comp N hN) := by
  rw [← lyapunovPerronMap_eq_add hs hu hα hN]
  exact (isFixedPt_lyapunovPerronSolution hs hu hα hN hsmall ξ).symm

include hsmall in
/-- Postcomposing pointwise multiplication by a family of operators of norm at most `ε` with the
Lyapunov--Perron integral operator gives an operator of norm less than `1`. -/
private theorem norm_lyapunovPerronIntegralCLM_comp_applyCLM_lt_one
    {Φ : ℝ≥0 →ᵇ (X →L[ℝ] X)} (hΦ : ‖Φ‖ ≤ ε) :
    ‖lyapunovPerronIntegralCLM A P hs hu hα ∘L BoundedContinuousFunction.applyCLM Φ‖ < 1 := by
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  have hsmallR : 2 * (K : ℝ) * ε < α := by exact_mod_cast hsmall
  calc _ ≤ ‖lyapunovPerronIntegralCLM A P hs hu hα‖ * ‖BoundedContinuousFunction.applyCLM Φ‖ :=
        opNorm_comp_le _ _
    _ ≤ 2 * K / α * ε := mul_le_mul (norm_lyapunovPerronIntegralCLM_le hs hu hα)
        ((BoundedContinuousFunction.norm_applyCLM_apply_le Φ).trans hΦ) (norm_nonneg _)
        (by positivity)
    _ = 2 * K * ε / α := by ring
    _ < 1 := (div_lt_one hαR).2 hsmallR

variable {N' : X → X →L[ℝ] X} {s : Set X} {δ : ℝ} {ξ₀ : X}

/-- Near a parameter whose solution stays a positive distance inside the region where the
nonlinearity is `C¹`, the Lyapunov--Perron solution agrees with a `C¹` function: the implicit
function of the equation `γ - T ξ γ = 0`. -/
private theorem exists_contDiffAt_eventuallyEq_lyapunovPerronSolution
    (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s) :
    ∃ ψ : X → ℝ≥0 →ᵇ X, ContDiffAt ℝ 1 ψ ξ₀ ∧
      ψ =ᶠ[𝓝 ξ₀] lyapunovPerronSolution A P N hs hu hα hN hsmall := by
  set γ₀ := lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀
  set E := lyapunovPerronHomogeneousCLM hs
  set I := lyapunovPerronIntegralCLM A P hs hu hα
  obtain ⟨Φ, hΦ⟩ := BoundedContinuousFunction.exists_eq_comp hN hNs hN'.continuousOn
    fun t ↦ hξ₀ t (mem_ball_self hδ)
  -- The equation `γ - T ξ γ = 0`, whose zeros are the Lyapunov--Perron solutions.
  set F : X × (ℝ≥0 →ᵇ X) → ℝ≥0 →ᵇ X := fun p ↦ p.2 - (E p.1 + I (p.2.comp N hN)) with hFdef
  have hF : ContDiffAt ℝ 1 F (ξ₀, γ₀) :=
    contDiffAt_snd.sub ((E.contDiff.contDiffAt.comp (ξ₀, γ₀) contDiffAt_fst).add
      (I.contDiff.contDiffAt.comp (ξ₀, γ₀)
        ((BoundedContinuousFunction.contDiffAt_comp hN hNs hN' hδ hξ₀).comp (ξ₀, γ₀)
          contDiffAt_snd)))
  have hsup : HasFDerivAt (fun p : X × (ℝ≥0 →ᵇ X) ↦ p.2.comp N hN)
      (BoundedContinuousFunction.applyCLM Φ ∘L snd ℝ X (ℝ≥0 →ᵇ X)) (ξ₀, γ₀) :=
    HasFDerivAt.comp (g := BoundedContinuousFunction.comp N hN) (f := Prod.snd) (ξ₀, γ₀)
      (BoundedContinuousFunction.hasFDerivAt_comp hN hNs hN' hδ hξ₀ hΦ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (ξ₀, γ₀)))
  have hF' : HasFDerivAt F (snd ℝ X (ℝ≥0 →ᵇ X) -
      (E ∘L fst ℝ X (ℝ≥0 →ᵇ X) +
        I ∘L BoundedContinuousFunction.applyCLM Φ ∘L snd ℝ X (ℝ≥0 →ᵇ X))) (ξ₀, γ₀) :=
    hasFDerivAt_snd.sub ((E.hasFDerivAt.comp (ξ₀, γ₀) hasFDerivAt_fst).add
      (I.hasFDerivAt.comp (ξ₀, γ₀) hsup))
  -- The partial derivative in `γ` is `1 - I ∘ (N' ∘ γ₀)`, a small perturbation of the identity.
  have hnorm : ‖I ∘L BoundedContinuousFunction.applyCLM Φ‖ < 1 :=
    norm_lyapunovPerronIntegralCLM_comp_applyCLM_lt_one hs hu hα hsmall <|
      (BoundedContinuousFunction.norm_le ε.coe_nonneg).2 fun t ↦ by
        rw [hΦ t]
        exact (hNs _ (hξ₀ t (mem_ball_self hδ))).le_of_lipschitz hN
  have hinv : (fderiv ℝ F (ξ₀, γ₀) ∘L inr ℝ X (ℝ≥0 →ᵇ X)).IsInvertible := by
    have hpartial : fderiv ℝ F (ξ₀, γ₀) ∘L inr ℝ X (ℝ≥0 →ᵇ X) =
        1 - I ∘L BoundedContinuousFunction.applyCLM Φ := by
      rw [hF'.fderiv]
      ext h : 1
      simp
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.ofUnit (isUnit_one_sub_of_norm_lt_one hnorm).unit, rfl⟩
  have hF0 : F (ξ₀, γ₀) = 0 := by
    rw [hFdef, sub_eq_zero]
    exact lyapunovPerronSolution_eq_add hs hu hα hN hsmall ξ₀
  refine ⟨hF.implicitFunction one_ne_zero hinv,
    hF.contDiffAt_implicitFunction one_ne_zero hinv, ?_⟩
  filter_upwards [hF.eventually_apply_implicitFunction one_ne_zero hinv] with ξ hξ
  -- A zero of the equation is a fixed point of the contraction `T ξ`, hence the solution.
  have hfix : hF.implicitFunction one_ne_zero hinv ξ =
      lyapunovPerronMap A P N hs hu hα hN ξ (hF.implicitFunction one_ne_zero hinv ξ) := by
    rw [lyapunovPerronMap_eq_add hs hu hα hN]
    exact sub_eq_zero.1 (hξ.trans hF0)
  exact eq_lyapunovPerronSolution hs hu hα hN hsmall fun t ↦ by
    rw [← lyapunovPerronMap_apply hs hu hα hN, ← hfix]

/-- **The Lyapunov--Perron solution is `C¹` in its parameter.** Suppose that the nonlinearity `N`
has derivative `N' x` at every point `x` of a set `s`, with `N'` uniformly continuous on `s`, and
that the values of the Lyapunov--Perron solution with parameter `ξ₀` stay a distance `δ > 0`
inside `s`. Then the solution, as a bounded continuous curve with the sup norm, depends
continuously differentiably on the parameter near `ξ₀`. -/
theorem contDiffAt_lyapunovPerronSolution
    (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s) :
    ContDiffAt ℝ 1 (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ :=
  let ⟨_, hψ, hψeq⟩ :=
    exists_contDiffAt_eventuallyEq_lyapunovPerronSolution hs hu hα hN hsmall hNs hN' hδ hξ₀
  hψ.congr_of_eventuallyEq hψeq.symm

/-- **The derivative of the Lyapunov--Perron solution solves the variational equation.** Under
the hypotheses of `ContinuousLinearMap.contDiffAt_lyapunovPerronSolution`, the derivative `η` of
the solution `γ₀` at `ξ₀` in the direction `v` satisfies the Lyapunov--Perron equation of the
linearization along `γ₀`:

`η t = exp (t A) (P v) + lyapunovPerronIntegral A P (s ↦ N' (γ₀ s) (η s)) t`. -/
theorem fderiv_lyapunovPerronSolution_apply
    (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s)
    (v : X) (t : ℝ≥0) :
    fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ v t =
      exp ((t : ℝ) • A) (P v) + lyapunovPerronIntegral A P
        (fun s ↦ N' (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ s.toNNReal)
          (fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ v s.toNNReal)) t := by
  set S := lyapunovPerronSolution A P N hs hu hα hN hsmall
  set D := fderiv ℝ S ξ₀
  obtain ⟨Φ, hΦ⟩ := BoundedContinuousFunction.exists_eq_comp hN hNs hN'.continuousOn
    fun t ↦ hξ₀ t (mem_ball_self hδ)
  have hS : HasFDerivAt S D ξ₀ :=
    ((contDiffAt_lyapunovPerronSolution hs hu hα hN hsmall hNs hN' hδ hξ₀).differentiableAt
      one_ne_zero).hasFDerivAt
  -- Differentiate the fixed-point identity `S ξ = E ξ + I (N ∘ S ξ)` at `ξ₀`.
  have hrhs : HasFDerivAt S (lyapunovPerronHomogeneousCLM hs +
      lyapunovPerronIntegralCLM A P hs hu hα ∘L BoundedContinuousFunction.applyCLM Φ ∘L D) ξ₀ := by
    have h := (lyapunovPerronHomogeneousCLM hs).hasFDerivAt.add
      ((lyapunovPerronIntegralCLM A P hs hu hα).hasFDerivAt.comp ξ₀
        ((BoundedContinuousFunction.hasFDerivAt_comp hN hNs hN' hδ hξ₀ hΦ).comp ξ₀ hS))
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ξ ↦
      lyapunovPerronSolution_eq_add hs hu hα hN hsmall ξ)
  have hD := congrArg (fun L : X →L[ℝ] ℝ≥0 →ᵇ X ↦ L v t) (hS.unique hrhs)
  simpa [lyapunovPerronHomogeneousCLM_apply, hΦ] using hD

/-- **The Lyapunov--Perron graph map is `C¹`** at every parameter whose solution stays a
positive distance inside the region where the nonlinearity is `C¹` with uniformly continuous
derivative. -/
theorem contDiffAt_lyapunovPerronGraphMap
    (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s) :
    ContDiffAt ℝ 1 (lyapunovPerronGraphMap A P N hs hu hα hN hsmall) ξ₀ := by
  have hgraph : lyapunovPerronGraphMap A P N hs hu hα hN hsmall =
      fun ξ ↦ BoundedContinuousFunction.evalCLM ℝ 0
        (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ) - P ξ := by
    funext ξ
    rw [BoundedContinuousFunction.evalCLM_apply,
      lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap, add_sub_cancel_left]
  rw [hgraph]
  exact ((BoundedContinuousFunction.evalCLM ℝ 0).contDiff.contDiffAt.comp ξ₀
    (contDiffAt_lyapunovPerronSolution hs hu hα hN hsmall hNs hN' hδ hξ₀)).sub
    P.contDiff.contDiffAt

end ContinuousLinearMap

end

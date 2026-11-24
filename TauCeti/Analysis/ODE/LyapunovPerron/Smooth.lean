/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Calculus.ContDiff.UniformOn
public import TauCeti.Analysis.ODE.LyapunovPerron.Graph
public import TauCeti.Analysis.ODE.LyapunovPerron.Linear
import TauCeti.Analysis.Calculus.Contracting
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
If `N` is uniformly `C^n` on `s` (`TauCeti.UniformContDiffOn`), the same argument with
`BoundedContinuousFunction.contDiffAt_comp_of_uniformContDiffOn` gives a `C^n` solution and graph
map. After a cutoff, the graph map describes the local stable manifold at a hyperbolic equilibrium
(`TauCeti/Analysis/ODE/LyapunovPerron/Local.lean`), so these results upgrade that Lipschitz graph
to a `C¹` one.

## Main declarations

* `ContinuousLinearMap.contDiffAt_lyapunovPerronSolution_of_uniformContDiffOn`: the
  Lyapunov--Perron solution is `C^n` in its parameter when the nonlinearity is uniformly `C^n`
  near the solution.
* `ContinuousLinearMap.contDiffAt_lyapunovPerronSolution`: the Lyapunov--Perron solution is `C¹`
  in its parameter at every parameter whose solution stays a positive distance inside the region
  where the nonlinearity is `C¹` with uniformly continuous derivative.
* `ContinuousLinearMap.fderiv_lyapunovPerronSolution_apply`: its derivative solves the
  variational Lyapunov--Perron equation.
* `ContinuousLinearMap.contDiffAt_lyapunovPerronGraphMap_of_uniformContDiffOn`: the graph map is
  `C^n` at such parameters.
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

variable {N' : X → X →L[ℝ] X} {s : Set X} {δ : ℝ} {ξ₀ : X}

/-- **The Lyapunov--Perron solution is `C^n` in its parameter.** Suppose that the nonlinearity `N`
is uniformly `C^n` on a set `s` (`TauCeti.UniformContDiffOn`), and that the values
of the Lyapunov--Perron solution with parameter `ξ₀` stay a distance `δ > 0` inside `s`. Then the
solution, as a bounded continuous curve with the sup norm, is `C^n` in the parameter near `ξ₀`. -/
theorem contDiffAt_lyapunovPerronSolution_of_uniformContDiffOn {n : ℕ}
    (hNn : TauCeti.UniformContDiffOn ℝ n N s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s) :
    ContDiffAt ℝ n (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ := by
  cases n with
  | zero =>
    exact (contDiff_zero.2 (lipschitzWith_lyapunovPerronSolution hs hu hα hN hsmall).continuous
      ).contDiffAt
  | succ m =>
    apply ContractingWith.contDiffAt_of_isFixedPt
      (F := lyapunovPerronMap A P N hs hu hα hN)
      (fun ξ ↦ contractingWith_lyapunovPerronMap hs hu hα hN hsmall ξ)
      (isFixedPt_lyapunovPerronSolution hs hu hα hN hsmall) (by simp)
    have hT : Function.uncurry (lyapunovPerronMap A P N hs hu hα hN) =
        fun p : X × (ℝ≥0 →ᵇ X) ↦ lyapunovPerronHomogeneousCLM hs p.1 +
          lyapunovPerronIntegralCLM A P hs hu hα (p.2.comp N hN) :=
      funext fun p ↦ lyapunovPerronMap_eq_add hs hu hα hN p.1 p.2
    rw [hT]
    exact ((lyapunovPerronHomogeneousCLM hs).contDiff.contDiffAt.comp _ contDiffAt_fst).add
      ((lyapunovPerronIntegralCLM A P hs hu hα).contDiff.contDiffAt.comp _
        ((BoundedContinuousFunction.contDiffAt_comp_of_uniformContDiffOn hN hNn hδ hξ₀).comp
          (ξ₀, lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀) contDiffAt_snd))

/-- **The Lyapunov--Perron solution is `C¹` in its parameter.** Suppose that the nonlinearity `N`
has derivative `N' x` at every point `x` of a set `s`, with `N'` uniformly continuous on `s`, and
that the values of the Lyapunov--Perron solution with parameter `ξ₀` stay a distance `δ > 0`
inside `s`. Then the solution, as a bounded continuous curve with the sup norm, depends
continuously differentiably on the parameter near `ξ₀`. -/
theorem contDiffAt_lyapunovPerronSolution
    (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s) :
    ContDiffAt ℝ 1 (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ :=
  contDiffAt_lyapunovPerronSolution_of_uniformContDiffOn hs hu hα hN hsmall
    (hN.uniformContDiffOn_one hNs hN') hδ hξ₀

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

/-- **The Lyapunov--Perron graph map is `C^n`** at every parameter whose solution stays
a positive distance inside the region where the nonlinearity is uniformly `C^n`. -/
theorem contDiffAt_lyapunovPerronGraphMap_of_uniformContDiffOn {n : ℕ}
    (hNn : TauCeti.UniformContDiffOn ℝ n N s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s) :
    ContDiffAt ℝ n (lyapunovPerronGraphMap A P N hs hu hα hN hsmall) ξ₀ := by
  rw [lyapunovPerronGraphMap_eq_evalCLM_sub]
  exact ((BoundedContinuousFunction.evalCLM ℝ 0).contDiff.contDiffAt.comp ξ₀
    (contDiffAt_lyapunovPerronSolution_of_uniformContDiffOn hs hu hα hN hsmall hNn hδ hξ₀)).sub
    P.contDiff.contDiffAt

/-- **The Lyapunov--Perron graph map is `C¹`** at every parameter whose solution stays a
positive distance inside the region where the nonlinearity is `C¹` with uniformly continuous
derivative. -/
theorem contDiffAt_lyapunovPerronGraphMap
    (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s) :
    ContDiffAt ℝ 1 (lyapunovPerronGraphMap A P N hs hu hα hN hsmall) ξ₀ :=
  contDiffAt_lyapunovPerronGraphMap_of_uniformContDiffOn hs hu hα hN hsmall
    (hN.uniformContDiffOn_one hNs hN') hδ hξ₀

/-- The derivative of a Lyapunov--Perron graph is evaluation at zero of the derivative of
its bounded forward solution, minus the fixed stable projection. -/
theorem fderiv_lyapunovPerronGraphMap
    (hNs : ∀ x ∈ s, HasFDerivAt N (N' x) x) (hN' : UniformContinuousOn N' s) (hδ : 0 < δ)
    (hξ₀ : ∀ t, ball (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ₀ t) δ ⊆ s) :
    fderiv ℝ (lyapunovPerronGraphMap A P N hs hu hα hN hsmall) ξ₀ =
      BoundedContinuousFunction.evalCLM ℝ 0 ∘L
        fderiv ℝ (lyapunovPerronSolution A P N hs hu hα hN hsmall) ξ₀ - P := by
  have hS := ((contDiffAt_lyapunovPerronSolution hs hu hα hN hsmall
    hNs hN' hδ hξ₀).differentiableAt one_ne_zero).hasFDerivAt
  have h := ((BoundedContinuousFunction.evalCLM ℝ 0).hasFDerivAt.comp ξ₀ hS).sub
    P.hasFDerivAt
  rw [lyapunovPerronGraphMap_eq_evalCLM_sub]
  exact h.fderiv

end ContinuousLinearMap

end

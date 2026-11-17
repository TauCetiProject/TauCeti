/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Smooth
public import TauCeti.Analysis.Calculus.Contracting
import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction
public import TauCeti.Topology.ContinuousMap.Bounded.Parameter

/-!
# Smooth families of Lyapunov--Perron graphs

Fix an exponential dichotomy and let its small Lipschitz remainder vary with a parameter.
The bounded forward solution and the stable graph depend jointly `C^n` on this parameter
and the stable coordinate. The differentiability is in the sup norm on the whole forward
half-line, not merely pointwise in time. Evaluation at zero gives the graph theorem.

The remainders have a common small Lipschitz bound in the state variable. No Lipschitz
bound in the auxiliary parameter is imposed. Joint regularity is needed only on a uniform
neighborhood of the base solution. Thus a Lipschitz cutoff outside that neighborhood
need not be smooth. The parameter may itself be a Banach
space, provided the stated uniform regularity holds. These are fixed-dichotomy results;
localizing a family of vector fields and transferring its graphs to manifold charts are
separate steps.

## References

* C. Chicone, *Ordinary Differential Equations with Applications*, second edition,
  Springer, 2006, §4.3 (parameter dependence of invariant manifolds).
* W. A. Coppel, *Dichotomies in Stability Theory*, Springer, 1978, Chapter 5.
-/

public section

open Function Metric NormedSpace Set
open scoped ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace ContinuousLinearMap

variable {Λ X : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {A P : X →L[ℝ] X} {K α ε : ℝ≥0} {N : Λ → X → X}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hN : ∀ p, LipschitzWith ε (N p)) (hsmall : 2 * K * ε < α)
  {s : Set (Λ × X)} {p₀ : Λ} {ξ₀ : X} {δ : ℝ}
  (hδ : 0 < δ)
  (hconf : ∀ t, ball (p₀, lyapunovPerronSolution A P (N p₀) hs hu hα (hN p₀)
    hsmall ξ₀ t) δ ⊆ s)

include hδ hconf

/-- The bounded forward solution is jointly `C^n` in the remainder parameter and stable
coordinate, under uniform `C^n` regularity near the base solution. -/
theorem contDiffAt_lyapunovPerronSolution_family {n : ℕ} (hn : 1 ≤ n)
    (hreg : TauCeti.UniformContDiffOn ℝ n (uncurry N) s) :
    ContDiffAt ℝ n (fun p : Λ × X ↦
      lyapunovPerronSolution A P (N p.1) hs hu hα (hN p.1) hsmall p.2) (p₀, ξ₀) := by
  let L := BoundedContinuousFunction.parameterLift ℝ ℝ≥0 Λ X
  let Θ : Λ × (ℝ≥0 →ᵇ X) → (ℝ≥0 →ᵇ X) := fun q ↦ q.2.comp (N q.1) (hN q.1)
  let γ₀ := lyapunovPerronSolution A P (N p₀) hs hu hα (hN p₀) hsmall ξ₀
  obtain ⟨Ψ, hΨ, hΨeq⟩ := BoundedContinuousFunction.exists_contDiffAt_superposition
    (f₀ := L (p₀, γ₀)) hreg hδ
    (by simpa only [L, BoundedContinuousFunction.parameterLift_apply, γ₀] using hconf)
    (γ₀.comp (N p₀) (hN p₀)) (fun t ↦ by
      simp only [L, BoundedContinuousFunction.parameterLift_apply, uncurry,
        BoundedContinuousFunction.comp_apply])
  have hΘ : ContDiffAt ℝ n Θ (p₀, γ₀) := by
    apply (hΨ.comp (p₀, γ₀) L.contDiff.contDiffAt).congr_of_eventuallyEq
    filter_upwards [L.continuous.continuousAt.preimage_mem_nhds hΨeq] with q hq
    exact BoundedContinuousFunction.ext fun t ↦ by
      simpa only [Θ, L, BoundedContinuousFunction.parameterLift_apply,
        BoundedContinuousFunction.comp_apply, uncurry, Function.comp_apply] using (hq t).symm
  let T : (Λ × X) → (ℝ≥0 →ᵇ X) → (ℝ≥0 →ᵇ X) := fun p ↦
    lyapunovPerronMap A P (N p.1) hs hu hα (hN p.1) p.2
  have hT : uncurry T = fun z : (Λ × X) × (ℝ≥0 →ᵇ X) ↦
      lyapunovPerronHomogeneousCLM hs z.1.2 +
        lyapunovPerronIntegralCLM A P hs hu hα (Θ (z.1.1, z.2)) := by
    ext z t
    simp [uncurry, T, Θ, lyapunovPerronMap_apply, lyapunovPerronIntegralCLM_apply]
  have hTsmooth : ContDiffAt ℝ n (uncurry T) ((p₀, ξ₀), γ₀) := by
    rw [hT]
    exact ((lyapunovPerronHomogeneousCLM hs).contDiff.contDiffAt.comp _
      (contDiffAt_snd.comp _ contDiffAt_fst)).add
      ((lyapunovPerronIntegralCLM A P hs hu hα).contDiff.contDiffAt.comp _
        (hΘ.comp ((p₀, ξ₀), γ₀)
          ((contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd)))
  exact ContractingWith.contDiffAt_of_isFixedPt (F := T) (n := (n : ℕ∞ω))
    (fun p ↦ contractingWith_lyapunovPerronMap hs hu hα (hN p.1) hsmall p.2)
    (fun p ↦ isFixedPt_lyapunovPerronSolution hs hu hα (hN p.1) hsmall p.2)
    (by exact_mod_cast Nat.ne_zero_of_lt hn) hTsmooth

/-- The stable graph depends jointly `C^n` on the remainder parameter and stable coordinate.
The graph is read against the same fixed projection `P` throughout the family. -/
theorem contDiffAt_lyapunovPerronGraphMap_family {n : ℕ} (hn : 1 ≤ n)
    (hreg : TauCeti.UniformContDiffOn ℝ n (uncurry N) s) :
    ContDiffAt ℝ n (fun p : Λ × X ↦
      lyapunovPerronGraphMap A P (N p.1) hs hu hα (hN p.1) hsmall p.2) (p₀, ξ₀) := by
  simp only [lyapunovPerronGraphMap_eq_evalCLM_sub]
  exact ((BoundedContinuousFunction.evalCLM ℝ 0).contDiff.contDiffAt.comp _
    (contDiffAt_lyapunovPerronSolution_family hs hu hα hN hsmall hδ hconf hn hreg)).sub
    (P.contDiff.contDiffAt.comp _ contDiffAt_snd)

end ContinuousLinearMap

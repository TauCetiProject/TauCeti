/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.SimpleFunc.SquareApproximation
public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.Finance.SimpleStrategy.Energy

/-!
# Finite-valued approximations to squared Brownian samples

For a fixed finite nondecreasing time grid, squared Brownian left-endpoint
samples admit explicit finite-valued predictable approximations. The height on
`(τ j, τ (j + 1)]` is `TauCeti.dyadicSquareApprox k (B (τ j))`. These are actual
simple functions for the predictable sigma-algebra, and converge in time-product
`L²` to the left-step process with heights `B (τ j)²`.

Only the fourth moments of the finitely many Gaussian samples are used. No path
continuity, usual filtration conditions, or moment of a path supremum is needed.
Repeated dates, arbitrary first dates and horizons, and the empty grid are allowed.
This is the value-approximation step in constructing the integral of `B²` from
bounded elementary integrands; taking the time mesh to zero is a separate step.

The construction uses Mathlib's `SimpleFunc.comp`, the existing
`TauCeti.Finance.simpleHolding`, and its predictable-measure energy API.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.2–§3.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open TauCeti TauCeti.Finance TauCeti.Probability
open scoped Topology NNReal ENNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {τ : ℕ → ℝ≥0} {n : ℕ}

/-- Squared Brownian left samples are limits in time-product `L²` of predictable
simple functions with the specified dyadic heights. Each approximant is in `L²`,
and its equality to the elementary holding is pointwise, including grid endpoints. -/
theorem exists_simpleFunc_sq_simpleHolding (hB : IsPreBrownianReal B P) (hBa : Adapted ℱ B)
    (hτ : MonotoneOn τ (Iic n)) (T : ℝ≥0) :
    ∃ K : ℕ → @SimpleFunc (ℝ≥0 × Ω) ℱ.predictable ℝ,
      (∀ k t ω, K k (t, ω) =
        simpleHolding τ n (fun j ω ↦ dyadicSquareApprox k (B (τ j) ω)) t ω) ∧
      (∀ k, MemLp (K k) 2 ((timeMeasure T).prod P)) ∧
      Tendsto (fun k ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦ K k p -
        simpleHolding τ n (fun j ω ↦ B (τ j) ω ^ 2) p.1 p.2)
          2 ((timeMeasure T).prod P)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hH : IsStronglyPredictable ℱ (simpleHolding τ n (fun j ↦ B (τ j))) :=
    isStronglyPredictable_simpleHolding fun j _ ↦ (hBa (τ j)).stronglyMeasurable
  have hHsq : IsStronglyPredictable ℱ
      (simpleHolding τ n (fun j ω ↦ B (τ j) ω ^ 2)) :=
    isStronglyPredictable_simpleHolding fun j _ ↦
      ((hBa (τ j)).pow_const 2).stronglyMeasurable
  have heq (t : ℝ≥0) (ω : Ω) :
      simpleHolding τ n (fun j ω ↦ B (τ j) ω ^ 2) t ω =
        simpleHolding τ n (fun j ↦ B (τ j)) t ω ^ 2 :=
    simpleHolding_comp hτ (fun x ↦ x ^ 2) (by norm_num) t ω
  have hsq : MemLp (fun p : ℝ≥0 × Ω ↦
      simpleHolding τ n (fun j ↦ B (τ j)) p.1 p.2 ^ 2) 2 ((timeMeasure T).prod P) := by
    have hheight (j : ℕ) : MemLp (fun ω ↦ B (τ j) ω ^ 2) 2 P := by
      let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by
        norm_num [Real.holderTriple_iff])
      have h := (hB.hasLaw_eval (τ j)).memLp (memLp_id_gaussianReal' 4 (by simp))
      simpa only [pow_two, Pi.mul_def] using h.mul h
    have h := memLp_simpleHolding_predictableMeasure
      (fun j (_ : j < n) ↦ ((hBa (τ j)).pow_const 2).stronglyMeasurable)
      (fun j _ ↦ hheight j) T
    rw [ℱ.memLp_predictableMeasure_iff P hHsq T 2] at h
    have hfun : Function.uncurry (simpleHolding τ n (fun j ω ↦ B (τ j) ω ^ 2)) =
        (fun p : ℝ≥0 × Ω ↦ simpleHolding τ n (fun j ↦ B (τ j)) p.1 p.2 ^ 2) :=
      funext fun p ↦ heq p.1 p.2
    rwa [hfun] at h
  let K (k : ℕ) : @SimpleFunc (ℝ≥0 × Ω) ℱ.predictable ℝ :=
    @SimpleFunc.comp _ _ _ ℱ.predictable _ (dyadicSquareApprox k)
      (Function.uncurry (simpleHolding τ n (fun j ↦ B (τ j)))) hH.measurable
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (simpleHolding τ n (fun j ↦ B (τ j)))) ((timeMeasure T).prod P) :=
    (hH.mono ℱ.predictable_le_prod).aestronglyMeasurable
  refine ⟨K, ?_, ?_, ?_⟩
  · intro k t ω
    exact (simpleHolding_comp hτ (dyadicSquareApprox k)
      (dyadicSquareApprox_zero k) t ω).symm
  · intro k
    exact memLp_dyadicSquareApprox_comp k hmeas hsq
  · simpa only [K, SimpleFunc.coe_comp, Function.comp_apply, Function.uncurry, heq] using
      tendsto_eLpNorm_dyadicSquareApprox_sub_sq hmeas hsq

end ProbabilityTheory.IsPreBrownianReal

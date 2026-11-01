/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.Regularization

/-!
# Monotonicity along a direction from the sign of a distributional derivative

Let `u` be a locally integrable function on a finite-dimensional real normed space `E` with an
additive Haar measure `μ`, and let `v ∈ E`. If the distributional derivative `∂_v u` is
nonpositive, that is `0 ≤ ∫ ∂_v ψ * u dμ` for every nonnegative test function `ψ`, then `u`
decreases in the direction `v`: `u (x + v) ≤ u x` for almost every `x`
(`TauCeti.ae_apply_add_le_of_forall_integral_lineDeriv_mul_nonneg`). Applied to `v` and `-v`, a
vanishing derivative `∂_v u = 0` makes `u` almost everywhere invariant under translation by `v`.

No differentiability of `u` is assumed. The regularizations `x ↦ ∫ ρ (y - x) u y dμ` of `u` by
nonnegative bumps `ρ` are smooth, with derivative in the direction `v` given by pairing `∂_v u`
with a translate of `ρ` (`Distribution.fderiv_translatePairing_apply`). They are therefore
nonincreasing along every line parallel to `v`
(`Distribution.antitoneOn_translatePairing_add_smul`). For normalized bumps they are convolutions
(`Distribution.translatePairing_ofFun_normedTestFunction`), and they converge to `u` almost
everywhere as the bumps shrink (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`).

For an indicator function this says that a set whose outer normal has a nonnegative component
along `v` contains, up to a null set, its translate by `-v`; this is how sets whose perimeter
measure has a constant normal are identified with half-spaces.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2 (the mollification argument in the proof of the blow-up theorem).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter LineDeriv
open ContinuousLinearMap (lsmul)
open scoped Distributions Topology Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → ℝ} {v : E}

/-- **A function with nonpositive distributional derivative in the direction `v` decreases in
that direction.** If `u` is locally integrable and `0 ≤ ∫ ∂_v ψ * u dμ` for every nonnegative test
function `ψ`, then `u (x + v) ≤ u x` for almost every `x`. -/
theorem ae_apply_add_le_of_forall_integral_lineDeriv_mul_nonneg (hu : LocallyIntegrable u μ)
    (h : ∀ ψ : 𝓓((⊤ : Opens E), ℝ), (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, ∂_{v} ψ x * u x ∂μ) :
    ∀ᵐ x ∂μ, u (x + v) ≤ u x := by
  set T : 𝓓'((⊤ : Opens E), ℝ) := Distribution.ofFun (⊤ : Opens E) u μ ⊤
  -- The regularization of `u` by a nonnegative test function decreases along `v`.
  have hanti (ρ : 𝓓((⊤ : Opens E), ℝ)) (hρ : ∀ x, 0 ≤ ρ x) (x : E) :
      T.translatePairing ρ (x + v) ≤ T.translatePairing ρ x := by
    have hT (φ : 𝓓((⊤ : Opens E), ℝ)) (hφ : ∀ y, 0 ≤ φ y) : 0 ≤ T (∂_{v} φ) := by
      rw [Distribution.ofFun_apply (hu.locallyIntegrableOn _)]
      exact h φ hφ
    simpa using T.antitoneOn_translatePairing_add_smul hT hρ convex_univ
      (fun _ _ _ _ => trivial) (mem_univ 0) (mem_univ 1) zero_le_one
  -- Regularize by normalized bumps shrinking to the origin.
  let ρ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking one_pos
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := μ) (K := 2)
    (ContDiffBump.tendsto_rOut_shrinking one_pos)
    (Eventually.of_forall fun n => (ContDiffBump.rOut_shrinking_eq_two_mul_rIn one_pos n).le) hu
  filter_upwards [hae, (measurePreserving_add_right μ v).quasiMeasurePreserving.ae hae]
    with x hx hxv
  refine le_of_tendsto_of_tendsto' hxv hx fun n => ?_
  rw [← Distribution.translatePairing_ofFun_normedTestFunction hu,
    ← Distribution.translatePairing_ofFun_normedTestFunction hu]
  exact hanti _ (fun z => by simpa using (ρ n).nonneg_normed (μ := μ) z) x

end TauCeti

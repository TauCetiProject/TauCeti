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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
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
nonincreasing along every line parallel to `v`, and they converge to `u` almost everywhere as the
bumps shrink (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`).

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
  have hT (φ : 𝓓((⊤ : Opens E), ℝ)) : T φ = ∫ x, φ x * u x ∂μ :=
    Distribution.ofFun_apply (hu.locallyIntegrableOn _)
  have hmaps (ρ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
      MapsTo (· + x) (tsupport ρ) ((⊤ : Opens E) : Set E) := fun _ _ => trivial
  -- Every translate `ρ (· - x)` of a test function is a test function.
  have htr (ρ : 𝓓((⊤ : Opens E), ℝ)) (x : E) : ∃ φ : 𝓓((⊤ : Opens E), ℝ), ∀ z, φ z = ρ (z - x) :=
    ⟨translateTestFunction (h := x) (V := ⊤) (fun _ _ => trivial) ρ,
      translateTestFunction_apply _ _⟩
  -- The regularization of `u` by a nonnegative test function decreases along `v`.
  have hanti (ρ : 𝓓((⊤ : Opens E), ℝ)) (hρ : ∀ x, 0 ≤ ρ x) (x : E) :
      T.translatePairing ρ (x + v) ≤ T.translatePairing ρ x := by
    have hd (y : E) : (∂_{v} T).translatePairing ρ y ≤ 0 := by
      obtain ⟨φ, hφ⟩ := htr ρ y
      rw [Distribution.translatePairing_eq _ hφ, Distribution.lineDerivOp_apply_apply, map_neg,
        hT, neg_nonpos]
      exact h φ fun z => (hφ z).symm ▸ hρ _
    have hg (t : ℝ) : HasDerivAt (fun t : ℝ => T.translatePairing ρ (x + t • v))
        ((∂_{v} T).translatePairing ρ (x + t • v)) t := by
      have hline : HasDerivAt (fun t : ℝ => x + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x
      have := (T.differentiableAt_translatePairing ρ (hmaps ρ _)).hasFDerivAt.comp_hasDerivAt t
        hline
      rwa [T.fderiv_translatePairing_apply ρ (hmaps ρ _)] at this
    have hmono := antitone_of_deriv_nonpos (fun t => (hg t).differentiableAt)
      (fun t => (hg t).deriv ▸ hd _) zero_le_one
    simpa using hmono
  -- Normalized bumps shrinking to the origin, as test functions.
  let ρ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hb (n : ℕ) : ∃ φ : 𝓓((⊤ : Opens E), ℝ), ∀ z, φ z = (ρ n).normed μ z :=
    ⟨⟨(ρ n).normed μ, (ρ n).contDiff_normed, (ρ n).hasCompactSupport_normed, by simp⟩,
      fun _ => rfl⟩
  choose bump hbump using hb
  -- The regularization by a normalized bump is the convolution with it.
  have hconv (n : ℕ) (x : E) :
      T.translatePairing (bump n) x = ((ρ n).normed μ ⋆[lsmul ℝ ℝ, μ] u) x := by
    obtain ⟨φ, hφ⟩ := htr (bump n) x
    rw [T.translatePairing_eq hφ, hT, convolution_lsmul_swap]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [hφ, hbump, smul_eq_mul, ← neg_sub, (ρ n).normed_neg]
  have hlim : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := μ) (K := 2)
    hlim (Eventually.of_forall fun n => le_of_eq (by ring)) hu
  filter_upwards [hae, (measurePreserving_add_right μ v).quasiMeasurePreserving.ae hae]
    with x hx hxv
  refine le_of_tendsto_of_tendsto' hxv hx fun n => ?_
  rw [← hconv, ← hconv]
  exact hanti _ (fun z => (hbump n z).symm ▸ (ρ n).nonneg_normed _) x

end TauCeti

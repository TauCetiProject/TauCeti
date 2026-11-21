/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# Directional derivatives of tempered distributions

Mathlib defines the directional derivative of a tempered distribution by duality,
`(∂_m f) u = f (-∂_m u)`. Since directional derivatives of Schwartz functions commute
(`SchwartzMap.lineDerivOp_comm`), so do those of tempered distributions. On the plane `ℂ` the
Laplacian of a tempered distribution is then `∂₁² f + ∂₂² f`, with `∂₁` and `∂₂` the derivatives
along `1` and `I`, as for Schwartz functions (`SchwartzMap.laplacian_eq_lineDerivOp_one_I`). These
are the identities needed to compute compositions of constant-coefficient first-order operators
on tempered distributions. Directional differentiation of the tempered distribution given by a
Schwartz function also commutes with a continuous real-linear map applied to its values, and its
iterated directional derivatives are those of the Schwartz function; likewise, the distributional
directional derivatives of bounded `C^k` functions agree with their classical derivatives.

## Main results

* `TemperedDistribution.lineDerivOp_comm`: `∂_v ∂_w f = ∂_w ∂_v f`.
* `TemperedDistribution.laplacian_eq_lineDerivOp_one_I`: `Δ f = ∂₁² f + ∂₂² f` on `ℂ`.
* `TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_postcompCLM`:
  `∂_v (L ∘ f) = L ∘ ∂_v f` for a Schwartz function `f` viewed as a tempered distribution.
* `TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq`: iterated directional
  derivatives of a Schwartz function viewed as a tempered distribution.
* `BoundedContinuousFunction.lineDerivOp_toLpTop_eq` and
  `BoundedContinuousFunction.iteratedLineDerivOp_toLpTop_eq`: distributional directional and
  iterated directional derivatives of bounded differentiable and `C^k` functions.
-/

public section

namespace TemperedDistribution

open MeasureTheory SchwartzMap
open scoped SchwartzMap LineDeriv Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- **Directional derivatives of tempered distributions commute.** -/
theorem lineDerivOp_comm (f : 𝓢'(E, F)) (v w : E) : ∂_{v} (∂_{w} f) = ∂_{w} (∂_{v} f) := by
  ext u
  simp [SchwartzMap.lineDerivOp_comm u]

/-- **The Laplacian on the plane in coordinates**: `Δ f = ∂₁² f + ∂₂² f` for a tempered
distribution `f` on `ℂ`, where `∂₁` and `∂₂` differentiate along `1` and `I`. -/
theorem laplacian_eq_lineDerivOp_one_I (f : 𝓢'(ℂ, F)) :
    Δ f = ∂_{(1 : ℂ)} (∂_{(1 : ℂ)} f) + ∂_{Complex.I} (∂_{Complex.I} f) := by
  simp [laplacian_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Directional differentiation of the tempered distribution given by a Schwartz function commutes
with a continuous real-linear map applied to the values of the function. -/
theorem lineDerivOp_toTemperedDistributionCLM_postcompCLM (L : G →L[ℝ] F) (f : 𝓢(E, G)) (m : E) :
    ∂_{m} (toTemperedDistributionCLM E F μ (f.postcompCLM L)) =
      toTemperedDistributionCLM E F μ ((∂_{m} f).postcompCLM L) := by
  rw [lineDerivOp_toTemperedDistributionCLM_eq, TauCeti.lineDerivOp_postcompCLM]

/-- Iterated directional derivatives of the tempered distribution given by a Schwartz function are
the tempered distributions of its iterated directional derivatives. -/
theorem iteratedLineDerivOp_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) {k : ℕ} (m : Fin k → E) :
    ∂^{m} (toTemperedDistributionCLM E F μ f) = toTemperedDistributionCLM E F μ (∂^{m} f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_toTemperedDistributionCLM_eq]

end TemperedDistribution

namespace BoundedContinuousFunction

open MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

/-- **Distributional directional derivative of a bounded differentiable function.** If `f` and `g`
are bounded continuous with `f` differentiable and `g x = fderiv ℝ f x v`, then `∂_v f = g` in
`𝓢'(E, F)` for any additive Haar measure `μ`. -/
theorem lineDerivOp_toLpTop_eq {μ : Measure E} [μ.IsAddHaarMeasure] {f g : E →ᵇ F}
    (hf : Differentiable ℝ f) (v : E) (hg : ∀ x, g x = fderiv ℝ f x v) :
    ∂_{v} (toLpTop μ ℂ f : 𝓢'(E, F)) = (toLpTop μ ℂ g : 𝓢'(E, F)) :=
  TauCeti.lineDerivOp_toTemperedDistribution_eq_of_hasLineDerivAt f.continuous.locallyIntegrable
    g.continuous.locallyIntegrable (coeFn_toLpTop μ f) (coeFn_toLpTop μ g)
    fun x ↦ (hg x).symm ▸ (hf x).hasFDerivAt.hasLineDerivAt v

/-- **Distributional iterated directional derivatives of bounded `C^k` functions.** If `f` is
bounded `C^k` with bounded derivatives of order `< k` and `g` is bounded continuous with
`g x = iteratedFDeriv ℝ k f x v`, then `∂^v f = g` in `𝓢'(E, F)` for any additive Haar
measure `μ`. -/
theorem iteratedLineDerivOp_toLpTop_eq {μ : Measure E} [μ.IsAddHaarMeasure] {k : ℕ} {f g : E →ᵇ F}
    (hf : ContDiff ℝ k f) (hbdd : ∀ i < k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (v : Fin k → E) (hg : ∀ x, g x = iteratedFDeriv ℝ k f x v) :
    ∂^{v} (toLpTop μ ℂ f : 𝓢'(E, F)) = (toLpTop μ ℂ g : 𝓢'(E, F)) := by
  induction k generalizing g with
  | zero =>
    have hfg : f = g := by
      ext x
      simpa only [iteratedFDeriv_zero_apply] using (hg x).symm
    simp [hfg]
  | succ k ih =>
    obtain ⟨C, hC⟩ := hbdd k (Nat.lt_succ_self k)
    have hcont : Continuous fun x ↦ iteratedFDeriv ℝ k f x (Fin.tail v) :=
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (Fin.tail v)).continuous).comp
        (hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ k))
    have hbd : ∀ x, ‖iteratedFDeriv ℝ k f x (Fin.tail v)‖ ≤ C * ∏ i, ‖Fin.tail v i‖ := fun x ↦
      (ContinuousMultilinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC x) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
    set g' : E →ᵇ F := ofNormedAddCommGroup (fun x ↦ iteratedFDeriv ℝ k f x (Fin.tail v))
      hcont (C * ∏ i, ‖Fin.tail v i‖) hbd
    have hih : ∂^{Fin.tail v} (toLpTop μ ℂ f : 𝓢'(E, F)) = (toLpTop μ ℂ g' : 𝓢'(E, F)) :=
      ih (hf.of_le (by exact_mod_cast Nat.le_succ k))
        (fun i hi ↦ hbdd i (hi.trans (Nat.lt_succ_self k))) (Fin.tail v)
        fun x ↦ by simp only [g', coe_ofNormedAddCommGroup]
    have hdiff : ∀ x, HasFDerivAt (g' : E → F)
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (Fin.tail v)).comp
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F
            (iteratedFDeriv ℝ (k + 1) f x))) x := fun x ↦ by
      have hF : HasFDerivAt (iteratedFDeriv ℝ k f)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F
            (iteratedFDeriv ℝ (k + 1) f x)) x := by
        have h := (hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k) x
          ).hasFDerivAt
        rwa [fderiv_iteratedFDeriv] at h
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (Fin.tail v)).hasFDerivAt.comp
        x hF
    rw [LineDeriv.iteratedLineDerivOp_succ_left, hih]
    refine lineDerivOp_toLpTop_eq (fun x ↦ (hdiff x).differentiableAt) (v 0) fun x ↦ ?_
    rw [hg x, (hdiff x).fderiv]
    simp [Fin.cons_self_tail]

end BoundedContinuousFunction

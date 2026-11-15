/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Directional derivatives of tempered distributions

Mathlib defines the directional derivative of a tempered distribution by duality,
`(∂_m f) u = f (-∂_m u)`. Since directional derivatives of Schwartz functions commute
(`SchwartzMap.lineDerivOp_comm`), so do those of tempered distributions. On the plane `ℂ` the
Laplacian of a tempered distribution is then `∂₁² f + ∂₂² f`, with `∂₁` and `∂₂` the derivatives
along `1` and `I`, as for Schwartz functions (`SchwartzMap.laplacian_eq_lineDerivOp_one_I`). These
are the identities needed to compute compositions of constant-coefficient first-order operators
on tempered distributions. Directional differentiation of the tempered distribution given by a
Schwartz function also commutes with a continuous real-linear map applied to its values.

## Main results

* `TemperedDistribution.lineDerivOp_comm`: `∂_v ∂_w f = ∂_w ∂_v f`.
* `TemperedDistribution.laplacian_eq_lineDerivOp_one_I`: `Δ f = ∂₁² f + ∂₂² f` on `ℂ`.
* `TemperedDistribution.iteratedLineDerivOp_apply_apply`: `(∂^{w} f) u = (-1) ^ j f (∂^{w ∘ rev} u)`
  for `w : Fin j → E`.
* `TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq`: `∂^{w}` of the tempered
  distribution given by a Schwartz function `f` is the tempered distribution of `∂^{w} f`.
* `TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_postcompCLM`:
  `∂_v (L ∘ f) = L ∘ ∂_v f` for a Schwartz function `f` viewed as a tempered distribution.
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

/-- Repeated directional differentiation of a tempered distribution transfers to the Schwartz
function in reverse order, with sign `(-1) ^ j`. -/
@[simp]
theorem iteratedLineDerivOp_apply_apply (f : 𝓢'(E, F)) {j : ℕ} (w : Fin j → E) (u : 𝓢(E, ℂ)) :
    (∂^{w} f) u = (-1 : ℂ) ^ j • f (∂^{w ∘ Fin.rev} u) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, lineDerivOp_apply_apply, map_neg, ih,
      LineDeriv.iteratedLineDerivOp_succ_right, pow_succ, mul_smul]
    simp [Fin.init_def, Fin.tail_def, Function.comp_def, Fin.rev_castSucc]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Directional differentiation of the tempered distribution given by a Schwartz function commutes
with a continuous real-linear map applied to the values of the function. -/
theorem lineDerivOp_toTemperedDistributionCLM_postcompCLM (L : G →L[ℝ] F) (f : 𝓢(E, G)) (m : E) :
    ∂_{m} (toTemperedDistributionCLM E F μ (f.postcompCLM L)) =
      toTemperedDistributionCLM E F μ ((∂_{m} f).postcompCLM L) := by
  rw [lineDerivOp_toTemperedDistributionCLM_eq, TauCeti.lineDerivOp_postcompCLM]

/-- Repeated directional differentiation of the tempered distribution given by a Schwartz function
is the tempered distribution of its repeated directional derivative. -/
theorem iteratedLineDerivOp_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) {j : ℕ} (w : Fin j → E) :
    ∂^{w} (toTemperedDistributionCLM E F μ f) = toTemperedDistributionCLM E F μ (∂^{w} f) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_toTemperedDistributionCLM_eq]

end TemperedDistribution

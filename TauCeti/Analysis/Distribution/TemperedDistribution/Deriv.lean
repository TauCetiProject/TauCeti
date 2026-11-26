/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

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
iterated directional derivatives are those of the Schwartz function.

## Main results

* `TemperedDistribution.iteratedLineDerivOp_apply_apply`: `(∂^m f) u = (-1)^n f (∂^(m ∘ rev) u)`,
  so iterated derivatives transfer to the Schwartz function in reverse order.
* `TemperedDistribution.iteratedLineDerivOp_delta_apply`:
  `(∂^m δ_x) f = (-1) ^ n D^n f(x) (m ∘ rev)`.
* `TemperedDistribution.lineDerivOp_comm`: `∂_v ∂_w f = ∂_w ∂_v f`.
* `TemperedDistribution.laplacian_eq_lineDerivOp_one_I`: `Δ f = ∂₁² f + ∂₂² f` on `ℂ`.
* `TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_postcompCLM`:
  `∂_v (L ∘ f) = L ∘ ∂_v f` for a Schwartz function `f` viewed as a tempered distribution.
* `TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq`: iterated directional
  derivatives of a Schwartz function viewed as a tempered distribution.

For a real `Lᵖ` function `u`, the directional derivative `∂_v u` of its complexified tempered
distribution pairs with a real Schwartz function `φ` as `-∫ ∂_v φ u`, the usual definition of a weak
derivative.

* `MeasureTheory.Lp.lineDerivOp_toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM`:
  `(∂_v u) φ = -∫ ∂_v φ u` for real `u ∈ Lᵖ` and real Schwartz `φ`.

On the Fourier side a directional derivative is multiplication by `2πi ⟪ξ, v⟫`
(`TemperedDistribution.fourier_lineDerivOp_eq`). For `L²` functions, whose Fourier transforms are
again `L²` functions, this becomes an identity of functions almost everywhere. Its use is to turn a
constant-coefficient differential equation satisfied by `L²` functions in the sense of
distributions into an algebraic relation between their Fourier transforms.

* `MeasureTheory.Lp.coeFn_fourier_of_lineDerivOp_eq`: if `∂_v f = g` for `f, g ∈ L²` as tempered
  distributions, then `𝓕 g (ξ) = 2πi ⟪ξ, v⟫ 𝓕 f (ξ)` for almost every `ξ`.
* `MeasureTheory.Lp.sum_smul_coeFn_fourier_of_sum_lineDerivOp_eq`: if
  `∑ⱼ ∂_{aⱼ} fⱼ = ∑ⱼ ∂_{bⱼ} gⱼ` for `fⱼ, gⱼ ∈ L²`, then
  `∑ⱼ ⟪ξ, aⱼ⟫ 𝓕 fⱼ (ξ) = ∑ⱼ ⟪ξ, bⱼ⟫ 𝓕 gⱼ (ξ)` for almost every `ξ`.
-/

public section

namespace TemperedDistribution

open MeasureTheory SchwartzMap
open scoped SchwartzMap LineDeriv Laplacian

/-- Repeated directional differentiation of a tempered distribution transfers to the Schwartz
function in reverse order with sign `(-1)^n`. -/
@[simp]
theorem iteratedLineDerivOp_apply_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousConstSMul ℂ F] (f : 𝓢'(E, F)) {n : ℕ} (m : Fin n → E) (u : 𝓢(E, ℂ)) :
    (∂^{m} f) u = (-1 : ℂ) ^ n • f (∂^{m ∘ Fin.rev} u) := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, lineDerivOp_apply_apply, map_neg, ih,
      LineDeriv.iteratedLineDerivOp_succ_right, pow_succ, mul_smul]
    simp [Fin.init_def, Fin.tail_def, Function.comp_def, Fin.rev_castSucc]

/-- The iterated derivative `∂^m δ_x` of the Dirac distribution at `x` evaluates the iterated
derivative of a Schwartz function at `x` on the reversed tuple, with sign `(-1) ^ n`. -/
theorem iteratedLineDerivOp_delta_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) {n : ℕ} (m : Fin n → E) (f : 𝓢(E, ℂ)) :
    (∂^{m} (delta x)) f = (-1) ^ n * iteratedFDeriv ℝ n f x (m ∘ Fin.rev) := by
  rw [iteratedLineDerivOp_apply_apply, delta_apply,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, smul_eq_mul]

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
  rw [lineDerivOp_toTemperedDistributionCLM_eq, SchwartzMap.lineDerivOp_postcompCLM]

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

namespace MeasureTheory.Lp

open SchwartzMap
open scoped SchwartzMap LineDeriv FourierTransform InnerProductSpace ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

omit [FiniteDimensional ℝ E] in
/-- The derivative in the direction `v` of the complex tempered distribution of a real `Lᵖ`
function `u`, evaluated at a real Schwartz function `φ`, is `-∫ ∂_v φ u`. -/
theorem lineDerivOp_toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM {μ : Measure E}
    [μ.HasTemperateGrowth] {p : ENNReal} [Fact (1 ≤ p)] (u : Lp ℝ p μ) (v : E) (φ : 𝓢(E, ℝ)) :
    (∂_{v} ((Complex.ofRealCLM.compLp u : Lp ℂ p μ) : 𝓢'(E, ℂ))) (φ.postcompCLM Complex.ofRealCLM) =
      -((∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ : ℝ) : ℂ) := by
  rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg, SchwartzMap.lineDerivOp_postcompCLM,
    toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM]
  simp only [SchwartzMap.lineDerivOp_apply]

/-- Pairing an `L²` function `f` with `∂_v` of the Fourier transform of a Schwartz function `φ`
is pairing `𝓕 f` with `-2πi ⟪·, v⟫ φ`. -/
private theorem toTemperedDistribution_lineDerivOp_fourier (f : Lp F 2 (volume : Measure E))
    (v : E) (φ : 𝓢(E, ℂ)) :
    (f : 𝓢'(E, F)) (∂_{v} (𝓕 φ)) =
      ∫ ξ, φ ξ • ((-(2 * Real.pi * Complex.I) * ⟪ξ, v⟫_ℝ) • 𝓕 f ξ) := by
  have ht : (fun ξ : E => ⟪ξ, v⟫_ℝ).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.lineDerivOp_fourier_eq, ← TemperedDistribution.fourier_apply,
    fourier_toTemperedDistribution_eq, toTemperedDistribution_apply]
  refine integral_congr_ae (.of_forall fun ξ => ?_)
  simp only [smul_apply, smulLeftCLM_apply_apply ht, smul_smul, Complex.real_smul]
  congr 1
  ring

/-- **The Fourier transform of a distributional derivative.** If the tempered distribution of
`g ∈ L²` is the derivative in the direction `v` of that of `f ∈ L²`, then
`𝓕 g (ξ) = 2πi ⟪ξ, v⟫ 𝓕 f (ξ)` for almost every `ξ`. -/
theorem coeFn_fourier_of_lineDerivOp_eq {f g : Lp F 2 (volume : Measure E)} {v : E}
    (h : ∂_{v} (f : 𝓢'(E, F)) = (g : 𝓢'(E, F))) :
    (𝓕 g : Lp F 2 (volume : Measure E)) =ᵐ[volume]
      fun ξ => (2 * Real.pi * Complex.I * ⟪ξ, v⟫_ℝ) • 𝓕 f ξ := by
  refine ae_eq_of_toTemperedDistribution_apply_eq _
    (((Lp.memLp (𝓕 f)).locallyIntegrable (by norm_num)).continuous_smul (by fun_prop))
    fun φ => ?_
  rw [← fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply, ← h,
    TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    toTemperedDistribution_lineDerivOp_fourier, ← integral_neg]
  refine integral_congr_ae (.of_forall fun ξ => ?_)
  dsimp only
  rw [smul_smul, smul_smul, ← neg_smul]
  congr 1
  ring

/-- **Fourier transform of an identity between sums of derivatives.** If
`∑ⱼ ∂_{aⱼ} fⱼ = ∑ⱼ ∂_{bⱼ} gⱼ` as tempered distributions, with `fⱼ, gⱼ ∈ L²`, then
`∑ⱼ ⟪ξ, aⱼ⟫ 𝓕 fⱼ (ξ) = ∑ⱼ ⟪ξ, bⱼ⟫ 𝓕 gⱼ (ξ)` for almost every `ξ`. -/
theorem sum_smul_coeFn_fourier_of_sum_lineDerivOp_eq {ι : Type*} [Fintype ι]
    {f g : ι → Lp F 2 (volume : Measure E)} {a b : ι → E}
    (h : ∑ j, ∂_{a j} (f j : 𝓢'(E, F)) = ∑ j, ∂_{b j} (g j : 𝓢'(E, F))) :
    (fun ξ => ∑ j, (⟪ξ, a j⟫_ℝ : ℂ) • 𝓕 (f j) ξ) =ᵐ[volume]
      fun ξ => ∑ j, (⟪ξ, b j⟫_ℝ : ℂ) • 𝓕 (g j) ξ := by
  have hloc : ∀ (k : Lp F 2 (volume : Measure E)) (c : E),
      LocallyIntegrable (fun ξ => (⟪ξ, c⟫_ℝ : ℂ) • 𝓕 k ξ) volume := fun k c =>
    ((Lp.memLp (𝓕 k)).locallyIntegrable (by norm_num)).continuous_smul (by fun_prop)
  -- Evaluating `∑ⱼ ∂_{cⱼ} kⱼ` at `𝓕 φ` integrates `φ` against `2πi ∑ⱼ ⟪ξ, cⱼ⟫ 𝓕 kⱼ`.
  have key : ∀ (k : ι → Lp F 2 (volume : Measure E)) (c : ι → E) (φ : 𝓢(E, ℂ)),
      HasCompactSupport φ →
      (∑ j, ∂_{c j} (k j : 𝓢'(E, F))) (𝓕 φ) =
        (2 * Real.pi * Complex.I) • ∫ ξ, φ ξ • ∑ j, (⟪ξ, c j⟫_ℝ : ℂ) • 𝓕 (k j) ξ := by
    intro k c φ hφ
    have hint : ∀ j, Integrable (fun ξ => φ ξ • ((⟪ξ, c j⟫_ℝ : ℂ) • 𝓕 (k j) ξ)) volume :=
      fun j => (hloc (k j) (c j)).integrable_smul_left_of_hasCompactSupport φ.continuous hφ
    simp only [sum_apply, TemperedDistribution.lineDerivOp_apply_apply, map_neg,
      toTemperedDistribution_lineDerivOp_fourier, Finset.smul_sum,
      integral_finsetSum _ fun j _ => hint j, ← integral_smul, ← integral_neg]
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae (.of_forall fun ξ => ?_)
    dsimp only
    rw [smul_smul, smul_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  refine ae_eq_of_integral_contDiff_smul_eq
    (by simpa using locallyIntegrable_finsetSum _ fun j _ => hloc (f j) (a j))
    (by simpa using locallyIntegrable_finsetSum _ fun j _ => hloc (g j) (b j))
    fun ψ hψ hψc => ?_
  -- A smooth compactly supported real function is a complex Schwartz function.
  have hψ₁ : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hψc.comp_left rfl
  have hψ₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have h' := congrArg (fun T : 𝓢'(E, F) => T (𝓕 (hψ₁.toSchwartzMap hψ₂))) h
  rw [key _ _ (hψ₁.toSchwartzMap hψ₂) hψ₁, key _ _ (hψ₁.toSchwartzMap hψ₂) hψ₁] at h'
  simpa [Complex.coe_smul] using
    smul_right_injective F (by simp [Real.pi_ne_zero, Complex.I_ne_zero]) h'

end MeasureTheory.Lp

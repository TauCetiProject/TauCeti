/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Translation
public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Smooth approximate identities in arbitrary-order Sobolev spaces

On the whole space, average translations of a function in `W^{k,p}` against a normalized smooth
bump. Translation preserves every weak derivative and the full iterated graph norm, so this gives
a contraction on `W^{k,p}`. For `p < ∞`, strong continuity of translation implies that these
averages converge in the Sobolev norm when the bump radii tend to zero.

The value and every highest weak derivative of the Sobolev average are the corresponding `Lᵖ`
averages. These identities make the construction usable together with the pointwise convolution
and smoothness theory for mollifiers.

The argument is the standard mollification proof from L. C. Evans, *Partial Differential
Equations*, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open ContinuousLinearMap Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

private theorem integrable_normed_smul_translate_neg (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) (k : ℕ) (u : Wkp mu ⊤ p k) :
    Integrable (fun t => phi.normed (mu.restrict ((⊤ : Opens E) : Set E)) t •
      translate (-t) k u) (mu.restrict ((⊤ : Opens E) : Set E)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact phi.continuous_normed.smul
      ((continuous_translate hp k u).comp continuous_neg)
  · exact phi.hasCompactSupport_normed.smul_right

/-- The normalized-bump average of a whole-space Sobolev function before it is bundled as a
continuous linear operator. -/
private def normedBumpFun (_hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p k) : Wkp mu ⊤ p k :=
  ∫ t, phi.normed (mu.restrict ((⊤ : Opens E) : Set E)) t • translate (-t) k u
    ∂(mu.restrict ((⊤ : Opens E) : Set E))

private theorem normedBumpFun_add (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u v : Wkp mu ⊤ p k) :
    normedBumpFun hp phi k (u + v) =
      normedBumpFun hp phi k u + normedBumpFun hp phi k v := by
  rw [normedBumpFun, normedBumpFun, normedBumpFun,
    ← integral_add (integrable_normed_smul_translate_neg hp phi k u)
      (integrable_normed_smul_translate_neg hp phi k v)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [← translateLIE_apply, map_add, smul_add]

private theorem normedBumpFun_smul (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (c : ℝ) (u : Wkp mu ⊤ p k) :
    normedBumpFun hp phi k (c • u) = c • normedBumpFun hp phi k u := by
  rw [normedBumpFun, normedBumpFun, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [← translateLIE_apply, map_smul, smul_smul, mul_comm c]

private theorem norm_normedBumpFun_le (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p k) :
    ‖normedBumpFun hp phi k u‖ ≤ ‖u‖ := by
  calc
    ‖normedBumpFun hp phi k u‖ ≤
        ∫ t, ‖phi.normed (mu.restrict ((⊤ : Opens E) : Set E)) t •
          translate (-t) k u‖ ∂(mu.restrict ((⊤ : Opens E) : Set E)) := by
      rw [normedBumpFun]
      exact norm_integral_le_of_norm_le
        (integrable_normed_smul_translate_neg hp phi k u).norm
        (Eventually.of_forall fun _ => le_rfl)
    _ = ∫ t, phi.normed (mu.restrict ((⊤ : Opens E) : Set E)) t * ‖u‖
          ∂(mu.restrict ((⊤ : Opens E) : Set E)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t), norm_translate]
    _ = ‖u‖ := by rw [integral_mul_const, phi.integral_normed, one_mul]

/-- Mollification by a normalized smooth bump on the whole-space Sobolev space `W^{k,p}`, as a
continuous linear operator. It averages the Sobolev translations in the Bochner sense. -/
def normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (k : ℕ) :
    Wkp mu ⊤ p k →L[ℝ] Wkp mu ⊤ p k :=
  LinearMap.mkContinuous
    { toFun := normedBumpFun hp phi k
      map_add' := normedBumpFun_add hp phi k
      map_smul' := normedBumpFun_smul hp phi k } 1
    fun u => by rw [one_mul]; exact norm_normedBumpFun_le hp phi k u

/-- The defining Bochner-integral formula for Sobolev mollification. -/
theorem normedBumpL_apply (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p k) :
    normedBumpL hp phi k u =
      ∫ t, phi.normed (mu.restrict ((⊤ : Opens E) : Set E)) t • translate (-t) k u
        ∂(mu.restrict ((⊤ : Opens E) : Set E)) := by
  rw [normedBumpL]
  rfl

/-- Mollification by a normalized nonnegative bump does not increase the `W^{k,p}` norm. -/
theorem norm_normedBumpL_le_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (k : ℕ) :
    ‖normedBumpL (mu := mu) hp phi k‖ ≤ 1 := by
  rw [normedBumpL]
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The value of a Sobolev mollification is the `Lᵖ` mollification of its value. -/
@[simp]
theorem value_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p k) :
    value k (normedBumpL hp phi k u) =
      TauCeti.normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) (value k u) := by
  rw [normedBumpL_apply, TauCeti.normedBumpLp_apply,
    ← valueL_apply,
    ← (valueL k).integral_comp_comm (integrable_normed_smul_translate_neg hp phi k u)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_smul, valueL_apply, value_translate]

/-- At order zero, Sobolev mollification is the existing `Lᵖ` approximate identity. -/
@[simp]
theorem normedBumpL_zero (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    normedBumpL (mu := mu) hp phi 0 =
      TauCeti.normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext 0
  rw [value_normedBumpL, value_zero, value_zero]

/-- Mollification commutes with forgetting the highest weak derivative. -/
@[simp]
theorem lowerOrder_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) :
    lowerOrder k (normedBumpL hp phi (k + 1) u) =
      normedBumpL hp phi k (lowerOrder k u) := by
  rw [normedBumpL_apply, normedBumpL_apply,
    ← lowerOrderL_apply,
    ← (lowerOrderL k).integral_comp_comm
      (integrable_normed_smul_translate_neg hp phi (k + 1) u)]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul, lowerOrderL_apply, lowerOrder_translate]

/-- The highest weak derivative of a Sobolev mollification is the `Lᵖ` mollification of the
highest weak derivative. -/
@[simp]
theorem iteratedGradient_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) :
    iteratedGradient k (normedBumpL hp phi (k + 1) u) =
      TauCeti.normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E))
        (iteratedGradient k u) := by
  rw [normedBumpL_apply, TauCeti.normedBumpLp_apply,
    ← iteratedGradientL_apply,
    ← (iteratedGradientL k).integral_comp_comm
      (integrable_normed_smul_translate_neg hp phi (k + 1) u)]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul, iteratedGradientL_apply, iteratedGradient_translate]

/-- **Smooth approximate identity in `W^{k,p}(ℝⁿ)`.** Normalized smooth bumps whose
outer radii tend to zero converge strongly to the identity on every finite-exponent whole-space
Sobolev space. -/
theorem tendsto_normedBumpL (hp : p ≠ ∞) {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (nhds 0))
    (k : ℕ) (u : Wkp mu ⊤ p k) :
    Tendsto (fun i => normedBumpL hp (phi i) k u) l (nhds u) := by
  have hval : ∀ i, normedBumpL hp (phi i) k u =
      ((phi i).normed (mu.restrict ((⊤ : Opens E) : Set E)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, mu.restrict ((⊤ : Opens E) : Set E)]
          fun h => translate h k u) 0 := fun i => by
    rw [normedBumpL_apply, convolution_lsmul]
    simp only [zero_sub]
  simpa only [hval, translate_zero] using
    ContDiffBump.convolution_tendsto_right_of_continuous hphi
      (continuous_translate hp k u) (0 : E)

end TauCeti.Wkp

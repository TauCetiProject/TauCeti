/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential
public import TauCeti.Analysis.Convolution.Holder
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian

/-!
# Fixed-disc Hölder bounds for the planar Newtonian potential

On a fixed output disc the logarithmic kernel may be truncated at the sum of the input and
output radii. Its finite `L¹` norm then controls the potential's supremum and Hölder constant.
The constants depend on the two discs, not on derivatives of the source.
-/

public noncomputable section

open MeasureTheory Metric Set ContinuousLinearMap
open scoped Convolution NNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℂ → F} {c w : ℂ} {r R : ℝ}

/-- The logarithmic kernel cut off at a finite radius is integrable, including at its pole. -/
theorem integrable_indicator_planarNewtonianKernel (ρ : ℝ) :
    Integrable ((closedBall (0 : ℂ) ρ).indicator planarNewtonianKernel) :=
  (locallyIntegrable_planarNewtonianKernel.integrableOn_isCompact
    (isCompact_closedBall 0 ρ)).integrable_indicator (measurableSet_closedBall)

/-- On the output disc, the Newtonian potential equals convolution with the logarithmic
kernel cut off at the sum of the input and output radii. -/
theorem planarNewtonianKernel_convolution_eq_indicator
    (hs : Function.support f ⊆ closedBall c r) (hw : w ∈ closedBall c R) :
    (planarNewtonianKernel ⋆ f) w =
      ∫ z, (closedBall (0 : ℂ) (r + R)).indicator planarNewtonianKernel z • f (w - z) := by
  rw [convolution_def]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ (indicator_kernel_smul_sub_eq hs hw z).symm

/-- The `L¹` norm of the truncated logarithmic kernel bounds the Newtonian potential on
a fixed output disc. -/
theorem norm_planarNewtonianKernel_convolution_le
    (hs : Function.support f ⊆ closedBall c r) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (hw : w ∈ closedBall c R) :
    ‖(planarNewtonianKernel ⋆ f) w‖ ≤
      (∫ z, ‖(closedBall (0 : ℂ) (r + R)).indicator planarNewtonianKernel z‖) * M := by
  rw [planarNewtonianKernel_convolution_eq_indicator hs hw]
  exact norm_integral_kernel_smul_sub_le (integrable_indicator_planarNewtonianKernel _) hM w

/-- The Newtonian potential preserves the source Hölder exponent on every fixed output disc,
with a constant depending only on the support and output radii. -/
theorem holderOnWith_planarNewtonianKernel_convolution
    {H α : ℝ≥0} (hα : 0 < α) (hf : HolderWith H α f)
    (hs : Function.support f ⊆ closedBall c r) :
    HolderOnWith
      ((∫ z, ‖(closedBall (0 : ℂ) (r + R)).indicator planarNewtonianKernel z‖).toNNReal * H)
      α (planarNewtonianKernel ⋆ f) (closedBall c R) := by
  have hc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
  obtain ⟨M, hM⟩ := (hf.continuous hα).bounded_above_of_compact_support hc
  have h := (holderWith_integral_kernel_smul_sub
    (integrable_indicator_planarNewtonianKernel (r + R)) hα hf hM).holderOnWith (closedBall c R)
  intro w hw v hv
  rw [planarNewtonianKernel_convolution_eq_indicator hs hw,
    planarNewtonianKernel_convolution_eq_indicator hs hv]
  exact h w hw v hv

end TauCeti

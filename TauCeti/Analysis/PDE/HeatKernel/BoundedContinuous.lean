/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Heat regularization of bounded continuous data

`TauCeti.heatCauchyPotentialBCF` bundles the Cauchy heat potential as a contraction on bounded
continuous functions. At positive times its spatial derivatives of every order are bounded,
and it is Lipschitz even when the initial datum is only bounded and continuous. For complete
targets it acts as the identity at nonpositive times.

The analytic inputs are the Cauchy potential estimates and the derivative bounds for heat
convolutions in `TauCeti.Analysis.PDE.HeatKernel.HeatEquation`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 4.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (diffusion on bounded uniformly continuous functions).
-/

public section

noncomputable section

namespace TauCeti

open BoundedContinuousFunction MeasureTheory
open scoped Convolution ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Cauchy heat potential as a bounded operator on bounded continuous functions. For complete
targets, negative times, like time zero, act as the identity. -/
def heatCauchyPotentialBCF (t : ℝ) : (E →ᵇ F) →L[ℝ] (E →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := fun g => BoundedContinuousFunction.ofNormedAddCommGroup
        (heatCauchyPotential g t)
        ((continuous_heatCauchyPotential g.continuous g.norm_coe_le_norm).comp
          (continuous_const.prodMk continuous_id))
        ‖g‖ (norm_heatCauchyPotential_le g.norm_coe_le_norm t)
      map_add' := fun g h => BoundedContinuousFunction.ext fun x =>
        heatCauchyPotential_add g.continuous g.norm_coe_le_norm h.continuous h.norm_coe_le_norm t x
      map_smul' := fun c g => BoundedContinuousFunction.ext fun x =>
        heatCauchyPotential_smul c g t x }
    1 (fun g => (BoundedContinuousFunction.norm_le (norm_nonneg g)).2
      (norm_heatCauchyPotential_le g.norm_coe_le_norm t) |>.trans_eq (one_mul _).symm)

/-- Pointwise evaluation of the bounded heat regularization. -/
@[simp]
theorem heatCauchyPotentialBCF_apply (t : ℝ) (g : E →ᵇ F) (x : E) :
    heatCauchyPotentialBCF t g x = heatCauchyPotential g t x :=
  (rfl)

/-- Heat regularization does not increase the supremum norm. -/
theorem norm_heatCauchyPotentialBCF_le (t : ℝ) :
    ‖heatCauchyPotentialBCF (E := E) (F := F) t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => ?_
  simpa only [one_mul] using (BoundedContinuousFunction.norm_le (norm_nonneg g)).2
    (norm_heatCauchyPotential_le g.norm_coe_le_norm t)

/-- At positive times the bounded heat regularization is convolution with the heat kernel. -/
theorem coe_heatCauchyPotentialBCF_of_pos {t : ℝ} (ht : 0 < t) (g : E →ᵇ F) :
    (heatCauchyPotentialBCF t g : E → F) = heatKernel t ⋆ (g : E → F) :=
  funext fun x => heatCauchyPotential_eq_convolution g ht x

/-- A positive-time heat regularization has bounded spatial derivatives of every order. -/
theorem norm_iteratedFDeriv_heatCauchyPotentialBCF_le {t : ℝ} (ht : 0 < t)
    (g : E →ᵇ F) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (heatCauchyPotentialBCF t g) x‖ ≤
      (∫ z, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖) * ‖g‖ := by
  rw [coe_heatCauchyPotentialBCF_of_pos ht]
  exact norm_iteratedFDeriv_heatKernel_convolution_le ht g.continuous.aestronglyMeasurable
    (ae_of_all _ g.norm_coe_le_norm) m x

/-- Heat regularization at positive time is Lipschitz, even for merely bounded continuous data.
The explicit constant is the `L¹` norm of the kernel's first derivative times the data norm. -/
theorem lipschitzWith_heatCauchyPotentialBCF {t : ℝ} (ht : 0 < t) (g : E →ᵇ F) :
    LipschitzWith ⟨(∫ z, ‖iteratedFDeriv ℝ 1 (heatKernel t : E → ℝ) z‖) * ‖g‖,
      mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _)⟩
      (heatCauchyPotentialBCF t g) := by
  rw [coe_heatCauchyPotentialBCF_of_pos ht]
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_heatKernel_convolution ht g.continuous.aestronglyMeasurable
      (ae_of_all _ g.norm_coe_le_norm)).differentiable (by simp))
  intro x
  have hbound := norm_iteratedFDeriv_heatKernel_convolution_le ht
    g.continuous.aestronglyMeasurable (ae_of_all _ g.norm_coe_le_norm) 1 x
  rw [norm_iteratedFDeriv_one] at hbound
  exact_mod_cast hbound

variable [CompleteSpace F]

/-- At nonpositive times the bounded heat regularization is the identity. -/
@[simp]
theorem heatCauchyPotentialBCF_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    heatCauchyPotentialBCF (E := E) (F := F) t = ContinuousLinearMap.id ℝ _ := by
  ext g x
  exact heatCauchyPotential_of_nonpos g ht x

end TauCeti

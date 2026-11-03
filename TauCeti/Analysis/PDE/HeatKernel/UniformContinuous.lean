/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.CauchyPotential
public import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
public import TauCeti.Topology.ContinuousMap.Bounded.UniformContinuous
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Heat regularization of bounded uniformly continuous data

The Cauchy heat potential acts by contractions on bounded continuous functions. At positive
times its spatial derivatives of every order are bounded, and it is Lipschitz even when the
initial datum is only bounded and continuous. Restricting to the closed subspace of bounded
uniformly continuous functions gives `TauCeti.heatCauchyPotentialBUC`.

On that subspace the regularizations converge in supremum norm to the initial datum. In
particular, smooth functions with bounded derivatives of every order are dense there, with no
increase of the supremum norm. Such approximants allow comparison estimates for smooth-data
parabolic problems to pass to uniformly continuous initial traces. This file asserts neither
solvability for variable coefficients nor a uniform bound on derivatives as time tends to zero.

The analytic inputs are the derivative bounds for heat convolutions in
`TauCeti.Analysis.PDE.HeatKernel.HeatEquation` and the uniform approximate-identity theorem
`TauCeti.tendstoUniformly_heatKernel_convolution`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 4.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (diffusion on bounded uniformly continuous functions).
-/

public section

noncomputable section

namespace TauCeti

open BoundedContinuousFunction Filter MeasureTheory
open scoped Topology Convolution ContDiff

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

/-- The heat regularization preserves uniform continuity, including at nonpositive times. -/
theorem uniformContinuous_heatCauchyPotentialBCF (t : ℝ) (g : E →ᵇ F)
    (hg : UniformContinuous g) : UniformContinuous (heatCauchyPotentialBCF t g) := by
  rcases le_or_gt t 0 with ht | ht
  · rw [heatCauchyPotentialBCF_of_nonpos ht]
    exact hg
  · exact (lipschitzWith_heatCauchyPotentialBCF ht g).uniformContinuous

/-- Heat regularization on the closed subspace of bounded uniformly continuous functions. -/
def heatCauchyPotentialBUC (t : ℝ) :
    uniformContinuousSubmodule ℝ E F →L[ℝ] uniformContinuousSubmodule ℝ E F :=
  ((heatCauchyPotentialBCF t).comp (uniformContinuousSubmodule ℝ E F).subtypeL).codRestrict
    (uniformContinuousSubmodule ℝ E F).toSubmodule
    (fun g => (mem_uniformContinuousSubmodule _).2
      (uniformContinuous_heatCauchyPotentialBCF t g.val
        ((mem_uniformContinuousSubmodule _).1 g.property)))

/-- The bounded continuous function underlying heat regularization on the uniformly continuous
subspace is the usual bounded heat regularization. -/
@[simp]
theorem coe_heatCauchyPotentialBUC (t : ℝ) (g : uniformContinuousSubmodule ℝ E F) :
    (heatCauchyPotentialBUC t g).val = heatCauchyPotentialBCF t g.val :=
  (rfl)

/-- At nonpositive times heat regularization on bounded uniformly continuous functions is the
identity. In particular, this gives the time-zero initial value. -/
@[simp]
theorem heatCauchyPotentialBUC_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    heatCauchyPotentialBUC (E := E) (F := F) t = ContinuousLinearMap.id ℝ _ := by
  ext g : 1
  apply Subtype.ext
  simp only [coe_heatCauchyPotentialBUC, heatCauchyPotentialBCF_of_nonpos ht,
    ContinuousLinearMap.id_apply]

/-- The heat operator on bounded uniformly continuous functions is a contraction. -/
theorem norm_heatCauchyPotentialBUC_le (t : ℝ) :
    ‖heatCauchyPotentialBUC (E := E) (F := F) t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => ?_
  rw [← ClosedSubmodule.norm_coe, coe_heatCauchyPotentialBUC]
  exact (heatCauchyPotentialBCF (E := E) (F := F) t).le_of_opNorm_le
    (norm_heatCauchyPotentialBCF_le t) g.val

/-- **Uniform attainment of the initial trace.** Heat regularizations of bounded uniformly
continuous data converge in the inherited supremum norm as `t → 0⁺`. -/
theorem tendsto_heatCauchyPotentialBUC (g : uniformContinuousSubmodule ℝ E F) :
    Tendsto (fun t : ℝ => heatCauchyPotentialBUC t g) (𝓝[>] 0) (𝓝 g) := by
  rw [tendsto_subtype_rng]
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  have heq : (fun t : ℝ => (heatCauchyPotentialBUC t g).val : ℝ → E → F) =ᶠ[𝓝[>] 0]
      (fun t => heatKernel t ⋆ (g.val : E → F)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact funext fun x => heatCauchyPotential_eq_convolution g.val ht x
  exact (tendstoUniformly_congr heq).mpr (tendstoUniformly_heatKernel_convolution g.val
    ((mem_uniformContinuousSubmodule _).1 g.property))

/-- **Smooth approximation of bounded uniformly continuous data.** For every positive tolerance
there is a bounded uniformly continuous, smooth approximant with bounded derivatives of every
order. Its supremum norm does not exceed that of the datum. -/
theorem exists_contDiff_bounded_derivatives_approximation
    (g : uniformContinuousSubmodule ℝ E F) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : uniformContinuousSubmodule ℝ E F,
      ContDiff ℝ ∞ (f.val : E → F) ∧ ‖f - g‖ < ε ∧ ‖f‖ ≤ ‖g‖ ∧
        ∀ m : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ m (f.val : E → F) x‖ ≤ C := by
  have hclose := (tendsto_heatCauchyPotentialBUC g).eventually
    (Metric.ball_mem_nhds g hε)
  obtain ⟨t, ht, htg⟩ := ((hclose.and self_mem_nhdsWithin).exists)
  refine ⟨heatCauchyPotentialBUC t g, ?_, ?_, ?_, fun m => ?_⟩
  · rw [coe_heatCauchyPotentialBUC, coe_heatCauchyPotentialBCF_of_pos htg]
    exact contDiff_heatKernel_convolution htg g.val.continuous.aestronglyMeasurable
      (ae_of_all _ g.val.norm_coe_le_norm)
  · simpa only [Metric.mem_ball, dist_eq_norm] using ht
  · simpa only [one_mul] using
      (heatCauchyPotentialBUC t).le_of_opNorm_le (norm_heatCauchyPotentialBUC_le t) g
  · exact ⟨_, norm_iteratedFDeriv_heatCauchyPotentialBCF_le htg g.val m⟩

end TauCeti

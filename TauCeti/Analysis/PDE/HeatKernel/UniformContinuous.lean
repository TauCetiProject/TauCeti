/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.BoundedContinuous
public import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
public import TauCeti.Topology.ContinuousMap.Bounded.UniformContinuous

/-!
# Heat regularization of bounded uniformly continuous data

Restricting the bounded continuous heat operator from
`TauCeti.Analysis.PDE.HeatKernel.BoundedContinuous` to the closed subspace of bounded uniformly
continuous functions gives `TauCeti.heatCauchyPotentialBUC`.

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

variable [CompleteSpace F]

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
    simpa only [coe_heatCauchyPotentialBUC] using coe_heatCauchyPotentialBCF_of_pos ht g.val
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

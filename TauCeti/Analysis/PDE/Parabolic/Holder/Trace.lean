/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
public import TauCeti.Analysis.Holder.Iterated
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Spatial traces of bounded parabolic Hölder maps

Every time slice of a bounded order-two parabolic Hölder map belongs to the spatial space
`C_b^{2,α}`. The restriction operator `ParabolicC2HolderSpace.spatialTraceL` has norm at most
one, uniformly over the closed time slab. In particular it supplies both the initial and the
terminal trace, including the endpoints without any extension in time.

The target is `CkHolderSpace 2`, with its sum of the supremum norms of the iterated Fréchet
derivatives and the Hölder seminorm of the Hessian. The continuous multilinear operator norm
agrees with the curried Hessian norm in the parabolic space.

## References

A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 3.
The construction uses the closed derivative graph of `ParabolicC2HolderSpace` and the spatial
constructor `CkHolderSpace.ofContDiff`.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- Every closed-slab spatial slice is twice continuously differentiable. -/
theorem contDiff_spatialSlice (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ContDiff ℝ 2 (fun x ↦ f (slabMk x t)) := by
  have hx : _root_.fderiv ℝ (fun x ↦ f (slabMk x t)) =
      fun x ↦ spatialFDerivL f (slabMk x t) := funext (f.fderiv_eq t)
  have hxx : _root_.fderiv ℝ (fun x ↦ spatialFDerivL f (slabMk x t)) =
      fun x ↦ spatialSecondFDerivL f (slabMk x t) :=
    funext (f.fderiv_spatialFDeriv_eq t)
  have hc : Continuous (fun x : E ↦ slabMk x t) :=
    continuous_slabMk.comp (continuous_id.prodMk continuous_const)
  rw [← one_add_one_eq_two, contDiff_succ_iff_fderiv]
  refine ⟨fun x ↦ (f.hasSpatialFDerivAt t x).differentiableAt, by simp, ?_⟩
  rw [hx, contDiff_one_iff_fderiv, hxx]
  exact ⟨fun x ↦ (f.hasSpatialSecondFDerivAt t x).differentiableAt,
    (spatialSecondFDerivL f).continuous.comp hc⟩

/-- The spatial Hessian has Hölder constant at most the parabolic Hessian seminorm, also
when represented as a continuous multilinear second derivative. -/
theorem holderWith_iteratedFDeriv_two_spatialSlice
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    HolderWith (nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _))
      α (iteratedFDeriv ℝ 2 (fun x ↦ f (slabMk x t))) := by
  have hh : HolderWith
      (nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _))
      α (fun x : E ↦ spatialSecondFDerivL f (slabMk x t)) := by
    intro x y
    simpa [edist_slabMk] using
      (spatialSecondFDerivL f).memHolder.holderWith (slabMk x t) (slabMk y t)
  let e := (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] F)).symm.trans
    (continuousMultilinearCurryRightEquiv' ℝ 1 E F).symm
  have he : (fun x ↦ e (spatialSecondFDerivL f (slabMk x t))) =
      iteratedFDeriv ℝ 2 (fun x ↦ f (slabMk x t)) := by
    funext x
    ext v
    simp [e, Fin.init, f.iteratedFDeriv_two_apply]
  simpa [Function.comp_def, he] using e.isometry.lipschitzWith.holderWith.comp hh

private theorem bounded_iteratedFDeriv_spatialSlice
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ∀ i ≤ 2, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i (fun y ↦ f (slabMk y t)) x‖ ≤ C := by
  intro i hi
  interval_cases i
  · exact ⟨‖valueL f‖, fun x ↦ by simpa using (valueL f).norm_coe_le_norm (slabMk x t)⟩
  · exact ⟨‖spatialFDerivL f‖, fun x ↦ by
      simpa using (spatialFDerivL f).norm_coe_le_norm (slabMk x t)⟩
  · exact ⟨‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖, fun x ↦ by
      simpa [f.norm_iteratedFDeriv_two t x] using
        (spatialSecondFDerivL f).toBoundedContinuousFunction.norm_coe_le_norm (slabMk x t)⟩

/-- Restrict a bounded order-two parabolic Hölder map to any time in the closed slab,
with values in the spatial sum-norm `C_b^{2,α}` space. -/
def spatialTrace (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    CkHolderSpace 2 α E F :=
  CkHolderSpace.ofContDiff (fun x ↦ f (slabMk x t)) (f.contDiff_spatialSlice t)
    (bounded_iteratedFDeriv_spatialSlice f t)
    (f.holderWith_iteratedFDeriv_two_spatialSlice t).memHolder

@[simp]
theorem spatialTrace_apply (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    f.spatialTrace t x = f (slabMk x t) := by
  simp [spatialTrace]

/-- The first derivative of the trace is the spatial gradient on the same slice. -/
@[simp]
theorem fderiv_spatialTrace (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    _root_.fderiv ℝ (f.spatialTrace t) x = spatialFDerivL f (slabMk x t) := by
  have h : (f.spatialTrace t : E → F) = fun y ↦ f (slabMk y t) :=
    funext (f.spatialTrace_apply t)
  rw [h, f.fderiv_eq]

/-- The second iterated derivative of the trace is the parabolic spatial Hessian. -/
theorem iteratedFDeriv_two_spatialTrace (f : ParabolicC2HolderSpace α E F hab)
    (t : Icc a b) (x : E) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (f.spatialTrace t) x v =
      spatialSecondFDerivL f (slabMk x t) (v 0) (v 1) := by
  have h : (f.spatialTrace t : E → F) = fun y ↦ f (slabMk y t) :=
    funext (f.spatialTrace_apply t)
  rw [h, f.iteratedFDeriv_two_apply]

/-- Spatial restriction is a contraction for the sum-norm spatial space, uniformly in time. -/
theorem norm_spatialTrace_le (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ‖f.spatialTrace t‖ ≤ ‖f‖ := by
  have hfun : (f.spatialTrace t : E → F) = fun y ↦ f (slabMk y t) :=
    funext (f.spatialTrace_apply t)
  have h0 : ‖(f.spatialTrace t).iteratedFDeriv 0‖ ≤ ‖valueL f‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg (valueL f))).2
    intro x
    rw [← CkHolderSpace.iteratedFDeriv_eq, Fin.val_zero, hfun, norm_iteratedFDeriv_zero]
    exact (valueL f).norm_coe_le_norm (slabMk x t)
  have h1 : ‖(f.spatialTrace t).iteratedFDeriv 1‖ ≤ ‖spatialFDerivL f‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg (spatialFDerivL f))).2
    intro x
    rw [← CkHolderSpace.iteratedFDeriv_eq, Fin.val_one, hfun, norm_iteratedFDeriv_one,
      f.fderiv_eq]
    exact (spatialFDerivL f).norm_coe_le_norm (slabMk x t)
  have h2 : ‖(f.spatialTrace t).iteratedFDeriv 2‖ ≤
      ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖ := by
    apply (BoundedContinuousFunction.norm_le
      (norm_nonneg (spatialSecondFDerivL f).toBoundedContinuousFunction)).2
    intro x
    rw [← CkHolderSpace.iteratedFDeriv_eq, Fin.val_two, hfun,
      f.norm_iteratedFDeriv_two]
    simpa only [HolderSpace.toBoundedContinuousFunction_apply] using
      (spatialSecondFDerivL f).toBoundedContinuousFunction.norm_coe_le_norm (slabMk x t)
  have hh := (f.holderWith_iteratedFDeriv_two_spatialSlice t).nnholderNorm_le
  have hh' : (nnHolderNorm α (iteratedFDeriv ℝ 2 (fun x ↦ f (slabMk x t))) : ℝ) ≤
      nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _) :=
    NNReal.coe_le_coe.mpr hh
  rw [CkHolderSpace.norm_eq, hfun, Fin.sum_univ_three]
  have hn := f.norm_def
  have ht := (timeDerivL f).norm_def
  linarith [norm_nonneg (timeDerivL f)]

/-- Spatial restriction as a bounded linear map. Taking `t = a` or `t = b` gives the initial
or terminal trace with the same operator bound. -/
def spatialTraceL (t : Icc a b) :
    ParabolicC2HolderSpace α E F hab →L[ℝ] CkHolderSpace 2 α E F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f.spatialTrace t
      map_add' := fun f g ↦ by
        ext x
        simp [CkHolderSpace.coe_add]
      map_smul' := fun c f ↦ by
        ext x
        simp [CkHolderSpace.coe_smul] }
    1 (fun f ↦ by simpa using f.norm_spatialTrace_le t)

@[simp]
theorem spatialTraceL_apply (t : Icc a b) (f : ParabolicC2HolderSpace α E F hab) :
    spatialTraceL t f = f.spatialTrace t := (rfl)

/-- All time-slice traces, including both endpoint traces, have operator norm at most one. -/
theorem norm_spatialTraceL_le_one (t : Icc a b) :
    ‖spatialTraceL (α := α) (E := E) (F := F) (hab := hab) t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end TauCeti.ParabolicC2HolderSpace

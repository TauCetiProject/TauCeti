/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.DuhamelPotential.Basic

/-!
# The spatial Hessian of the bounded Hölder Duhamel potential

The spatial slices of `heatDuhamelPotentialHolderL` are `C²`, including the initial slice.
Their Hessians form a bounded parabolic Hölder field, and taking this field is a continuous
linear map `heatDuhamelPotentialHessianL`. The Hessians use the native continuous multilinear
operator norm. The estimate is uniform in the time horizon apart from the factor
`1 + (√T)^α`.

This supplies the top-order spatial field for the classical inhomogeneous heat solution
operator. It does not assert a time derivative or the heat equation. The joint Hölder bound
uses the spatial and temporal estimates for the Hessian in
`TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic`.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open Set MeasureTheory ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α T : ℝ≥0}

/-- Every spatial slice of the bounded Hölder Duhamel potential is `C²`, including time zero.
Only positivity of the spatial Hölder exponent is needed for this regularity. -/
theorem contDiff_heatDuhamelPotentialHolderL [CompleteSpace F] (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ 2 (fun x => heatDuhamelPotentialHolderL hα hα₂ f (slabMk x t)) := by
  simp only [heatDuhamelPotentialHolderL_apply, time_slabMk, space_slabMk]
  rcases t.2.1.eq_or_lt with hzero | hpos
  · simp only [← hzero, heatDuhamelPotential_zero, Pi.zero_apply]
    exact contDiff_const
  · exact contDiff_heatDuhamelPotential_of_holderWith
      (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
      (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le T.coe_nonneg f s x)
      (ae_of_all _ fun s => holderWith_timeExtension T.coe_nonneg (C := ‖f‖₊) (f := f) (by
        simpa only [HolderSpace.coe_toBoundedContinuousFunction] using
          f.memHolder.holderWith.mono f.nnHolderNorm_le) s) hα hpos

private def hessian (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    E [×2]→L[ℝ] F :=
  iteratedFDeriv ℝ 2 (fun x => heatDuhamelPotentialHolderL hα hα₂ f
    (slabMk x (slabTime p))) (p : ParabolicSpaceTime E).space

private theorem hessian_apply (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    hessian hα hα₂ f p =
      iteratedFDeriv ℝ 2 (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time) (p : ParabolicSpaceTime E).space := by
  simp only [hessian, heatDuhamelPotentialHolderL_apply, time_slabMk, space_slabMk, coe_slabTime]

variable [CompleteSpace F]

private theorem exists_holderWith_hessian (hα : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ (T : ℝ≥0) (f : HolderSpace α (slab (E := E) 0 T) F),
      HolderWith (C * ‖f‖₊) α (hessian hα (hα₁.le.trans (by norm_num)) f) := by
  obtain ⟨C, hC⟩ := exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential_slab
    (E := E) (F := F) hα hα₁
  refine ⟨C, fun T f => ?_⟩
  -- Rewrite the whole field: the Hölder predicate takes a function, not a point evaluation.
  rw [show hessian hα (hα₁.le.trans (by norm_num)) f = _ from
    funext (hessian_apply _ _ f)]
  exact hC (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
    (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le T.coe_nonneg f s x)
    (ae_of_all _ fun s => holderWith_timeExtension T.coe_nonneg (f := f) (by
      simpa only [HolderSpace.coe_toBoundedContinuousFunction] using
        f.memHolder.holderWith.mono f.nnHolderNorm_le) s)

private def hessianConstant (hα : 0 < α) (hα₁ : α < 1) : ℝ≥0 :=
  Classical.choose (exists_holderWith_hessian (E := E) (F := F) hα hα₁)

private theorem holderWith_hessian (hα : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderWith (hessianConstant (E := E) (F := F) hα hα₁ * ‖f‖₊) α
      (hessian hα (hα₁.le.trans (by norm_num)) f) :=
  Classical.choose_spec (exists_holderWith_hessian hα hα₁) T f

private theorem norm_hessian_le (hα : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    ‖hessian hα (hα₁.le.trans (by norm_num)) f p‖ ≤
      hessianConstant (E := E) (F := F) hα hα₁ * ‖f‖ * (Real.sqrt T) ^ (α : ℝ) := by
  let q := slabMk (p : ParabolicSpaceTime E).space (⟨0, by simp⟩ : Icc (0 : ℝ) T)
  have hzero : hessian hα (hα₁.le.trans (by norm_num)) f q = 0 := by
    simp [hessian_apply, q, heatDuhamelPotential_zero]
  have hd : dist p q ≤ Real.sqrt T := by
    simp only [Subtype.dist_eq, ParabolicSpaceTime.dist_eq, q, space_slabMk, time_slabMk,
      dist_self, zero_add, sub_zero]
    have hp := (slabTime p).2
    rw [coe_slabTime] at hp
    rw [abs_of_nonneg hp.1]
    exact Real.sqrt_le_sqrt hp.2
  simpa only [hzero, dist_zero_right, NNReal.coe_mul, coe_nnnorm] using
    (holderWith_hessian hα hα₁ f).dist_le_of_le hd

private def hessianHolder (hα : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderSpace α (slab (E := E) 0 T) (E [×2]→L[ℝ] F) :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup _
      ((holderWith_hessian hα hα₁ f).continuous hα) _ (norm_hessian_le hα hα₁ f))
    (by
      rw [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
      exact (holderWith_hessian hα hα₁ f).memHolder)

private theorem hessianHolder_apply (hα : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    hessianHolder hα hα₁ f p = hessian hα (hα₁.le.trans (by norm_num)) f p := by
  rw [hessianHolder, HolderSpace.ofBoundedContinuousFunction_apply,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup]

private theorem norm_hessianHolder_le (hα : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ‖hessianHolder hα hα₁ f‖ ≤ hessianConstant (E := E) (F := F) hα hα₁ *
      (1 + (Real.sqrt T) ^ (α : ℝ)) * ‖f‖ := by
  have hB : ‖(hessianHolder hα hα₁ f).toBoundedContinuousFunction‖ ≤
      hessianConstant (E := E) (F := F) hα hα₁ * ‖f‖ * (Real.sqrt T) ^ (α : ℝ) := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p => ?_
    rw [HolderSpace.toBoundedContinuousFunction_apply, hessianHolder_apply]
    exact norm_hessian_le hα hα₁ f p
  have hH := (holderWith_hessian hα hα₁ f).nnholderNorm_le
  rw [HolderSpace.norm_def]
  simp only [HolderSpace.coe_toBoundedContinuousFunction]
  -- The seminorm also needs an equality of whole functions rather than pointwise rewrites.
  rw [show (hessianHolder hα hα₁ f : _ → _) = _ from
    funext (hessianHolder_apply hα hα₁ f)]
  have hH' : (nnHolderNorm α (hessian hα (hα₁.le.trans (by norm_num)) f) : ℝ) ≤
      hessianConstant (E := E) (F := F) hα hα₁ * ‖f‖ := by exact_mod_cast hH
  nlinarith

/-- The spatial Hessian of the Duhamel heat potential as a continuous linear map between
bounded parabolic Hölder spaces, for `0 < α < 1`. The target uses continuous multilinear
second derivatives and their operator norms. -/
def heatDuhamelPotentialHessianL (hα : 0 < α) (hα₁ : α < 1) :
    HolderSpace α (slab (E := E) 0 T) F →L[ℝ]
      HolderSpace α (slab (E := E) 0 T) (E [×2]→L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun := hessianHolder hα hα₁
      map_add' f g := by
        apply HolderSpace.ext
        intro p
        simp only [hessianHolder_apply, HolderSpace.add_apply, hessian]
        simp_rw [map_add, HolderSpace.add_apply]
        exact iteratedFDeriv_add_apply
          ((contDiff_heatDuhamelPotentialHolderL hα _ f (slabTime p)).contDiffAt)
          ((contDiff_heatDuhamelPotentialHolderL hα _ g (slabTime p)).contDiffAt)
      map_smul' c f := by
        apply HolderSpace.ext
        intro p
        simp only [hessianHolder_apply, HolderSpace.smul_apply, hessian, RingHom.id_apply]
        simp_rw [map_smul, HolderSpace.smul_apply]
        exact iteratedFDeriv_const_smul_apply
          ((contDiff_heatDuhamelPotentialHolderL hα _ f (slabTime p)).contDiffAt) }
    _ (norm_hessianHolder_le hα hα₁)

/-- The Hessian operator is the native second iterated Fréchet derivative of each spatial
slice of the Duhamel potential. This also characterizes the field at the initial time. -/
@[simp]
theorem heatDuhamelPotentialHessianL_apply (hα : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    heatDuhamelPotentialHessianL hα hα₁ f p =
      iteratedFDeriv ℝ 2 (fun x => heatDuhamelPotentialHolderL hα
        (hα₁.le.trans (by norm_num)) f (slabMk x (slabTime p)))
        (p : ParabolicSpaceTime E).space :=
  hessianHolder_apply hα hα₁ f p

/-- A horizon-independent constant controls the Hessian operator norm, with the explicit
horizon factor `1 + (√T)^α`. -/
theorem exists_norm_heatDuhamelPotentialHessianL_le (hα : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ T : ℝ≥0,
      ‖heatDuhamelPotentialHessianL (E := E) (F := F) (T := T) hα hα₁‖ ≤
        C * (1 + (Real.sqrt T) ^ (α : ℝ)) := by
  refine ⟨hessianConstant (E := E) (F := F) hα hα₁, fun T => ?_⟩
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_hessianHolder_le hα hα₁)

end TauCeti

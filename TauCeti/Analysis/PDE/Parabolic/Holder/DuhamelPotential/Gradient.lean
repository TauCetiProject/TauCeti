/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.DuhamelPotential.Basic
import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Gradient

/-!
# The spatial gradient of the bounded Hölder Duhamel potential

For forcing `f` in the bounded parabolic Hölder space `C_b^{α,α/2}` on the slab `E × [0, T]`, with
`0 < α < 2`, the spatial slices of the Duhamel potential `heatDuhamelPotentialHolderL f` are `C²`,
including the initial slice (`TauCeti.contDiff_spatialSlice_heatDuhamelPotentialHolderL`), and
their gradients form a bounded continuous field on the closed slab. Taking this field is a
continuous linear map `heatDuhamelPotentialGradientL` into `slab →ᵇ (E →L[ℝ] F)`, with
`‖D w‖_∞ ≤ C √T ‖f‖` for a constant `C` independent of the horizon `T`. This is the gradient
field of the order-two parabolic Hölder space `ParabolicC2HolderSpace`, together with the
derivative identity that its constructor `ParabolicC2HolderSpace.mk` requires.

The bound on the gradient is `TauCeti.exists_norm_fderiv_heatDuhamelPotential_le`, and its joint
continuity on `[0, T] × E` is `TauCeti.continuousOn_fderiv_heatDuhamelPotential`, transported to
the slab along the continuous coordinate map.

## Main declarations

* `TauCeti.heatDuhamelPotentialGradientL`: the gradient of the Duhamel potential, as a continuous
  linear map from `C_b^{α,α/2}` to bounded continuous gradient fields.
* `TauCeti.hasFDerivAt_heatDuhamelPotentialHolderL`: the field is the spatial derivative of the
  Duhamel potential at every point of the slab.
* `TauCeti.exists_norm_heatDuhamelPotentialGradientL_apply_le`: the bound `O(√T)` on the operator
  norm, uniformly in the horizon.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open Filter MeasureTheory Set Topology ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α T : ℝ≥0}

/-- The forcing of the Duhamel potential of a slab map, extended to all times. -/
private abbrev forcing (f : HolderSpace α (slab (E := E) 0 T) F) : ℝ → E → F :=
  fun s x => timeExtension T.coe_nonneg f x s

private theorem norm_forcing_le (f : HolderSpace α (slab (E := E) 0 T) F) :
    ∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖forcing f r y‖ ≤ (‖f‖₊ : ℝ≥0) :=
  fun r _ y => norm_timeExtension_le T.coe_nonneg f r y

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem stronglyMeasurable_forcing (f : HolderSpace α (slab (E := E) 0 T) F) :
    StronglyMeasurable (Function.uncurry (forcing f)) :=
  (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable

/-- Each spatial slice of the bounded Hölder Duhamel potential is a slice of the Duhamel
potential of the extended forcing. -/
private theorem slice_eq (hα : 0 < α) (hα₂ : α ≤ 2) (f : HolderSpace α (slab (E := E) 0 T) F)
    (t : Icc (0 : ℝ) T) :
    (fun x => heatDuhamelPotentialHolderL hα hα₂ f (slabMk x t)) =
      heatDuhamelPotential (forcing f) t := by
  funext x
  simp only [heatDuhamelPotentialHolderL_apply, time_slabMk, space_slabMk]

/-- The gradient of the Duhamel potential at a slab point. -/
private def gradient (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    E →L[ℝ] F :=
  fderiv ℝ (heatDuhamelPotential (forcing f) (p : ParabolicSpaceTime E).time)
    (p : ParabolicSpaceTime E).space

private theorem gradient_eq (hα : 0 < α) (hα₂ : α ≤ 2) (f : HolderSpace α (slab (E := E) 0 T) F)
    (p : slab (E := E) 0 T) :
    gradient f p = fderiv ℝ (fun x => heatDuhamelPotentialHolderL hα hα₂ f (slabMk x (slabTime p)))
      (p : ParabolicSpaceTime E).space := by
  rw [slice_eq, gradient, coe_slabTime]

variable [CompleteSpace F]

private theorem differentiableAt_spatialSlice (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (t : Icc (0 : ℝ) T) (x : E) :
    DifferentiableAt ℝ (fun y => heatDuhamelPotentialHolderL hα hα₂ f (slabMk y t)) x :=
  (contDiff_spatialSlice_heatDuhamelPotentialHolderL hα hα₂ f t).differentiable two_ne_zero x

private theorem exists_norm_gradient_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ≥0} (f : HolderSpace α (slab (E := E) 0 T) F) p,
      ‖gradient f p‖ ≤ C * ‖f‖ * √T := by
  obtain ⟨C, hC⟩ := exists_norm_fderiv_heatDuhamelPotential_le (E := E) (F := F)
  refine ⟨max C 0, le_max_right _ _, fun {T} f p => ?_⟩
  have ht := (slabTime p).2
  rw [coe_slabTime] at ht
  rcases ht.1.eq_or_lt with h0 | hpos
  · simp only [gradient, ← h0, heatDuhamelPotential_zero, Pi.zero_def, fderiv_const_apply,
      norm_zero]
    positivity
  refine (hC (stronglyMeasurable_forcing f) (ae_norm_le_of_forall_mem_Icc (norm_forcing_le f) ht.2)
    hpos _).trans ?_
  simp only [coe_nnnorm]
  gcongr
  · exact le_max_left _ _
  · exact ht.2

/-- The gradient field is jointly continuous on the closed slab. -/
private theorem continuous_gradient (hα : 0 < α) (hα₂ : α < 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) : Continuous (gradient f) :=
  (continuousOn_fderiv_heatDuhamelPotential (stronglyMeasurable_forcing f) (norm_forcing_le f)
    (fun r _ => holderWith_timeExtension_holderSpace T.coe_nonneg f r) hα hα₂).comp_continuous
    ((continuous_time.comp continuous_subtype_val).prodMk
      (continuous_space.comp continuous_subtype_val))
    fun p => ⟨mem_slab.1 p.2, mem_univ _⟩

/-- The gradient field as a bounded continuous map on the slab. -/
private def gradientBCF (hα : 0 < α) (hα₂ : α < 2) (f : HolderSpace α (slab (E := E) 0 T) F) :
    slab (E := E) 0 T →ᵇ (E →L[ℝ] F) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gradient f) (continuous_gradient hα hα₂ f)
    ((exists_norm_gradient_le (α := α) (E := E) (F := F)).choose * ‖f‖ * √T)
    ((exists_norm_gradient_le (α := α) (E := E) (F := F)).choose_spec.2 f)

/-- **The gradient of the Duhamel potential** as a continuous linear map from the bounded
parabolic Hölder space `C_b^{α,α/2}` on `E × [0, T]` to bounded continuous gradient fields on the
slab, for `0 < α < 2`. -/
def heatDuhamelPotentialGradientL (hα : 0 < α) (hα₂ : α < 2) :
    HolderSpace α (slab (E := E) 0 T) F →L[ℝ] (slab (E := E) 0 T →ᵇ (E →L[ℝ] F)) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := gradientBCF hα hα₂
      map_add' f g := by
        ext p : 1
        simp only [gradientBCF, _root_.add_apply,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup, gradient_eq hα hα₂.le, map_add,
          HolderSpace.add_apply]
        exact fderiv_add (differentiableAt_spatialSlice hα hα₂.le f (slabTime p) _)
          (differentiableAt_spatialSlice hα hα₂.le g (slabTime p) _)
      map_smul' c f := by
        ext p : 1
        simp only [gradientBCF, _root_.smul_apply,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup, gradient_eq hα hα₂.le, map_smul,
          HolderSpace.smul_apply, RingHom.id_apply]
        exact fderiv_const_smul (differentiableAt_spatialSlice hα hα₂.le f (slabTime p) _) c }
    (by
      obtain ⟨C, hC₀, hC⟩ := exists_norm_gradient_le (α := α) (E := E) (F := F)
      refine ⟨C * √T, fun f => (BoundedContinuousFunction.norm_le (by positivity)).2 fun p => ?_⟩
      refine (hC f p).trans_eq ?_
      ring)

/-- The gradient operator evaluates to the Fréchet derivative of each spatial slice of the
Duhamel potential. This also describes the field at the initial time, where it vanishes. -/
@[simp]
theorem heatDuhamelPotentialGradientL_apply (hα : 0 < α) (hα₂ : α < 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    heatDuhamelPotentialGradientL hα hα₂ f p =
      fderiv ℝ (fun x => heatDuhamelPotentialHolderL hα hα₂.le f (slabMk x (slabTime p)))
        (p : ParabolicSpaceTime E).space :=
  gradient_eq hα hα₂.le f p

/-- The gradient field is the spatial Fréchet derivative of the Duhamel potential at every point
of the closed slab. This is the first derivative identity of `ParabolicC2HolderSpace.mk`. -/
theorem hasFDerivAt_heatDuhamelPotentialHolderL (hα : 0 < α) (hα₂ : α < 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (t : Icc (0 : ℝ) T) (x : E) :
    HasFDerivAt (fun y => heatDuhamelPotentialHolderL hα hα₂.le f (slabMk y t))
      (heatDuhamelPotentialGradientL hα hα₂ f (slabMk x t)) x := by
  rw [heatDuhamelPotentialGradientL_apply, slabTime_slabMk, space_slabMk]
  exact (differentiableAt_spatialSlice hα hα₂.le f t x).hasFDerivAt

/-- The gradient map has operator norm `O(√T)`: `‖D w‖_∞ ≤ C √T ‖f‖`, with a constant `C`
independent of the horizon `T`. -/
theorem exists_norm_heatDuhamelPotentialGradientL_apply_le (hα : 0 < α) (hα₂ : α < 2) :
    ∃ C : ℝ, ∀ {T : ℝ≥0} (f : HolderSpace α (slab (E := E) 0 T) F),
      ‖heatDuhamelPotentialGradientL hα hα₂ f‖ ≤ C * √T * ‖f‖ := by
  obtain ⟨C, hC₀, hC⟩ := exists_norm_gradient_le (α := α) (E := E) (F := F)
  refine ⟨C, fun {T} f => (BoundedContinuousFunction.norm_le (by positivity)).2 fun p => ?_⟩
  rw [heatDuhamelPotentialGradientL_apply, ← gradient_eq]
  refine (hC f p).trans_eq ?_
  ring

end TauCeti

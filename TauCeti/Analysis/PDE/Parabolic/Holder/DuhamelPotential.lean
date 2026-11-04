/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Gradient
public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Holder
public import TauCeti.Analysis.PDE.Parabolic.Holder.Two

/-!
# The Duhamel potential and its gradient as bounded maps on a slab

`heatDuhamelPotentialHolderL` sends bounded parabolic Hölder forcing on `E × [0,T]` to its
Duhamel heat potential in the same space. Its operator norm is at most
`T (2 + M_α) + max(1,T)`, where `M_α` is the heat-kernel moment. Its initial value is zero,
and, for complete codomains, constant forcing `c` produces exactly `t • c`.

This is the value component of the classical inhomogeneous heat solution operator. Spatial
Hölder regularity of the forcing controls the value's parabolic seminorm; time regularity is
not needed for that estimate.

`heatDuhamelPotentialFDerivL` is the gradient component, for complete codomains. It sends bounded
continuous forcing on `E × [0,T]` to the spatial gradient `D w` of its Duhamel potential `w`, as a
bounded continuous field on the slab, with operator norm at most `C √T` for a constant `C`
independent of `T`. Its continuity is `TauCeti.continuousOn_fderiv_heatDuhamelPotential`; no
Hölder regularity of the forcing is needed. For Hölder forcing it is the spatial derivative of the
value field (`hasFDerivAt_heatDuhamelPotentialHolderL`), which is the gradient identity required
of a map in the order-two space `ParabolicC2HolderSpace`. The second spatial derivative and the
time derivative are not treated here.

## Main declarations

* `TauCeti.heatDuhamelPotentialHolderL`: the Duhamel potential as a bounded operator on
  `C_b^{α,α/2}`.
* `TauCeti.heatDuhamelPotentialFDerivL`: its spatial gradient, as a bounded operator from bounded
  continuous forcing to bounded continuous gradient fields.
* `TauCeti.exists_norm_heatDuhamelPotentialFDerivL_le`: the gradient operator has norm `O(√T)`.
* `TauCeti.hasFDerivAt_heatDuhamelPotentialHolderL`: the gradient field is the spatial derivative
  of the value field.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open MeasureTheory Set Real ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal Interval BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α T : ℝ≥0}

private theorem holderWith_potential (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderWith (T * ‖f‖₊ * (1 + heatKernelMoment E α) + ‖f‖₊ * max 1 T) α
      (fun p : slab (E := E) 0 T =>
        heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
          (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space) :=
  holderWith_heatDuhamelPotential
    (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
    (fun s _ x => norm_timeExtension_le T.coe_nonneg f s x)
    (fun s _ => holderWith_timeExtension T.coe_nonneg (f := f) (by
      simpa only [HolderSpace.coe_toBoundedContinuousFunction] using
        f.memHolder.holderWith.mono f.nnHolderNorm_le) s) hα hα₂

private theorem norm_forcing_potential_le (f : HolderSpace α (slab (E := E) 0 T) F)
    (p : slab (E := E) 0 T) :
    ‖heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
      (p : ParabolicSpaceTime E).time
      (p : ParabolicSpaceTime E).space‖ ≤ (T : ℝ) * ‖f‖ := by
  have hp := (slabTime p).2
  rw [coe_slabTime] at hp
  exact ((norm_heatDuhamelPotential_le hp.1
    (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le T.coe_nonneg f s x) _).trans
    (mul_le_mul_of_nonneg_left hp.2 (norm_nonneg f))).trans_eq (mul_comm _ _)

private def potentialBCF (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) : slab (E := E) 0 T →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup _
    ((holderWith_potential hα hα₂ f).continuous hα) ((T : ℝ) * ‖f‖)
    (norm_forcing_potential_le f)

private theorem coe_potentialBCF (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ⇑(potentialBCF hα hα₂ f) = fun p : slab (E := E) 0 T =>
      heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _

private def potential (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) : HolderSpace α (slab (E := E) 0 T) F :=
  HolderSpace.ofBoundedContinuousFunction (potentialBCF hα hα₂ f) (by
    rw [coe_potentialBCF]
    exact (holderWith_potential hα hα₂ f).memHolder)

private theorem coe_potential (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ⇑(potential hα hα₂ f) = fun p : slab (E := E) 0 T =>
      heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  funext p
  rw [potential, HolderSpace.ofBoundedContinuousFunction_apply, coe_potentialBCF]

private theorem norm_potential_le (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ‖potential hα hα₂ f‖ ≤ (T * (2 + heatKernelMoment E α) + max 1 T : ℝ≥0) * ‖f‖ := by
  have hH := (holderWith_potential hα hα₂ f).nnholderNorm_le
  have hB : ‖(potential hα hα₂ f).toBoundedContinuousFunction‖ ≤ (T : ℝ) * ‖f‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p => ?_
    rw [HolderSpace.toBoundedContinuousFunction_apply, coe_potential]
    exact norm_forcing_potential_le f p
  rw [HolderSpace.norm_def]
  have hH' : (nnHolderNorm α ((potential hα hα₂ f).toBoundedContinuousFunction : _ → _) : ℝ) ≤
      (T * ‖f‖₊ * (1 + heatKernelMoment E α) + ‖f‖₊ * max 1 T : ℝ≥0) := by
    rw [HolderSpace.coe_toBoundedContinuousFunction, coe_potential]
    exact_mod_cast hH
  push_cast at hH' ⊢
  linarith

/-- The Duhamel heat potential as a bounded linear endomorphism of the bounded parabolic
`α`-Hölder space on `E × [0,T]`, for `0 < α ≤ 2`. Its values are independent of the constant
extension of the forcing outside the slab used in the formula. -/
def heatDuhamelPotentialHolderL (hα : 0 < α) (hα₂ : α ≤ 2) :
    HolderSpace α (slab (E := E) 0 T) F →L[ℝ] HolderSpace α (slab (E := E) 0 T) F :=
  LinearMap.mkContinuous
    { toFun := potential hα hα₂
      map_add' f g := by
        have hfg : ⇑(f + g) = ⇑f + ⇑g := funext (HolderSpace.add_apply f g)
        ext p
        simp only [HolderSpace.add_apply, coe_potential, hfg, timeExtension_add, Pi.add_apply]
        simpa only [Pi.add_def, coe_slabTime] using
          heatDuhamelPotential_add
            (f := fun s x => timeExtension T.coe_nonneg f x s)
            (g := fun s x => timeExtension T.coe_nonneg g x s)
            (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
            (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le T.coe_nonneg f s x)
            (continuous_timeExtension T.coe_nonneg g.continuous).stronglyMeasurable
            (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le T.coe_nonneg g s x)
            (slabTime p).2.1 (p : ParabolicSpaceTime E).space
      map_smul' c f := by
        have hcf : ⇑(c • f) = c • ⇑f := funext (HolderSpace.smul_apply c f)
        ext p
        simp only [HolderSpace.smul_apply, coe_potential, RingHom.id_apply, hcf,
          timeExtension_smul, Pi.smul_apply]
        exact heatDuhamelPotential_smul c (fun s x => timeExtension T.coe_nonneg f x s)
            (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space }
    (T * (2 + heatKernelMoment E α) + max 1 T : ℝ≥0)
    (norm_potential_le hα hα₂)

/-- Evaluation of the bounded Hölder Duhamel operator. The clamped extension only uses the
given forcing at times in `[0,t]` when evaluating at a slab point of time `t`. -/
@[simp]
theorem heatDuhamelPotentialHolderL_apply (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    heatDuhamelPotentialHolderL hα hα₂ f p =
      heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  exact congrFun (coe_potential hα hα₂ f) p

/-- The norm of the Duhamel operator is bounded in terms of the horizon, exponent and
heat-kernel moment, independently of the forcing and the codomain. -/
theorem norm_heatDuhamelPotentialHolderL_le (hα : 0 < α) (hα₂ : α ≤ 2) :
    ‖heatDuhamelPotentialHolderL (E := E) (F := F) (T := T) hα hα₂‖ ≤
      (T * (2 + heatKernelMoment E α) + max 1 T : ℝ≥0) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_potential_le hα hα₂)

/-! ### The spatial gradient -/

section Gradient

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] in
/-- The clamped time extension of bounded continuous forcing is jointly continuous. -/
private theorem continuous_uncurry_timeExtension (f : slab (E := E) 0 T →ᵇ F) :
    Continuous (Function.uncurry fun s x => timeExtension T.coe_nonneg f x s) :=
  continuous_timeExtension T.coe_nonneg f.continuous

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] in
/-- The clamped time extension of bounded continuous forcing is bounded by its norm. -/
private theorem norm_timeExtension_le_norm (f : slab (E := E) 0 T →ᵇ F) (s : ℝ) (x : E) :
    ‖timeExtension T.coe_nonneg f x s‖ ≤ ‖f‖ := by
  rw [timeExtension_def]
  exact f.norm_coe_le_norm _

variable [CompleteSpace F]

/-- A local shortcut for bounded gradient fields, keeping instance search shallow. -/
local instance : NormedAddCommGroup (slab (E := E) 0 T →ᵇ (E →L[ℝ] F)) := inferInstance
/-- A local shortcut for scalar operations on bounded gradient fields. -/
local instance : NormedSpace ℝ (slab (E := E) 0 T →ᵇ (E →L[ℝ] F)) := inferInstance

/-- At every nonnegative time the Duhamel potential is differentiable in space. -/
private theorem differentiable_potential (f : slab (E := E) 0 T →ᵇ F) {t : ℝ} (ht : 0 ≤ t) :
    Differentiable ℝ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s) t) := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [heatDuhamelPotential_zero]
    exact differentiable_const 0
  · exact (contDiff_heatDuhamelPotential (continuous_uncurry_timeExtension f).stronglyMeasurable
      (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le_norm f s x)
      ht).differentiable one_ne_zero

/-- A nonnegative constant in the gradient bound `‖D w(t, x)‖ ≤ C M √t`. -/
private theorem exists_nonneg_norm_fderiv_le :
    ∃ C, 0 ≤ C ∧ ∀ (T : ℝ≥0) (f : slab (E := E) 0 T →ᵇ F) (p : slab (E := E) 0 T),
      ‖fderiv ℝ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time) (p : ParabolicSpaceTime E).space‖ ≤ C * ‖f‖ * √T := by
  obtain ⟨C, hC⟩ := exists_norm_fderiv_heatDuhamelPotential_le (E := E) (F := F)
  refine ⟨max C 0, le_max_right _ _, fun T f p => ?_⟩
  have hp := (slabTime p).2
  rw [coe_slabTime] at hp
  rcases hp.1.eq_or_lt with h | h
  · rw [← h, heatDuhamelPotential_zero, fderiv_zero, Pi.zero_apply, norm_zero]
    positivity
  · calc _ ≤ C * ‖f‖ * √(p : ParabolicSpaceTime E).time :=
          hC (continuous_uncurry_timeExtension f).stronglyMeasurable
            (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le_norm f s x) h _
      _ ≤ max C 0 * ‖f‖ * √(p : ParabolicSpaceTime E).time := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 * ‖f‖ * √T := by
          gcongr
          exact hp.2

/-- The constant of the gradient bound, depending only on the spaces. -/
private def gradientConstant : ℝ :=
  Classical.choose (exists_nonneg_norm_fderiv_le (E := E) (F := F))

private theorem gradientConstant_nonneg : 0 ≤ gradientConstant (E := E) (F := F) :=
  (Classical.choose_spec (exists_nonneg_norm_fderiv_le (E := E) (F := F))).1

private theorem norm_fderiv_le (f : slab (E := E) 0 T →ᵇ F) (p : slab (E := E) 0 T) :
    ‖fderiv ℝ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
      (p : ParabolicSpaceTime E).time) (p : ParabolicSpaceTime E).space‖ ≤
        gradientConstant (E := E) (F := F) * ‖f‖ * √T :=
  (Classical.choose_spec (exists_nonneg_norm_fderiv_le (E := E) (F := F))).2 T f p

/-- The gradient field of the Duhamel potential of bounded continuous forcing. -/
private def gradient (f : slab (E := E) 0 T →ᵇ F) : slab (E := E) 0 T →ᵇ (E →L[ℝ] F) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => fderiv ℝ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
      (p : ParabolicSpaceTime E).time) (p : ParabolicSpaceTime E).space)
    ((continuousOn_fderiv_heatDuhamelPotential (continuous_uncurry_timeExtension f)
      (norm_timeExtension_le_norm f)).comp_continuous
        ((continuous_time.comp continuous_subtype_val).prodMk
          (continuous_space.comp continuous_subtype_val))
        fun p => ⟨(mem_slab.1 p.2).1, mem_univ _⟩)
    _ (norm_fderiv_le f)

private theorem gradient_apply (f : slab (E := E) 0 T →ᵇ F) (p : slab (E := E) 0 T) :
    gradient f p = fderiv ℝ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
      (p : ParabolicSpaceTime E).time) (p : ParabolicSpaceTime E).space :=
  (rfl)

private theorem norm_gradient_le (f : slab (E := E) 0 T →ᵇ F) :
    ‖gradient f‖ ≤ gradientConstant (E := E) (F := F) * √T * ‖f‖ :=
  (BoundedContinuousFunction.norm_le (by
    have := gradientConstant_nonneg (E := E) (F := F)
    positivity)).2 fun p => by
      rw [gradient_apply, mul_right_comm]
      exact norm_fderiv_le f p

/-- **The gradient of the Duhamel potential** as a bounded linear map from bounded continuous
forcing on the slab `E × [0,T]` to bounded continuous gradient fields on the same slab:
`f ↦ ((x, t) ↦ D w(t, x))`, where `w` is the Duhamel heat potential of `f`, extended constantly
in time outside `[0,T]`. -/
def heatDuhamelPotentialFDerivL :
    (slab (E := E) 0 T →ᵇ F) →L[ℝ] (slab (E := E) 0 T →ᵇ (E →L[ℝ] F)) :=
  LinearMap.mkContinuous
    { toFun := gradient
      map_add' f g := by
        have hfg : ⇑(f + g) = ⇑f + ⇑g := FunLike.coe_add f g
        ext p : 1
        have hp := (mem_slab.1 p.2).1
        have hadd : heatDuhamelPotential
            (fun s x => timeExtension T.coe_nonneg (f + g) x s) (p : ParabolicSpaceTime E).time =
            heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
                (p : ParabolicSpaceTime E).time +
              heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg g x s)
                (p : ParabolicSpaceTime E).time := by
          funext x
          rw [hfg, timeExtension_add]
          exact heatDuhamelPotential_add (continuous_uncurry_timeExtension f).stronglyMeasurable
              (ae_of_all _ fun s => ae_of_all _ fun y => norm_timeExtension_le_norm f s y)
              (continuous_uncurry_timeExtension g).stronglyMeasurable
              (ae_of_all _ fun s => ae_of_all _ fun y => norm_timeExtension_le_norm g s y) hp x
        rw [_root_.add_apply, gradient_apply, gradient_apply, gradient_apply,
          hadd, fderiv_add ((differentiable_potential f hp) _) ((differentiable_potential g hp) _)]
      map_smul' c f := by
        have hcf : ⇑(c • f) = c • ⇑f := FunLike.coe_smul c f
        ext p : 1
        have hp := (mem_slab.1 p.2).1
        have hsmul : heatDuhamelPotential
            (fun s x => timeExtension T.coe_nonneg (c • f) x s) (p : ParabolicSpaceTime E).time =
            c • heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
              (p : ParabolicSpaceTime E).time := by
          funext x
          rw [hcf, timeExtension_smul]
          exact heatDuhamelPotential_smul c (fun s x => timeExtension T.coe_nonneg f x s)
              (p : ParabolicSpaceTime E).time x
        rw [RingHom.id_apply, _root_.smul_apply, gradient_apply,
          gradient_apply, hsmul, fderiv_const_smul ((differentiable_potential f hp) _)] }
    (gradientConstant (E := E) (F := F) * √T) norm_gradient_le

/-- Evaluation of the gradient operator: the spatial derivative of the Duhamel potential of the
clamped extension of the forcing, at the time and position of the slab point. -/
@[simp]
theorem heatDuhamelPotentialFDerivL_apply (f : slab (E := E) 0 T →ᵇ F)
    (p : slab (E := E) 0 T) :
    heatDuhamelPotentialFDerivL f p =
      fderiv ℝ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time) (p : ParabolicSpaceTime E).space :=
  (rfl)

/-- **The gradient bound.** The norm of the gradient operator on `E × [0,T]` is at most
`C √T`, with `C` depending only on `E` and `F`. -/
theorem exists_norm_heatDuhamelPotentialFDerivL_le :
    ∃ C, ∀ T : ℝ≥0, ‖heatDuhamelPotentialFDerivL (E := E) (F := F) (T := T)‖ ≤ C * √T :=
  ⟨gradientConstant (E := E) (F := F), fun T => ContinuousLinearMap.opNorm_le_bound _
    (by have := gradientConstant_nonneg (E := E) (F := F); positivity) norm_gradient_le⟩

/-- **The gradient field is the spatial derivative of the value field.** For Hölder forcing
`f`, the value field of the Duhamel operator has spatial derivative given by the gradient
operator applied to `f`, on every time slice of the slab. -/
theorem hasFDerivAt_heatDuhamelPotentialHolderL (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (t : Icc (0 : ℝ) T) (x : E) :
    HasFDerivAt (fun y => heatDuhamelPotentialHolderL hα hα₂ f (slabMk y t))
      (heatDuhamelPotentialFDerivL f.toBoundedContinuousFunction (slabMk x t)) x := by
  have hfun : (fun y => heatDuhamelPotentialHolderL hα hα₂ f (slabMk y t)) =
      heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f.toBoundedContinuousFunction x s)
        t := by
    funext y
    rw [heatDuhamelPotentialHolderL_apply, space_slabMk, time_slabMk,
      HolderSpace.coe_toBoundedContinuousFunction]
  rw [hfun, heatDuhamelPotentialFDerivL_apply, space_slabMk, time_slabMk]
  exact ((differentiable_potential f.toBoundedContinuousFunction t.2.1) x).hasFDerivAt

end Gradient

end TauCeti

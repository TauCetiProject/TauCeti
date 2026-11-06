/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Bilinear
public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Gradient
public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.HeatEquation
public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Holder
public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# The Duhamel heat potential as a bounded map on a slab

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
Hölder regularity of the forcing is needed. It is the spatial derivative of the Duhamel potential
(`hasFDerivAt_heatDuhamelPotentialFDerivL`); for Hölder forcing it is therefore the spatial
derivative of the value field (`hasFDerivAt_heatDuhamelPotentialHolderL`), which is the gradient
identity required of a map in the order-two space `ParabolicC2HolderSpace`.

`heatDuhamelPotentialL` assembles the solution operator of `∂ₜw = Δw + f`, `w(·, 0) = 0`, in
parabolic Hölder spaces: for `0 < α < 1`, `T > 0` and complete codomains, it sends forcing in
`C_b^{α,α/2}(E × [0,T])` to its Duhamel potential in the order-two space
`C_b^{2+α,1+α/2}(E × [0,T])`, with operator norm at most `C (1 + T)` for a constant `C` depending
only on `α`, `E` and `F`. Its spatial Hessian is parabolically `α`-Hölder because the Hessian of
the potential is `α`-Hölder in space (this needs `α < 1`) and `α / 2`-Hölder in time, with
constants proportional to the Hölder norm of the forcing; its time derivative is `Δw + f`, also
at the endpoints of the slab. It is the forcing part of the solution operator of the Cauchy
problem `∂ₜu - Δu = f`, `u(·, 0) = g`, whose initial-data part is the Cauchy potential
`TauCeti.heatCauchyPotentialL`.

## Main declarations

* `TauCeti.heatDuhamelPotentialHolderL`: the Duhamel potential as a bounded operator on
  `C_b^{α,α/2}`.
* `TauCeti.heatDuhamelPotentialFDerivL`: its spatial gradient, as a bounded operator from bounded
  continuous forcing to bounded continuous gradient fields.
* `TauCeti.exists_norm_heatDuhamelPotentialFDerivL_le`: the gradient operator has norm `O(√T)`.
* `TauCeti.hasFDerivAt_heatDuhamelPotentialFDerivL`,
  `TauCeti.hasFDerivAt_heatDuhamelPotentialHolderL`: the gradient field is the spatial derivative
  of the Duhamel potential, and of the value field for Hölder forcing.
* `TauCeti.heatDuhamelPotentialL`: the Duhamel potential as a bounded linear map
  `C_b^{α,α/2} → C_b^{2+α,1+α/2}` on `E × [0,T]`, with its four fields
  (`TauCeti.heatDuhamelPotentialL_apply` and its companions).
* `TauCeti.timeDerivL_heatDuhamelPotentialL_eq_laplacian_add`: the inhomogeneous heat equation
  `∂ₜw = Δw + f` on the closed slab.
* `TauCeti.spatialTrace_heatDuhamelPotentialL_zero`: the initial trace is zero.
* `TauCeti.exists_norm_heatDuhamelPotentialL_le`: the operator norm is `O(1 + T)`.

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
    (fun s _ x => by
      simpa only [HolderSpace.coe_toBoundedContinuousFunction, coe_nnnorm] using
        (norm_timeExtension_le T.coe_nonneg f.toBoundedContinuousFunction s x).trans
          f.norm_toBoundedContinuousFunction_le)
    (fun s _ => holderWith_timeExtension T.coe_nonneg (f := f) f.holderWith_nnnorm s) hα hα₂

private theorem norm_forcing_potential_le (f : HolderSpace α (slab (E := E) 0 T) F)
    (p : slab (E := E) 0 T) :
    ‖heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
      (p : ParabolicSpaceTime E).time
      (p : ParabolicSpaceTime E).space‖ ≤ (T : ℝ) * ‖f‖ := by
  have hp := (slabTime p).2
  rw [coe_slabTime] at hp
  exact ((norm_heatDuhamelPotential_le hp.1
    (ae_of_all _ fun s => ae_of_all _ fun x => by
      simpa only [HolderSpace.coe_toBoundedContinuousFunction] using
        (norm_timeExtension_le T.coe_nonneg f.toBoundedContinuousFunction s x).trans
          f.norm_toBoundedContinuousFunction_le) _).trans
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

/-- The Duhamel potential of the clamped extension is additive in bounded continuous forcing. -/
private theorem heatDuhamelPotential_timeExtension_add (f g : slab (E := E) 0 T →ᵇ F) {t : ℝ}
    (ht : 0 ≤ t) :
    heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg (⇑f + ⇑g) x s) t =
      heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s) t +
        heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg g x s) t := by
  funext x
  rw [timeExtension_add]
  exact heatDuhamelPotential_add
    (f := fun s x => timeExtension T.coe_nonneg f x s)
    (g := fun s x => timeExtension T.coe_nonneg g x s)
    (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
    (ae_of_all _ fun s => ae_of_all _ fun y => norm_timeExtension_le T.coe_nonneg f s y)
    (continuous_timeExtension T.coe_nonneg g.continuous).stronglyMeasurable
    (ae_of_all _ fun s => ae_of_all _ fun y => norm_timeExtension_le T.coe_nonneg g s y) ht x

/-- The Duhamel potential of the clamped extension is homogeneous in the forcing. -/
private theorem heatDuhamelPotential_timeExtension_smul (c : ℝ) (f : slab (E := E) 0 T → F)
    (t : ℝ) :
    heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg (c • f) x s) t =
      c • heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s) t := by
  funext x
  rw [timeExtension_smul]
  exact heatDuhamelPotential_smul c _ t x

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
        simp only [HolderSpace.add_apply, coe_potential, hfg]
        simpa only [HolderSpace.coe_toBoundedContinuousFunction, Pi.add_apply] using
          congrFun (heatDuhamelPotential_timeExtension_add f.toBoundedContinuousFunction
            g.toBoundedContinuousFunction (mem_slab.1 p.2).1) (p : ParabolicSpaceTime E).space
      map_smul' c f := by
        have hcf : ⇑(c • f) = c • ⇑f := funext (HolderSpace.smul_apply c f)
        ext p
        simp only [HolderSpace.smul_apply, coe_potential, RingHom.id_apply, hcf]
        exact congrFun (heatDuhamelPotential_timeExtension_smul c f _) _ }
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
  · exact (contDiff_heatDuhamelPotential
      (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
      (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le T.coe_nonneg f s x)
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
          hC (f := fun s x => timeExtension T.coe_nonneg f x s)
            (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
            (ae_of_all _ fun s => ae_of_all _ fun x => norm_timeExtension_le T.coe_nonneg f s x) h _
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
    ((continuousOn_fderiv_heatDuhamelPotential (continuous_timeExtension T.coe_nonneg f.continuous)
      (norm_timeExtension_le T.coe_nonneg f)).comp_continuous
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
        rw [_root_.add_apply, gradient_apply, gradient_apply, gradient_apply, hfg,
          heatDuhamelPotential_timeExtension_add f g hp,
          fderiv_add ((differentiable_potential f hp) _) ((differentiable_potential g hp) _)]
      map_smul' c f := by
        have hcf : ⇑(c • f) = c • ⇑f := FunLike.coe_smul c f
        ext p : 1
        have hp := (mem_slab.1 p.2).1
        rw [RingHom.id_apply, _root_.smul_apply, gradient_apply, gradient_apply, hcf,
          heatDuhamelPotential_timeExtension_smul,
          fderiv_const_smul ((differentiable_potential f hp) _)] }
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

/-- **The gradient field is the spatial derivative of the Duhamel potential.** For bounded
continuous forcing `f`, the gradient operator applied to `f` is the spatial derivative of the
Duhamel potential of the clamped extension of `f`, on every time slice of the slab. -/
theorem hasFDerivAt_heatDuhamelPotentialFDerivL (f : slab (E := E) 0 T →ᵇ F)
    (t : Icc (0 : ℝ) T) (x : E) :
    HasFDerivAt (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s) t)
      (heatDuhamelPotentialFDerivL f (slabMk x t)) x := by
  rw [heatDuhamelPotentialFDerivL_apply, space_slabMk, time_slabMk]
  exact ((differentiable_potential f t.2.1) x).hasFDerivAt

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
  rw [hfun]
  exact hasFDerivAt_heatDuhamelPotentialFDerivL _ t x

end Gradient

/-! ### The Duhamel potential in the order-two space -/

section OrderTwo

open InnerProductSpace Laplacian

/-- The forcing of the Duhamel potential: a slab field, extended constantly in time outside the
slab. -/
private abbrev forcing (f : slab (E := E) 0 T → F) : ℝ → E → F :=
  fun s x => timeExtension T.coe_nonneg f x s

private theorem stronglyMeasurable_forcing (f : HolderSpace α (slab (E := E) 0 T) F) :
    StronglyMeasurable (Function.uncurry (forcing (T := T) f)) :=
  (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_forcing_le (f : HolderSpace α (slab (E := E) 0 T) F) (s : ℝ) (x : E) :
    ‖forcing (T := T) f s x‖ ≤ ‖f‖ := by
  simpa only [HolderSpace.coe_toBoundedContinuousFunction] using
    (norm_timeExtension_le T.coe_nonneg f.toBoundedContinuousFunction s x).trans
      f.norm_toBoundedContinuousFunction_le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem holderWith_forcing (f : HolderSpace α (slab (E := E) 0 T) F) (s : ℝ) :
    HolderWith ‖f‖₊ α (forcing (T := T) f s) :=
  holderWith_timeExtension T.coe_nonneg f.holderWith_nnnorm s

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- On the slab the clamped forcing is the slab field itself, so it is parabolically Hölder
there. -/
private theorem holderOnWith_forcing (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderOnWith ‖f‖₊ α (fun p : ParabolicSpaceTime E => forcing (T := T) f p.time p.space)
      (slab 0 T) := by
  have h (r : ParabolicSpaceTime E) (hr : r ∈ slab (0 : ℝ) T) :
      forcing (T := T) f r.time r.space = f ⟨r, hr⟩ := by
    simpa only [coe_slabTime] using
      congrFun (timeExtension_space_slabTime T.coe_nonneg (f : slab (E := E) 0 T → F)) ⟨r, hr⟩
  intro p hp q hq
  dsimp only
  rw [h p hp, h q hq]
  exact f.holderWith_nnnorm ⟨p, hp⟩ ⟨q, hq⟩

/-- The spatial Hessian of the Duhamel potential of the clamped forcing, on the slab. -/
private def hessian (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    E →L[ℝ] E →L[ℝ] F :=
  fderiv ℝ (fderiv ℝ (heatDuhamelPotential (forcing (T := T) f) (p : ParabolicSpaceTime E).time))
    (p : ParabolicSpaceTime E).space

private theorem hessian_slabMk (f : HolderSpace α (slab (E := E) 0 T) F) (x : E)
    (t : Icc (0 : ℝ) T) :
    hessian f (slabMk x t) = fderiv ℝ (fderiv ℝ (heatDuhamelPotential (forcing f) t)) x := by
  rw [hessian, space_slabMk, time_slabMk]

variable [CompleteSpace F]

/-- A local shortcut for bounded gradient fields, keeping instance search shallow. -/
local instance : NormedAddCommGroup (slab (E := E) 0 T →ᵇ (E →L[ℝ] F)) := inferInstance
/-- A local shortcut for scalar operations on bounded gradient fields. -/
local instance : NormedSpace ℝ (slab (E := E) 0 T →ᵇ (E →L[ℝ] F)) := inferInstance

/-- One constant controls both the supremum and the parabolic `α`-Hölder seminorm of the Hessian:
`‖D²w‖_∞ ≤ C ‖f‖ T^(α/2)` and `[D²w]_{α,par} ≤ C ‖f‖`. -/
private theorem exists_hessian_bounds (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ (T : ℝ≥0) (f : HolderSpace α (slab (E := E) 0 T) F),
      (∀ p, ‖hessian f p‖ ≤ C * ‖f‖ * (T : ℝ) ^ ((α : ℝ) / 2)) ∧
        HolderWith (C * ‖f‖₊) α (hessian f) := by
  obtain ⟨C₂, hC₂⟩ :=
    exists_norm_iteratedFDeriv_two_heatDuhamelPotential_le (E := E) (F := F) hα₀
  obtain ⟨Cs, hCs⟩ :=
    exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential (E := E) (F := F) hα₀ hα₁
  obtain ⟨Ct, hCt⟩ := exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential (E := E)
    (F := F) hα₀ (hα₁.trans one_lt_two)
  refine ⟨max C₂.toNNReal (Cs + Ct), fun T f => ⟨fun p => ?_, ?_⟩⟩
  all_goals
    have hfM {t : ℝ} : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖forcing (T := T) f s y‖ ≤ ‖f‖ :=
      ae_of_all _ fun s => ae_of_all _ fun y => norm_forcing_le f s y
    have hH {t : ℝ} : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith ‖f‖₊ α (forcing (T := T) f s) :=
      ae_of_all _ fun s => holderWith_forcing f s
  · -- The supremum bound: the Hessian vanishes at time zero.
    obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
    rw [hessian_slabMk]
    rcases t.2.1.eq_or_lt with h0 | ht
    · simp only [← h0, heatDuhamelPotential_zero, fderiv_zero, Pi.zero_apply]
      rw [ContinuousLinearMap.opNorm_zero]
      positivity
    rw [← continuousMultilinearCurryFin2_iteratedFDeriv_two, LinearIsometryEquiv.norm_map]
    calc _ ≤ C₂ * ‖f‖₊ * (t : ℝ) ^ ((α : ℝ) / 2) :=
          hC₂ (stronglyMeasurable_forcing f) hfM hH ht x
      _ ≤ C₂.toNNReal * ‖f‖ * (T : ℝ) ^ ((α : ℝ) / 2) := by
          rw [coe_nnnorm]
          gcongr
          · exact le_coe_toNNReal C₂
          · exact t.2.2
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _
  · -- The Hölder bound: the parabolic seminorm is at most the spatial `α`-seminorm plus the
    -- temporal `α / 2`-seminorm.
    have hsp : spaceEHolderNorm α (hessian f) ≤ ((Cs * ‖f‖₊ : ℝ≥0) : ENNReal) := by
      refine spaceEHolderNorm_le_iff.2 fun t x y => ?_
      rw [hessian_slabMk, hessian_slabMk]
      rcases t.2.1.eq_or_lt with h0 | ht
      · simp [← h0]
      rw [← continuousMultilinearCurryFin2_iteratedFDeriv_two,
        ← continuousMultilinearCurryFin2_iteratedFDeriv_two, LinearIsometryEquiv.edist_map]
      exact hCs (stronglyMeasurable_forcing f) hfM hH ht x y
    have htm : timeEHolderNorm (α / 2) (hessian f) ≤ ((Ct * ‖f‖₊ : ℝ≥0) : ENNReal) := by
      refine timeEHolderNorm_le_iff.2 fun x t s => ?_
      rw [hessian_slabMk, hessian_slabMk, ← continuousMultilinearCurryFin2_iteratedFDeriv_two,
        ← continuousMultilinearCurryFin2_iteratedFDeriv_two, LinearIsometryEquiv.edist_map]
      exact hCt (stronglyMeasurable_forcing f) hfM hH x t t.2 s s.2
    refine eHolderNorm_le_iff.1 ((eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm α _).trans
      ((add_le_add hsp htm).trans ?_))
    rw [← ENNReal.coe_add, ← add_mul, ENNReal.coe_le_coe]
    gcongr
    exact le_max_right _ _

/-- The constant of `exists_hessian_bounds`, depending only on `α`, `E` and `F`. -/
private def hessianConstant (hα₀ : 0 < α) (hα₁ : α < 1) : ℝ≥0 :=
  Classical.choose (exists_hessian_bounds (E := E) (F := F) hα₀ hα₁)

private theorem norm_hessian_le (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    ‖hessian f p‖ ≤ hessianConstant (E := E) (F := F) hα₀ hα₁ * ‖f‖ * (T : ℝ) ^ ((α : ℝ) / 2) :=
  ((Classical.choose_spec (exists_hessian_bounds (E := E) (F := F) hα₀ hα₁)) T f).1 p

private theorem holderWith_hessian (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderWith (hessianConstant (E := E) (F := F) hα₀ hα₁ * ‖f‖₊) α (hessian f) :=
  ((Classical.choose_spec (exists_hessian_bounds (E := E) (F := F) hα₀ hα₁)) T f).2

/-- The Hessian of the Duhamel potential as an element of the bounded parabolic Hölder space. -/
private def hessianHolder (hα₀ : 0 < α) (hα₁ : α < 1) (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderSpace α (slab (E := E) 0 T) (E →L[ℝ] E →L[ℝ] F) :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup (hessian f)
      ((holderWith_hessian hα₀ hα₁ f).continuous hα₀) _ (norm_hessian_le hα₀ hα₁ f))
    (by
      rw [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
      exact (holderWith_hessian hα₀ hα₁ f).memHolder)

private theorem hessianHolder_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    hessianHolder hα₀ hα₁ f p = hessian f p := by
  rw [hessianHolder, HolderSpace.ofBoundedContinuousFunction_apply,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup]

private theorem norm_hessianHolder_le (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ‖hessianHolder hα₀ hα₁ f‖ ≤
      hessianConstant (E := E) (F := F) hα₀ hα₁ * ((T : ℝ) ^ ((α : ℝ) / 2) + 1) * ‖f‖ := by
  have hB := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    ((holderWith_hessian hα₀ hα₁ f).continuous hα₀)
    (by have := Real.rpow_nonneg T.coe_nonneg ((α : ℝ) / 2); positivity)
    (norm_hessian_le hα₀ hα₁ f)
  have hH := (holderWith_hessian hα₀ hα₁ f).nnholderNorm_le
  rw [HolderSpace.norm_def, hessianHolder,
    HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  have hH' : (nnHolderNorm α (hessian f) : ℝ) ≤ hessianConstant (E := E) (F := F) hα₀ hα₁ * ‖f‖ :=
    by exact_mod_cast hH
  linarith

/-- A local shortcut for the norm on Hessians, needed to apply Hölder-space operations to
Hessian fields. -/
private local instance hessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
private local instance hessianNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- The time-derivative field `Δw + f` of the Duhamel potential, as an element of the bounded
parabolic Hölder space. -/
private def timeField (hα₀ : 0 < α) (hα₁ : α < 1) (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderSpace α (slab (E := E) 0 T) F :=
  (ContinuousLinearMap.id ℝ ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)).compHolder₂
    (HolderSpace.const traceL) (hessianHolder hα₀ hα₁ f) + f

private theorem timeField_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    timeField hα₀ hα₁ f p =
      Δ (heatDuhamelPotential (forcing f) (p : ParabolicSpaceTime E).time)
        (p : ParabolicSpaceTime E).space + f p := by
  rw [timeField, HolderSpace.add_apply, ContinuousLinearMap.compHolder₂_apply,
    HolderSpace.const_apply, ContinuousLinearMap.id_apply, hessianHolder_apply, hessian,
    ← laplacian_eq_traceL]

private theorem norm_timeField_le (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ‖timeField hα₀ hα₁ f‖ ≤ ‖traceL (E := E) (F := F)‖ * ‖hessianHolder hα₀ hα₁ f‖ + ‖f‖ :=
  (norm_add_le _ _).trans (add_le_add_left ((ContinuousLinearMap.norm_id_compHolder₂_apply_le
    _ _).trans (mul_le_mul_of_nonneg_right (HolderSpace.norm_const_le _) (norm_nonneg _))) _)

/-- The gradient of the Duhamel potential is differentiable in space at every time of the slab,
with derivative the Hessian. -/
private theorem hasFDerivAt_fderiv (hα₀ : 0 < α) (f : HolderSpace α (slab (E := E) 0 T) F)
    {t : ℝ} (ht : 0 ≤ t) (x : E) :
    HasFDerivAt (fderiv ℝ (heatDuhamelPotential (forcing (T := T) f) t))
      (fderiv ℝ (fderiv ℝ (heatDuhamelPotential (forcing f) t)) x) x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [heatDuhamelPotential_zero, fderiv_zero]
    exact hasFDerivAt_const _ x
  have h := contDiff_heatDuhamelPotential_of_holderWith (stronglyMeasurable_forcing f)
    (ae_of_all _ fun s => ae_of_all _ fun y => norm_forcing_le f s y)
    (ae_of_all _ fun s => holderWith_forcing f s) hα₀ ht
  exact ((h.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt

/-- The Duhamel potential of Hölder forcing, assembled from its four fields. -/
private def potentialTwo (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (f : HolderSpace α (slab (E := E) 0 T) F) : ParabolicC2HolderSpace α E F hT :=
  ParabolicC2HolderSpace.mk
    (heatDuhamelPotentialHolderL hα₀ (hα₁.trans one_lt_two).le f).toBoundedContinuousFunction
    (heatDuhamelPotentialFDerivL f.toBoundedContinuousFunction)
    (hessianHolder hα₀ hα₁ f) (timeField hα₀ hα₁ f)
    (fun t x => by
      simpa only [HolderSpace.toBoundedContinuousFunction_apply] using
        hasFDerivAt_heatDuhamelPotentialHolderL hα₀ _ f t x)
    (fun t x => by
      rw [hessianHolder_apply, hessian_slabMk]
      simp only [heatDuhamelPotentialFDerivL_apply, space_slabMk, time_slabMk,
        HolderSpace.coe_toBoundedContinuousFunction]
      exact hasFDerivAt_fderiv hα₀ f t.2.1 x)
    (fun x t => by
      rw [timeField_apply, space_slabMk, time_slabMk,
        ← timeExtension_of_mem T.coe_nonneg (f : slab (E := E) 0 T → F) x t]
      refine (hasDerivWithinAt_heatDuhamelPotential_of_holderOnWith
        (stronglyMeasurable_forcing f)
        (ae_of_all _ fun s => ae_of_all _ fun y => norm_forcing_le f s y)
        (holderOnWith_forcing f) hα₀ (hα₁.trans one_lt_two) t.2 x).congr_of_mem
          (fun s hs => ?_) t.2
      rw [timeExtension_def]
      dsimp only
      rw [projIcc_of_mem hT.le hs, HolderSpace.toBoundedContinuousFunction_apply,
        heatDuhamelPotentialHolderL_apply, space_slabMk, time_slabMk])

private theorem potentialTwo_apply (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    potentialTwo hα₀ hα₁ hT f p =
      heatDuhamelPotentialHolderL hα₀ (hα₁.trans one_lt_two).le f p := by
  rw [potentialTwo, ParabolicC2HolderSpace.mk_apply, HolderSpace.toBoundedContinuousFunction_apply]

/-- The constant of the operator-norm bound, depending only on `α`, `E` and `F`. -/
private def duhamelConstant (hα₀ : 0 < α) (hα₁ : α < 1) : ℝ :=
  2 + gradientConstant (E := E) (F := F) +
    2 * (‖traceL (E := E) (F := F)‖ + 1) * (hessianConstant (E := E) (F := F) hα₀ hα₁ : ℝ)

private theorem duhamelConstant_nonneg (hα₀ : 0 < α) (hα₁ : α < 1) :
    0 ≤ duhamelConstant (E := E) (F := F) hα₀ hα₁ := by
  have := gradientConstant_nonneg (E := E) (F := F)
  unfold duhamelConstant
  positivity

private theorem norm_potentialTwo_le (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ‖potentialTwo hα₀ hα₁ hT f‖ ≤ duhamelConstant (E := E) (F := F) hα₀ hα₁ * (1 + T) * ‖f‖ := by
  set Cg := gradientConstant (E := E) (F := F)
  set Ch : ℝ := (hessianConstant (E := E) (F := F) hα₀ hα₁ : ℝ)
  set L := ‖traceL (E := E) (F := F)‖
  have hCg : 0 ≤ Cg := gradientConstant_nonneg
  have hCh : 0 ≤ Ch := NNReal.coe_nonneg _
  have hL : 0 ≤ L := norm_nonneg _
  have hf : 0 ≤ ‖f‖ := norm_nonneg _
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  -- The four fields of the potential.
  have h₀ : ‖(heatDuhamelPotentialHolderL hα₀ (hα₁.trans one_lt_two).le
      f).toBoundedContinuousFunction‖ ≤ T * ‖f‖ :=
    (BoundedContinuousFunction.norm_le (by positivity)).2 fun p => by
      rw [HolderSpace.toBoundedContinuousFunction_apply, heatDuhamelPotentialHolderL_apply]
      exact norm_forcing_potential_le f p
  have h₁ : ‖heatDuhamelPotentialFDerivL (T := T) f.toBoundedContinuousFunction‖ ≤
      Cg * √T * ‖f‖ :=
    (norm_gradient_le _).trans (by gcongr; exact f.norm_toBoundedContinuousFunction_le)
  have h₂ := norm_hessianHolder_le hα₀ hα₁ f
  have h₃ := norm_timeField_le hα₀ hα₁ f
  -- Each power of `T` is at most `1 + T`.
  have hs : √T ≤ 1 + T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_one_add hT0 (by norm_num) (by norm_num)
  have hp : (T : ℝ) ^ ((α : ℝ) / 2) ≤ 1 + T :=
    Real.rpow_le_one_add hT0 (by positivity) (by linarith [show (α : ℝ) < 1 from hα₁])
  rw [ParabolicC2HolderSpace.norm_eq, potentialTwo, valueL_mk, spatialFDerivL_mk,
    spatialSecondFDerivL_mk, timeDerivL_mk, duhamelConstant]
  have hH : ‖hessianHolder hα₀ hα₁ f‖ ≤ 2 * Ch * (1 + T) * ‖f‖ := by
    refine h₂.trans ?_
    nlinarith [mul_nonneg hCh hf]
  have hg : Cg * √T * ‖f‖ ≤ Cg * (1 + T) * ‖f‖ := by gcongr
  have hTf : T * ‖f‖ ≤ (1 + T) * ‖f‖ := by gcongr; linarith
  have hf1 : ‖f‖ ≤ (1 + T) * ‖f‖ := le_mul_of_one_le_left hf (by linarith)
  have hLH : L * ‖hessianHolder hα₀ hα₁ f‖ ≤ L * (2 * Ch * (1 + T) * ‖f‖) := by gcongr
  nlinarith [h₀, h₁, h₃, hH, hg, hTf, hf1, hLH]

variable (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)

/-- **The Duhamel heat potential in `C_b^{2+α,1+α/2}`.** For `0 < α < 1` and `T > 0`, the Duhamel
potential `w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` of forcing `f ∈ C_b^{α,α/2}(E × [0, T])`,
extended constantly in time outside the slab, as a continuous linear map into the bounded
order-two parabolic Hölder space on `E × [0, T]`. It solves the inhomogeneous heat equation
`∂ₜw = Δw + f` (`TauCeti.timeDerivL_heatDuhamelPotentialL_eq_laplacian_add`) with zero initial
trace (`TauCeti.spatialTrace_heatDuhamelPotentialL_zero`), and its operator norm is `O(1 + T)`
(`TauCeti.exists_norm_heatDuhamelPotentialL_le`). -/
def heatDuhamelPotentialL :
    HolderSpace α (slab (E := E) 0 T) F →L[ℝ] ParabolicC2HolderSpace α E F hT :=
  LinearMap.mkContinuous
    { toFun := potentialTwo hα₀ hα₁ hT
      map_add' f g := by
        ext p
        rw [ParabolicC2HolderSpace.add_apply, potentialTwo_apply, potentialTwo_apply,
          potentialTwo_apply, map_add, HolderSpace.add_apply]
      map_smul' c f := by
        ext p
        rw [ParabolicC2HolderSpace.smul_apply, potentialTwo_apply, potentialTwo_apply, map_smul,
          HolderSpace.smul_apply, RingHom.id_apply] }
    (duhamelConstant (E := E) (F := F) hα₀ hα₁ * (1 + T)) (norm_potentialTwo_le hα₀ hα₁ hT)

private theorem heatDuhamelPotentialL_eq_potentialTwo (f : HolderSpace α (slab (E := E) 0 T) F) :
    heatDuhamelPotentialL hα₀ hα₁ hT f = potentialTwo hα₀ hα₁ hT f :=
  (rfl)

variable {hα₀ hα₁ hT}

/-- The value of the Duhamel operator at a point of the slab. -/
@[simp]
theorem heatDuhamelPotentialL_apply (f : HolderSpace α (slab (E := E) 0 T) F)
    (p : slab (E := E) 0 T) :
    heatDuhamelPotentialL hα₀ hα₁ hT f p =
      heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [heatDuhamelPotentialL_eq_potentialTwo, potentialTwo_apply,
    heatDuhamelPotentialHolderL_apply]

/-- The spatial gradient of the Duhamel operator is the spatial derivative of the potential. -/
@[simp]
theorem spatialFDerivL_heatDuhamelPotentialL (f : HolderSpace α (slab (E := E) 0 T) F)
    (p : slab (E := E) 0 T) :
    spatialFDerivL (heatDuhamelPotentialL hα₀ hα₁ hT f) p =
      fderiv ℝ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time) (p : ParabolicSpaceTime E).space := by
  rw [heatDuhamelPotentialL_eq_potentialTwo, potentialTwo, spatialFDerivL_mk,
    heatDuhamelPotentialFDerivL_apply, HolderSpace.coe_toBoundedContinuousFunction]

/-- The spatial Hessian of the Duhamel operator is the second spatial derivative of the
potential. -/
@[simp]
theorem spatialSecondFDerivL_heatDuhamelPotentialL (f : HolderSpace α (slab (E := E) 0 T) F)
    (p : slab (E := E) 0 T) :
    spatialSecondFDerivL (heatDuhamelPotentialL hα₀ hα₁ hT f) p =
      fderiv ℝ (fderiv ℝ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time)) (p : ParabolicSpaceTime E).space := by
  rw [heatDuhamelPotentialL_eq_potentialTwo, potentialTwo, spatialSecondFDerivL_mk,
    hessianHolder_apply, hessian]

/-- The time derivative of the Duhamel operator is `Δw + f`, also at the endpoints of the slab. -/
@[simp]
theorem timeDerivL_heatDuhamelPotentialL (f : HolderSpace α (slab (E := E) 0 T) F)
    (p : slab (E := E) 0 T) :
    timeDerivL (heatDuhamelPotentialL hα₀ hα₁ hT f) p =
      Δ (heatDuhamelPotential (fun s x => timeExtension T.coe_nonneg f x s)
        (p : ParabolicSpaceTime E).time) (p : ParabolicSpaceTime E).space + f p := by
  rw [heatDuhamelPotentialL_eq_potentialTwo, potentialTwo, timeDerivL_mk, timeField_apply]

/-- **The inhomogeneous heat equation.** The time derivative of the Duhamel potential `w` of `f`
is `Δw + f` at every point of the closed slab, where `Δw` is the Laplacian of the time slice. -/
theorem timeDerivL_heatDuhamelPotentialL_eq_laplacian_add
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    timeDerivL (heatDuhamelPotentialL hα₀ hα₁ hT f) p =
      Δ (fun y ↦ heatDuhamelPotentialL hα₀ hα₁ hT f (slabMk y (slabTime p)))
        (p : ParabolicSpaceTime E).space + f p := by
  simp only [timeDerivL_heatDuhamelPotentialL, heatDuhamelPotentialL_apply, space_slabMk,
    time_slabMk, coe_slabTime]

/-- **Zero initial trace.** The time slice of the Duhamel operator at `t = 0` vanishes. -/
@[simp]
theorem spatialTrace_heatDuhamelPotentialL_zero (f : HolderSpace α (slab (E := E) 0 T) F) :
    (heatDuhamelPotentialL hα₀ hα₁ hT f).spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 := by
  ext x
  simp

variable (α E F) in
/-- **The operator-norm bound.** There is a constant `C`, depending only on `α`, `E` and `F`, such
that the Duhamel operator on `E × [0, T]` has norm at most `C (1 + T)` for every horizon `T > 0`. -/
theorem exists_norm_heatDuhamelPotentialL_le (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C, ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T),
      ‖heatDuhamelPotentialL (E := E) (F := F) hα₀ hα₁ hT‖ ≤ C * (1 + T) :=
  ⟨duhamelConstant (E := E) (F := F) hα₀ hα₁, fun T hT =>
    ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (duhamelConstant_nonneg hα₀ hα₁) (by positivity))
      fun f => by
        rw [heatDuhamelPotentialL_eq_potentialTwo]
        exact norm_potentialTwo_le hα₀ hα₁ hT f⟩

end OrderTwo

end TauCeti

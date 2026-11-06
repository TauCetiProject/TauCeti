/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Bilinear
public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.HeatEquation
public import TauCeti.Analysis.PDE.Parabolic.Holder.DuhamelPotential.Spatial
public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# The Duhamel heat potential in the order-two parabolic Hölder space

`heatDuhamelPotentialL` assembles the solution operator of `∂ₜw = Δw + f`, `w(·, 0) = 0`, in
parabolic Hölder spaces: for `0 < α < 1`, `T > 0` and complete codomains, it sends forcing in
`C_b^{α,α/2}(E × [0,T])` to its Duhamel potential in the order-two space
`C_b^{2+α,1+α/2}(E × [0,T])`, with operator norm at most `C (1 + T)` for a constant `C` depending
only on `α`, `E` and `F`. Its value, gradient and Hessian fields are the bounded operators
`heatDuhamelPotentialHolderL`, `heatDuhamelPotentialFDerivL` and `heatDuhamelPotentialHessianL`;
its time derivative is `Δw + f`, also at the endpoints of the slab. It is the forcing part of the
solution operator of the Cauchy problem `∂ₜu - Δu = f`, `u(·, 0) = g`, whose initial-data part is
the Cauchy potential `TauCeti.heatCauchyPotentialL`.

## Main declarations

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

open MeasureTheory Set ParabolicSpaceTime ParabolicC2HolderSpace InnerProductSpace Laplacian
open scoped NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α T : ℝ≥0}

/-- The forcing of the Duhamel potential: a slab field, extended constantly in time outside the
slab. -/
private abbrev forcing (f : slab (E := E) 0 T → F) : ℝ → E → F :=
  fun s x => timeExtension T.coe_nonneg f x s

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

/-- The curried spatial Hessian of the Duhamel potential of the clamped forcing, on the slab. -/
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

/-- A local shortcut for the norm on Hessians, needed to apply Hölder-space operations to
Hessian fields. -/
private local instance hessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
private local instance hessianNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Currying second derivatives, as a continuous linear map. -/
private def curryL : (E [×2]→L[ℝ] F) →L[ℝ] E →L[ℝ] E →L[ℝ] F :=
  (continuousMultilinearCurryFin2 ℝ E F).toLinearIsometry.toContinuousLinearMap

/-- The curried Hessian field `heatDuhamelPotentialHessianL f`, as an element of the bounded
parabolic Hölder space. -/
private def hessianHolder (hα₀ : 0 < α) (hα₁ : α < 1) (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderSpace α (slab (E := E) 0 T) (E →L[ℝ] E →L[ℝ] F) :=
  (ContinuousLinearMap.id ℝ ((E [×2]→L[ℝ] F) →L[ℝ] E →L[ℝ] E →L[ℝ] F)).compHolder₂
    (HolderSpace.const (curryL (E := E) (F := F))) (heatDuhamelPotentialHessianL hα₀ hα₁ f)

private theorem hessianHolder_apply (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    hessianHolder hα₀ hα₁ f p = hessian f p := by
  rw [hessianHolder, ContinuousLinearMap.compHolder₂_apply, HolderSpace.const_apply,
    ContinuousLinearMap.id_apply, heatDuhamelPotentialHessianL_apply]
  simp only [curryL, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, heatDuhamelPotentialHolderL_apply, space_slabMk,
    time_slabMk, coe_slabTime, hessian]
  exact continuousMultilinearCurryFin2_iteratedFDeriv_two _ _

private theorem norm_hessianHolder_le (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ‖hessianHolder hα₀ hα₁ f‖ ≤
      ‖heatDuhamelPotentialHessianL (E := E) (F := F) (T := T) hα₀ hα₁‖ * ‖f‖ := by
  refine (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _).trans ?_
  have hc : ‖HolderSpace.const (α := α) (X := slab (E := E) 0 T)
      (curryL (E := E) (F := F))‖ ≤ 1 :=
    (HolderSpace.norm_const_le _).trans (LinearIsometry.norm_toContinuousLinearMap_le _)
  calc _ ≤ 1 * (‖heatDuhamelPotentialHessianL (E := E) (F := F) (T := T) hα₀ hα₁‖ * ‖f‖) :=
        mul_le_mul hc (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

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
  have h := contDiff_heatDuhamelPotential_of_holderWith
    (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
    (ae_of_all _ fun s => ae_of_all _ fun y => norm_timeExtension_holderSpace_le T.coe_nonneg f s y)
    (ae_of_all _ fun s => holderWith_timeExtension_holderSpace T.coe_nonneg f s) hα₀ ht
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
        (continuous_timeExtension T.coe_nonneg f.continuous).stronglyMeasurable
        (ae_of_all _ fun s => ae_of_all _ fun y =>
          norm_timeExtension_holderSpace_le T.coe_nonneg f s y)
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

/-- The operator-norm bound of the assembled potential, in terms of the operator norms of its
value, gradient and Hessian components. -/
private def duhamelBound (hα₀ : 0 < α) (hα₁ : α < 1) (T : ℝ≥0) : ℝ :=
  ‖heatDuhamelPotentialHolderL (E := E) (F := F) (T := T) hα₀ (hα₁.trans one_lt_two).le‖ +
    ‖heatDuhamelPotentialFDerivL (E := E) (F := F) (T := T)‖ +
      (‖traceL (E := E) (F := F)‖ + 1) *
        ‖heatDuhamelPotentialHessianL (E := E) (F := F) (T := T) hα₀ hα₁‖ + 1

private theorem duhamelBound_nonneg (hα₀ : 0 < α) (hα₁ : α < 1) (T : ℝ≥0) :
    0 ≤ duhamelBound (E := E) (F := F) hα₀ hα₁ T := by
  unfold duhamelBound
  positivity

private theorem norm_potentialTwo_le (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ‖potentialTwo hα₀ hα₁ hT f‖ ≤ duhamelBound (E := E) (F := F) hα₀ hα₁ T * ‖f‖ := by
  have h₀ : ‖(heatDuhamelPotentialHolderL hα₀ (hα₁.trans one_lt_two).le
      f).toBoundedContinuousFunction‖ ≤
      ‖heatDuhamelPotentialHolderL (E := E) (F := F) (T := T) hα₀ (hα₁.trans one_lt_two).le‖ *
        ‖f‖ :=
    (HolderSpace.norm_toBoundedContinuousFunction_le _).trans (ContinuousLinearMap.le_opNorm _ _)
  have h₁ : ‖heatDuhamelPotentialFDerivL (T := T) f.toBoundedContinuousFunction‖ ≤
      ‖heatDuhamelPotentialFDerivL (E := E) (F := F) (T := T)‖ * ‖f‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (by gcongr; exact f.norm_toBoundedContinuousFunction_le)
  have h₂ := norm_hessianHolder_le hα₀ hα₁ f
  have h₃ := norm_timeField_le hα₀ hα₁ f
  have hLH : ‖traceL (E := E) (F := F)‖ * ‖hessianHolder hα₀ hα₁ f‖ ≤
      ‖traceL (E := E) (F := F)‖ *
        (‖heatDuhamelPotentialHessianL (E := E) (F := F) (T := T) hα₀ hα₁‖ * ‖f‖) := by
    gcongr
  rw [ParabolicC2HolderSpace.norm_eq, potentialTwo, valueL_mk, spatialFDerivL_mk,
    spatialSecondFDerivL_mk, timeDerivL_mk, duhamelBound]
  linarith

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
    (duhamelBound (E := E) (F := F) hα₀ hα₁ T) (norm_potentialTwo_le hα₀ hα₁ hT)

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
      ‖heatDuhamelPotentialL (E := E) (F := F) hα₀ hα₁ hT‖ ≤ C * (1 + T) := by
  obtain ⟨Cg, hCg⟩ := exists_norm_heatDuhamelPotentialFDerivL_le (E := E) (F := F)
  obtain ⟨Ch, hCh⟩ := exists_norm_heatDuhamelPotentialHessianL_le (E := E) (F := F) hα₀ hα₁
  refine ⟨3 + heatKernelMoment E α + Cg + (‖traceL (E := E) (F := F)‖ + 1) * (2 * Ch) + 1,
    fun T hT => (ContinuousLinearMap.opNorm_le_bound _ (duhamelBound_nonneg hα₀ hα₁ T) fun f => by
      rw [heatDuhamelPotentialL_eq_potentialTwo]
      exact norm_potentialTwo_le hα₀ hα₁ hT f).trans ?_⟩
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hCg0 : 0 ≤ Cg := by
    have h1 := (norm_nonneg _).trans (hCg 1)
    simpa using h1
  -- The value operator: `T (2 + M) + max 1 T ≤ (3 + M) (1 + T)`.
  have h₀ := norm_heatDuhamelPotentialHolderL_le (E := E) (F := F) (T := T) hα₀
    (hα₁.trans one_lt_two).le
  push_cast at h₀
  have hmax : max 1 (T : ℝ) ≤ 1 + T := max_le (by linarith) (by linarith)
  have hM : (0 : ℝ) ≤ heatKernelMoment E α := NNReal.coe_nonneg _
  -- The gradient operator: `√T ≤ 1 + T`.
  have hs : √(T : ℝ) ≤ 1 + T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_one_add hT0 (by norm_num) (by norm_num)
  have h₁ : ‖heatDuhamelPotentialFDerivL (E := E) (F := F) (T := T)‖ ≤ Cg * (1 + T) :=
    (hCg T).trans (by gcongr)
  -- The Hessian operator: `1 + (√T)^α ≤ 2 (1 + T)`.
  have hp : √(T : ℝ) ^ (α : ℝ) ≤ 1 + T := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0]
    exact Real.rpow_le_one_add hT0 (by positivity) (by linarith [show (α : ℝ) < 1 from hα₁])
  have h₂ : ‖heatDuhamelPotentialHessianL (E := E) (F := F) (T := T) hα₀ hα₁‖ ≤
      2 * Ch * (1 + T) :=
    (hCh T).trans (by nlinarith [NNReal.coe_nonneg Ch])
  have hL : 0 ≤ ‖traceL (E := E) (F := F)‖ + 1 := by positivity
  have h₂' := mul_le_mul_of_nonneg_left h₂ hL
  unfold duhamelBound
  nlinarith

end TauCeti

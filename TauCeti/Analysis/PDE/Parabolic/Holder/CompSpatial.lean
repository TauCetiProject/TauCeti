/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
public import TauCeti.Analysis.Holder.Bilinear
public import TauCeti.Analysis.Holder.CompLinear
public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace

/-!
# Linear changes of spatial variables on order-two parabolic Hölder spaces

A continuous linear map `e : E →L[ℝ] E'` acts on order-two parabolic Hölder maps by a change of
spatial variables, `u ↦ u ∘ (e × id)`. This file shows that this is a bounded linear map
`C_b^{2+α,1+α/2}(E' × [a, b]) → C_b^{2+α,1+α/2}(E × [a, b])`, with operator norm at most
`max ‖e‖ 1 ^ (2 + α)`, and computes its fields by the chain rule: the gradient and the Hessian
are pulled back by `e`, while the value and the time derivative are simply precomposed. For a
continuous linear equivalence it is an isomorphism, with inverse given by `e⁻¹`.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.compSpatialL`: the change of spatial variables
  `u ↦ u ∘ (e × id)`, with its four fields and operator-norm bound.
* `TauCeti.ParabolicC2HolderSpace.compSpatialCLE`: the change of variables by a continuous linear
  equivalence, as an isomorphism.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

namespace ParabolicC2HolderSpace

variable {α : ℝ≥0} {E E' E'' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- A local shortcut for the norm on Hessians. Without it, instance search for the operator norm
on maps between spaces of bilinear maps fails, for the reason explained in
`TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
private local instance hessNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
private local instance hessNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on Hessians over the target space. -/
private local instance hessNormedAddCommGroup' :
    NormedAddCommGroup (E' →L[ℝ] E' →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians over the target space. -/
private local instance hessNormedSpace' : NormedSpace ℝ (E' →L[ℝ] E' →L[ℝ] F) := inferInstance

/-- The change of spatial variables `u ↦ u ∘ (e × id)` of an order-two parabolic Hölder map. -/
private def compSpatial (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab) :
    ParabolicC2HolderSpace α E F hab :=
  mk ((valueL u).compContinuous ⟨_, (lipschitzWith_slabSpaceMap e.lipschitzWith).continuous⟩)
    ((e.precomp F).compLeftContinuousBounded _
      ((spatialFDerivL u).compContinuous
        ⟨_, (lipschitzWith_slabSpaceMap e.lipschitzWith).continuous⟩))
    ((ContinuousLinearMap.id ℝ _).compHolder₂
      (HolderSpace.const
        (ContinuousLinearMap.postcomp E (e.precomp F) ∘L e.precomp (E' →L[ℝ] F)))
      (HolderSpace.compLipschitzL _ (lipschitzWith_slabSpaceMap e.lipschitzWith)
        (spatialSecondFDerivL u)))
    (HolderSpace.compLipschitzL _ (lipschitzWith_slabSpaceMap e.lipschitzWith) (timeDerivL u))
    (fun t x ↦ by
      simpa [Function.comp_def] using (u.hasSpatialFDerivAt t (e x)).comp x e.hasFDerivAt)
    (fun t x ↦ by
      simpa [Function.comp_def] using (e.precomp F).hasFDerivAt.comp x
        ((u.hasSpatialSecondFDerivAt t (e x)).comp x e.hasFDerivAt))
    (fun x t ↦ by
      simpa [timeExtension_def] using u.hasTimeDerivWithinAt (e x) t)

private theorem compSpatial_apply (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab)
    (p : slab (E := E) a b) : compSpatial e u p = u (slabSpaceMap e p) := by
  simp [compSpatial]

/-- Precomposition of a Hölder field with `(x, t) ↦ (e x, t)` multiplies its norm by at most
`max ‖e‖ 1 ^ α`. -/
private theorem norm_compLipschitzL_slabSpaceMap_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (e : E →L[ℝ] E') (f : HolderSpace α (slab (E := E') a b) G) :
    ‖HolderSpace.compLipschitzL _
        (lipschitzWith_slabSpaceMap (a := a) (b := b) e.lipschitzWith) f‖ ≤
      max ‖e‖ 1 ^ (α : ℝ) * ‖f‖ := by
  have hMα : 1 ≤ max ‖e‖ 1 ^ (α : ℝ) := Real.one_le_rpow (le_max_right _ _) (by positivity)
  have hK : max 1 (((max ‖e‖₊ 1 : ℝ≥0) : ℝ) ^ (α : ℝ)) = max ‖e‖ 1 ^ (α : ℝ) := by
    simpa using max_eq_right hMα
  have h := (HolderSpace.compLipschitzL _ _).le_of_opNorm_le
    (HolderSpace.norm_compLipschitzL_le
      (lipschitzWith_slabSpaceMap (a := a) (b := b) e.lipschitzWith)) f
  rwa [hK] at h

private theorem norm_compSpatial_le (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab) :
    ‖compSpatial e u‖ ≤ max ‖e‖ 1 ^ 2 * max ‖e‖ 1 ^ (α : ℝ) * ‖u‖ := by
  set M := max ‖e‖ 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMα : 1 ≤ M ^ (α : ℝ) := Real.one_le_rpow hM (by positivity)
  -- Bounds for the four fields.
  have h₀ : ‖valueL (compSpatial e u)‖ ≤ ‖valueL u‖ := by
    rw [compSpatial, valueL_mk]
    exact BoundedContinuousFunction.norm_compContinuous_le _ _
  have h₁ : ‖spatialFDerivL (compSpatial e u)‖ ≤ ‖e‖ * ‖spatialFDerivL u‖ := by
    rw [compSpatial, spatialFDerivL_mk]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
    rw [ContinuousLinearMap.compLeftContinuousBounded_apply, ContinuousLinearMap.precomp_apply]
    calc ‖(spatialFDerivL u (slabSpaceMap e p)).comp e‖
        ≤ ‖spatialFDerivL u (slabSpaceMap e p)‖ * ‖e‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖spatialFDerivL u‖ * ‖e‖ := by gcongr; exact (spatialFDerivL u).norm_coe_le_norm _
      _ = ‖e‖ * ‖spatialFDerivL u‖ := mul_comm _ _
  have h₂ : ‖spatialSecondFDerivL (compSpatial e u)‖ ≤
      ‖e‖ ^ 2 * (M ^ (α : ℝ) * ‖spatialSecondFDerivL u‖) := by
    rw [compSpatial, spatialSecondFDerivL_mk]
    refine (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _).trans ?_
    gcongr
    · refine (HolderSpace.norm_const_le _).trans <|
        ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun H ↦ ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.postcomp_apply,
        ContinuousLinearMap.precomp_apply]
      calc ‖H (e v) (e w)‖ ≤ ‖H‖ * ‖e v‖ * ‖e w‖ := H.le_opNorm₂ _ _
        _ ≤ ‖H‖ * (‖e‖ * ‖v‖) * (‖e‖ * ‖w‖) := by gcongr <;> exact e.le_opNorm _
        _ = ‖e‖ ^ 2 * ‖H‖ * ‖v‖ * ‖w‖ := by ring
    · exact norm_compLipschitzL_slabSpaceMap_le e _
  have h₃ : ‖timeDerivL (compSpatial e u)‖ ≤ M ^ (α : ℝ) * ‖timeDerivL u‖ := by
    rw [compSpatial, timeDerivL_mk]
    exact norm_compLipschitzL_slabSpaceMap_le e _
  -- Each field is multiplied by at most `B = M ^ 2 * M ^ α`.
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hB₀ : 1 ≤ M ^ 2 * M ^ (α : ℝ) := one_le_mul_of_one_le_of_one_le (by nlinarith) hMα
  have hB₁ : ‖e‖ ≤ M ^ 2 * M ^ (α : ℝ) :=
    (le_max_left _ _).trans (hM2.trans (le_mul_of_one_le_right (by positivity) hMα))
  have hB₂ : ‖e‖ ^ 2 * M ^ (α : ℝ) ≤ M ^ 2 * M ^ (α : ℝ) := by
    gcongr
    exact le_max_left _ _
  have hB₃ : M ^ (α : ℝ) ≤ M ^ 2 * M ^ (α : ℝ) :=
    le_mul_of_one_le_left (by positivity) (by nlinarith)
  rw [norm_eq, norm_eq u]
  linarith [mul_le_mul_of_nonneg_right hB₀ (norm_nonneg (valueL u)),
    mul_le_mul_of_nonneg_right hB₁ (norm_nonneg (spatialFDerivL u)),
    mul_le_mul_of_nonneg_right hB₂ (norm_nonneg (spatialSecondFDerivL u)),
    mul_le_mul_of_nonneg_right hB₃ (norm_nonneg (timeDerivL u))]

variable (α F hab) in
/-- The change of spatial variables `u ↦ u ∘ (e × id)` by a continuous linear map
`e : E →L[ℝ] E'`, from order-two parabolic Hölder maps on `E' × [a, b]` to those on
`E × [a, b]`, as a continuous linear map. -/
def compSpatialL (e : E →L[ℝ] E') :
    ParabolicC2HolderSpace α E' F hab →L[ℝ] ParabolicC2HolderSpace α E F hab :=
  LinearMap.mkContinuous
    { toFun := compSpatial e
      map_add' u v := by ext p; simp only [compSpatial_apply, add_apply]
      map_smul' c u := by ext p; simp only [compSpatial_apply, smul_apply, RingHom.id_apply] }
    (max ‖e‖ 1 ^ 2 * max ‖e‖ 1 ^ (α : ℝ)) fun u ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact norm_compSpatial_le e u

private theorem compSpatialL_eq_compSpatial (e : E →L[ℝ] E')
    (u : ParabolicC2HolderSpace α E' F hab) : compSpatialL α F hab e u = compSpatial e u :=
  (rfl)

@[simp]
theorem compSpatialL_apply (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab)
    (p : slab (E := E) a b) : compSpatialL α F hab e u p = u (slabSpaceMap e p) := by
  rw [compSpatialL_eq_compSpatial, compSpatial_apply]

/-- Taking a spatial trace commutes with a linear change of spatial variables. -/
@[simp]
theorem spatialTrace_compSpatialL (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab)
    (t : Icc a b) :
    (compSpatialL α F hab e u).spatialTrace t = CkHolderSpace.compLinearL e (u.spatialTrace t) := by
  ext x
  simp

/-- The spatial gradient of `u ∘ (e × id)` is the gradient of `u`, pulled back by `e`. -/
@[simp]
theorem spatialFDerivL_compSpatialL (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab)
    (p : slab (E := E) a b) :
    spatialFDerivL (compSpatialL α F hab e u) p = (spatialFDerivL u (slabSpaceMap e p)).comp e := by
  rw [compSpatialL_eq_compSpatial, compSpatial, spatialFDerivL_mk]
  simp

/-- The spatial Hessian of `u ∘ (e × id)` is the Hessian of `u`, pulled back by `e` in both
slots. -/
@[simp]
theorem spatialSecondFDerivL_compSpatialL (e : E →L[ℝ] E')
    (u : ParabolicC2HolderSpace α E' F hab) (p : slab (E := E) a b) :
    spatialSecondFDerivL (compSpatialL α F hab e u) p =
      (spatialSecondFDerivL u (slabSpaceMap e p)).bilinearComp e e := by
  rw [compSpatialL_eq_compSpatial, compSpatial, spatialSecondFDerivL_mk]
  ext v w
  simp

/-- The time derivative of `u ∘ (e × id)` is the time derivative of `u`, precomposed. -/
@[simp]
theorem timeDerivL_compSpatialL (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab)
    (p : slab (E := E) a b) :
    timeDerivL (compSpatialL α F hab e u) p = timeDerivL u (slabSpaceMap e p) := by
  rw [compSpatialL_eq_compSpatial, compSpatial, timeDerivL_mk, HolderSpace.compLipschitzL_apply]

variable (α F hab) in
/-- The change of spatial variables by `e` has operator norm at most `max ‖e‖ 1 ^ (2 + α)`. -/
theorem norm_compSpatialL_le (e : E →L[ℝ] E') :
    ‖compSpatialL α F hab e‖ ≤ max ‖e‖ 1 ^ 2 * max ‖e‖ 1 ^ (α : ℝ) :=
  have h₀ : 0 ≤ max ‖e‖ 1 := le_max_of_le_right zero_le_one
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (pow_nonneg h₀ 2) (Real.rpow_nonneg h₀ _))
    fun u ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact norm_compSpatial_le e u

variable (α F hab) in
/-- If `‖e‖ ≤ K` with `1 ≤ K`, the change of spatial variables by `e` has operator norm at most
`K ^ (2 + α)`. -/
theorem norm_compSpatialL_le_of_norm_le {e : E →L[ℝ] E'} {K : ℝ} (hK : 1 ≤ K) (he : ‖e‖ ≤ K) :
    ‖compSpatialL α F hab e‖ ≤ K ^ 2 * K ^ (α : ℝ) := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  exact (norm_compSpatialL_le α F hab e).trans
    (mul_le_mul (pow_le_pow_left₀ (by positivity) (max_le he hK) 2)
      (Real.rpow_le_rpow (by positivity) (max_le he hK) (by positivity))
      (by positivity) (by positivity))

/-- The change of spatial variables by the identity does nothing. -/
@[simp]
theorem compSpatialL_id (u : ParabolicC2HolderSpace α E F hab) :
    compSpatialL α F hab (ContinuousLinearMap.id ℝ E) u = u := by
  ext p
  simp

/-- Successive changes of spatial variables compose. -/
theorem compSpatialL_comp (e' : E' →L[ℝ] E'') (e : E →L[ℝ] E')
    (u : ParabolicC2HolderSpace α E'' F hab) :
    compSpatialL α F hab (e'.comp e) u = compSpatialL α F hab e (compSpatialL α F hab e' u) := by
  ext p
  simp [ContinuousLinearMap.coe_comp]

variable (α F hab) in
/-- The change of spatial variables `u ↦ u ∘ (e × id)` by a continuous linear equivalence
`e : E ≃L[ℝ] E'`, as an isomorphism between order-two parabolic Hölder spaces. Its inverse is the
change of variables by `e⁻¹`. -/
def compSpatialCLE (e : E ≃L[ℝ] E') :
    ParabolicC2HolderSpace α E' F hab ≃L[ℝ] ParabolicC2HolderSpace α E F hab :=
  ContinuousLinearEquiv.equivOfInverse (compSpatialL α F hab (e : E →L[ℝ] E'))
    (compSpatialL α F hab (e.symm : E' →L[ℝ] E))
    (fun u ↦ by ext p; simp)
    (fun v ↦ by ext p; simp)

@[simp]
theorem compSpatialCLE_apply (e : E ≃L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab) :
    compSpatialCLE α F hab e u = compSpatialL α F hab (e : E →L[ℝ] E') u :=
  (rfl)

@[simp]
theorem compSpatialCLE_symm_apply (e : E ≃L[ℝ] E') (v : ParabolicC2HolderSpace α E F hab) :
    (compSpatialCLE α F hab e).symm v = compSpatialL α F hab (e.symm : E' →L[ℝ] E) v :=
  (rfl)

end ParabolicC2HolderSpace

end TauCeti

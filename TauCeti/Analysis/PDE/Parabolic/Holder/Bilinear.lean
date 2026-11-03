/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Interpolation
public import TauCeti.Analysis.Holder.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Continuous bilinear operations on order-two parabolic Hölder spaces

A continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` acts pointwise on bounded order-two parabolic
Hölder maps on a slab `E × [a, b]`: for `u ∈ C_b^{2+α,1+α/2}(F)` and `v ∈ C_b^{2+α,1+α/2}(G)`
with `α ≤ 1`, the map `(x, t) ↦ B (u (x, t)) (v (x, t))` belongs to `C_b^{2+α,1+α/2}(H)`. Its
fields are given by the Leibniz rule,

* `D_x (B u v) h = B u (D_x v h) + B (D_x u h) v`;
* `D_x² (B u v) h k = B u (D_x² v h k) + B (D_x u h) (D_x v k) + B (D_x u k) (D_x v h) +
  B (D_x² u h k) v`;
* `∂ₜ (B u v) = B u (∂ₜ v) + B (∂ₜ u) v`, also at the endpoints of `[a, b]`,

and the resulting continuous bilinear map has operator norm at most `1200 ‖B‖`, uniformly over the
spaces and the slab. The Hessian and the time derivative are parabolically `α`-Hölder because the
value and the spatial gradient of an order-two parabolic Hölder map are (the absorption estimate
`ParabolicC2HolderSpace.norm_valueHolderL_add_norm_spatialFDerivHolderL_le`, which is the source of
the constant), and products of bounded Hölder fields are Hölder (`ContinuousLinearMap.compHolder₂`).

With `B` the multiplication of `ℝ` or the scalar multiplication `ℝ × F → F`, this is the product
estimate of the order-two space: multiplying a solution by a space-time cutoff or a smooth weight
stays in the space, with norm controlled by the product of the norms. This is what localization
in parabolic Schauder estimates uses.

## Main declarations

* `ContinuousLinearMap.compParabolicC2Holder₂`: pointwise application of `B` as a continuous
  bilinear map of order-two parabolic Hölder spaces.
* `ContinuousLinearMap.spatialFDerivL_compParabolicC2Holder₂`,
  `ContinuousLinearMap.spatialSecondFDerivL_compParabolicC2Holder₂` and
  `ContinuousLinearMap.timeDerivL_compParabolicC2Holder₂`: the Leibniz rules for its fields.
* `ContinuousLinearMap.norm_compParabolicC2Holder₂_le`: the operator-norm bound `1200 ‖B‖`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 3
  (the parabolic Hölder norms).
-/

public section
noncomputable section

namespace ContinuousLinearMap

open Set TauCeti ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {a b : ℝ} {hab : a < b}

/-- A local shortcut for the norm on `G`-valued gradients. Without these shortcuts, instance search
for the operator norms of `B.precompR E` and of `(B.precompR E).precompR E`, whose domains and
codomains are spaces of gradients and Hessians, fails: the norm instance on such a space only arises
as a nested instance problem during unification. -/
private local instance instNormedAddCommGroupGradient : NormedAddCommGroup (E →L[ℝ] G) :=
  inferInstance
/-- A local shortcut for the norm on `H`-valued Hessians, needed for the same reason. -/
private local instance instNormedAddCommGroupHessian : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] H) :=
  inferInstance
/-- A local shortcut for scalar operations on `H`-valued Hessians, needed for the same reason. -/
private local instance instNormedSpaceHessian : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] H) :=
  inferInstance

variable (B : F →L[ℝ] G →L[ℝ] H) (hα : α ≤ 1)

/-! ### The fields of the pointwise product -/

/-- The value field `B u v`, as a parabolically Hölder field. -/
private def valueField (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) : HolderSpace α (slab (E := E) a b) H :=
  B.compHolder₂ (valueHolderL hα u) (valueHolderL hα v)

/-- The spatial gradient field `B u (D_x v) + B (D_x u) v` of `B u v`. -/
private def spatialFDerivField (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) : HolderSpace α (slab (E := E) a b) (E →L[ℝ] H) :=
  (B.precompR E).compHolder₂ (valueHolderL hα u) (spatialFDerivHolderL hα v) +
    (B.precompL E).compHolder₂ (spatialFDerivHolderL hα u) (valueHolderL hα v)

/-- The spatial Hessian field of `B u v`, the derivative of `spatialFDerivField` term by term. -/
private def spatialSecondFDerivField (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) :
    HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] H) :=
  (((B.precompR E).precompR E).compHolder₂ (valueHolderL hα u) (spatialSecondFDerivL v) +
      ((B.precompR E).precompL E).compHolder₂ (spatialFDerivHolderL hα u)
        (spatialFDerivHolderL hα v)) +
    (((B.precompL E).precompR E).compHolder₂ (spatialFDerivHolderL hα u)
        (spatialFDerivHolderL hα v) +
      ((B.precompL E).precompL E).compHolder₂ (spatialSecondFDerivL u) (valueHolderL hα v))

/-- The time-derivative field `B u (∂ₜ v) + B (∂ₜ u) v` of `B u v`. -/
private def timeDerivField (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) : HolderSpace α (slab (E := E) a b) H :=
  B.compHolder₂ (valueHolderL hα u) (timeDerivL v) +
    B.compHolder₂ (timeDerivL u) (valueHolderL hα v)

/-- The pointwise product `B u v` as an order-two parabolic Hölder map. -/
private def compParabolicC2HolderAux (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) : ParabolicC2HolderSpace α E H hab :=
  ParabolicC2HolderSpace.mk (valueField B hα u v).toBoundedContinuousFunction
    (spatialFDerivField B hα u v).toBoundedContinuousFunction
    (spatialSecondFDerivField B hα u v) (timeDerivField B hα u v)
    (fun t x ↦ by
      simpa [valueField, spatialFDerivField, HolderSpace.add_apply] using
        B.hasFDerivAt_of_bilinear (u.hasSpatialFDerivAt t x) (v.hasSpatialFDerivAt t x))
    (fun t x ↦ by
      refine ((((B.precompR E).hasFDerivAt_of_bilinear (u.hasSpatialFDerivAt t x)
          (v.hasSpatialSecondFDerivAt t x)).add ((B.precompL E).hasFDerivAt_of_bilinear
          (u.hasSpatialSecondFDerivAt t x) (v.hasSpatialFDerivAt t x))).congr_of_eventuallyEq
          (.of_forall fun y ↦ ?_)).congr_fderiv ?_ <;>
        simp [spatialFDerivField, spatialSecondFDerivField, HolderSpace.add_apply])
    (fun x t ↦ by
      simpa [valueField, timeDerivField, timeExtension_def, HolderSpace.add_apply] using
        B.hasDerivWithinAt_of_bilinear (u.hasTimeDerivWithinAt x t) (v.hasTimeDerivWithinAt x t))

private theorem compParabolicC2HolderAux_apply (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) (p : slab (E := E) a b) :
    compParabolicC2HolderAux B hα u v p = B (u p) (v p) := by
  simp [compParabolicC2HolderAux, valueField]

/-- The operator-norm bound for the pointwise product, before bundling. -/
private theorem norm_compParabolicC2HolderAux_le (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) :
    ‖compParabolicC2HolderAux B hα u v‖ ≤ 1200 * ‖B‖ * ‖u‖ * ‖v‖ := by
  set U := ‖u‖
  set V := ‖v‖
  set u₀ := ‖valueHolderL hα u‖
  set u₁ := ‖spatialFDerivHolderL hα u‖
  set v₀ := ‖valueHolderL hα v‖
  set v₁ := ‖spatialFDerivHolderL hα v‖
  set u₂ := ‖spatialSecondFDerivL u‖
  set uₜ := ‖timeDerivL u‖
  set v₂ := ‖spatialSecondFDerivL v‖
  set vₜ := ‖timeDerivL v‖
  -- `precompR` and `precompL` do not increase the norm of a bilinear map.
  have hR : ‖B.precompR E‖ ≤ ‖B‖ := norm_precompR_le _ _
  have hL : ‖B.precompL E‖ ≤ ‖B‖ := norm_precompL_le _ _
  have hRR : ‖(B.precompR E).precompR E‖ ≤ ‖B‖ := (norm_precompR_le _ _).trans hR
  have hRL : ‖(B.precompR E).precompL E‖ ≤ ‖B‖ := (norm_precompL_le _ _).trans hR
  have hLR : ‖(B.precompL E).precompR E‖ ≤ ‖B‖ := (norm_precompR_le _ _).trans hL
  have hLL : ‖(B.precompL E).precompL E‖ ≤ ‖B‖ := (norm_precompL_le _ _).trans hL
  -- The four fields of the product, each bounded by the product rule for `compHolder₂`.
  have h₀ : ‖(valueField B hα u v).toBoundedContinuousFunction‖ ≤ ‖B‖ * u₀ * v₀ :=
    (HolderSpace.norm_toBoundedContinuousFunction_le _).trans (B.norm_compHolder₂_apply_le _ _)
  have h₁ : ‖(spatialFDerivField B hα u v).toBoundedContinuousFunction‖ ≤
      ‖B‖ * u₀ * v₁ + ‖B‖ * u₁ * v₀ :=
    (HolderSpace.norm_toBoundedContinuousFunction_le _).trans ((norm_add_le _ _).trans
      (add_le_add ((B.precompR E).norm_compHolder₂_apply_le _ _ |>.trans (by gcongr))
        ((B.precompL E).norm_compHolder₂_apply_le _ _ |>.trans (by gcongr))))
  have h₂ : ‖spatialSecondFDerivField B hα u v‖ ≤
      ‖B‖ * u₀ * v₂ + ‖B‖ * u₁ * v₁ + (‖B‖ * u₁ * v₁ + ‖B‖ * u₂ * v₀) :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        (((B.precompR E).precompR E).norm_compHolder₂_apply_le _ _ |>.trans (by gcongr))
        (((B.precompR E).precompL E).norm_compHolder₂_apply_le _ _ |>.trans (by gcongr))))
      ((norm_add_le _ _).trans (add_le_add
        (((B.precompL E).precompR E).norm_compHolder₂_apply_le _ _ |>.trans (by gcongr))
        (((B.precompL E).precompL E).norm_compHolder₂_apply_le _ _ |>.trans (by gcongr)))))
  have hₜ : ‖timeDerivField B hα u v‖ ≤ ‖B‖ * u₀ * vₜ + ‖B‖ * uₜ * v₀ :=
    (norm_add_le _ _).trans (add_le_add (B.norm_compHolder₂_apply_le _ _)
      (B.norm_compHolder₂_apply_le _ _))
  -- The lower-order Hölder norms are absorbed into the order-two norm, with constant `24`.
  have hu : u₀ + u₁ ≤ 24 * U := norm_valueHolderL_add_norm_spatialFDerivHolderL_le_mul hα u
  have hv : v₀ + v₁ ≤ 24 * V := norm_valueHolderL_add_norm_spatialFDerivHolderL_le_mul hα v
  have hu' : u₂ + uₜ ≤ U := norm_spatialSecondFDerivL_add_norm_timeDerivL_le u
  have hv' : v₂ + vₜ ≤ V := norm_spatialSecondFDerivL_add_norm_timeDerivL_le v
  have hB := norm_nonneg B
  have hu₀ := norm_nonneg (valueHolderL hα u)
  have hu₁ := norm_nonneg (spatialFDerivHolderL hα u)
  have hv₀ := norm_nonneg (valueHolderL hα v)
  have hv₁ := norm_nonneg (spatialFDerivHolderL hα v)
  have hu₂ := norm_nonneg (spatialSecondFDerivL u)
  have huₜ := norm_nonneg (timeDerivL u)
  have hv₂ := norm_nonneg (spatialSecondFDerivL v)
  have hvₜ := norm_nonneg (timeDerivL v)
  -- Every product of field norms is bounded by `2 (u₀ + u₁) (v₀ + v₁) + u₀ (v₂ + vₜ) +
  -- (u₂ + uₜ) v₀ ≤ 1200 U V`.
  have hsum : u₀ * v₀ + (u₀ * v₁ + u₁ * v₀) + (u₀ * v₂ + 2 * (u₁ * v₁) + u₂ * v₀) +
      (u₀ * vₜ + uₜ * v₀) ≤ 1200 * (U * V) := by
    have hU : 0 ≤ U := norm_nonneg u
    have hV : 0 ≤ V := norm_nonneg v
    nlinarith [mul_le_mul hu hv (by positivity) (by positivity),
      mul_le_mul (show u₀ ≤ 24 * U by linarith) hv' (by positivity) (by positivity),
      mul_le_mul hu' (show v₀ ≤ 24 * V by linarith) (by positivity) (by positivity)]
  rw [ParabolicC2HolderSpace.norm_eq, compParabolicC2HolderAux, valueL_mk, spatialFDerivL_mk,
    spatialSecondFDerivL_mk, timeDerivL_mk]
  nlinarith [mul_le_mul_of_nonneg_left hsum hB]

/-! ### The bundled bilinear map -/

/-- For `α ≤ 1`, pointwise application `(u, v) ↦ B u v` of a continuous bilinear map, as a
continuous bilinear map of bounded order-two parabolic Hölder spaces on a slab. -/
def compParabolicC2Holder₂ :
    ParabolicC2HolderSpace α E F hab →L[ℝ] ParabolicC2HolderSpace α E G hab →L[ℝ]
      ParabolicC2HolderSpace α E H hab :=
  (LinearMap.mk₂ ℝ (compParabolicC2HolderAux B hα)
    (fun _ _ _ ↦ ParabolicC2HolderSpace.ext fun _ ↦ by
      simp [compParabolicC2HolderAux_apply])
    (fun _ _ _ ↦ ParabolicC2HolderSpace.ext fun _ ↦ by
      simp [compParabolicC2HolderAux_apply])
    (fun _ _ _ ↦ ParabolicC2HolderSpace.ext fun _ ↦ by
      simp [compParabolicC2HolderAux_apply])
    (fun _ _ _ ↦ ParabolicC2HolderSpace.ext fun _ ↦ by
      simp [compParabolicC2HolderAux_apply])).mkContinuous₂
    (1200 * ‖B‖) (norm_compParabolicC2HolderAux_le B hα)

/- This is `LinearMap.mkContinuous₂_apply` followed by `LinearMap.mk₂_apply`, both proved by `rfl`
in Mathlib. Using them here fails: instantiating `LinearMap.mkContinuous₂_apply` reports an invalid
projection out of `ParabolicC2HolderSpace`, whose definition as a submodule is not exposed, and
`rw` or `simp only` with them cannot match the goal. So the equation is closed by `rfl` directly. -/
private theorem compParabolicC2Holder₂_eq (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) :
    B.compParabolicC2Holder₂ hα u v = compParabolicC2HolderAux B hα u v := (rfl)

@[simp]
theorem compParabolicC2Holder₂_apply (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) (p : slab (E := E) a b) :
    B.compParabolicC2Holder₂ hα u v p = B (u p) (v p) := by
  rw [compParabolicC2Holder₂_eq, compParabolicC2HolderAux_apply]

/-- **The Leibniz rule for the spatial gradient.** -/
@[simp]
theorem spatialFDerivL_compParabolicC2Holder₂ (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) (p : slab (E := E) a b) (h : E) :
    spatialFDerivL (B.compParabolicC2Holder₂ hα u v) p h =
      B (u p) (spatialFDerivL v p h) + B (spatialFDerivL u p h) (v p) := by
  simp [compParabolicC2Holder₂_eq, compParabolicC2HolderAux, spatialFDerivField]

/-- **The Leibniz rule for the spatial Hessian.** -/
@[simp]
theorem spatialSecondFDerivL_compParabolicC2Holder₂ (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) (p : slab (E := E) a b) (h k : E) :
    spatialSecondFDerivL (B.compParabolicC2Holder₂ hα u v) p h k =
      B (u p) (spatialSecondFDerivL v p h k) + B (spatialFDerivL u p h) (spatialFDerivL v p k) +
        (B (spatialFDerivL u p k) (spatialFDerivL v p h) +
          B (spatialSecondFDerivL u p h k) (v p)) := by
  simp [compParabolicC2Holder₂_eq, compParabolicC2HolderAux, spatialSecondFDerivField,
    HolderSpace.add_apply]

/-- **The Leibniz rule for the time derivative**, also at the endpoints of the slab. -/
@[simp]
theorem timeDerivL_compParabolicC2Holder₂ (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) (p : slab (E := E) a b) :
    timeDerivL (B.compParabolicC2Holder₂ hα u v) p =
      B (u p) (timeDerivL v p) + B (timeDerivL u p) (v p) := by
  simp [compParabolicC2Holder₂_eq, compParabolicC2HolderAux, timeDerivField, HolderSpace.add_apply]

/-- **The product estimate.** Pointwise application of `B` to order-two parabolic Hölder maps has
operator norm at most `1200 ‖B‖`, uniformly over the spaces and the slab. -/
theorem norm_compParabolicC2Holder₂_le :
    ‖B.compParabolicC2Holder₂ (E := E) (hab := hab) hα‖ ≤ 1200 * ‖B‖ :=
  opNorm_le_bound₂ _ (by positivity) fun u v ↦ by
    rw [compParabolicC2Holder₂_eq]
    exact norm_compParabolicC2HolderAux_le B hα u v

/-- The order-two norm of `B u v` is at most `1200 ‖B‖ ‖u‖ ‖v‖`. -/
theorem norm_compParabolicC2Holder₂_apply_le (u : ParabolicC2HolderSpace α E F hab)
    (v : ParabolicC2HolderSpace α E G hab) :
    ‖B.compParabolicC2Holder₂ hα u v‖ ≤ 1200 * ‖B‖ * ‖u‖ * ‖v‖ := by
  rw [compParabolicC2Holder₂_eq]
  exact norm_compParabolicC2HolderAux_le B hα u v

/-- Applying the flipped bilinear map is the flipped bilinear map of order-two spaces. -/
@[simp]
theorem compParabolicC2Holder₂_flip :
    B.flip.compParabolicC2Holder₂ (E := E) (hab := hab) hα =
      (B.compParabolicC2Holder₂ hα).flip := by
  ext v u p
  simp

/-- On constant maps, `B` acts by its value on the constants. -/
@[simp]
theorem compParabolicC2Holder₂_const (f : F) (g : G) :
    B.compParabolicC2Holder₂ hα (ParabolicC2HolderSpace.const (E := E) (hab := hab) f)
        (ParabolicC2HolderSpace.const g) =
      ParabolicC2HolderSpace.const (B f g) := by
  ext p
  simp

end ContinuousLinearMap

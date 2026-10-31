/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
public import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Constant-coefficient parabolic operators as the heat operator in linear coordinates

A continuous linear map `e : E →L[ℝ] E'` acts on order-two parabolic Hölder maps by a change of
spatial variables, `u ↦ u ∘ (e × id)`. This file shows that this is a bounded linear map
`C_b^{2+α,1+α/2}(E' × [a, b]) → C_b^{2+α,1+α/2}(E × [a, b])`, with operator norm at most
`max ‖e‖ 1 ^ (2 + α)`, and computes its fields by the chain rule: the gradient and the Hessian
are pulled back by `e`, while the value and the time derivative are simply precomposed. For a
continuous linear equivalence it is an isomorphism, with inverse given by `e⁻¹`.

The application is the reduction of a constant-coefficient parabolic operator to the heat
operator. Let `A` be a constant matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and write
`P_A u = ∂ₜu - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. There is a linear automorphism `e` of `ℝⁿ`, stretching lengths by
at most `√Λ` and with inverse stretching lengths by at most `1 / √λ`, such that

`P_I (u ∘ (e × id)) = (P_A u) ∘ (e × id)`

for every `u ∈ C_b^{2+α,1+α/2}`, where `P_I = ∂ₜ - Δ` is the heat operator. As `u ↦ u ∘ (e × id)`
is an isomorphism whose norm and inverse norm are bounded in terms of `λ`, `Λ` and `α`, this is
the identity through which the solution theory of the heat operator in parabolic Hölder spaces
passes to `P_A`. The pointwise identity is the elliptic one,
`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`, applied to each time slice.

## Main declarations

* `TauCeti.ParabolicSpaceTime.slabSpaceMap`: the slab map `(x, t) ↦ (f x, t)`, Lipschitz for the
  parabolic distance when `f` is.
* `TauCeti.ParabolicC2HolderSpace.compSpatialL`: the change of spatial variables
  `u ↦ u ∘ (e × id)`, with its four fields and operator-norm bound.
* `TauCeti.ParabolicC2HolderSpace.compSpatialCLE`: the change of variables by a continuous linear
  equivalence, as an isomorphism.
* `TauCeti.ParabolicC2HolderSpace.exists_continuousLinearEquiv_heatOperator_compSpatialL_eq`: a
  constant-coefficient operator is the heat operator in suitable linear coordinates.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables).
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

/-! ### Change of spatial variables -/

section CompSpatial

/-- A local shortcut for the norm on Hessians. Without it, instance search for the operator norm
on maps between spaces of bilinear maps fails, for the reason explained in
`TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on Hessians over the target space. -/
local instance : NormedAddCommGroup (E' →L[ℝ] E' →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians over the target space. -/
local instance : NormedSpace ℝ (E' →L[ℝ] E' →L[ℝ] F) := inferInstance

/-- Precomposition `g ↦ g ∘ e` of covectors with `e`. -/
private abbrev gradPrecomp (e : E →L[ℝ] E') : (E' →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ E E' F).flip e

/-- Precomposition `H ↦ H (e ·) (e ·)` of bilinear maps with `e` in both slots. -/
private abbrev hessPrecomp (e : E →L[ℝ] E') :
    (E' →L[ℝ] E' →L[ℝ] F) →L[ℝ] (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.compL ℝ E (E' →L[ℝ] F) (E →L[ℝ] F) (gradPrecomp e) ∘L
    (ContinuousLinearMap.compL ℝ E E' (E' →L[ℝ] F)).flip e

private theorem hessPrecomp_apply (e : E →L[ℝ] E') (H : E' →L[ℝ] E' →L[ℝ] F) :
    hessPrecomp e H = H.bilinearComp e e := by
  ext v w
  simp

private theorem norm_hessPrecomp_le (e : E →L[ℝ] E') :
    ‖hessPrecomp (F := F) e‖ ≤ ‖e‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun H ↦ ?_
  rw [hessPrecomp_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  rw [ContinuousLinearMap.bilinearComp_apply]
  calc ‖H (e v) (e w)‖ ≤ ‖H‖ * ‖e v‖ * ‖e w‖ := H.le_opNorm₂ _ _
    _ ≤ ‖H‖ * (‖e‖ * ‖v‖) * (‖e‖ * ‖w‖) := by gcongr <;> exact e.le_opNorm _
    _ = ‖e‖ ^ 2 * ‖H‖ * ‖v‖ * ‖w‖ := by ring

/-- The slab map `(x, t) ↦ (e x, t)` is `max ‖e‖ 1`-Lipschitz for the parabolic distance. -/
private theorem lipschitzWith_slabSpaceMap_clm (e : E →L[ℝ] E') :
    LipschitzWith (max ‖e‖₊ 1) (slabSpaceMap (a := a) (b := b) e) :=
  lipschitzWith_slabSpaceMap e.lipschitzWith

/-- The change of spatial variables `u ↦ u ∘ (e × id)` of an order-two parabolic Hölder map. -/
private def compSpatial (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab) :
    ParabolicC2HolderSpace α E F hab :=
  mk ((valueL u).compContinuous ⟨_, (lipschitzWith_slabSpaceMap_clm e).continuous⟩)
    ((gradPrecomp e).compLeftContinuousBounded _
      ((spatialFDerivL u).compContinuous ⟨_, (lipschitzWith_slabSpaceMap_clm e).continuous⟩))
    ((ContinuousLinearMap.id ℝ _).compHolder₂ (HolderSpace.const (hessPrecomp e))
      (HolderSpace.compLipschitzL _ (lipschitzWith_slabSpaceMap_clm e) (spatialSecondFDerivL u)))
    (HolderSpace.compLipschitzL _ (lipschitzWith_slabSpaceMap_clm e) (timeDerivL u))
    (fun t x ↦ by
      simpa [Function.comp_def] using (u.hasSpatialFDerivAt t (e x)).comp x e.hasFDerivAt)
    (fun t x ↦ by
      simpa [Function.comp_def] using (gradPrecomp e).hasFDerivAt.comp x
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
    ‖HolderSpace.compLipschitzL _ (lipschitzWith_slabSpaceMap_clm (a := a) (b := b) e) f‖ ≤
      max ‖e‖ 1 ^ (α : ℝ) * ‖f‖ := by
  have hMα : 1 ≤ max ‖e‖ 1 ^ (α : ℝ) := Real.one_le_rpow (le_max_right _ _) (by positivity)
  have hK : max 1 (((max ‖e‖₊ 1 : ℝ≥0) : ℝ) ^ (α : ℝ)) = max ‖e‖ 1 ^ (α : ℝ) := by
    simpa using max_eq_right hMα
  have h := (HolderSpace.compLipschitzL _ _).le_of_opNorm_le
    (HolderSpace.norm_compLipschitzL_le (lipschitzWith_slabSpaceMap_clm (a := a) (b := b) e)) f
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
    rw [ContinuousLinearMap.compLeftContinuousBounded_apply]
    calc ‖(spatialFDerivL u (slabSpaceMap e p)).comp e‖
        ≤ ‖spatialFDerivL u (slabSpaceMap e p)‖ * ‖e‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖spatialFDerivL u‖ * ‖e‖ := by gcongr; exact (spatialFDerivL u).norm_coe_le_norm _
      _ = ‖e‖ * ‖spatialFDerivL u‖ := mul_comm _ _
  have h₂ : ‖spatialSecondFDerivL (compSpatial e u)‖ ≤
      ‖e‖ ^ 2 * (M ^ (α : ℝ) * ‖spatialSecondFDerivL u‖) := by
    rw [compSpatial, spatialSecondFDerivL_mk]
    refine (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _).trans ?_
    gcongr
    · exact (HolderSpace.norm_const_le _).trans (norm_hessPrecomp_le e)
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
  rw [compSpatialL_eq_compSpatial, compSpatial, spatialSecondFDerivL_mk,
    ContinuousLinearMap.compHolder₂_apply, HolderSpace.const_apply,
    HolderSpace.compLipschitzL_apply, ContinuousLinearMap.id_apply, hessPrecomp_apply]

/-- The time derivative of `u ∘ (e × id)` is the time derivative of `u`, precomposed. -/
@[simp]
theorem timeDerivL_compSpatialL (e : E →L[ℝ] E') (u : ParabolicC2HolderSpace α E' F hab)
    (p : slab (E := E) a b) :
    timeDerivL (compSpatialL α F hab e u) p = timeDerivL u (slabSpaceMap e p) := by
  rw [compSpatialL_eq_compSpatial, compSpatial, timeDerivL_mk, HolderSpace.compLipschitzL_apply]

variable (α F hab) in
/-- The change of spatial variables by `e` has operator norm at most `max ‖e‖ 1 ^ (2 + α)`. -/
theorem norm_compSpatialL_le (e : E →L[ℝ] E') :
    ‖compSpatialL α F hab e‖ ≤ max ‖e‖ 1 ^ 2 * max ‖e‖ 1 ^ (α : ℝ) := by
  have h₀ : 0 ≤ max ‖e‖ 1 := le_max_of_le_right zero_le_one
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (pow_nonneg h₀ 2) (Real.rpow_nonneg h₀ _)) fun u ↦ ?_
  rw [compSpatialL_eq_compSpatial]
  exact norm_compSpatial_le e u

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

end CompSpatial

/-! ### Reduction of a constant-coefficient operator to the heat operator -/

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A constant-coefficient parabolic operator is the heat operator in suitable linear
coordinates.** Let `A` be a square matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let
`P_A u = ∂ₜu - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` act on `C_b^{2+α,1+α/2}(ℝⁿ × [a, b])`. There is a continuous linear
automorphism `e` of `ℝⁿ = EuclideanSpace ℝ ι`, with `‖e⁻¹ x‖ ≤ ‖x‖ / √λ` and `‖e y‖ ≤ √Λ ‖y‖`, such
that the heat operator `P_I = ∂ₜ - Δ` satisfies

`P_I (u ∘ (e × id)) = (P_A u) ∘ (e × id)`

for every `u`. Since `u ↦ u ∘ (e × id)` is an isomorphism (`compSpatialCLE`), this transfers
solvability and estimates for the heat operator to `P_A`. -/
theorem exists_continuousLinearEquiv_heatOperator_compSpatialL_eq (hα : α ≤ 1)
    {A : Matrix ι ι ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) :
    ∃ e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι,
      (∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) ∧ (∀ y, ‖e y‖ ≤ √Lam * ‖y‖) ∧
      ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab,
        euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) 0 0
            (compSpatialL α ℝ hab (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) u) =
          HolderSpace.compLipschitzL _
            (lipschitzWith_slabSpaceMap (e : _ →L[ℝ] _).lipschitzWith)
            (euclideanParabolicOperatorL hα (fun i j ↦ HolderSpace.const (A i j)) 0 0 u) := by
  obtain ⟨e, he₁, he₂, he⟩ :=
    PDE.exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam hA hA'
  refine ⟨e, he₁, he₂, fun u ↦ HolderSpace.ext fun p ↦ ?_⟩
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  -- On the time slice through `t`, both sides are the elliptic identity for `u(·, t)`.
  have hgg : fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) (e x) =
      spatialSecondFDerivL u (slabMk (e x) t) := by
    have hg : fderiv ℝ (fun y ↦ u (slabMk y t)) = fun y ↦ spatialFDerivL u (slabMk y t) :=
      funext (u.fderiv_eq t)
    rw [hg, u.fderiv_spatialFDeriv_eq]
  have key := he _ x (u.contDiff_spatialSlice t).contDiffAt
  rw [laplacian_comp_continuousLinearEquiv_right_apply e (EuclideanSpace.basisFun ι ℝ)] at key
  simp only [u.iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.basisFun_apply, hgg, smul_eq_mul] at key
  simp only [euclideanParabolicOperatorL_apply, HolderSpace.compLipschitzL_apply,
    HolderSpace.const_apply, Pi.zero_apply, HolderSpace.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, timeDerivL_compSpatialL, spatialSecondFDerivL_compSpatialL,
    slabSpaceMap_slabMk, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
    Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, key]

end Euclidean

end ParabolicC2HolderSpace

end TauCeti

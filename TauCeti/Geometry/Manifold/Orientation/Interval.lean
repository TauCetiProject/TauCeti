/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation
public import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# The increasing orientation of a closed interval

The preferred left half-line chart has positive sign and the preferred right half-line chart
has negative sign. These source signs define the increasing orientation despite the reversing
transition between the two half-line charts.
-/

public section

noncomputable section

open Set Fact.Manifold
open scoped Manifold

namespace TauCeti

variable {a b : ℝ} [hab : Fact (a < b)]

/-- The preferred interval transition derivative is the product of the two chart signs. -/
theorem tangentCoordChange_Icc (α β x : Icc a b)
    (hx : x ∈ (extChartAt (𝓡∂ 1) α).source) :
    tangentCoordChange (𝓡∂ 1) α β x =
      ((if (β : ℝ) < b then (1 : ℝ) else -1) *
        (if (α : ℝ) < b then (1 : ℝ) else -1)) •
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  have hd := hasFDerivWithinAt_subtypeVal_extChartAt_Icc_symm α
    ((extChartAt (𝓡∂ 1) α).map_source hx)
  let L := (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap
  have hlin (r : ℝ) : L.comp (ContinuousLinearMap.pi
      (fun _ : Fin 1 ↦ r • EuclideanSpace.proj 0)) =
        r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
    ext v i
    rw [Subsingleton.elim i 0]
    rfl
  by_cases hβ : (β : ℝ) < b
  · have hp := hasFDerivWithinAt_pi.mpr (fun _ : Fin 1 ↦ hd.sub_const a)
    have h := L.hasFDerivAt.comp_hasFDerivWithinAt (extChartAt (𝓡∂ 1) α x) hp
    have he : (extChartAt (𝓡∂ 1) β ∘ (extChartAt (𝓡∂ 1) α).symm) =
        fun z ↦ L (fun _ : Fin 1 ↦ ((extChartAt (𝓡∂ 1) α).symm z : ℝ) - a) := by
      funext z
      simp only [Function.comp_apply, extChartAt_Icc_apply, hβ, ↓reduceIte]
      rfl
    rw [tangentCoordChange_def, he]
    apply (h.fderivWithin ((𝓡∂ 1).uniqueDiffOn _ (extChartAt_target_subset_range α
      ((extChartAt (𝓡∂ 1) α).map_source hx)))).trans
    rw [hlin]
    simp only [hβ, ↓reduceIte, one_mul]
  · have hp := hasFDerivWithinAt_pi.mpr (fun _ : Fin 1 ↦ hd.const_sub b)
    have h := L.hasFDerivAt.comp_hasFDerivWithinAt (extChartAt (𝓡∂ 1) α x) hp
    have he : (extChartAt (𝓡∂ 1) β ∘ (extChartAt (𝓡∂ 1) α).symm) =
        fun z ↦ L (fun _ : Fin 1 ↦ b - ((extChartAt (𝓡∂ 1) α).symm z : ℝ)) := by
      funext z
      simp only [Function.comp_apply, extChartAt_Icc_apply, hβ, ↓reduceIte]
      rfl
    rw [tangentCoordChange_def, he]
    apply (h.fderivWithin ((𝓡∂ 1).uniqueDiffOn _ (extChartAt_target_subset_range α
      ((extChartAt (𝓡∂ 1) α).map_source hx)))).trans
    simp only [hβ, ↓reduceIte, neg_one_mul]
    rw [← neg_smul, hlin]

/-- The increasing interval orientation is represented by positive signs in left half-line
charts and negative signs in right half-line charts. -/
def Manifold.OrientationLift.interval (a b : ℝ) [Fact (a < b)] :
    Manifold.OrientationLift (𝓡∂ 1) (Icc a b) (Fin 1) where
  modelOrientation := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation
  card_eq := by simp
  sign α _ := if (α : ℝ) < b then 1 else -1
  locallyConstant_sign _ := IsLocallyConstant.const _
  compatible α β x hα _ := by
    rw [← tangentCoordChange_def, tangentCoordChange_Icc α β x
      (by simpa only [extChartAt_source] using hα)]
    have hn : LinearMap.det (-LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin 1)) = -1 := by
      rw [← neg_one_smul ℝ (LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin 1)), LinearMap.det_smul]
      simp
    by_cases ha : (α : ℝ) < b <;> by_cases hb : (β : ℝ) < b <;>
      simp [ha, hb, ContinuousLinearMap.det, hn]

/-- The interval lift uses the standard positive model orientation. -/
@[simp]
theorem Manifold.OrientationLift.interval_modelOrientation (a b : ℝ) [Fact (a < b)] :
    (interval a b).modelOrientation = (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation :=
  (rfl)

/-- The interval lift's chart sign is determined by the actual preferred chart. -/
@[simp]
theorem Manifold.OrientationLift.interval_sign (a b : ℝ) [Fact (a < b)] (α : Icc a b)
    (x : (chartAt (EuclideanHalfSpace 1) α).source) :
    (interval a b).sign α x = if (α : ℝ) < b then 1 else -1 := (rfl)

/-- The canonical increasing orientation of a nondegenerate closed interval. -/
def Manifold.Orientation.interval (a b : ℝ) [Fact (a < b)] :
    Manifold.Orientation (𝓡∂ 1) (Icc a b) (Fin 1) :=
  Manifold.Orientation.mk (Manifold.OrientationLift.interval a b)

/-- The canonical interval orientation is represented by its explicit left/right chart lift. -/
@[simp]
theorem Manifold.Orientation.interval_eq_mk (a b : ℝ) [Fact (a < b)] :
    interval a b = Manifold.Orientation.mk (Manifold.OrientationLift.interval a b) := (rfl)

/-- The increasing interval orientation has positive own-chart coordinates except at the
right endpoint, whose preferred half-line chart points towards decreasing real coordinates. -/
theorem Manifold.Orientation.orientationAt_interval (a b : ℝ) [Fact (a < b)] (x : Icc a b) :
    Manifold.Orientation.orientationAt (interval a b) x =
      if (x : ℝ) < b then (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation
      else -(EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation := by
  rw [interval_eq_mk, Manifold.Orientation.orientationAt_mk,
    Manifold.OrientationLift.orientationAt_eq,
    Manifold.OrientationLift.chartOrientation_eq_ite, OrientationLift.interval_sign,
    OrientationLift.interval_modelOrientation]
  split_ifs <;> simp_all <;> rfl

/-- The derivative of interval inclusion, identified with the real target model, as an
invertible continuous linear map. Its own-chart sign changes at the right endpoint. -/
def subtypeValIccTangentEquiv (x : Icc a b) : TangentSpace (𝓡∂ 1) x ≃L[ℝ] ℝ :=
  if (x : ℝ) < b then PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  else (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).trans (ContinuousLinearEquiv.neg ℝ)

/-- The tangent equivalence is the actual inclusion derivative, with the canonical real
model tangent identification on its target. -/
theorem subtypeValIccTangentEquiv_toContinuousLinearMap (x : Icc a b) :
    (subtypeValIccTangentEquiv x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : ℝ)).toContinuousLinearMap.comp
        (mfderiv (𝓡∂ 1) 𝓘(ℝ) Subtype.val x) := by
  rw [mfderiv_subtypeVal_Icc]
  ext v
  by_cases hx : (x : ℝ) < b <;>
    simp only [subtypeValIccTangentEquiv, hx, ↓reduceIte, one_smul, neg_smul]
  all_goals rfl

/-- Interval inclusion carries its increasing tangent orientation to the positive real
orientation at every point, including both endpoints. -/
theorem Manifold.Orientation.map_orientationAt_interval (x : Icc a b) :
    _root_.Orientation.map (Fin 1) (subtypeValIccTangentEquiv x).toLinearEquiv
      ((interval a b).orientationAt x) = (Module.Basis.singleton (Fin 1) ℝ).orientation := by
  classical
  rw [orientationAt_interval]
  let B := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  let R := Module.Basis.singleton (Fin 1) ℝ
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    if (x : ℝ) < b then PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
    else (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).trans (ContinuousLinearEquiv.neg ℝ)
  -- Tangent fibers are model copies; state the orientation calculation in that model.
  change _root_.Orientation.map (Fin 1) e.toLinearEquiv
    (if (x : ℝ) < b then B.orientation else -B.orientation) = R.orientation
  by_cases hx : (x : ℝ) < b
  · rw [ite_eq_left hx, ← Module.Basis.orientation_map]
    have he : B.map e.toLinearEquiv = R := by
      ext i
      rw [Subsingleton.elim i 0]
      simp [B, R, e, hx, EuclideanSpace.basisFun_apply,
        PiLp.equivOfUnique_apply]
    exact congrArg Module.Basis.orientation he
  · rw [ite_eq_right hx, _root_.Orientation.map_neg, ← Module.Basis.orientation_map]
    have he : B.map e.toLinearEquiv = R.unitsSMul (fun _ ↦ -1) := by
      ext i
      rw [Subsingleton.elim i 0]
      simp [B, R, e, hx, EuclideanSpace.basisFun_apply,
        PiLp.equivOfUnique_apply, Module.Basis.unitsSMul_apply]
    rw [he, Module.Basis.orientation_unitsSMul]
    simp only [Fin.prod_univ_one, inv_neg, inv_one]
    rw [Module.Ray.units_smul_of_neg (-1) (by norm_num)]
    exact _root_.neg_neg R.orientation

/-- The interval charted structure, with its model dimension written as a successor so that
zero-dimensional boundary constructions infer the canonical interval charts. -/
@[reducible] local instance intervalSuccessorChartedSpace :
    ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc a b) :=
  instIccChartedSpace a b

local instance : IsManifold (𝓡∂ (0 + 1)) 1 (Icc a b) := instIsManifoldIcc a b

/-- The canonical zero-dimensional charted structure on the two interval endpoints. -/
@[reducible] local instance intervalBoundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 0))
    ((𝓡∂ (0 + 1)).boundary (Icc a b)) := boundaryChartedSpace (n := 0)

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 1
    ((𝓡∂ (0 + 1)).boundary (Icc a b)) := isManifold_boundary (n := 0) (Icc a b) one_ne_zero

/-- The left endpoint of an increasing closed interval has negative boundary orientation. -/
theorem orientationAt_boundaryOrientation_interval_left :
    Manifold.Orientation.orientationAt
        (boundaryOrientation (n := 0) (Manifold.Orientation.interval a b))
        ⟨⊥, Icc_isBoundaryPoint_bot⟩ =
      -(EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.orientation := by
  rw [orientationAt_boundaryOrientation, Manifold.Orientation.orientationAt_interval]
  simp only [Icc.coe_bot, hab.out, ↓reduceIte, halfSpaceBoundaryOrientation_basisFun]
  rfl

/-- The right endpoint of an increasing closed interval has positive boundary orientation. -/
theorem orientationAt_boundaryOrientation_interval_right :
    Manifold.Orientation.orientationAt
        (boundaryOrientation (n := 0) (Manifold.Orientation.interval a b))
        ⟨⊤, Icc_isBoundaryPoint_top⟩ =
      (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.orientation := by
  rw [orientationAt_boundaryOrientation, Manifold.Orientation.orientationAt_interval]
  simp only [Icc.coe_top, lt_self_iff_false, ↓reduceIte,
    halfSpaceBoundaryOrientation_neg, halfSpaceBoundaryOrientation_basisFun]
  exact _root_.neg_neg ((EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.orientation)

end TauCeti

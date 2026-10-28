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

/-- Interval inclusion carries its increasing tangent orientation to the positive real
orientation at every point, including both endpoints. -/
theorem Manifold.Orientation.map_orientationAt_interval (x : Icc a b) :
    _root_.Orientation.map (Fin 1) (subtypeValIccTangentEquiv x).toLinearEquiv
      ((interval a b).orientationAt x) = (Module.Basis.singleton (Fin 1) ℝ).orientation := by
  classical
  rw [orientationAt_interval]
  let B := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  let R := Module.Basis.singleton (Fin 1) ℝ
  by_cases hx : (x : ℝ) < b
  · rw [ite_eq_left hx, ← Module.Basis.orientation_map]
    have he : B.map (subtypeValIccTangentEquiv x).toLinearEquiv = R := by
      ext i
      rw [Subsingleton.elim i 0]
      simp [B, R, hx, EuclideanSpace.basisFun_apply]
    exact congrArg Module.Basis.orientation he
  · rw [ite_eq_right hx, _root_.Orientation.map_neg, ← Module.Basis.orientation_map]
    have he : B.map (subtypeValIccTangentEquiv x).toLinearEquiv =
        R.unitsSMul (fun _ ↦ -1) := by
      ext i
      rw [Subsingleton.elim i 0]
      simp [B, R, hx, EuclideanSpace.basisFun_apply, Module.Basis.unitsSMul_apply]
    rw [he, Module.Basis.orientation_unitsSMul]
    simp only [Fin.prod_univ_one, inv_neg, inv_one]
    rw [Module.Ray.units_smul_of_neg (-1) (by norm_num)]
    exact _root_.neg_neg R.orientation

/-- The increasing and decreasing interval orientations admit tangent bases whose actual
inclusion velocities are respectively one and minus one, including at the endpoints. -/
theorem exists_interval_tangent_bases {a b : ℝ} [Fact (a < b)] (x : Icc a b) :
    ∃ B C : Module.Basis (Fin 1) ℝ (EuclideanSpace ℝ (Fin 1)),
      B.orientation = (Manifold.Orientation.interval a b).orientationAt x ∧
      C.orientation = (-Manifold.Orientation.interval a b).orientationAt x ∧
      subtypeValIccTangentEquiv x (B 0) = 1 ∧ subtypeValIccTangentEquiv x (C 0) = -1 := by
  let e := subtypeValIccTangentEquiv x
  let B := (Module.Basis.singleton (Fin 1) ℝ).map e.symm.toLinearEquiv
  have hB : B.orientation = (Manifold.Orientation.interval a b).orientationAt x := by
    rw [Module.Basis.orientation_map]
    rw [← Manifold.Orientation.map_orientationAt_interval x]
    exact (Orientation.map (Fin 1) e.toLinearEquiv).symm_apply_apply _
  let C := B.unitsSMul (fun _ ↦ (-1 : ℝˣ))
  have hC : C.orientation = (-Manifold.Orientation.interval a b).orientationAt x := by
    rw [Manifold.Orientation.orientationAt_neg, ← hB]
    -- Express the negated manifold orientation on its model before applying basis scaling.
    change (B.unitsSMul _).orientation = -B.orientation
    rw [Module.Basis.orientation_unitsSMul]
    simp only [Fin.prod_univ_one, inv_neg, inv_one]
    exact Module.Ray.units_smul_of_neg (-1) (by norm_num) _
  refine ⟨B, C, hB, hC, ?_, ?_⟩
  · simp [B, e, Module.Basis.map_apply]
  · by_cases hx : (x : ℝ) < b <;>
      simp [C, Module.Basis.unitsSMul_apply, B, e, Module.Basis.map_apply, hx]

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
  simp only [Icc.coe_bot, hab.out, ↓reduceIte, Orientation.halfSpaceBoundaryOrientation_basisFun]
  rfl

/-- The right endpoint of an increasing closed interval has positive boundary orientation. -/
theorem orientationAt_boundaryOrientation_interval_right :
    Manifold.Orientation.orientationAt
        (boundaryOrientation (n := 0) (Manifold.Orientation.interval a b))
        ⟨⊤, Icc_isBoundaryPoint_top⟩ =
      (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.orientation := by
  rw [orientationAt_boundaryOrientation, Manifold.Orientation.orientationAt_interval]
  simp only [Icc.coe_top, lt_self_iff_false, ↓reduceIte,
    Orientation.halfSpaceBoundaryOrientation_neg, Orientation.halfSpaceBoundaryOrientation_basisFun]
  exact _root_.neg_neg ((EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.orientation)

end TauCeti

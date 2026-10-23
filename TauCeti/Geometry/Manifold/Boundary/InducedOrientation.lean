/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.Orientation.Basic

/-!
# The induced boundary orientation

The normal coordinate of a half-space transition has strictly positive derivative. Restricting
chart signs therefore constructs the actual boundary orientation. The model orientation uses
the outward-first convention, so the standard ambient orientation induces the negative standard
orientation on the coordinate-zero boundary, including a zero-dimensional boundary.
-/

public section

noncomputable section

open Set
open scoped Manifold



namespace TauCeti.Manifold.OrientationLift

open TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero

/-- Restriction of the source signs to boundary charts, with the outward-first model orientation. -/
def boundary (l : OrientationLift (𝓡∂ (n + 1)) M (Fin (n + 1))) :
    OrientationLift 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) (Fin n) := by
  refine {
    modelOrientation := Orientation.halfSpaceBoundaryOrientation l.modelOrientation
    card_eq := by simp
    sign α x := l.sign (α : M) ⟨x.val.val, by
      simpa only [boundaryChartedSpace_chartAt_source, mem_preimage] using x.property⟩
    locallyConstant_sign := ?_
    compatible := ?_ }
  · intro α
    exact (l.locallyConstant_sign (α : M)).comp_continuous
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  · intro α β x hα hβ
    have hα' : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (α : M)).source := by
      simpa only [boundaryChartedSpace_chartAt_source, mem_preimage] using hα
    have hβ' : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (β : M)).source := by
      simpa only [boundaryChartedSpace_chartAt_source, mem_preimage] using hβ
    have hd := l.compatible (α : M) (β : M) (x : M) hα' hβ'
    obtain ⟨a, ha, he⟩ := exists_pos_det_tangentCoordChange_boundary
      (by simpa only [extChartAt_source] using hα)
      (by simpa only [extChartAt_source] using hβ)
    rw [← tangentCoordChange_def, he] at hd
    rw [← tangentCoordChange_def]
    have he' : ((l.sign (α : M) ⟨(x : M), hα'⟩ : ℤ) : ℝ) *
        ((l.sign (β : M) ⟨(x : M), hβ'⟩ : ℤ) : ℝ) *
        (a * (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α β x).det) =
      a * (((l.sign (α : M) ⟨(x : M), hα'⟩ : ℤ) : ℝ) *
        ((l.sign (β : M) ⟨(x : M), hβ'⟩ : ℤ) : ℝ) *
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) α β x).det) := by ring
    rw [he'] at hd
    exact (mul_pos_iff_of_pos_left ha).mp hd

/-- The boundary lift uses the outward-first model orientation. -/
@[simp]
theorem boundary_modelOrientation (l : OrientationLift (𝓡∂ (n + 1)) M (Fin (n + 1))) :
    l.boundary.modelOrientation =
      Orientation.halfSpaceBoundaryOrientation l.modelOrientation := (rfl)

/-- The boundary lift restricts the actual ambient source-indexed signs. -/
@[simp]
theorem boundary_sign (l : OrientationLift (𝓡∂ (n + 1)) M (Fin (n + 1)))
    (α : (𝓡∂ (n + 1)).boundary M)
    (x : (chartAt (EuclideanSpace ℝ (Fin n)) α).source) :
    l.boundary.sign α x = l.sign (α : M) ⟨x.val.val, by
      simpa only [boundaryChartedSpace_chartAt_source, mem_preimage] using x.property⟩ := (rfl)

/-- Diagonal reversal commutes with passage to the boundary lift. -/
@[simp]
theorem boundary_flip (l : OrientationLift (𝓡∂ (n + 1)) M (Fin (n + 1))) :
    l.flip.boundary = l.boundary.flip := by
  apply OrientationLift.ext
  · simp only [boundary, flip_modelOrientation]
    exact Orientation.halfSpaceBoundaryOrientation_neg l.modelOrientation
  · funext α x
    simp only [flip_sign, boundary]

end TauCeti.Manifold.OrientationLift

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero

/-- The canonical boundary orientation, with the outward vector first. -/
def boundaryOrientation (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1))) :
    Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((𝓡∂ (n + 1)).boundary M) (Fin n) :=
  Manifold.Orientation.mk (Classical.choose o.exists_lift).boundary

/-- Passage to the boundary orientation is independent of the chosen representative lift. -/
@[simp]
theorem boundaryOrientation_mk (l : Manifold.OrientationLift (𝓡∂ (n + 1)) M (Fin (n + 1))) :
    boundaryOrientation (Manifold.Orientation.mk l) = Manifold.Orientation.mk l.boundary := by
  have h := Classical.choose_spec (Manifold.Orientation.mk l).exists_lift
  rw [boundaryOrientation]
  rcases (Manifold.Orientation.mk_eq_mk_iff _ _).mp h with h | h
  · rw [h]
  · rw [h, Manifold.OrientationLift.boundary_flip]
    exact (Manifold.Orientation.mk_eq_mk_iff _ _).mpr (.inr rfl)

private theorem orientationAt_boundaryOrientation_mk
    (l : Manifold.OrientationLift (𝓡∂ (n + 1)) M (Fin (n + 1)))
    (x : (𝓡∂ (n + 1)).boundary M) :
    Manifold.Orientation.orientationAt (boundaryOrientation (Manifold.Orientation.mk l)) x =
      Orientation.halfSpaceBoundaryOrientation
        (Manifold.Orientation.orientationAt (Manifold.Orientation.mk l) (x : M)) := by
  rw [boundaryOrientation_mk, Manifold.Orientation.orientationAt_mk,
    Manifold.OrientationLift.orientationAt_eq, Manifold.OrientationLift.chartOrientation_eq_ite,
    Manifold.Orientation.orientationAt_mk,
    Manifold.OrientationLift.orientationAt_eq, Manifold.OrientationLift.chartOrientation_eq_ite]
  -- Unfold the induced lift: its source subtype proof differs from the ambient lift,
  -- so a rewrite cannot identify the two dependent source arguments directly.
  change (if l.sign (x : M) ⟨(x : M), _⟩ = 1 then
      Orientation.halfSpaceBoundaryOrientation l.modelOrientation
      else -Orientation.halfSpaceBoundaryOrientation l.modelOrientation) = _
  split_ifs with h
  · rfl
  · exact (Orientation.halfSpaceBoundaryOrientation_neg l.modelOrientation).symm

/-- Outward-first: an oriented boundary basis preceded by any outward vector is oriented for
the ambient manifold. This characterization includes zero-dimensional boundaries. -/
theorem boundaryOrientation_spec
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    (x : (𝓡∂ (n + 1)).boundary M) {v : TangentSpace (𝓡∂ (n + 1)) (x : M)}
    (hv : IsOutwardPointing (x : M) v)
    (b : Module.Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (b' : Module.Basis (Fin (n + 1)) ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)))
    (hb' : ⇑b' = Fin.cons v (fun i ↦
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x (b i))) :
    b.orientation = Manifold.Orientation.orientationAt (boundaryOrientation o) x ↔
      b'.orientation = Manifold.Orientation.orientationAt o (x : M) := by
  obtain ⟨l, rfl⟩ := o.exists_lift
  rw [orientationAt_boundaryOrientation_mk]
  have hv' : (fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦ w 0) v < 0 := by
    have h := hv.coordinate_deriv_neg
    rw [mfderiv_extChartAt_self] at h
    exact h
  apply Orientation.halfSpaceBoundaryOrientation_spec _ hv' b b'
  rw [mfderiv_subtypeVal_boundary] at hb'
  convert hb' using 1 <;> rfl

/-- The induced boundary orientation at each point is the outward-first half-space orientation. -/
theorem orientationAt_boundaryOrientation
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    (x : (𝓡∂ (n + 1)).boundary M) :
    Manifold.Orientation.orientationAt (boundaryOrientation o) x =
      Orientation.halfSpaceBoundaryOrientation (Manifold.Orientation.orientationAt o (x : M)) := by
  obtain ⟨l, rfl⟩ := o.exists_lift
  exact orientationAt_boundaryOrientation_mk l x

/-- Reversing the ambient orientation reverses the induced boundary orientation. -/
@[simp]
theorem boundaryOrientation_neg
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1))) :
    boundaryOrientation (-o) = -boundaryOrientation o := by
  apply Manifold.Orientation.ext
  intro x
  rw [Manifold.Orientation.orientationAt_neg, orientationAt_boundaryOrientation,
    orientationAt_boundaryOrientation, Manifold.Orientation.orientationAt_neg]
  exact Orientation.halfSpaceBoundaryOrientation_neg (Manifold.Orientation.orientationAt o (x : M))

/-- The standard half-space orientation induces the negative standard orientation on its
coordinate-zero boundary. The formula also applies to the zero-dimensional boundary of a ray. -/
theorem orientationAt_boundaryOrientation_model (n : ℕ)
    (x : (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1))) :
    Manifold.Orientation.orientationAt (boundaryOrientation
      (Manifold.Orientation.model (I := 𝓡∂ (n + 1))
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation (by simp))) x =
      -(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation := by
  rw [orientationAt_boundaryOrientation, Manifold.Orientation.orientationAt_model]
  exact Orientation.halfSpaceBoundaryOrientation_basisFun n

end TauCeti

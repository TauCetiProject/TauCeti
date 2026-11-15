/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Orientation
public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation

/-!
# Planar velocities and induced boundary orientation

An orientation-preserving tangent identification with the complex plane sends an outward-first
frame to `(-I * v, v)`. Consequently, a boundary tangent parametrization with velocity `v` is
positive whenever the transported normal `-I * v` points outward. The derivative in the statement
is the actual inclusion derivative of the intrinsic boundary manifold.
-/

public section
noncomputable section

open scoped Manifold

namespace TauCeti.Green

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (1 + 1)) M]
  [IsManifold (𝓡∂ (1 + 1)) 1 M]

local instance : IsManifold (𝓡 1) 1 ((𝓡∂ (1 + 1)).boundary M) :=
  isManifold_boundary M one_ne_zero

/-- A planar boundary parametrization is positive for the induced orientation when its
clockwise quarter-turn normal points outward and the actual ambient tangent identification
preserves orientation. No integral or coordinate sign identity is assumed. -/
theorem map_orientation_eq_boundaryOrientation_of_outwardFirst
    (o : Manifold.Orientation (𝓡∂ (1 + 1)) M (Fin 2)) (x : (𝓡∂ (1 + 1)).boundary M)
    (F : TangentSpace (𝓡∂ (1 + 1)) (x : M) ≃L[ℝ] ℂ)
    (hF : Orientation.map (Fin 2) F.toLinearEquiv (o.orientationAt (x : M)) =
      Complex.orientation)
    (e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] TangentSpace (𝓡 1) x) (v : ℂ)
    (hv : F (mfderiv (𝓡 1) (𝓡∂ (1 + 1)) (Subtype.val : (𝓡∂ (1 + 1)).boundary M → M) x
      (e ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0))) = v)
    (hout : IsOutwardPointing (x : M) (F.symm (-Complex.I * v))) :
    Orientation.map (Fin 1) e.toLinearEquiv
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
        (boundaryOrientation o).orientationAt x := by
  have hv0 : v ≠ 0 := by
    intro h
    apply hout.ne_zero
    rw [h, mul_zero, map_zero]
  let b := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.map e.toLinearEquiv
  let b' := (outwardFirstBasis v hv0).map F.symm.toLinearEquiv
  have hb' : ⇑b' = Fin.cons (F.symm (-Complex.I * v))
      (fun i ↦ mfderiv (𝓡 1) (𝓡∂ (1 + 1)) (Subtype.val : (𝓡∂ (1 + 1)).boundary M → M) x (b i)) := by
    funext i
    fin_cases i
    · -- Evaluate the mapped basis at index zero before using its outward-first definition.
      change F.symm (outwardFirstBasis v hv0 0) = _
      rw [outwardFirstBasis_apply]
      rfl
    · -- Evaluate the mapped basis at index one before using its tangential component.
      change F.symm (outwardFirstBasis v hv0 1) = _
      rw [outwardFirstBasis_apply]
      -- Normalize the singleton index and mapped basis before applying the velocity hypothesis.
      change F.symm v = mfderiv (𝓡 1) (𝓡∂ (1 + 1))
        (Subtype.val : (𝓡∂ (1 + 1)).boundary M → M) x (b 0)
      apply F.injective
      rw [F.apply_symm_apply]
      exact hv.symm
  have hb'o : b'.orientation = o.orientationAt (x : M) := by
    rw [Module.Basis.orientation_map, orientation_outwardFirstBasis]
    apply (Orientation.map (Fin 2) F.toLinearEquiv).injective
    -- Turn transport by the inverse linear equivalence into the inverse orientation equivalence.
    change (Orientation.map (Fin 2) F.toLinearEquiv)
      ((Orientation.map (Fin 2) F.toLinearEquiv).symm Complex.orientation) = _
    rw [Equiv.apply_symm_apply]
    exact hF.symm
  have hb := (boundaryOrientation_spec o x hout b b' hb').mpr hb'o
  rw [Module.Basis.orientation_map] at hb
  exact hb

end TauCeti.Green

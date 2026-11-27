/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Connected
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.StandardComodule
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Center

/-!
# Check: Lie–Kolchin needs an algebraically closed field

The special orthogonal group `SO₂` over `ℝ` is geometrically connected (main's
`TauCeti.SpecialOrthogonal.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two`)
and commutative on points over every commutative ring
(main's `Matrix.SpecialOrthogonalGroup.mul_comm_of_le_two`), but its standard comodule `ℝ²` has
no nonzero weight vector
(`TauCeti.Examples.LieKolchinSpecialOrthogonalTwo.not_hasNonzeroWeightVector`): the rational point
rotation by `90°` (main's `TauCeti.Matrix.SpecialOrthogonalGroup.coordinateRotation 0 1`) would
act on a weight vector by a real scalar, and it has no real eigenvector.
So the conclusion of the Lie–Kolchin theorem fails over the non-algebraically-closed field `ℝ`.
-/

public section

open Matrix TauCeti

noncomputable section

-- Mathlib's `Matrix.orthogonalGroup` over a commutative ring uses this star structure.
attribute [local instance] starRingOfComm

namespace TauCeti.Examples.LieKolchinSpecialOrthogonalTwo

/-- `SO₂` over `ℝ` is geometrically connected. -/
example :
    geometricallyConnectedCommHopfAlgProperty ℝ (SpecialOrthogonal.coordinateHopfAlgebra ℝ 2) :=
  SpecialOrthogonal.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two ℝ

/-- **`SO₂` is commutative**: special orthogonal `2 × 2` matrices over a commutative ring
commute. -/
example {R : Type*} [CommRing R] (g h : specialOrthogonalGroup (Fin 2) R) : g * h = h * g :=
  SpecialOrthogonalGroup.mul_comm_of_le_two le_rfl g h

/-- Rotation by `90°`, the coordinate rotation `!![0, -1; 1, 0]`, has no real eigenvector. -/
theorem eq_zero_of_coordinateRotation_mulVec_eq_smul {a : ℝ} {v : Fin 2 → ℝ}
    (h : (Matrix.SpecialOrthogonalGroup.coordinateRotation (R := ℝ) (0 : Fin 2) 1 (by decide) :
      Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v = a • v) :
    v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg a]
  have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg a]
  ext i
  fin_cases i
  exacts [hv0, hv1]

/-- **The standard comodule of `SO₂` over `ℝ` has no weight vector**: the rational point rotation
by `90°` would act on it by a real scalar. -/
theorem not_hasNonzeroWeightVector :
    letI := SpecialOrthogonal.standardComodule ℝ 2
    ¬Comodule.HasNonzeroWeightVector ℝ (SpecialOrthogonal.coordinateHopfAlgebra ℝ 2)
      (Fin 2 → ℝ) := by
  let := SpecialOrthogonal.standardComodule ℝ 2
  rw [Comodule.hasNonzeroWeightVector_iff]
  rintro ⟨v, c, hv, -, hcoact⟩
  let g := (SpecialOrthogonal.pointsMulEquiv ℝ 2 (A := ℝ)).symm
    (Matrix.SpecialOrthogonalGroup.coordinateRotation 0 1 (by decide))
  have h := SpecialOrthogonal.basePointsRepresentation_eq_mulVec ℝ 2 g v
  rw [Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, hcoact] at h
  simp only [g, MulEquiv.apply_symm_apply] at h
  exact hv <|
    eq_zero_of_coordinateRotation_mulVec_eq_smul (a := g.ofConv c) (by simpa using h.symm)

end TauCeti.Examples.LieKolchinSpecialOrthogonalTwo

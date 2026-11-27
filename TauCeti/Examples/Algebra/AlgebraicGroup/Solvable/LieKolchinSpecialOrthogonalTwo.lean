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

/-!
# Check: Lie–Kolchin needs an algebraically closed field

The special orthogonal group `SO₂` over `ℝ` is geometrically connected (main's
`TauCeti.SpecialOrthogonal.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two`)
and commutative on points over every commutative ring
(`TauCeti.Examples.LieKolchinSpecialOrthogonalTwo.mul_comm`), but its standard comodule `ℝ²` has
no nonzero weight vector
(`TauCeti.Examples.LieKolchinSpecialOrthogonalTwo.not_hasNonzeroWeightVector`): the rational point
rotation by `90°` would act on a weight vector by a real scalar, and it has no real eigenvector.
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

/-- A special orthogonal `2 × 2` matrix is `!![a, -b; b, a]`: its transpose is its inverse, the
adjugate. -/
theorem transpose_eq_adjugate {R : Type*} [CommRing R] {A : Matrix (Fin 2) (Fin 2) R}
    (hA : A ∈ specialOrthogonalGroup (Fin 2) R) : Aᵀ = adjugate A := by
  obtain ⟨hA, hdet⟩ := _root_.Matrix.mem_specialOrthogonalGroup_iff.mp hA
  have : TrivialStar R := ⟨fun _ ↦ rfl⟩
  have h1 : Aᵀ * A = 1 := by
    have := hA.1
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  calc Aᵀ = Aᵀ * (A * adjugate A) := by rw [mul_adjugate, hdet, one_smul, Matrix.mul_one]
    _ = adjugate A := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **`SO₂` is commutative**: special orthogonal `2 × 2` matrices over a commutative ring
commute. -/
theorem mul_comm {R : Type*} [CommRing R] (g h : specialOrthogonalGroup (Fin 2) R) :
    g * h = h * g := by
  have hg := congrFun₂ (transpose_eq_adjugate g.property)
  have hh := congrFun₂ (transpose_eq_adjugate h.property)
  have g00 := hg 0 0
  have g01 := hg 0 1
  have h00 := hh 0 0
  have h01 := hh 0 1
  simp [adjugate_fin_two] at g00 g01 h00 h01
  refine Subtype.ext (Matrix.ext fun i j ↦ ?_)
  simp only [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
    simp only [g00, g01, h00, h01] <;> ring

/-- Rotation by `90°`, `!![0, -1; 1, 0]`. -/
def rotation : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- Rotation by `90°` is special orthogonal. -/
theorem rotation_mem : rotation ∈ specialOrthogonalGroup (Fin 2) ℝ := by
  refine _root_.Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose]
  · simp [rotation, det_fin_two]

/-- Rotation by `90°` has no real eigenvector. -/
theorem eq_zero_of_rotation_mulVec_eq_smul {a : ℝ} {v : Fin 2 → ℝ} (h : rotation *ᵥ v = a • v) :
    v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotation, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
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
  let g := (SpecialOrthogonal.pointsMulEquiv ℝ 2 (A := ℝ)).symm ⟨rotation, rotation_mem⟩
  have h := SpecialOrthogonal.basePointsRepresentation_eq_mulVec ℝ 2 g v
  rw [Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, hcoact] at h
  simp only [g, MulEquiv.apply_symm_apply] at h
  exact hv (eq_zero_of_rotation_mulVec_eq_smul (a := g.ofConv c) (by simpa using h.symm))

end TauCeti.Examples.LieKolchinSpecialOrthogonalTwo

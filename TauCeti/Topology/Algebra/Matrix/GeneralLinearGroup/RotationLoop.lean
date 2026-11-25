/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LeftMulMatrix
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal

import Mathlib.RingTheory.Complex
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.Matrix.Polar.Deformation
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Euclidean
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.LeftMulMatrix

/-!
# The rotation loop of a coordinate plane is not nullhomotopic

For `k ≥ 2`, the **rotation loop** `TauCeti.circleRotationLoop` sends a unit complex number `z`
to the invertible real `k × k` matrix which rotates the plane of the first two coordinates by `z`,
`!![Re z, -Im z; Im z, Re z]`, and is the identity on the remaining coordinates. It is the
identity stabilization (`TauCeti.stabilizeGL`) of the left multiplication matrix of `z` in the
basis `1, i` of `ℂ`. This file proves that the loop is not homotopic to the constant loop
relative to the base point `1`, in `GL (Fin k) ℝ`.

The proof lifts the loop through the compact real Spin double cover. Let `e₀, e₁` be the first
two standard basis vectors. The Spin rotation path `CliffordAlgebra.spinRotationPath` of the pair
`(e₁, e₀)` runs from `1` to `-1`, and at time `t` it projects to the rotation of the plane by
`exp (2π i t)` (`TauCeti.coe_symm_realCliffordSpinProjectionZero_spinRotationPath`). So the
rotation loop, run along `t ↦ exp (2π i t)`, lifts to a path which does not close up. A based
nullhomotopy in `GL (Fin k) ℝ` is first pushed into the special orthogonal group by the unitary
polar factor: the polar factor of an orthogonal matrix is itself, and the determinant of the
polar factor is a continuous sign, which is `1` on the connected square because it is `1` at a
corner. Lifting the resulting homotopy relative to the endpoints, the endpoints of the lifts of
the rotation loop and of the constant loop would agree, forcing `-1 = 1` in the Spin group.

Evaluated on the real circle, the matrix `!![x, -y; y, x]` over the coordinate ring
`ℝ[x, y] / (x² + y² - 1)` gives exactly this loop, and every identity stabilization of it gives
the corresponding loop of larger size. This is the topological input to the classical argument
that no identity stabilization of that matrix is a product of elementary matrices, whose evaluated
loops are nullhomotopic, so that it defines a nontrivial class in `SK₁` of the circle ring.

## Main definitions

* `TauCeti.circleRotationLoop`: the loop `z ↦ diag (!![Re z, -Im z; Im z, Re z], 1)` in
  `GL (Fin k) ℝ`, for `2 ≤ k`.

## Main results

* `TauCeti.coe_symm_realCliffordSpinProjectionZero_spinRotationPath`: the Spin rotation path of
  `(e₁, e₀)` lifts the rotation loop through the compact Spin double cover.
* `TauCeti.not_homotopicRel_circleRotationLoop_const`: the rotation loop is not homotopic to the
  constant loop relative to the base point.

## References

* C. A. Weibel, *The K-book: An introduction to algebraic K-theory*, Graduate Studies in
  Mathematics 145, American Mathematical Society, 2013, Example III.1.5.4.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter I, Section 2.
-/

public section

noncomputable section

open Matrix CliffordAlgebra
open scoped unitInterval Real

namespace TauCeti

/-! ### The rotation loop -/

/-- **The rotation loop of the first coordinate plane** of `ℝᵏ`, for `2 ≤ k`: the unit complex
number `z` goes to the matrix which rotates the plane of the first two coordinates by `z`,
`!![Re z, -Im z; Im z, Re z]`, and fixes the other coordinates. -/
def circleRotationLoop {k : ℕ} (hk : 2 ≤ k) : C(Circle, GL (Fin k) ℝ) where
  toFun z := stabilizeGL ℝ hk (unitsLeftMulMatrix Complex.basisOneI (Circle.toUnits z))
  continuous_toFun := (continuous_stabilizeGL hk).comp
    ((continuous_unitsLeftMulMatrix Complex.basisOneI).comp Circle.continuous_toUnits)

/-- The rotation loop is the identity stabilization of the left multiplication matrix. -/
theorem circleRotationLoop_apply {k : ℕ} (hk : 2 ≤ k) (z : Circle) :
    circleRotationLoop hk z =
      stabilizeGL ℝ hk (unitsLeftMulMatrix Complex.basisOneI (Circle.toUnits z)) :=
  (rfl)

/-- The entries of the rotation loop: the rotation `!![Re z, -Im z; Im z, Re z]` in the first two
rows and columns, and the identity matrix elsewhere. -/
theorem coe_circleRotationLoop_apply {k : ℕ} (hk : 2 ≤ k) (z : Circle) (i j : Fin k) :
    (circleRotationLoop hk z : Matrix (Fin k) (Fin k) ℝ) i j =
      if hij : (i : ℕ) < 2 ∧ (j : ℕ) < 2 then
        !![(z : ℂ).re, -(z : ℂ).im; (z : ℂ).im, (z : ℂ).re] ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
  simp [circleRotationLoop_apply, coe_stabilizeGL_apply, Algebra.leftMulMatrix_complex]

/-- The rotation loop takes the value `1` at the base point `1`. -/
@[simp]
theorem circleRotationLoop_one {k : ℕ} (hk : 2 ≤ k) : circleRotationLoop hk 1 = 1 := by
  rw [circleRotationLoop_apply, map_one, map_one, map_one]

/-! ### The lift through the Spin double cover -/

/-- The circle subgroup of `Spin` in the plane of `e₁, e₀` acts on the standard basis vectors by
the rotation matrix of the square: the image of `eⱼ` is column `j` of the rotation loop at
`z²`. -/
private theorem spinVectorAction_spinCircle_single (n : ℕ) (z : Circle) (i j : Fin (n + 2)) :
    spinVectorAction (realCliffordForm (n + 2) 0)
        (spinCircle (realCliffordForm (n + 2) 0) (Pi.single 1 1) (Pi.single 0 1)
          (isOrtho_realCliffordForm_single (by simp) 1 1)
          (by rw [realCliffordForm_zero_single_one, realCliffordForm_zero_single_one, mul_one]) z)
        (Pi.single j 1) i =
      (circleRotationLoop (Nat.le_add_left 2 n) (z ^ 2) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
        i j := by
  rw [coe_circleRotationLoop_apply]
  rcases j with ⟨_ | _ | j, hj⟩
  · rw [Fin.zero_eta, spinVectorAction_spinCircle_right,
      realCliffordForm_zero_single_one, mul_one]
    rcases i with ⟨_ | _ | i, hi⟩ <;> simp [Fin.ext_iff]
  · rw [Fin.mk_one, spinVectorAction_spinCircle_left,
      realCliffordForm_zero_single_one, mul_one]
    rcases i with ⟨_ | _ | i, hi⟩ <;> simp [Fin.ext_iff]
  · rw [spinVectorAction_spinCircle_of_isOrtho _ _ (isOrtho_realCliffordForm_single
      (by simp [Fin.ext_iff]) 1 1) (isOrtho_realCliffordForm_single (by simp [Fin.ext_iff]) 1 1)]
    rcases i with ⟨_ | _ | i, hi⟩ <;> simp [Pi.single_apply, Fin.ext_iff, Matrix.one_apply]

/-- **The Spin lift of the rotation loop.** Let `e₀, e₁` be the first two standard basis vectors
of `ℝⁿ⁺²`. The Spin rotation path of the pair `(e₁, e₀)`, which runs from `1` to `-1` in the
compact Spin group, projects at time `t` to the rotation loop at `exp (2π i t)`. -/
theorem coe_symm_realCliffordSpinProjectionZero_spinRotationPath (n : ℕ) (t : I) :
    ((QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm (n + 2)).symm
        (realCliffordSpinProjectionZero (n + 2)
          (spinRotationPath (realCliffordForm (n + 2) 0) (Pi.single 1 1) (Pi.single 0 1)
            (realCliffordForm_zero_single_one _ 1) (realCliffordForm_zero_single_one _ 0)
            (isOrtho_realCliffordForm_single (by simp) 1 1) t)) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) =
      circleRotationLoop (Nat.le_add_left 2 n) (Circle.exp (2 * π * t)) := by
  ext i j
  simp only [CliffordAlgebra.coe_symm_realCliffordSpinProjectionZero_apply, spinRotationPath_apply,
    spinRotation_eq_spinCircle, spinVectorAction_spinCircle_single, ← Circle.exp_natCast_mul,
    Nat.cast_ofNat, mul_assoc]

/-! ### The rotation loop is not nullhomotopic -/

section NotNullhomotopic

open scoped MatrixOrder Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable (n : ℕ)

/-- The Spin rotation path of `(e₁, e₀)` in compact `Spin(n + 2)`, from `1` to `-1`. -/
private def spinLift :=
  spinRotationPath (realCliffordForm (n + 2) 0) (Pi.single 1 1) (Pi.single 0 1)
    (realCliffordForm_zero_single_one _ 1) (realCliffordForm_zero_single_one _ 0)
    (isOrtho_realCliffordForm_single (by simp) 1 1)

/-- The rotation loop at `exp (2π i t)` is the invertible matrix of a special orthogonal
matrix, the projection of the Spin lift at time `t`. -/
private theorem circleRotationLoop_exp_eq_toUnits (t : I) :
    circleRotationLoop (Nat.le_add_left 2 n) (Circle.exp (2 * π * t)) =
      Unitary.toUnits (⟨_, ((QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm
        (n + 2)).symm (realCliffordSpinProjectionZero (n + 2) (spinLift n t))).property.1⟩ :
          unitary (Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)) :=
  Units.ext <| by
    rw [Unitary.val_toUnits_apply]
    exact (coe_symm_realCliffordSpinProjectionZero_spinRotationPath n t).symm

/-- A based nullhomotopy of the rotation loop in `GL (Fin (n + 2)) ℝ` gives a homotopy relative to
the endpoints from the projection of the Spin lift to the constant path in `SO(n + 2)`. Run the
nullhomotopy along `s ↦ exp (2π i s)` and take unitary polar factors; their determinant is a
continuous sign on the square, equal to `1` at a corner, hence everywhere. -/
private theorem homotopicRel_comp_spinLift
    (H : (circleRotationLoop (Nat.le_add_left 2 n)).HomotopyRel (.const Circle 1) {1}) :
    ContinuousMap.HomotopicRel
      ((spinLift n).map (realCliffordSpinProjectionZero (n + 2)).continuous).toContinuousMap
      (.const I 1) {0, 1} := by
  -- The nullhomotopy run along the loop `s ↦ exp (2π i s)`.
  let F : C(I × I, GL (Fin (n + 2)) ℝ) := H.toContinuousMap.comp
    (ContinuousMap.prodMap (.id I) (Circle.exp.comp ⟨fun s : I => 2 * π * s, by fun_prop⟩))
  have hF0 (s : I) : F (0, s) = circleRotationLoop _ (Circle.exp (2 * π * s)) :=
    H.apply_zero _
  have hF1 (s : I) : F (1, s) = 1 := H.apply_one _
  have hFends (t : I) (s : I) (hs : s ∈ ({0, 1} : Set I)) : F (t, s) = 1 := by
    have he : Circle.exp (2 * π * s) = 1 := by
      rcases hs with rfl | rfl <;> simp
    simpa [F, he] using H.eq_fst t (Set.mem_singleton (1 : Circle))
  have hU : Continuous fun p => ((F p).polarUnitary : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :=
    (GeneralLinearGroup.contMDiff_coe_polarUnitary (n := Fin (n + 2)) (𝕜 := ℝ)
      (k := 0)).continuous.comp F.continuous
  -- The polar factors have determinant `1`: a continuous sign which is `1` at `(0, 0)`.
  have hdet (p : I × I) : ((F p).polarUnitary : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ).det = 1 := by
    rcases isPreconnected_univ.eq_one_or_eq_neg_one_of_sq_eq hU.matrix_det.continuousOn
      (fun p _ => sq_eq_one_iff.2 (det_eq_one_or_neg_one_of_mem_orthogonalGroup
        (F p).polarUnitary.property)) with h | h
    · exact h (Set.mem_univ p)
    · have h0 : _ = _ := h (Set.mem_univ (0, 0))
      simp only [hFends 0 0 (by simp), Units.polarUnitary_one, Pi.neg_apply, Pi.one_apply] at h0
      norm_num at h0
  let Φ := QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm (n + 2)
  refine ⟨{
    toFun := fun p => Φ ⟨(F p).polarUnitary, (F p).polarUnitary.property, hdet p⟩
    continuous_toFun := Φ.continuous.comp (hU.subtype_mk _)
    map_zero_left := fun s => ?_
    map_one_left := fun s => ?_
    prop' := fun t s hs => ?_ }⟩
  · simp only [hF0, circleRotationLoop_exp_eq_toUnits, Units.polarUnitary_toUnits]
    exact Φ.apply_symm_apply _
  · simp only [hF1, Units.polarUnitary_one]
    exact map_one Φ
  · have h := hFends t s hs
    rcases hs with rfl | rfl <;> simp [h, Subtype.ext_iff]

end NotNullhomotopic

/-- **The rotation loop is not nullhomotopic.** For `k ≥ 2`, the loop
`z ↦ diag (!![Re z, -Im z; Im z, Re z], 1)` in `GL (Fin k) ℝ` is not homotopic to the constant
loop `1` relative to the base point `1` of the circle. Its lift through the compact Spin double
cover runs from `1` to `-1`, whereas a based nullhomotopy would lift to one ending at `1`. -/
theorem not_homotopicRel_circleRotationLoop_const {k : ℕ} (hk : 2 ≤ k) :
    ¬ (circleRotationLoop hk).HomotopicRel (.const Circle 1) {1} := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rintro ⟨H⟩
  have cov := isCoveringMap_realCliffordSpinProjectionZero (n + 2)
  -- Lifting from `1`, the two homotopic paths lift to the Spin lift and to the constant path.
  have h := cov.liftPath_apply_one_eq_of_homotopicRel (homotopicRel_comp_spinLift n H) 1
    (by simp) (by simp)
  rw [cov.liftPath_const, ← (cov.eq_liftPath_iff' _).2 ⟨rfl, (spinLift n).source⟩] at h
  exact spinGroup.negOne_ne_one _ _ ((spinLift n).target.symm.trans h)

end TauCeti

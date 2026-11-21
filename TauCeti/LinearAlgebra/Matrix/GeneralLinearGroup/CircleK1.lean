/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
public import TauCeti.RingTheory.DedekindDomain.CircleRing

import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Matrix.Polar.SpecialLinear
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Elementary
import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal
import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Nontriviality of `SK₁` for the real algebraic circle

Although the coordinate ring `CircleRing = ℝ[x, y] / (x² + y² - 1)` of the real algebraic circle
is a Dedekind domain (`TauCeti.CircleRing.instIsDedekindDomain`), its special Whitehead group
`SK₁(CircleRing)` does not vanish. The determinant-one rotation matrix

  `circleRotation = !![x, -y; y, x] ∈ SL₂(CircleRing)`

has nontrivial class in `AlgebraicK1 CircleRing`, equivalently no identity stabilization of
`circleRotation` to any size `N ≥ 2` belongs to `TauCeti.elementarySubgroup (Fin N) CircleRing`.

Evaluating entries along `CircleRing.evalContinuousMap : CircleRing →ₐ[ℝ] C(Circle, ℝ)` carries
any stabilized elementary matrix to a based nullhomotopic loop in `SL(N, ℝ)`, which the polar
retraction `Matrix.SpecialLinearGroup.polarRetraction` pushes to a based nullhomotopic loop in
`SO(N)`. On the other hand, the evaluated stabilized rotation loop lifts through the compact
real Spin double cover `CliffordAlgebra.realCliffordSpinProjectionZero N` to the path
`CliffordAlgebra.spinRotationPath` from `1` to `-1 ≠ 1` in `Spin(N)`, contradicting covering
homotopy lifting.

## Main definitions

* `TauCeti.CircleRing.evalContinuousMap`: evaluation of `CircleRing` as continuous real
  functions on the unit circle `Circle`.
* `TauCeti.circleRotation`: the determinant-one rotation matrix `!![x, -y; y, x]` over
  `CircleRing`.

## Main results

* `TauCeti.circleRotation_not_mem_elementarySubgroup`: no stabilization of `circleRotation` is
  elementary.
* `TauCeti.circle_rotation_not_stably_elementary`: the class of `circleRotation` in
  `TauCeti.AlgebraicK1 CircleRing` is nontrivial.
* `TauCeti.specialAlgebraicK1_circleRing_ne_bot`: `SK₁(CircleRing) ≠ ⊥`.
* `TauCeti.not_det_circleRing_injective`: the determinant `K₁(CircleRing) →* CircleRingˣ` is not
  injective.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Example 1.5.4 (p. 185).
-/

public section

open Matrix
open scoped unitInterval

namespace TauCeti

noncomputable section

/-! ## Evaluation on the unit circle -/

namespace CircleRing

/-- Evaluation of `CircleRing` into continuous real-valued functions on the unit circle `Circle`,
sending `x ↦ (z ↦ Re z)` and `y ↦ (z ↦ Im z)`. -/
def evalContinuousMap : CircleRing →ₐ[ℝ] C(Circle, ℝ) :=
  liftAlgHom
    ⟨fun z : Circle ↦ (z : ℂ).re, Complex.continuous_re.comp continuous_subtype_val⟩
    ⟨fun z : Circle ↦ (z : ℂ).im, Complex.continuous_im.comp continuous_subtype_val⟩
    (by
      ext z
      exact Circle.re_sq_add_im_sq z)

/-- Evaluation sends `x` at `z : Circle` to `Re z`. -/
@[simp]
theorem evalContinuousMap_x_apply (z : Circle) : evalContinuousMap x z = (z : ℂ).re := by
  simp [evalContinuousMap]

/-- Evaluation sends `y` at `z : Circle` to `Im z`. -/
@[simp]
theorem evalContinuousMap_y_apply (z : Circle) : evalContinuousMap y z = (z : ℂ).im := by
  simp [evalContinuousMap]

/-- Evaluation sends `x` at `Circle.exp θ` to `cos θ`. -/
theorem evalContinuousMap_x_exp (θ : ℝ) : evalContinuousMap x (Circle.exp θ) = Real.cos θ := by
  simp [Circle.coe_exp]

/-- Evaluation sends `y` at `Circle.exp θ` to `sin θ`. -/
theorem evalContinuousMap_y_exp (θ : ℝ) : evalContinuousMap y (Circle.exp θ) = Real.sin θ := by
  simp [Circle.coe_exp]

end CircleRing

/-! ## The circle rotation matrix -/

/-- The determinant-one rotation matrix `!![x, -y; y, x]` over the coordinate ring of the real
algebraic circle. -/
def circleRotation : Matrix.SpecialLinearGroup (Fin 2) CircleRing :=
  ⟨!![CircleRing.x, -CircleRing.y; CircleRing.y, CircleRing.x], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination CircleRing.x_sq_add_y_sq⟩

/-- Entry `(0, 0)` of `circleRotation` is `x`. -/
@[simp]
theorem circleRotation_apply_zero_zero : (circleRotation : Matrix (Fin 2) (Fin 2) CircleRing) 0 0 =
    CircleRing.x :=
  (rfl)

/-- Entry `(0, 1)` of `circleRotation` is `-y`. -/
@[simp]
theorem circleRotation_apply_zero_one : (circleRotation : Matrix (Fin 2) (Fin 2) CircleRing) 0 1 =
    -CircleRing.y :=
  (rfl)

/-- Entry `(1, 0)` of `circleRotation` is `y`. -/
@[simp]
theorem circleRotation_apply_one_zero : (circleRotation : Matrix (Fin 2) (Fin 2) CircleRing) 1 0 =
    CircleRing.y :=
  (rfl)

/-- Entry `(1, 1)` of `circleRotation` is `x`. -/
@[simp]
theorem circleRotation_apply_one_one : (circleRotation : Matrix (Fin 2) (Fin 2) CircleRing) 1 1 =
    CircleRing.x :=
  (rfl)

/-- `circleRotation` is algebraically orthogonal over `CircleRing`. -/
theorem circleRotation_mul_transpose :
    (circleRotation : Matrix (Fin 2) (Fin 2) CircleRing) *
      (circleRotation : Matrix (Fin 2) (Fin 2) CircleRing)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  · linear_combination CircleRing.x_sq_add_y_sq
  · ring
  · ring
  · linear_combination CircleRing.x_sq_add_y_sq

/-- The class of `circleRotation` in algebraic `K₁` lies in `SK₁(CircleRing)`. -/
theorem circleRotation_mk_mem_specialAlgebraicK1 :
    AlgebraicK1.mk CircleRing 2 (SpecialLinearGroup.toGL circleRotation) ∈
      specialAlgebraicK1 CircleRing := by
  rw [AlgebraicK1.mk_mem_specialAlgebraicK1_iff]
  ext
  simp

/-! ## Stabilized rotation loops and Spin lifting -/

/-- The identity stabilization of `circleRotation` to size `N ≥ 2`, in `SL(N, CircleRing)`. -/
private def circleRotationStabilizedSL (N : ℕ) (hN : 2 ≤ N) :
    SpecialLinearGroup (Fin N) CircleRing :=
  ⟨(stabilizeGL CircleRing hN (SpecialLinearGroup.toGL circleRotation) :
      Matrix (Fin N) (Fin N) CircleRing), by
    have hdet := congrArg Units.val
      (det_stabilizeGL (R := CircleRing) hN (SpecialLinearGroup.toGL circleRotation))
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply] at hdet
    exact hdet.trans circleRotation.2⟩

private theorem toGL_circleRotationStabilizedSL (N : ℕ) (hN : 2 ≤ N) :
    SpecialLinearGroup.toGL (circleRotationStabilizedSL N hN) =
      stabilizeGL CircleRing hN (SpecialLinearGroup.toGL circleRotation) :=
  Units.ext rfl

private theorem coe_circleRotationStabilizedSL (N : ℕ) (hN : 2 ≤ N) :
    (circleRotationStabilizedSL N hN : Matrix (Fin N) (Fin N) CircleRing) =
      (stabilizeGL CircleRing hN (SpecialLinearGroup.toGL circleRotation) :
        Matrix (Fin N) (Fin N) CircleRing) :=
  rfl

/-- Every identity stabilization of `circleRotation` is orthogonal over `CircleRing`. -/
private theorem circleRotationStabilizedSL_mul_transpose (N : ℕ) (hN : 2 ≤ N) :
    (circleRotationStabilizedSL N hN : Matrix (Fin N) (Fin N) CircleRing) *
      (circleRotationStabilizedSL N hN : Matrix (Fin N) (Fin N) CircleRing)ᵀ = 1 := by
  set g : GL (Fin 2) CircleRing := SpecialLinearGroup.toGL circleRotation
  have hg : (g : Matrix (Fin 2) (Fin 2) CircleRing) = circleRotation := rfl
  have hinv : (↑g⁻¹ : Matrix (Fin 2) (Fin 2) CircleRing) =
      (g : Matrix (Fin 2) (Fin 2) CircleRing)ᵀ := by
    calc
      (↑g⁻¹ : Matrix (Fin 2) (Fin 2) CircleRing)
          = (↑g⁻¹ : Matrix (Fin 2) (Fin 2) CircleRing) *
              ((g : Matrix (Fin 2) (Fin 2) CircleRing) *
                (g : Matrix (Fin 2) (Fin 2) CircleRing)ᵀ) := by
                  rw [hg, circleRotation_mul_transpose, mul_one]
      _ = ((↑g⁻¹ : Matrix (Fin 2) (Fin 2) CircleRing) *
              (g : Matrix (Fin 2) (Fin 2) CircleRing)) *
              (g : Matrix (Fin 2) (Fin 2) CircleRing)ᵀ := by
                  rw [Matrix.mul_assoc]
      _ = (g : Matrix (Fin 2) (Fin 2) CircleRing)ᵀ := by
                  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  set u : GL (Fin N) CircleRing := stabilizeGL CircleRing hN g
  have huinv : u⁻¹ = stabilizeGL CircleRing hN g⁻¹ :=
    (map_inv (stabilizeGL CircleRing hN) g).symm
  have htrans : (u : Matrix (Fin N) (Fin N) CircleRing)ᵀ =
      (↑u⁻¹ : Matrix (Fin N) (Fin N) CircleRing) := by
    ext i j
    rw [Matrix.transpose_apply, huinv, coe_stabilizeGL_apply, coe_stabilizeGL_apply]
    by_cases h : (i : ℕ) < 2 ∧ (j : ℕ) < 2
    · simp only [h.1, h.2, and_self, ↓reduceDIte, hinv, Matrix.transpose_apply]
    · have h' : ¬((j : ℕ) < 2 ∧ (i : ℕ) < 2) := fun ⟨hj, hi⟩ ↦ h ⟨hi, hj⟩
      simp only [h, h', ↓reduceDIte, Matrix.one_apply, eq_comm]
  rw [coe_circleRotationStabilizedSL, htrans, ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- Evaluating the stabilized circle rotation at `z : Circle` yields an element of `SO(N)`. -/
private def evalCircleRotationSO (N : ℕ) (hN : 2 ≤ N) (z : Circle) :
    Matrix.specialOrthogonalGroup (Fin N) ℝ :=
  ⟨(CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
      (circleRotationStabilizedSL N hN) z : Matrix (Fin N) (Fin N) ℝ), by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    refine ⟨?_, (CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
      (circleRotationStabilizedSL N hN) z).2⟩
    rw [Matrix.mem_orthogonalGroup_iff]
    let φ : CircleRing →+* ℝ :=
      (ContinuousMap.evalAlgHom ℝ ℝ z).toRingHom.comp CircleRing.evalContinuousMap.toRingHom
    have hmap : (CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
        (circleRotationStabilizedSL N hN) z : Matrix (Fin N) (Fin N) ℝ) =
        φ.mapMatrix (circleRotationStabilizedSL N hN : Matrix (Fin N) (Fin N) CircleRing) := by
      ext i j
      simp [φ]
    have htr :
        (φ.mapMatrix (circleRotationStabilizedSL N hN : Matrix (Fin N) (Fin N) CircleRing))ᵀ =
          φ.mapMatrix (circleRotationStabilizedSL N hN : Matrix (Fin N) (Fin N) CircleRing)ᵀ :=
      rfl
    rw [hmap, htr, ← map_mul, circleRotationStabilizedSL_mul_transpose N hN, map_one]⟩

private theorem toSL_evalCircleRotationSO (N : ℕ) (hN : 2 ≤ N) (z : Circle) :
    Matrix.specialUnitaryGroup.toSL (evalCircleRotationSO N hN z) =
      CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
        (circleRotationStabilizedSL N hN) z :=
  Subtype.ext (by simp [Matrix.specialUnitaryGroup.coe_toSL, evalCircleRotationSO])

private theorem evalCircleRotationStabilizedSL_one (N : ℕ) (hN : 2 ≤ N) :
    CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
      (circleRotationStabilizedSL N hN) 1 = 1 := by
  ext i j
  rw [RingHom.coe_mapSLContinuousMap_apply, coe_circleRotationStabilizedSL,
    coe_stabilizeGL_apply, SpecialLinearGroup.coe_one]
  split_ifs with hij
  · obtain ⟨hi, hj⟩ := hij
    have hi' : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
    have hj' : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    rcases hi' with hi0 | hi1 <;> rcases hj' with hj0 | hj1
    · have h0 : (⟨(i : ℕ), hi⟩ : Fin 2) = 0 := Fin.ext hi0
      have h1 : (⟨(j : ℕ), hj⟩ : Fin 2) = 0 := Fin.ext hj0
      have hij' : i = j := Fin.ext (hi0.trans hj0.symm)
      rw [h0, h1]
      simp [hij', Matrix.one_apply]
    · have h0 : (⟨(i : ℕ), hi⟩ : Fin 2) = 0 := Fin.ext hi0
      have h1 : (⟨(j : ℕ), hj⟩ : Fin 2) = 1 := Fin.ext hj1
      have hij' : i ≠ j := fun h ↦ by have := congrArg Fin.val h; omega
      rw [h0, h1]
      simp [hij']
    · have h0 : (⟨(i : ℕ), hi⟩ : Fin 2) = 1 := Fin.ext hi1
      have h1 : (⟨(j : ℕ), hj⟩ : Fin 2) = 0 := Fin.ext hj0
      have hij' : i ≠ j := fun h ↦ by have := congrArg Fin.val h; omega
      rw [h0, h1]
      simp [hij']
    · have h0 : (⟨(i : ℕ), hi⟩ : Fin 2) = 1 := Fin.ext hi1
      have h1 : (⟨(j : ℕ), hj⟩ : Fin 2) = 1 := Fin.ext hj1
      have hij' : i = j := Fin.ext (hi1.trans hj1.symm)
      rw [h0, h1]
      simp [hij', Matrix.one_apply]
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

/-- The Spin rotation path in the `(e₁, e₀)` plane projects under
`realCliffordSpinProjectionZero N` to `evalCircleRotationSO N hN (Circle.exp (2π u))`
transported to `SO(realCliffordForm N 0)`. -/
private theorem realCliffordSpinProjectionZero_spinRotationPath_eq (N : ℕ) (hN : 2 ≤ N)
    [NeZero N] (u : I) :
    CliffordAlgebra.realCliffordSpinProjectionZero N
        (CliffordAlgebra.spinRotationPath (realCliffordForm N 0)
          (Pi.single ⟨1, by omega⟩ 1) (Pi.single ⟨0, by omega⟩ 1)
          (realCliffordForm_zero_single_one N ⟨1, by omega⟩)
          (realCliffordForm_zero_single_one N ⟨0, by omega⟩)
          (isOrtho_realCliffordForm_single (by simp [Fin.ext_iff]) 1 1) u) =
      QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm N
        (evalCircleRotationSO N hN (Circle.exp (2 * Real.pi * (u : ℝ)))) := by
  set i₀ : Fin N := ⟨0, by omega⟩
  set i₁ : Fin N := ⟨1, by omega⟩
  have hi0lt : (i₀ : ℕ) < 2 := Nat.zero_lt_two
  have hi1lt : (i₁ : ℕ) < 2 := Nat.one_lt_two
  have hi10 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have he₁ : realCliffordForm N 0 (Pi.single i₁ 1) = 1 :=
    realCliffordForm_zero_single_one N i₁
  have he₀ : realCliffordForm N 0 (Pi.single i₀ 1) = 1 :=
    realCliffordForm_zero_single_one N i₀
  have h10 : (realCliffordForm N 0).IsOrtho (Pi.single i₁ 1) (Pi.single i₀ 1) :=
    isOrtho_realCliffordForm_single hi10 1 1
  have htoGL :
      (SpecialLinearGroup.toGL circleRotation : Matrix (Fin 2) (Fin 2) CircleRing) =
        circleRotation := rfl
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun ℝ (Fin N)).ext fun j ↦ ?_
  simp only [LinearEquiv.coe_toLinearMap, Pi.basisFun_apply]
  rw [QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_apply,
    CliffordAlgebra.realCliffordSpinProjectionZero_apply,
    CliffordAlgebra.realCliffordSpinDoubleCoverZero_rightHom,
    CliffordAlgebra.coe_spinToSpecialOrthogonal_apply,
    CliffordAlgebra.spinRotationPath_apply,
    CliffordAlgebra.spinRotation_eq_spinCircle]
  set z : Circle := Circle.exp (Real.pi * (u : ℝ))
  have hz2 : (z : ℂ) ^ 2 = Complex.exp (((2 * Real.pi * (u : ℝ)) : ℝ) * Complex.I) := by
    simp only [z, Circle.coe_exp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzsq_re : ((z : ℂ) ^ 2).re = Real.cos (2 * Real.pi * (u : ℝ)) := by
    rw [hz2, Complex.exp_ofReal_mul_I_re]
  have hzsq_im : ((z : ℂ) ^ 2).im = Real.sin (2 * Real.pi * (u : ℝ)) := by
    rw [hz2, Complex.exp_ofReal_mul_I_im]
  by_cases hj0 : j = i₀
  · subst hj0
    rw [CliffordAlgebra.spinVectorAction_spinCircle_right, he₀, mul_one, hzsq_re, hzsq_im]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.toLin'_apply,
      Matrix.mulVec_single_one, Matrix.col_apply, evalCircleRotationSO,
      RingHom.coe_mapSLContinuousMap_apply, coe_circleRotationStabilizedSL, coe_stabilizeGL_apply,
      Pi.single_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    by_cases hk0 : k = i₀
    · subst hk0
      have h0 : (⟨(i₀ : ℕ), hi0lt⟩ : Fin 2) = 0 := rfl
      simp only [hi0lt, and_self, ↓reduceDIte, h0, htoGL, circleRotation_apply_zero_zero,
        CircleRing.evalContinuousMap_x_exp]
      simp [i₀, Fin.ext_iff]
    · by_cases hk1 : k = i₁
      · subst hk1
        have h0 : (⟨(i₀ : ℕ), hi0lt⟩ : Fin 2) = 0 := rfl
        have h1 : (⟨(i₁ : ℕ), hi1lt⟩ : Fin 2) = 1 := rfl
        simp only [hi1lt, hi0lt, and_self, ↓reduceDIte, h0, h1, htoGL,
          circleRotation_apply_one_zero, CircleRing.evalContinuousMap_y_exp]
        simp [i₁, Fin.ext_iff]
      · have hk2 : ¬((k : ℕ) < 2) := fun hk ↦ by
          have : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by omega
          rcases this with h | h
          · exact hk0 (Fin.ext h)
          · exact hk1 (Fin.ext h)
        simp only [hk2, false_and, ↓reduceDIte, Matrix.one_apply, hk0, ↓reduceIte, map_zero,
          ContinuousMap.zero_apply]
        have hk0' : (k : ℕ) ≠ 0 := fun h ↦ hk0 (Fin.ext h)
        have hk1' : (k : ℕ) ≠ 1 := fun h ↦ hk1 (Fin.ext h)
        simp [Fin.ext_iff, hk0', hk1']
  · by_cases hj1 : j = i₁
    · subst hj1
      rw [CliffordAlgebra.spinVectorAction_spinCircle_left, he₁, mul_one, hzsq_re, hzsq_im]
      ext k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.toLin'_apply,
        Matrix.mulVec_single_one, Matrix.col_apply, evalCircleRotationSO,
        RingHom.coe_mapSLContinuousMap_apply, coe_circleRotationStabilizedSL,
        coe_stabilizeGL_apply, Pi.single_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      by_cases hk0 : k = i₀
      · subst hk0
        have h0 : (⟨(i₀ : ℕ), hi0lt⟩ : Fin 2) = 0 := rfl
        have h1 : (⟨(i₁ : ℕ), hi1lt⟩ : Fin 2) = 1 := rfl
        simp only [hi0lt, hi1lt, and_self, ↓reduceDIte, h0, h1, htoGL,
          circleRotation_apply_zero_one, map_neg, ContinuousMap.neg_apply,
          CircleRing.evalContinuousMap_y_exp]
        simp [i₀, Fin.ext_iff]
      · by_cases hk1 : k = i₁
        · subst hk1
          have h1 : (⟨(i₁ : ℕ), hi1lt⟩ : Fin 2) = 1 := rfl
          simp only [hi1lt, and_self, ↓reduceDIte, h1, htoGL, circleRotation_apply_one_one,
            CircleRing.evalContinuousMap_x_exp]
          simp [i₁, Fin.ext_iff]
        · have hk2 : ¬((k : ℕ) < 2) := fun hk ↦ by
            have : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by omega
            rcases this with h | h
            · exact hk0 (Fin.ext h)
            · exact hk1 (Fin.ext h)
          simp only [hk2, false_and, ↓reduceDIte, Matrix.one_apply, hk1, ↓reduceIte, map_zero,
            ContinuousMap.zero_apply]
          have hk0' : (k : ℕ) ≠ 0 := fun h ↦ hk0 (Fin.ext h)
          have hk1' : (k : ℕ) ≠ 1 := fun h ↦ hk1 (Fin.ext h)
          simp [Fin.ext_iff, hk0', hk1']
    · rw [CliffordAlgebra.spinVectorAction_spinCircle_of_isOrtho h10
        (by rw [he₁, he₀, mul_one])
        (isOrtho_realCliffordForm_single (Ne.symm hj1) 1 1)
        (isOrtho_realCliffordForm_single (Ne.symm hj0) 1 1)]
      have hj2 : ¬((j : ℕ) < 2) := fun hj ↦ by
        have : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
        rcases this with h | h
        · exact hj0 (Fin.ext h)
        · exact hj1 (Fin.ext h)
      ext k
      simp only [Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply,
        evalCircleRotationSO, RingHom.coe_mapSLContinuousMap_apply,
        coe_circleRotationStabilizedSL, coe_stabilizeGL_apply, hj2, and_false, ↓reduceDIte,
        Matrix.one_apply, Pi.single_apply]
      split_ifs <;> simp

/-! ## Nonvanishing in algebraic `K₁` and `SK₁` -/

/-- **No identity stabilization of `circleRotation` is elementary.** -/
theorem circleRotation_not_mem_elementarySubgroup (N : ℕ) (hN : 2 ≤ N) :
    stabilizeGL CircleRing hN (SpecialLinearGroup.toGL circleRotation) ∉
      elementarySubgroup (Fin N) CircleRing := by
  intro hg
  have : NeZero N := ⟨by omega⟩
  let gSL := circleRotationStabilizedSL N hN
  have hgSL : SpecialLinearGroup.toGL gSL ∈ elementarySubgroup (Fin N) CircleRing := by
    rwa [toGL_circleRotationStabilizedSL]
  -- Evaluate the elementary matrix on `Circle` to get a based nullhomotopy in `SL(N, ℝ)`.
  have hrelSL : ContinuousMap.HomotopicRel
      (1 : C(Circle, SpecialLinearGroup (Fin N) ℝ))
      (CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap gSL) {1} :=
    CircleRing.evalContinuousMap.toRingHom
      |>.homotopicRel_one_mapSLContinuousMap_of_toGL_mem_elementarySubgroup
          (PathConnectedSpace.joined 0 1) hgSL (evalCircleRotationStabilizedSL_one N hN)
  -- Precompose with `u ↦ Circle.exp (2π u)` to get a based nullhomotopy of loops in `SL(N, ℝ)`.
  let circleLoop : C(I, Circle) :=
    ⟨fun u : I ↦ Circle.exp (2 * Real.pi * (u : ℝ)),
      Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)⟩
  have hpre : ({0, 1} : Set I) ⊆ circleLoop ⁻¹' {1} := by
    rintro u (rfl | rfl)
    · simp [circleLoop]
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, circleLoop, ContinuousMap.coe_mk,
        Set.Icc.coe_one, mul_one]
      exact Circle.ext (by simp [Circle.coe_exp, Complex.exp_two_pi_mul_I])
  have hloopSL : ContinuousMap.HomotopicRel
      ((1 : C(Circle, SpecialLinearGroup (Fin N) ℝ)).comp circleLoop)
      ((CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap gSL).comp circleLoop)
      {0, 1} :=
    (hrelSL.precomp circleLoop).mono hpre
  -- Retract from `SL(N, ℝ)` onto `SO(N)` via polar retraction, then to `SO(realCliffordForm)`.
  let retractToClifford :
      C(SpecialLinearGroup (Fin N) ℝ,
        QuadraticMap.specialOrthogonalGroup (realCliffordForm N 0)) :=
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm N :
        C(Matrix.specialOrthogonalGroup (Fin N) ℝ,
          QuadraticMap.specialOrthogonalGroup (realCliffordForm N 0))).comp
      (SpecialLinearGroup.polarRetraction (Fin N) ℝ)
  have hloopSO : ContinuousMap.HomotopicRel
      (retractToClifford.comp ((1 : C(Circle, SpecialLinearGroup (Fin N) ℝ)).comp circleLoop))
      (retractToClifford.comp
        ((CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap gSL).comp circleLoop))
      {0, 1} :=
    hloopSL.comp_continuousMap retractToClifford
  -- Identify the two endpoints of `hloopSO` with `Path.refl 1` and the Spin-projected loop.
  let γSpin := CliffordAlgebra.spinRotationPath (realCliffordForm N 0)
    (Pi.single ⟨1, by omega⟩ 1) (Pi.single ⟨0, by omega⟩ 1)
    (realCliffordForm_zero_single_one N ⟨1, by omega⟩)
    (realCliffordForm_zero_single_one N ⟨0, by omega⟩)
    (isOrtho_realCliffordForm_single (by simp [Fin.ext_iff]) 1 1)
  let p := CliffordAlgebra.realCliffordSpinProjectionZero N
  have hp : IsCoveringMap p := CliffordAlgebra.isCoveringMap_realCliffordSpinProjectionZero N
  let δ : Path (1 : QuadraticMap.specialOrthogonalGroup (realCliffordForm N 0)) 1 :=
    (γSpin.map p.continuous).cast (map_one p).symm
      (CliffordAlgebra.realCliffordSpinProjectionZero_negOne N).symm
  have hsrc :
      retractToClifford.comp ((1 : C(Circle, SpecialLinearGroup (Fin N) ℝ)).comp circleLoop) =
        (Path.refl (1 : QuadraticMap.specialOrthogonalGroup
          (realCliffordForm N 0))).toContinuousMap := by
    refine ContinuousMap.ext fun u ↦ ?_
    have h1 : SpecialLinearGroup.polarRetraction (Fin N) ℝ 1 = 1 := by
      simpa only [map_one] using
        SpecialLinearGroup.polarRetraction_toSL (n := Fin N) (𝕜 := ℝ) 1
    simp [retractToClifford, h1]
  have hdst :
      retractToClifford.comp
        ((CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap gSL).comp circleLoop) =
        δ.toContinuousMap := by
    refine ContinuousMap.ext fun u ↦ ?_
    simp only [ContinuousMap.comp_apply, retractToClifford, circleLoop, ContinuousMap.coe_mk,
      Path.coe_toContinuousMap, δ, Path.cast_coe, Path.map_coe, Function.comp_apply]
    rw [← toSL_evalCircleRotationSO N hN (Circle.exp (2 * Real.pi * (u : ℝ))),
      SpecialLinearGroup.polarRetraction_toSL]
    exact (realCliffordSpinProjectionZero_spinRotationPath_eq N hN u).symm
  rw [hsrc, hdst] at hloopSO
  -- Covering homotopy lifting forces the Spin lift starting at `1` to end at `1`, contradicting
  -- `-1 ≠ 1` in `Spin(N)`.
  have hδ0 : δ.toContinuousMap 0 = p 1 := δ.source.trans (map_one p).symm
  have hrefl0 :
      (Path.refl (1 : QuadraticMap.specialOrthogonalGroup
        (realCliffordForm N 0))).toContinuousMap 0 = p 1 :=
    (map_one p).symm
  have hlift_δ : hp.liftPath δ.toContinuousMap 1 hδ0 = γSpin.toContinuousMap :=
    ((hp.eq_liftPath_iff' _).mpr ⟨rfl, γSpin.source⟩).symm
  have hlift_refl : hp.liftPath (Path.refl 1).toContinuousMap 1 hrefl0 = ContinuousMap.const I 1 :=
    hp.liftPath_const (map_one p).symm
  have hend := hp.liftPath_apply_one_eq_of_homotopicRel hloopSO 1 hrefl0 hδ0
  rw [hlift_refl, hlift_δ] at hend
  have hneg : CliffordAlgebra.spinGroup.negOne (realCliffordForm N 0)
      (nondegenerate_realCliffordForm N 0).ne_zero = 1 := by
    simpa [γSpin] using hend.symm
  exact CliffordAlgebra.spinGroup.negOne_ne_one (realCliffordForm N 0)
    (nondegenerate_realCliffordForm N 0).ne_zero hneg

/-- **The circle rotation has nontrivial class in algebraic `K₁`**: no identity stabilization of
`circleRotation` is elementary, so it represents a nontrivial class in `SK₁(CircleRing)`. -/
theorem circle_rotation_not_stably_elementary :
    AlgebraicK1.mk CircleRing 2 (SpecialLinearGroup.toGL circleRotation) ≠ 1 := by
  rw [ne_eq, AlgebraicK1.mk_eq_one_iff]
  rintro ⟨N, hN, hmem⟩
  exact circleRotation_not_mem_elementarySubgroup N hN hmem

/-- `SK₁(CircleRing)` is nontrivial: even for a Dedekind domain, `SK₁` need not vanish. -/
theorem specialAlgebraicK1_circleRing_ne_bot : specialAlgebraicK1 CircleRing ≠ ⊥ := by
  intro hbot
  have hmem := circleRotation_mk_mem_specialAlgebraicK1
  rw [hbot, Subgroup.mem_bot] at hmem
  exact circle_rotation_not_stably_elementary hmem

/-- The determinant homomorphism `K₁(CircleRing) →* CircleRingˣ` is not injective. -/
theorem not_det_circleRing_injective : ¬ Function.Injective (AlgebraicK1.det CircleRing) := by
  intro hinj
  have hdet : AlgebraicK1.det CircleRing
      (AlgebraicK1.mk CircleRing 2 (SpecialLinearGroup.toGL circleRotation)) =
      AlgebraicK1.det CircleRing 1 := by
    rw [map_one]
    exact mem_specialAlgebraicK1_iff.mp circleRotation_mk_mem_specialAlgebraicK1
  exact circle_rotation_not_stably_elementary (hinj hdet)

end

end TauCeti

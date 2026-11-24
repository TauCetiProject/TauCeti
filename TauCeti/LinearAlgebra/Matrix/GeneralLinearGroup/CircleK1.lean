/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
public import TauCeti.RingTheory.DedekindDomain.Circle

import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.Matrix.Polar.SpecialLinear
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Elementary
import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal
import TauCeti.Topology.Homotopy.Covering
import TauCeti.Topology.Homotopy.Homotopic.Rel
import TauCeti.Topology.Homotopy.Path

/-!
# Nontriviality of `SK₁` for the algebraic circle

Although the coordinate ring `CircleRing k = k[x, y] ⧸ (x² + y² - 1)` of the algebraic circle
over a field `k` with `2 ≠ 0` is a Dedekind domain (`TauCeti.CircleRing.instIsDedekindDomain`),
its special Whitehead group `SK₁(CircleRing k)` does not vanish whenever `k` admits a ring
homomorphism `k →+* ℝ` (for instance `k = ℤ`, `ℚ`, or `ℝ`). For any commutative ring `k`, the
determinant-one rotation matrix

  `circleRotation k = !![x, -y; y, x] ∈ SL₂(CircleRing k)`

defines a class in `SK₁(CircleRing k)`. Over `ℝ`, evaluating entries along
`CircleRing.evalContinuousMap : CircleRing ℝ →ₐ[ℝ] C(Circle, ℝ)` carries any stabilized
elementary matrix to a based nullhomotopic loop in `SL(N, ℝ)`, which the polar retraction
`Matrix.SpecialLinearGroup.polarRetraction` pushes to a based nullhomotopic loop in `SO(N)`.
On the other hand, the evaluated stabilized rotation loop lifts through the compact real Spin
double cover `CliffordAlgebra.realCliffordSpinProjectionZero N` to the path
`CliffordAlgebra.spinRotationPath` from `1` to `-1 ≠ 1` in `Spin(N)`, contradicting covering
homotopy lifting. Base change along `k →+* ℝ` then propagates nonvanishing from `ℝ` to `k`.

## Main definitions

* `TauCeti.CircleRing.evalContinuousMap`: evaluation of `CircleRing ℝ` as continuous real
  functions on the unit circle `Circle`.
* `TauCeti.circleRotation`: the determinant-one rotation matrix `!![x, -y; y, x]` over
  `CircleRing k`.

## Main results

* `TauCeti.circleRotation_mul_transpose`: `circleRotation k` is algebraically orthogonal.
* `TauCeti.circleRotation_mk_mem_specialAlgebraicK1`: the class of `circleRotation k` lies in
  `SK₁(CircleRing k)`.
* `TauCeti.map_circleRotation`, `TauCeti.map_toGL_circleRotation`: base change on `CircleRing`
  preserves `circleRotation`.
* `TauCeti.circleRotation_not_mem_elementarySubgroup`: no stabilization of `circleRotation k` is
  elementary when `k` admits `k →+* ℝ`.
* `TauCeti.circle_rotation_not_stably_elementary`: the class of `circleRotation k` in
  `TauCeti.AlgebraicK1 (CircleRing k)` is nontrivial when `k` admits `k →+* ℝ`.
* `TauCeti.specialAlgebraicK1_circleRing_ne_bot`: `SK₁(CircleRing k) ≠ ⊥` when `k` admits `k →+* ℝ`.
* `TauCeti.not_det_circleRing_injective`: the determinant
  `K₁(CircleRing k) →* (CircleRing k)ˣ` is not injective when `k` admits `k →+* ℝ`.

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

/-- Evaluation of `CircleRing ℝ` into continuous real-valued functions on the unit circle `Circle`,
sending `x ↦ (z ↦ Re z)` and `y ↦ (z ↦ Im z)`. -/
def evalContinuousMap : CircleRing ℝ →ₐ[ℝ] C(Circle, ℝ) :=
  CircleRing.lift
    ⟨fun z : Circle ↦ (z : ℂ).re, Complex.continuous_re.comp continuous_subtypeVal⟩
    ⟨fun z : Circle ↦ (z : ℂ).im, Complex.continuous_im.comp continuous_subtypeVal⟩
    (by
      ext z
      exact Circle.re_sq_add_im_sq z)

/-- Evaluation sends `x` at `z : Circle` to `Re z`. -/
@[simp]
theorem evalContinuousMap_x_apply (z : Circle) :
    evalContinuousMap (CircleRing.x : CircleRing ℝ) z = (z : ℂ).re := by
  simp [evalContinuousMap]

/-- Evaluation sends `y` at `z : Circle` to `Im z`. -/
@[simp]
theorem evalContinuousMap_y_apply (z : Circle) :
    evalContinuousMap (CircleRing.y : CircleRing ℝ) z = (z : ℂ).im := by
  simp [evalContinuousMap]

/-- Evaluation sends `x` at `Circle.exp θ` to `cos θ`. -/
theorem evalContinuousMap_x_exp (θ : ℝ) :
    evalContinuousMap (CircleRing.x : CircleRing ℝ) (Circle.exp θ) = Real.cos θ := by
  simp [Circle.coe_exp]

/-- Evaluation sends `y` at `Circle.exp θ` to `sin θ`. -/
theorem evalContinuousMap_y_exp (θ : ℝ) :
    evalContinuousMap (CircleRing.y : CircleRing ℝ) (Circle.exp θ) = Real.sin θ := by
  simp [Circle.coe_exp]

end CircleRing

/-! ## The circle rotation matrix -/

section CircleRotation

variable (k : Type*) [CommRing k]

/-- The determinant-one rotation matrix `!![x, -y; y, x]` over the coordinate ring of the
algebraic circle over `k`. -/
def circleRotation : Matrix.SpecialLinearGroup (Fin 2) (CircleRing k) :=
  ⟨!![CircleRing.x, -CircleRing.y; CircleRing.y, CircleRing.x], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination CircleRing.x_sq_add_y_sq (k := k)⟩

variable {k}

/-- Entry `(0, 0)` of `circleRotation k` is `x`. -/
@[simp]
theorem circleRotation_apply_zero_zero :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) 0 0 = CircleRing.x :=
  (rfl)

/-- Entry `(0, 1)` of `circleRotation k` is `-y`. -/
@[simp]
theorem circleRotation_apply_zero_one :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) 0 1 = -CircleRing.y :=
  (rfl)

/-- Entry `(1, 0)` of `circleRotation k` is `y`. -/
@[simp]
theorem circleRotation_apply_one_zero :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) 1 0 = CircleRing.y :=
  (rfl)

/-- Entry `(1, 1)` of `circleRotation k` is `x`. -/
@[simp]
theorem circleRotation_apply_one_one :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) 1 1 = CircleRing.x :=
  (rfl)

/-- `circleRotation k` is algebraically orthogonal over `CircleRing k`. -/
theorem circleRotation_mul_transpose :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) *
      (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k))ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  · linear_combination CircleRing.x_sq_add_y_sq (k := k)
  · ring
  · ring
  · linear_combination CircleRing.x_sq_add_y_sq (k := k)

/-- The class of `circleRotation k` in algebraic `K₁` lies in `SK₁(CircleRing k)`. -/
theorem circleRotation_mk_mem_specialAlgebraicK1 (k : Type*) [CommRing k] :
    AlgebraicK1.mk (CircleRing k) 2 (SpecialLinearGroup.toGL (circleRotation k)) ∈
      specialAlgebraicK1 (CircleRing k) := by
  rw [AlgebraicK1.mk_mem_specialAlgebraicK1_iff]
  ext
  simp

end CircleRotation

/-! ## Stabilized rotation loops and Spin lifting -/

/-- Every identity stabilization of `circleRotation ℝ` is orthogonal over `CircleRing ℝ`. -/
private theorem circleRotationStabilizedSL_mul_transpose (N : ℕ) (hN : 2 ≤ N) :
    (stabilizeSL hN (circleRotation ℝ) : Matrix (Fin N) (Fin N) (CircleRing ℝ)) *
      (stabilizeSL hN (circleRotation ℝ) : Matrix (Fin N) (Fin N) (CircleRing ℝ))ᵀ = 1 := by
  rw [coe_stabilizeSL]
  exact stabilizeGL_mul_transpose hN circleRotation_mul_transpose

/-- Evaluating the stabilized circle rotation at `z : Circle` yields an element of `SO(N)`. -/
private def evalCircleRotationSO (N : ℕ) (hN : 2 ≤ N) (z : Circle) :
    Matrix.specialOrthogonalGroup (Fin N) ℝ :=
  ⟨(CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
      (stabilizeSL hN (circleRotation ℝ)) z : Matrix (Fin N) (Fin N) ℝ), by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    refine ⟨?_, (CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
      (stabilizeSL hN (circleRotation ℝ)) z).property⟩
    rw [Matrix.mem_orthogonalGroup_iff, RingHom.mapSLContinuousMap_apply,
      SpecialLinearGroup.map_apply_coe, ← Matrix.transpose_map,
      ← Matrix.map_mul, circleRotationStabilizedSL_mul_transpose N hN,
      Matrix.map_one _ (map_zero _) (map_one _)]⟩

private theorem toSL_evalCircleRotationSO (N : ℕ) (hN : 2 ≤ N) (z : Circle) :
    Matrix.specialUnitaryGroup.toSL (evalCircleRotationSO N hN z) =
      CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
        (stabilizeSL hN (circleRotation ℝ)) z :=
  Subtype.ext (by simp [Matrix.specialUnitaryGroup.coe_toSL, evalCircleRotationSO])

private theorem evalCircleRotationStabilizedSL_one (N : ℕ) (hN : 2 ≤ N) :
    CircleRing.evalContinuousMap.toRingHom.mapSLContinuousMap
      (stabilizeSL hN (circleRotation ℝ)) 1 = 1 := by
  let φ : CircleRing ℝ →+* ℝ :=
    (ContinuousMap.evalAlgHom ℝ ℝ (1 : Circle)).toRingHom.comp
      CircleRing.evalContinuousMap.toRingHom
  rw [RingHom.mapSLContinuousMap_apply, ← stabilizeSL_map hN φ (circleRotation ℝ)]
  have h2 : SpecialLinearGroup.map φ (circleRotation ℝ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [φ]
  rw [h2, map_one]

private theorem evalCircleRotationSO_apply (N : ℕ) (hN : 2 ≤ N) (z : Circle) (k j : Fin N) :
    (evalCircleRotationSO N hN z : Matrix (Fin N) (Fin N) ℝ) k j =
      if hkj : (k : ℕ) < 2 ∧ (j : ℕ) < 2 then
        CircleRing.evalContinuousMap
          ((circleRotation ℝ : Matrix (Fin 2) (Fin 2) (CircleRing ℝ)) ⟨k, hkj.1⟩ ⟨j, hkj.2⟩) z
      else (1 : Matrix (Fin N) (Fin N) ℝ) k j := by
  simp only [evalCircleRotationSO, RingHom.coe_mapSLContinuousMap_apply, coe_stabilizeSL_apply]
  split_ifs with hkj
  · rfl
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

private theorem evalCircleRotationSO_toLin'_single_of_lt_two (N : ℕ) (hN : 2 ≤ N) (z : Circle)
    {j : Fin N} (hj : (j : ℕ) < 2) :
    Matrix.toLin' (evalCircleRotationSO N hN z : Matrix (Fin N) (Fin N) ℝ) (Pi.single j 1) =
      CircleRing.evalContinuousMap
          ((circleRotation ℝ : Matrix (Fin 2) (Fin 2) (CircleRing ℝ)) 0 ⟨j, hj⟩) z •
          Pi.single ⟨0, by omega⟩ 1 +
        CircleRing.evalContinuousMap
          ((circleRotation ℝ : Matrix (Fin 2) (Fin 2) (CircleRing ℝ)) 1 ⟨j, hj⟩) z •
          Pi.single ⟨1, by omega⟩ 1 := by
  ext k
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    evalCircleRotationSO_apply N hN z k j]
  rcases lt_or_ge (k : ℕ) 2 with hk | hk
  · have hk' : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by omega
    rcases hk' with hk0 | hk1
    · simp [hj, hk0, Pi.single_apply, Fin.ext_iff]
    · simp [hj, hk1, Pi.single_apply, Fin.ext_iff]
  · have hkj : k ≠ j := fun h ↦ by subst h; omega
    have hk0 : k ≠ ⟨0, by omega⟩ := fun h ↦ by
      have := congrArg Fin.val h; dsimp only at this; omega
    have hk1 : k ≠ ⟨1, by omega⟩ := fun h ↦ by
      have := congrArg Fin.val h; dsimp only at this; omega
    simp [Nat.not_lt.mpr hk, Matrix.one_apply_ne hkj, hk0, hk1]

private theorem evalCircleRotationSO_toLin'_single_zero (N : ℕ) (hN : 2 ≤ N) (z : Circle) :
    Matrix.toLin' (evalCircleRotationSO N hN z : Matrix (Fin N) (Fin N) ℝ)
        (Pi.single ⟨0, by omega⟩ 1) =
      (z : ℂ).re • Pi.single ⟨0, by omega⟩ 1 + (z : ℂ).im • Pi.single ⟨1, by omega⟩ 1 := by
  rw [evalCircleRotationSO_toLin'_single_of_lt_two N hN z (by simp)]
  simp

private theorem evalCircleRotationSO_toLin'_single_one (N : ℕ) (hN : 2 ≤ N) (z : Circle) :
    Matrix.toLin' (evalCircleRotationSO N hN z : Matrix (Fin N) (Fin N) ℝ)
        (Pi.single ⟨1, by omega⟩ 1) =
      (z : ℂ).re • Pi.single ⟨1, by omega⟩ 1 - (z : ℂ).im • Pi.single ⟨0, by omega⟩ 1 := by
  rw [evalCircleRotationSO_toLin'_single_of_lt_two N hN z (by simp)]
  simp [sub_eq_add_neg, add_comm]

private theorem evalCircleRotationSO_toLin'_single_of_two_le (N : ℕ) (hN : 2 ≤ N) (z : Circle)
    {j : Fin N} (hj : 2 ≤ (j : ℕ)) :
    Matrix.toLin' (evalCircleRotationSO N hN z : Matrix (Fin N) (Fin N) ℝ)
        (Pi.single j 1) =
      Pi.single j 1 := by
  ext k
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    evalCircleRotationSO_apply N hN z k j]
  simp [Nat.not_lt.mpr hj, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- The Spin rotation path in the `(e₁, e₀)` plane of `realCliffordForm N 0`. -/
private def spinRotationPathE10 (N : ℕ) (hN : 2 ≤ N) :
    Path (1 : CliffordAlgebra.realCliffordSpinGroupZero N)
      (CliffordAlgebra.spinGroup.negOne (realCliffordForm N 0)
        (by have : NeZero N := ⟨by omega⟩; exact (nondegenerate_realCliffordForm N 0).ne_zero)) :=
  CliffordAlgebra.spinRotationPath (realCliffordForm N 0)
    (Pi.single ⟨1, by omega⟩ 1) (Pi.single ⟨0, by omega⟩ 1)
    (realCliffordForm_zero_single_one N ⟨1, by omega⟩)
    (realCliffordForm_zero_single_one N ⟨0, by omega⟩)
    (isOrtho_realCliffordForm_single (by simp [Fin.ext_iff]) 1 1)

/-- The Spin rotation path in the `(e₁, e₀)` plane projects under
`realCliffordSpinProjectionZero N` to `evalCircleRotationSO N hN (Circle.exp (2π u))`
transported to `SO(realCliffordForm N 0)`. -/
private theorem realCliffordSpinProjectionZero_spinRotationPath_eq (N : ℕ) (hN : 2 ≤ N)
    [NeZero N] (u : I) :
    CliffordAlgebra.realCliffordSpinProjectionZero N (spinRotationPathE10 N hN u) =
      QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm N
        (evalCircleRotationSO N hN (Circle.exp (2 * Real.pi * (u : ℝ)))) := by
  set i₀ : Fin N := ⟨0, by omega⟩
  set i₁ : Fin N := ⟨1, by omega⟩
  have hi10 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have he₁ : realCliffordForm N 0 (Pi.single i₁ 1) = 1 :=
    realCliffordForm_zero_single_one N i₁
  have he₀ : realCliffordForm N 0 (Pi.single i₀ 1) = 1 :=
    realCliffordForm_zero_single_one N i₀
  have h10 : (realCliffordForm N 0).IsOrtho (Pi.single i₁ 1) (Pi.single i₀ 1) :=
    isOrtho_realCliffordForm_single hi10 1 1
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun ℝ (Fin N)).ext fun j ↦ ?_
  simp only [LinearEquiv.coe_toLinearMap, Pi.basisFun_apply]
  rw [QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm_apply,
    CliffordAlgebra.coe_realCliffordSpinProjectionZero_apply,
    spinRotationPathE10,
    CliffordAlgebra.spinRotationPath_apply,
    CliffordAlgebra.spinRotation_eq_spinCircle]
  have hz_sq : ((Circle.exp (Real.pi * (u : ℝ)) : ℂ) ^ 2) =
      (Circle.exp (2 * Real.pi * (u : ℝ)) : ℂ) := by
    rw [← Circle.coe_pow, ← Circle.exp_natCast_mul]
    congr 2
    push_cast
    ring
  rcases lt_or_ge (j : ℕ) 2 with hj | hj
  · have hj' : j = i₀ ∨ j = i₁ := by
      simp only [i₀, i₁, Fin.ext_iff]
      omega
    rcases hj' with rfl | rfl
    · rw [CliffordAlgebra.spinVectorAction_spinCircle_right, he₀, mul_one, hz_sq,
        evalCircleRotationSO_toLin'_single_zero N hN]
    · rw [CliffordAlgebra.spinVectorAction_spinCircle_left, he₁, mul_one, hz_sq,
        evalCircleRotationSO_toLin'_single_one N hN, sub_eq_add_neg]
  · have hj0 : j ≠ i₀ := fun h ↦ by have := congrArg Fin.val h; dsimp [i₀] at this; omega
    have hj1 : j ≠ i₁ := fun h ↦ by have := congrArg Fin.val h; dsimp [i₁] at this; omega
    rw [CliffordAlgebra.spinVectorAction_spinCircle_of_isOrtho h10
        (by rw [he₁, he₀, mul_one])
        (isOrtho_realCliffordForm_single hj1.symm 1 1)
        (isOrtho_realCliffordForm_single hj0.symm 1 1),
      evalCircleRotationSO_toLin'_single_of_two_le N hN _ hj]

/-! ## Nonvanishing in algebraic `K₁` and `SK₁` -/

private theorem circleRotation_not_mem_elementarySubgroup_real (N : ℕ) (hN : 2 ≤ N) :
    stabilizeGL (CircleRing ℝ) hN (SpecialLinearGroup.toGL (circleRotation ℝ)) ∉
      elementarySubgroup (Fin N) (CircleRing ℝ) := by
  intro hg
  have : NeZero N := ⟨by omega⟩
  let gSL := stabilizeSL hN (circleRotation ℝ)
  have hgSL : SpecialLinearGroup.toGL gSL ∈ elementarySubgroup (Fin N) (CircleRing ℝ) := by
    rwa [toGL_stabilizeSL]
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
      Circle.exp.continuous.comp (continuous_const.mul continuous_subtypeVal)⟩
  have hpre : ({0, 1} : Set I) ⊆ circleLoop ⁻¹' {1} := by
    rintro u (rfl | rfl)
    · simp [circleLoop]
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, circleLoop, ContinuousMap.coe_mk,
        Set.Icc.coe_one, mul_one]
      exact Circle.ext (by simp)
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
  let γSpin := spinRotationPathE10 N hN
  let p := CliffordAlgebra.realCliffordSpinProjectionZero N
  have hp : IsCoveringMap p := CliffordAlgebra.isCoveringMap_realCliffordSpinProjectionZero N
  have hp1 : p 1 = p (CliffordAlgebra.spinGroup.negOne (realCliffordForm N 0)
      (nondegenerate_realCliffordForm N 0).ne_zero) :=
    (map_one p).trans (CliffordAlgebra.realCliffordSpinProjectionZero_negOne N).symm
  let δ : Path (p 1) (p 1) := (γSpin.map p.continuous).cast rfl hp1
  have hsrc :
      retractToClifford.comp ((1 : C(Circle, SpecialLinearGroup (Fin N) ℝ)).comp circleLoop) =
        (Path.refl (p 1)).toContinuousMap := by
    refine ContinuousMap.ext fun u ↦ ?_
    have h1 : SpecialLinearGroup.polarRetraction (Fin N) ℝ 1 = 1 := by
      simpa only [map_one] using
        SpecialLinearGroup.polarRetraction_toSL (n := Fin N) (𝕜 := ℝ) 1
    simp [retractToClifford, h1, p]
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
  -- Covering homotopy lifting forces `1 = -1` in `Spin(N)`, a contradiction.
  have hneq := IsCoveringMap.eq_of_map_homotopic_refl hp γSpin hp1
    (Path.homotopic_iff_homotopicRel.mpr hloopSO.symm)
  exact CliffordAlgebra.spinGroup.negOne_ne_one (realCliffordForm N 0)
    (nondegenerate_realCliffordForm N 0).ne_zero hneq.symm

private theorem circle_rotation_not_stably_elementary_real :
    AlgebraicK1.mk (CircleRing ℝ) 2 (SpecialLinearGroup.toGL (circleRotation ℝ)) ≠ 1 := by
  rw [ne_eq, AlgebraicK1.mk_eq_one_iff]
  rintro ⟨N, hN, hmem⟩
  exact circleRotation_not_mem_elementarySubgroup_real N hN hmem

/-- Base change along `f : k →+* S` carries `circleRotation k` to `circleRotation S`. -/
@[simp]
theorem map_circleRotation {k S : Type*} [CommRing k] [CommRing S] (f : k →+* S) :
    SpecialLinearGroup.map (CircleRing.map f) (circleRotation k) = circleRotation S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Base change along `f : k →+* S` carries `toGL (circleRotation k)` to
`toGL (circleRotation S)`. -/
theorem map_toGL_circleRotation {k S : Type*} [CommRing k] [CommRing S] (f : k →+* S) :
    Units.map ((CircleRing.map f).mapMatrix (m := Fin 2)).toMonoidHom
        (SpecialLinearGroup.toGL (circleRotation k)) =
      SpecialLinearGroup.toGL (circleRotation S) :=
  (SpecialLinearGroup.toGL_map (CircleRing.map f) (circleRotation k)).symm.trans
    (congrArg SpecialLinearGroup.toGL (map_circleRotation f))

/-- **The circle rotation has nontrivial class in algebraic `K₁`**: for any commutative ring
`k` admitting a ring homomorphism `k →+* ℝ` (such as `ℤ`, `ℚ`, or `ℝ`), `circleRotation k`
represents a nontrivial class in `SK₁(CircleRing k)`. -/
theorem circle_rotation_not_stably_elementary {k : Type*} [CommRing k] (f : k →+* ℝ) :
    AlgebraicK1.mk (CircleRing k) 2 (SpecialLinearGroup.toGL (circleRotation k)) ≠ 1 := by
  intro h
  apply circle_rotation_not_stably_elementary_real
  have hmap := congrArg (AlgebraicK1.map (CircleRing.map f)) h
  rw [AlgebraicK1.map_mk, map_one, map_toGL_circleRotation f] at hmap
  exact hmap

/-- **No identity stabilization of `circleRotation k` is elementary** when `k` admits a ring
homomorphism `k →+* ℝ`. -/
theorem circleRotation_not_mem_elementarySubgroup {k : Type*} [CommRing k] (f : k →+* ℝ)
    (N : ℕ) (hN : 2 ≤ N) :
    stabilizeGL (CircleRing k) hN (SpecialLinearGroup.toGL (circleRotation k)) ∉
      elementarySubgroup (Fin N) (CircleRing k) := by
  intro hmem
  exact circle_rotation_not_stably_elementary f (AlgebraicK1.mk_eq_one_iff.2 ⟨N, hN, hmem⟩)

/-- `SK₁(CircleRing k)` is nontrivial whenever `k` admits a ring homomorphism `k →+* ℝ`: even
for a Dedekind domain such as `CircleRing ℚ` or `CircleRing ℝ`, `SK₁` need not vanish. -/
theorem specialAlgebraicK1_circleRing_ne_bot {k : Type*} [CommRing k] (f : k →+* ℝ) :
    specialAlgebraicK1 (CircleRing k) ≠ ⊥ := by
  intro hbot
  have hmem := circleRotation_mk_mem_specialAlgebraicK1 k
  rw [hbot, Subgroup.mem_bot] at hmem
  exact circle_rotation_not_stably_elementary f hmem

/-- The determinant homomorphism `K₁(CircleRing k) →* (CircleRing k)ˣ` is not injective
whenever `k` admits a ring homomorphism `k →+* ℝ`. -/
theorem not_det_circleRing_injective {k : Type*} [CommRing k] (f : k →+* ℝ) :
    ¬ Function.Injective (AlgebraicK1.det (CircleRing k)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hker : (AlgebraicK1.det (CircleRing k)).ker = specialAlgebraicK1 (CircleRing k) := by
    ext x
    exact mem_specialAlgebraicK1_iff.symm
  rw [hker]
  exact specialAlgebraicK1_circleRing_ne_bot f

end

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Analysis.Matrix.Exponential.Log
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Geometry.Lie.Exponential.Matrix.Symplectic

/-!
# Polar coordinates on `Sp(2, ℝ)`

A real symplectic matrix `A` factors as `A = P U`, with `P = √(A Aᵀ)` positive definite and `U`
orthogonal, both symplectic. The positive factor is the exponential `P = exp X` of the symmetric
matrix `X = log P` (`TauCeti.GLSymplectic.polarLog`), which lies in the symplectic Lie algebra
(`TauCeti.GLSymplectic.polarLog_mem_sp`), and `X` is determined by this factorization
(`TauCeti.GLSymplectic.polarLog_eq_and_maslovPhase_eq_of_mul_eq`). The positive factor stands on
the left, in the order `P U` of the polar deformation `P ^ (1 - t) U`
(`Matrix.GeneralLinearGroup.polarDeformation`); the Cartan decomposition
`TauCeti.GLSymplectic.cartanHomeomorph` uses the other order `A = U exp Y`, with
`Y = log √(Aᵀ A) = Uᵀ X U`.

In dimension two, that is for symplectic matrices indexed by `n ⊕ n` with `n` a one-point type,
both factors have explicit coordinates.

* The symmetric matrices of the symplectic Lie algebra are exactly the matrices
  `[[a, b], [b, -a]]` (`TauCeti.GLSymplectic.polarLogMatrix`,
  `TauCeti.GLSymplectic.polarLogMatrix_polarLogCoord`), so the positive factor is
  `P = exp [[a, b], [b, -a]]` for a unique point `(a, b)` of the plane
  (`TauCeti.GLSymplectic.polarLogCoord`). The radial map `v ↦ v / √(1 + ‖v‖²)` of Mathlib's
  `Homeomorph.unitBall`, with inverse `w ↦ w / √(1 - ‖w‖²)`, moves this point to the open unit
  disc.
* The orthogonal symplectic matrices of size two are the realified `1 × 1` unitary matrices, the
  rotations `[[cos θ, -sin θ], [sin θ, cos θ]]`
  (`TauCeti.GLSymplectic.coe_ofUnitary_circleScalar`). The rotation by `z = e^{iθ}` is the
  orthogonal factor `U` of `A` exactly when `z` is the Maslov phase `ρ(A)` of
  `TauCeti.GLSymplectic.maslovPhase`.

Together they give the homeomorphism (`TauCeti.GLSymplectic.polarCoordinates`)

`Sp(2, ℝ) ≃ₜ D² × S¹`, `A ↦ ((a, b) / √(1 + a² + b²), ρ(A))`,

whose inverse is the product in the factor order `P U`: a point `(w, z)` goes to
`exp [[a, b], [b, -a]] · R_z`, with `(a, b) = w / √(1 - ‖w‖²)` and `R_z` the rotation by `z`
(`TauCeti.GLSymplectic.coe_polarCoordinates_symm_apply`). The parametrization by the plane and
the circle is smooth (`TauCeti.GLSymplectic.contDiff_exp_polarLogMatrix_mul_realify`).

The second coordinate is the Maslov phase, so the Maslov index of a loop of `2 × 2` symplectic
matrices is the winding number of its circle coordinate
(`TauCeti.GLSymplectic.maslovIndex_eq_degree_polarCoordinates_snd`). In particular a loop that
turns the circle coordinate once in the positive direction, such as the loop of rotations
`t ↦ R_{e^{2π i t}}`, has Maslov index `1` (`TauCeti.GLSymplectic.maslovIndex_scalarRotationLoop`).

## Main definitions

* `TauCeti.GLSymplectic.polarLog`: the logarithm `log √(A Aᵀ)` of the positive polar factor.
* `TauCeti.GLSymplectic.polarLogMatrix`: the matrix `[[a, b], [b, -a]]` of a point of the plane.
* `TauCeti.GLSymplectic.polarLogCoord`: the coordinates `(a, b)` of a `2 × 2` matrix.
* `TauCeti.GLSymplectic.polarExp`: the positive symplectic matrix `exp [[a, b], [b, -a]]`.
* `TauCeti.GLSymplectic.polarCoordinates`: the homeomorphism `Sp(2, ℝ) ≃ₜ D² × S¹`.

## Main results

* `TauCeti.GLSymplectic.exp_polarLog_mul_polarUnitary`: `A = exp (log P) · U`.
* `TauCeti.GLSymplectic.polarLog_eq_and_maslovPhase_eq_of_mul_eq`: if `A = exp X · U` with `X`
  symmetric and `U` the realification of a unitary matrix `u`, then `log P = X` and
  `ρ(A) = det u`.
* `TauCeti.GLSymplectic.polarLogMatrix_polarLogCoord`: in dimension two, every symmetric element
  of the symplectic Lie algebra is `[[a, b], [b, -a]]`.
* `TauCeti.GLSymplectic.maslovIndex_eq_degree_polarCoordinates_snd`: the Maslov index of a loop in
  `Sp(2, ℝ)` is the winding number of its circle coordinate.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (Proposition 2.2.11
  for the polar decomposition of symplectic matrices and the map `ρ`).
-/

public section

noncomputable section

open Matrix Matrix.UnitaryGroup Metric NormedSpace
open scoped ContDiff MatrixOrder

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The logarithm of the positive polar factor -/

/-- The logarithm `log P` of the positive polar factor `P = √(A Aᵀ)` of a real symplectic matrix
`A = P U`. -/
def polarLog (A : GLSymplectic n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  cfc Real.log (CFC.sqrt (((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
    star ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)))

/-- The logarithm of the positive polar factor is symmetric. -/
theorem isHermitian_polarLog (A : GLSymplectic n ℝ) : (polarLog A).IsHermitian :=
  isHermitian_iff_isSelfAdjoint.2 (cfc_predicate _ _)

/-- The exponential of `TauCeti.GLSymplectic.polarLog A` is the positive polar factor of `A`. -/
theorem exp_polarLog (A : GLSymplectic n ℝ) :
    exp (polarLog A) = CFC.sqrt (((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
      star ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) :=
  (isStrictlyPositive_iff_posDef.1 (Units.isStrictlyPositive_sqrt_mul_star _)).exp_cfc_log

/-- **The polar decomposition through the logarithm**: `A = exp (log P) · U`, with `U` the
orthogonal polar factor `TauCeti.GLSymplectic.polarUnitary A`. -/
theorem exp_polarLog_mul_polarUnitary (A : GLSymplectic n ℝ) :
    exp (polarLog A) *
        ((polarUnitary A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  rw [exp_polarLog, coe_polarUnitary, Units.sqrt_mul_star_mul_polarUnitary]

/-- The logarithm of the positive polar factor of a symplectic matrix lies in the symplectic Lie
algebra. -/
theorem polarLog_mem_sp (A : GLSymplectic n ℝ) : polarLog A ∈ LieAlgebra.Symplectic.sp n ℝ := by
  rw [← (isHermitian_polarLog A).exp_mem_symplecticGroup_iff, exp_polarLog]
  exact SymplecticGroup.sqrt_mul_star_mem (mem_iff_mem_symplecticGroup.1 A.2)

section Continuity

open scoped Matrix.Norms.L2Operator

/-- The logarithm of the positive polar factor depends continuously on the symplectic matrix. -/
theorem continuous_polarLog : Continuous (polarLog : GLSymplectic n ℝ → _) := by
  have hA : Continuous fun A : GLSymplectic n ℝ ↦
      ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hsq := (contDiffOn_sqrt (𝕜 := ℝ) (k := 0)).continuousOn.comp_continuous
    (hA.mul (continuous_star.comp hA)) fun A ↦
      (Units.isStrictlyPositive_mul_star (A : GL (n ⊕ n) ℝ)).posDef
  exact (contDiffOn_cfc_log (𝕜 := ℝ) (k := 0)).continuousOn.comp_continuous hsq fun A ↦
    isStrictlyPositive_iff_posDef.1 (Units.isStrictlyPositive_sqrt_mul_star _)

end Continuity

/-- **Uniqueness of the polar coordinates.** If `A = exp X · U` with `X` symmetric and `U` the
realification of a unitary matrix `u`, then `X` is the logarithm of the positive polar factor of
`A` and the Maslov phase `ρ(A)` is the determinant of `u`. -/
theorem polarLog_eq_and_maslovPhase_eq_of_mul_eq {A : GLSymplectic n ℝ}
    {X : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hX : X.IsHermitian) {u : unitaryGroup n ℂ}
    (h : exp X * ((ofUnitary u : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) :
    polarLog A = X ∧ maslovPhase A = detCircle u := by
  let U : unitary (Matrix (n ⊕ n) (n ⊕ n) ℝ) := ⟨_, coe_ofUnitary_mem_unitary u⟩
  have hP := Units.sqrt_mul_star_eq_of_mul_eq _ hX.posDef_exp.posSemidef.nonneg (v := U) h
  have hU := Units.polarUnitary_eq_of_mul_eq _ hX.posDef_exp.posSemidef.nonneg (v := U) h
  refine ⟨by rw [polarLog, hP, hX.cfc_log_exp], ?_⟩
  rw [← maslovPhase_inclusion_polarUnitary, ← maslovPhase_ofUnitary]
  congr 1
  exact Subtype.ext (Units.ext (by rw [Subgroup.coe_inclusion, coe_polarUnitary, hU]))

/-! ### Symmetric symplectic Lie matrices of size two -/

/-- The symmetric matrix `[[a, b], [b, -a]]` of a point `(a, b)` of the plane, with blocks
`a • 1`, `b • 1`, `b • 1` and `-a • 1`. For `n` a one-point type these are exactly the symmetric
elements of the symplectic Lie algebra (`TauCeti.GLSymplectic.polarLogMatrix_polarLogCoord`). -/
def polarLogMatrix (v : EuclideanSpace ℝ (Fin 2)) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks (v 0 • 1) (v 1 • 1) (v 1 • 1) (-v 0 • 1)

omit [Fintype n] in
/-- The matrix `[[a, b], [b, -a]]` is symmetric. -/
theorem isHermitian_polarLogMatrix (v : EuclideanSpace ℝ (Fin 2)) :
    (polarLogMatrix (n := n) v).IsHermitian := by
  simp [polarLogMatrix, IsHermitian, fromBlocks_transpose]

/-- The matrix `[[a, b], [b, -a]]` lies in the symplectic Lie algebra. -/
theorem polarLogMatrix_mem_sp (v : EuclideanSpace ℝ (Fin 2)) :
    polarLogMatrix (n := n) v ∈ LieAlgebra.Symplectic.sp n ℝ := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;>
    by_cases h : i = j <;> simp [polarLogMatrix, h, eq_comm]

omit [Fintype n] in
/-- The matrix `[[a, b], [b, -a]]` depends continuously on `(a, b)`. -/
theorem continuous_polarLogMatrix : Continuous (polarLogMatrix (n := n)) := by
  unfold polarLogMatrix
  fun_prop

section Unique

variable [Unique n]

/-- The coordinates `(a, b) = (X₁₁, X₁₂)` of a `2 × 2` matrix `X`, indexed by `n ⊕ n` with `n` a
one-point type. On the symmetric elements of the symplectic Lie algebra they invert
`TauCeti.GLSymplectic.polarLogMatrix`. -/
def polarLogCoord (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[X (.inl default) (.inl default), X (.inl default) (.inr default)]

omit [Fintype n] in
/-- The coordinates of `[[a, b], [b, -a]]` are `(a, b)`. -/
@[simp]
theorem polarLogCoord_polarLogMatrix (v : EuclideanSpace ℝ (Fin 2)) :
    polarLogCoord (polarLogMatrix (n := n) v) = v := by
  ext i
  fin_cases i <;> simp [polarLogCoord, polarLogMatrix]

/-- **Symmetric symplectic Lie matrices of size two.** A symmetric element `X` of the symplectic
Lie algebra `sp(2, ℝ)` is `[[a, b], [b, -a]]` for its coordinates `(a, b) = (X₁₁, X₁₂)`. -/
theorem polarLogMatrix_polarLogCoord {X : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hX : X.IsHermitian) (hsp : X ∈ LieAlgebra.Symplectic.sp n ℝ) :
    polarLogMatrix (polarLogCoord X) = X := by
  obtain ⟨-, -, h⟩ := (mem_symplecticLieAlgebra_iff X).1 hsp
  have hX' : X (.inr default) (.inl default) = X (.inl default) (.inr default) := by
    simpa using hX.apply (.inl default) (.inr default)
  ext (i | i) (j | j) <;> rw [Subsingleton.elim i default, Subsingleton.elim j default] <;>
    simp [polarLogMatrix, polarLogCoord, h, hX']

omit [Fintype n] [DecidableEq n] in
/-- The coordinates of a matrix depend continuously on it. -/
theorem continuous_polarLogCoord : Continuous (polarLogCoord (n := n)) := by
  unfold polarLogCoord
  fun_prop

end Unique

/-! ### The positive factors and the rotations -/

/-- The positive definite symplectic matrix `exp [[a, b], [b, -a]]` of a point `(a, b)` of the
plane. -/
def polarExp (v : EuclideanSpace ℝ (Fin 2)) : GLSymplectic n ℝ :=
  symplecticGroupContinuousMulEquiv n ℝ
    ⟨exp (polarLogMatrix v), exp_mem_symplecticGroup_of_mem_sp _ (polarLogMatrix_mem_sp v)⟩

/-- The underlying matrix of `TauCeti.GLSymplectic.polarExp v` is `exp [[a, b], [b, -a]]`. -/
@[simp]
theorem coe_polarExp (v : EuclideanSpace ℝ (Fin 2)) :
    ((polarExp (n := n) v : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      exp (polarLogMatrix v) := by
  simp [polarExp]

section Smooth

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The positive factor `exp [[a, b], [b, -a]]` depends continuously on `(a, b)`. -/
theorem continuous_polarExp : Continuous (polarExp (n := n)) :=
  (symplecticGroupContinuousMulEquiv n ℝ).continuous.comp (Continuous.subtype_mk
    ((NormedSpace.contDiff_exp ℝ (k := 0)).continuous.comp continuous_polarLogMatrix) _)

omit [Fintype n] in
/-- The matrix `[[a, b], [b, -a]]` is `a • diag(1, -1) + b • [[0, 1], [1, 0]]`. -/
theorem polarLogMatrix_eq (v : EuclideanSpace ℝ (Fin 2)) :
    polarLogMatrix (n := n) v = v 0 • fromBlocks 1 0 0 (-1) + v 1 • fromBlocks 0 1 1 0 := by
  simp [polarLogMatrix, fromBlocks_smul, fromBlocks_add]

/-- **The polar parametrization is smooth.** The map `((a, b), z) ↦ exp [[a, b], [b, -a]] · R_z`
from the plane and the complex numbers to the matrices, with `R_z = re z • 1 + im z • J` the
realification of `z • 1`, is smooth. On the unit circle in the second factor it is the inverse of
`TauCeti.GLSymplectic.polarCoordinates`, read through the radial map of the plane onto the disc. -/
theorem contDiff_exp_polarLogMatrix_mul_realify {k : ℕ∞ω} :
    ContDiff ℝ k fun p : EuclideanSpace ℝ (Fin 2) × ℂ ↦
      exp (polarLogMatrix (n := n) p.1) * (p.2 • 1 : Matrix n n ℂ).realify := by
  simp only [polarLogMatrix_eq, realify_smul_one, RCLike.re_to_complex, RCLike.im_to_complex]
  have hS : ContDiff ℝ k fun v : EuclideanSpace ℝ (Fin 2) ↦
      v 0 • (fromBlocks 1 0 0 (-1) : Matrix (n ⊕ n) (n ⊕ n) ℝ) + v 1 • fromBlocks 0 1 1 0 := by
    have h₀ : ContDiff ℝ k fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0 :=
      contDiff_piLp_apply 2
    have h₁ : ContDiff ℝ k fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1 :=
      contDiff_piLp_apply 2
    exact (h₀.smul contDiff_const).add (h₁.smul contDiff_const)
  have hR : ContDiff ℝ k fun z : ℂ ↦ z.re • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) + z.im • J n ℝ := by
    have hre : ContDiff ℝ k fun z : ℂ ↦ z.re := Complex.reCLM.contDiff
    have him : ContDiff ℝ k fun z : ℂ ↦ z.im := Complex.imCLM.contDiff
    exact (hre.smul contDiff_const).add (him.smul contDiff_const)
  exact ((NormedSpace.contDiff_exp ℝ).comp (hS.comp contDiff_fst)).mul (hR.comp contDiff_snd)

end Smooth

/-- The realification of the scalar unitary matrix `z • 1` is the rotation `re z • 1 + im z • J`
by `z`; in dimension two it is `[[cos θ, -sin θ], [sin θ, cos θ]]` for `z = e^{iθ}`. -/
theorem coe_ofUnitary_circleScalar (z : Circle) :
    ((ofUnitary (circleScalar (n := n) z) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (z : ℂ).re • 1 + (z : ℂ).im • J n ℝ := by
  rw [coe_ofUnitary, coe_circleScalar, realify_smul_one, RCLike.re_to_complex,
    RCLike.im_to_complex]

/-- In dimension two the orthogonal polar factor is the rotation by the Maslov phase. -/
theorem ofUnitary_circleScalar_maslovPhase [Unique n] (A : GLSymplectic n ℝ) :
    ofUnitary (circleScalar (maslovPhase A)) = Subgroup.inclusion inf_le_left (polarUnitary A) := by
  rw [← maslovPhase_inclusion_polarUnitary, maslovPhase_inclusion, circleScalar_detCircle,
    ofUnitary_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The positive polar factor of `exp [[a, b], [b, -a]] · R_z` is `exp [[a, b], [b, -a]]`. -/
@[simp]
theorem polarLog_polarExp_mul_ofUnitary (v : EuclideanSpace ℝ (Fin 2)) (u : unitaryGroup n ℂ) :
    polarLog (polarExp v * ofUnitary u) = polarLogMatrix v :=
  (polarLog_eq_and_maslovPhase_eq_of_mul_eq (isHermitian_polarLogMatrix v) (u := u)
    (by rw [Subgroup.coe_mul, Units.val_mul, coe_polarExp])).1

/-- The Maslov phase of `exp [[a, b], [b, -a]] · U` is the determinant of the unitary matrix
realified by `U`. -/
@[simp]
theorem maslovPhase_polarExp_mul_ofUnitary (v : EuclideanSpace ℝ (Fin 2))
    (u : unitaryGroup n ℂ) : maslovPhase (polarExp v * ofUnitary u) = detCircle u :=
  (polarLog_eq_and_maslovPhase_eq_of_mul_eq (isHermitian_polarLogMatrix v) (u := u)
    (by rw [Subgroup.coe_mul, Units.val_mul, coe_polarExp])).2

/-! ### Polar coordinates -/

variable [Unique n]

/-- **Polar coordinates on `Sp(2, ℝ)`.** A `2 × 2` real symplectic matrix `A = P U` is determined
by the point `(a, b)` of the plane with `P = exp [[a, b], [b, -a]]`, moved to the open unit disc by
`v ↦ v / √(1 + ‖v‖²)`, and by its Maslov phase `ρ(A)`, the point of the circle by which `U`
rotates. This is a homeomorphism `Sp(2, ℝ) ≃ₜ D² × S¹`, whose inverse is the product in the factor
order `P U`. -/
def polarCoordinates : GLSymplectic n ℝ ≃ₜ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 × Circle where
  toFun A := (Homeomorph.unitBall (polarLogCoord (polarLog A)), maslovPhase A)
  invFun p := polarExp (Homeomorph.unitBall.symm p.1) * ofUnitary (circleScalar p.2)
  left_inv A := by
    refine Subtype.ext (Units.ext ?_)
    simp only [Homeomorph.symm_apply_apply, Subgroup.coe_mul, Units.val_mul, coe_polarExp,
      ofUnitary_circleScalar_maslovPhase, Subgroup.coe_inclusion,
      polarLogMatrix_polarLogCoord (isHermitian_polarLog A) (polarLog_mem_sp A)]
    exact exp_polarLog_mul_polarUnitary A
  right_inv p := by
    simp only [polarLog_polarExp_mul_ofUnitary, maslovPhase_polarExp_mul_ofUnitary,
      polarLogCoord_polarLogMatrix, Homeomorph.apply_symm_apply, detCircle_circleScalar]
  continuous_toFun :=
    (Homeomorph.unitBall.continuous.comp (continuous_polarLogCoord.comp continuous_polarLog)).prodMk
      continuous_maslovPhase
  continuous_invFun :=
    (continuous_polarExp.comp (Homeomorph.unitBall.symm.continuous.comp continuous_fst)).mul
      (continuous_ofUnitary.comp (continuous_circleScalar.comp continuous_snd))

/-- The disc coordinate of `A` is the radial image of the coordinates of `log √(A Aᵀ)`. -/
@[simp]
theorem polarCoordinates_apply_fst (A : GLSymplectic n ℝ) :
    (polarCoordinates A).1 = Homeomorph.unitBall (polarLogCoord (polarLog A)) :=
  (rfl)

/-- The circle coordinate of `A` is its Maslov phase. -/
@[simp]
theorem polarCoordinates_apply_snd (A : GLSymplectic n ℝ) :
    (polarCoordinates A).2 = maslovPhase A :=
  (rfl)

/-- The inverse of the polar coordinates is the product `exp [[a, b], [b, -a]] · R_z` in the factor
order `P U`, with `(a, b)` the radial preimage of the point of the disc. -/
@[simp]
theorem polarCoordinates_symm_apply (p : ball (0 : EuclideanSpace ℝ (Fin 2)) 1 × Circle) :
    polarCoordinates.symm p =
      polarExp (n := n) (Homeomorph.unitBall.symm p.1) * ofUnitary (circleScalar p.2) :=
  (rfl)

/-- The underlying matrix of the inverse of the polar coordinates at `(w, z)` is
`exp [[a, b], [b, -a]] · R_z`, with `(a, b) = w / √(1 - ‖w‖²)`. -/
theorem coe_polarCoordinates_symm_apply (p : ball (0 : EuclideanSpace ℝ (Fin 2)) 1 × Circle) :
    (((polarCoordinates.symm p : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) :
      Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      exp (polarLogMatrix ((√(1 - ‖(p.1 : EuclideanSpace ℝ (Fin 2))‖ ^ 2))⁻¹ • p.1)) *
        ((p.2 : ℂ) • 1 : Matrix n n ℂ).realify := by
  rw [polarCoordinates_symm_apply, Subgroup.coe_mul, Units.val_mul, coe_polarExp,
    Homeomorph.unitBall_symm_apply_coe, coe_ofUnitary, coe_circleScalar]

/-- **The Maslov index is the winding number of the circle coordinate.** For a loop `γ` of
`2 × 2` real symplectic matrices, the Maslov index is the degree of the loop traced by the second
polar coordinate of `γ`. -/
theorem maslovIndex_eq_degree_polarCoordinates_snd {A : GLSymplectic n ℝ} (γ : Path A A) :
    maslovIndex γ =
      Circle.degree (γ.map (continuous_snd.comp (polarCoordinates (n := n)).continuous)) :=
  (maslovIndex_def γ).trans (rfl)

end TauCeti.GLSymplectic

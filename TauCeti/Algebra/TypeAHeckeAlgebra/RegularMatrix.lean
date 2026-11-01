/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.Matrix

/-!
# Regular Hecke matrices on a fixed carrier

The orthonormal PBW vectors `T_w` identify every real-parameter regular Hecke module with
one fixed coordinate space. In these coordinates, multiplication by `g_i = q T_i` has
an off-diagonal entry `q`, a descent diagonal entry `q² - 1`, and all other entries zero.
We define these matrices without using a parameter-dependent quotient as their carrier.
Both left and right matrices are symmetric, commute with the opposite action, and satisfy
the quadratic relation. At `q = √Q` their entries depend continuously on `Q`, including
at `Q = 1`. This fixed-carrier realization permits continuous finite-dimensional spectral
projection and rank arguments.

The comparison with multiplication uses the PBW basis; its orthonormality for the positive
regular form is established in `TauCeti.Algebra.TypeAHeckeAlgebra.RegularForm`.

## References

* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

open Matrix

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {n : ℕ} {W : Type*} [Group W]
variable (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

open Classical in
/-- Left regular multiplication by a rescaled simple generator, in orthonormal PBW
coordinates. The formula makes sense even when the scalar parameter is not a unit. -/
noncomputable def regularLeftMatrix (s : R) (i : Fin (n - 1)) : Matrix W W R :=
  fun v w ↦ (if v = cs.simple i * w then s else 0) +
    if v = w ∧ cs.IsLeftDescent w i then s ^ 2 - 1 else 0

open Classical in
/-- Right regular multiplication by a rescaled simple generator, in orthonormal PBW
coordinates. The formula makes sense even when the scalar parameter is not a unit. -/
noncomputable def regularRightMatrix (s : R) (i : Fin (n - 1)) : Matrix W W R :=
  fun v w ↦ (if v = w * cs.simple i then s else 0) +
    if v = w ∧ cs.IsRightDescent w i then s ^ 2 - 1 else 0

open Classical in
/-- The entries of the left regular matrix. -/
@[simp]
theorem regularLeftMatrix_apply (s : R) (i : Fin (n - 1)) (v w : W) :
    regularLeftMatrix cs s i v w = (if v = cs.simple i * w then s else 0) +
      if v = w ∧ cs.IsLeftDescent w i then s ^ 2 - 1 else 0 := (rfl)

open Classical in
/-- The entries of the right regular matrix. -/
@[simp]
theorem regularRightMatrix_apply (s : R) (i : Fin (n - 1)) (v w : W) :
    regularRightMatrix cs s i v w = (if v = w * cs.simple i then s else 0) +
      if v = w ∧ cs.IsRightDescent w i then s ^ 2 - 1 else 0 := (rfl)

/-- The left regular matrix is symmetric over any commutative coefficient ring. -/
@[simp]
theorem transpose_regularLeftMatrix (s : R) (i : Fin (n - 1)) :
    (regularLeftMatrix cs s i)ᵀ = regularLeftMatrix cs s i := by
  classical
  ext v w
  have h : w = cs.simple i * v ↔ v = cs.simple i * w := by
    constructor <;> rintro rfl <;> simp
  simp only [Matrix.transpose_apply, regularLeftMatrix_apply, h]
  by_cases hvw : v = w
  · subst w; rfl
  · simp [hvw, Ne.symm hvw]

/-- The right regular matrix is symmetric over any commutative coefficient ring. -/
@[simp]
theorem transpose_regularRightMatrix (s : R) (i : Fin (n - 1)) :
    (regularRightMatrix cs s i)ᵀ = regularRightMatrix cs s i := by
  classical
  ext v w
  have h : w = v * cs.simple i ↔ v = w * cs.simple i := by
    constructor <;> rintro rfl <;> simp
  simp only [Matrix.transpose_apply, regularRightMatrix_apply, h]
  by_cases hvw : v = w
  · subst w; rfl
  · simp [hvw, Ne.symm hvw]

section Multiplication

variable [Fintype W] (q : Rˣ)

open Classical in
/-- The explicit left matrix is the matrix of multiplication by `g_i = q T_i` in the
PBW basis. For a star-fixed real or complex parameter this basis is orthonormal for the
regular trace form. -/
theorem regularLeftMatrix_eq_leftMulMatrix [DecidableEq W] (i : Fin (n - 1)) :
    regularLeftMatrix cs (q : R) i =
      Algebra.leftMulMatrix (basisTw q cs) ((q : R) • T q i) := by
  ext v w
  rw [Algebra.leftMulMatrix_eq_repr_mul, coe_basisTw, smul_mul_assoc]
  by_cases h : cs.IsLeftDescent w i
  · rw [T_mul_Tw_of_isLeftDescent cs h]
    by_cases hvw : v = w <;>
      simp [regularLeftMatrix_apply, h, ← coe_basisTw, Finsupp.single_apply, eq_comm,
        smul_add, smul_smul, mul_sub, sq, add_comm, hvw]
  · rw [T_mul_Tw_of_not_isLeftDescent cs h]
    simp [regularLeftMatrix_apply, h, ← coe_basisTw, Finsupp.single_apply, eq_comm]

open Classical in
/-- The explicit right matrix is the matrix of right multiplication by `g_i = q T_i`
in the PBW basis. -/
theorem regularRightMatrix_eq_toMatrix [DecidableEq W] (i : Fin (n - 1)) :
    regularRightMatrix cs (q : R) i = LinearMap.toMatrix (basisTw q cs) (basisTw q cs)
      (LinearMap.mulRight R ((q : R) • T q i)) := by
  ext v w
  rw [LinearMap.toMatrix_apply, coe_basisTw, LinearMap.mulRight_apply, mul_smul_comm]
  by_cases h : cs.IsRightDescent w i
  · rw [Tw_mul_T_of_isRightDescent cs h]
    by_cases hvw : v = w <;>
      simp [regularRightMatrix_apply, h, ← coe_basisTw, Finsupp.single_apply, eq_comm,
        smul_add, smul_smul, mul_sub, sq, add_comm, hvw]
  · rw [Tw_mul_T_of_not_isRightDescent cs h]
    simp [regularRightMatrix_apply, h, ← coe_basisTw, Finsupp.single_apply, eq_comm]

/-- The fixed-coordinate left action agrees with multiplication on every vector. -/
theorem regularLeftMatrix_mulVec_repr (i : Fin (n - 1))
    (x : TypeAHeckeAlgebra R q n) :
    regularLeftMatrix cs (q : R) i *ᵥ (basisTw q cs).repr x =
      (basisTw q cs).repr (((q : R) • T q i) * x) := by
  classical
  rw [regularLeftMatrix_eq_leftMulMatrix, Algebra.leftMulMatrix_mulVec_repr]

/-- The fixed-coordinate right action agrees with multiplication on every vector. -/
theorem regularRightMatrix_mulVec_repr (i : Fin (n - 1))
    (x : TypeAHeckeAlgebra R q n) :
    regularRightMatrix cs (q : R) i *ᵥ (basisTw q cs).repr x =
      (basisTw q cs).repr (x * ((q : R) • T q i)) := by
  classical
  rw [regularRightMatrix_eq_toMatrix, LinearMap.toMatrix_mulVec_repr,
    LinearMap.mulRight_apply]

/-- Left and right regular generator matrices commute. -/
theorem commute_regularLeftMatrix_regularRightMatrix (i j : Fin (n - 1)) :
    Commute (regularLeftMatrix cs (q : R) i) (regularRightMatrix cs (q : R) j) := by
  classical
  rw [commute_iff_eq, regularLeftMatrix_eq_leftMulMatrix,
    Algebra.leftMulMatrix_apply, regularRightMatrix_eq_toMatrix,
    ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  exact congrArg (LinearMap.toMatrix (basisTw q cs) (basisTw q cs))
    (LinearMap.commute_mulLeft_right (R := R) _ _).eq

open Classical in
/-- The rescaled left regular matrix satisfies `(g_i + 1)(g_i - q²) = 0`. -/
theorem regularLeftMatrix_mul_self [DecidableEq W] (i : Fin (n - 1)) :
    regularLeftMatrix cs (q : R) i * regularLeftMatrix cs (q : R) i =
      ((q : R) ^ 2 - 1) • regularLeftMatrix cs (q : R) i + (q : R) ^ 2 • 1 := by
  rw [regularLeftMatrix_eq_leftMulMatrix]
  simpa only [map_mul, map_add, map_smul, map_one] using
    congrArg (Algebra.leftMulMatrix (basisTw q cs)) (rescaled_T_mul_self (q := q) i)

open Classical in
/-- The rescaled right regular matrix satisfies `(g_i + 1)(g_i - q²) = 0`. -/
theorem regularRightMatrix_mul_self [DecidableEq W] (i : Fin (n - 1)) :
    regularRightMatrix cs (q : R) i * regularRightMatrix cs (q : R) i =
      ((q : R) ^ 2 - 1) • regularRightMatrix cs (q : R) i + (q : R) ^ 2 • 1 := by
  have hm : LinearMap.mulRight R ((q : R) • T q i) *
      LinearMap.mulRight R ((q : R) • T q i) =
      ((q : R) ^ 2 - 1) • LinearMap.mulRight R ((q : R) • T q i) +
        (q : R) ^ 2 • 1 := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.mulRight_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [mul_assoc, rescaled_T_mul_self]
    simp [mul_add]
  simpa only [LinearMap.toMatrix_mul, map_add, map_smul, LinearMap.toMatrix_one,
    ← regularRightMatrix_eq_toMatrix] using
    congrArg (LinearMap.toMatrix (basisTw q cs) (basisTw q cs)) hm

/-- The left regular matrices satisfy the adjacent braid relation. -/
theorem regularLeftMatrix_braid {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    regularLeftMatrix cs (q : R) i * regularLeftMatrix cs (q : R) j *
        regularLeftMatrix cs (q : R) i =
      regularLeftMatrix cs (q : R) j * regularLeftMatrix cs (q : R) i *
        regularLeftMatrix cs (q : R) j := by
  classical
  simp only [regularLeftMatrix_eq_leftMulMatrix, ← map_mul, smul_mul_smul, T_braid h]

/-- The right regular matrices satisfy the adjacent braid relation. -/
theorem regularRightMatrix_braid {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    regularRightMatrix cs (q : R) i * regularRightMatrix cs (q : R) j *
        regularRightMatrix cs (q : R) i =
      regularRightMatrix cs (q : R) j * regularRightMatrix cs (q : R) i *
        regularRightMatrix cs (q : R) j := by
  classical
  simp only [regularRightMatrix_eq_toMatrix, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  simp only [Module.End.mul_apply, LinearMap.mulRight_apply]
  have hb : ((q : R) • T q i) * ((q : R) • T q j) * ((q : R) • T q i) =
      ((q : R) • T q j) * ((q : R) • T q i) * ((q : R) • T q j) := by
    simp only [smul_mul_smul, T_braid h]
  simpa only [mul_assoc] using congrArg (fun a ↦ x * a) hb

/-- Distant left regular matrices commute. -/
theorem commute_regularLeftMatrix {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (regularLeftMatrix cs (q : R) i) (regularLeftMatrix cs (q : R) j) := by
  classical
  rw [regularLeftMatrix_eq_leftMulMatrix, regularLeftMatrix_eq_leftMulMatrix]
  exact (((commute_T h).smul_left (q : R)).smul_right (q : R)).map _

/-- Distant right regular matrices commute. -/
theorem commute_regularRightMatrix {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (regularRightMatrix cs (q : R) i) (regularRightMatrix cs (q : R) j) := by
  classical
  rw [commute_iff_eq, regularRightMatrix_eq_toMatrix, regularRightMatrix_eq_toMatrix,
    ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  simp [smul_smul, mul_assoc, (commute_T (R := R) (q := q) h).eq]

end Multiplication

section Continuity

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- On the fixed PBW coordinate carrier, the left regular generator matrices vary
continuously with the square-root parameter, without any invertibility restriction. -/
@[fun_prop]
theorem continuous_regularLeftMatrix (i : Fin (n - 1)) :
    Continuous (fun s : R ↦ regularLeftMatrix cs s i) := by
  classical
  refine continuous_pi fun v ↦ continuous_pi fun w ↦ ?_
  simp only [regularLeftMatrix_apply]
  exact (continuous_if_const _ (fun _ ↦ continuous_id) (fun _ ↦ continuous_const)).add
    (continuous_if_const _ (fun _ ↦ (continuous_id.pow 2).sub continuous_const)
      (fun _ ↦ continuous_const))

/-- On the fixed PBW coordinate carrier, the right regular generator matrices vary
continuously with the square-root parameter, without any invertibility restriction. -/
@[fun_prop]
theorem continuous_regularRightMatrix (i : Fin (n - 1)) :
    Continuous (fun s : R ↦ regularRightMatrix cs s i) := by
  classical
  refine continuous_pi fun v ↦ continuous_pi fun w ↦ ?_
  simp only [regularRightMatrix_apply]
  exact (continuous_if_const _ (fun _ ↦ continuous_id) (fun _ ↦ continuous_const)).add
    (continuous_if_const _ (fun _ ↦ (continuous_id.pow 2).sub continuous_const)
      (fun _ ↦ continuous_const))

/-- Left multiplication by `g_i` in the orthonormal regular carrier is continuous in
`Q > 0`, and through `Q = 1`, when `q = √Q`. The entry formula extends continuously to
all real `Q`; its interpretation as a Hecke module requires `Q > 0`. -/
@[fun_prop]
theorem continuous_regularLeftMatrix_sqrt (i : Fin (n - 1)) :
    Continuous (fun Q : ℝ ↦ regularLeftMatrix cs (Real.sqrt Q) i) :=
  (continuous_regularLeftMatrix cs i).comp Real.continuous_sqrt

/-- Right multiplication by `g_i` in the orthonormal regular carrier is continuous in
`Q > 0`, and through `Q = 1`, when `q = √Q`. -/
@[fun_prop]
theorem continuous_regularRightMatrix_sqrt (i : Fin (n - 1)) :
    Continuous (fun Q : ℝ ↦ regularRightMatrix cs (Real.sqrt Q) i) :=
  (continuous_regularRightMatrix cs i).comp Real.continuous_sqrt

end Continuity

end TauCeti.TypeAHeckeAlgebra

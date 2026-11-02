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
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Regular Hecke matrices on a fixed carrier

The orthonormal PBW vectors `T_w` identify every real-parameter regular Hecke module with
one fixed coordinate space. In these coordinates, multiplication by `g_i = q T_i` has
an off-diagonal entry `q`, a descent diagonal entry `q² - 1`, and all other entries zero.
We define these matrices for any Coxeter system, without using a parameter-dependent
quotient as their carrier. Both left and right matrices are symmetric, commute with the
opposite action, and satisfy the quadratic relation. At `q = √Q` their entries depend
continuously on `Q`, including at `Q = 1`. This fixed-carrier realization permits continuous
finite-dimensional spectral projection and rank arguments.

The general relations reuse the regular operators from
`TauCeti.GroupTheory.Coxeter.HeckeOperator`. The type-A comparison with multiplication uses
the PBW basis; its orthonormality for the positive regular form is established in
`TauCeti.Algebra.TypeAHeckeAlgebra.RegularForm`.

## References

* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

open Matrix

namespace CoxeterSystem

open TauCeti TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {B W : Type*} [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

open Classical in
/-- Left regular multiplication by a rescaled Hecke generator, in orthonormal PBW
coordinates. The formula makes sense even when the scalar parameter is not a unit. -/
noncomputable def heckeLeftMatrix (s : R) (i : B) : Matrix W W R :=
  fun v w ↦ (if v = cs.simple i * w then s else 0) +
    if v = w ∧ cs.IsLeftDescent w i then s ^ 2 - 1 else 0

open Classical in
/-- Right regular multiplication by a rescaled Hecke generator, in orthonormal PBW
coordinates. The formula makes sense even when the scalar parameter is not a unit. -/
noncomputable def heckeRightMatrix (s : R) (i : B) : Matrix W W R :=
  fun v w ↦ (if v = w * cs.simple i then s else 0) +
    if v = w ∧ cs.IsRightDescent w i then s ^ 2 - 1 else 0

open Classical in
/-- The entries of the left regular Hecke matrix. -/
@[simp]
theorem heckeLeftMatrix_apply (s : R) (i : B) (v w : W) :
    heckeLeftMatrix cs s i v w = (if v = cs.simple i * w then s else 0) +
      if v = w ∧ cs.IsLeftDescent w i then s ^ 2 - 1 else 0 := (rfl)

open Classical in
/-- The entries of the right regular Hecke matrix. -/
@[simp]
theorem heckeRightMatrix_apply (s : R) (i : B) (v w : W) :
    heckeRightMatrix cs s i v w = (if v = w * cs.simple i then s else 0) +
      if v = w ∧ cs.IsRightDescent w i then s ^ 2 - 1 else 0 := (rfl)

/-- The left regular Hecke matrix is symmetric over any commutative coefficient ring. -/
@[simp]
theorem transpose_heckeLeftMatrix (s : R) (i : B) :
    (heckeLeftMatrix cs s i)ᵀ = heckeLeftMatrix cs s i := by
  classical
  ext v w
  have h : w = cs.simple i * v ↔ v = cs.simple i * w := by
    constructor <;> rintro rfl <;> simp
  simp only [Matrix.transpose_apply, heckeLeftMatrix_apply, h]
  by_cases hvw : v = w
  · subst w; rfl
  · simp [hvw, Ne.symm hvw]

/-- The right regular Hecke matrix is symmetric over any commutative coefficient ring. -/
@[simp]
theorem transpose_heckeRightMatrix (s : R) (i : B) :
    (heckeRightMatrix cs s i)ᵀ = heckeRightMatrix cs s i := by
  classical
  ext v w
  have h : w = v * cs.simple i ↔ v = w * cs.simple i := by
    constructor <;> rintro rfl <;> simp
  simp only [Matrix.transpose_apply, heckeRightMatrix_apply, h]
  by_cases hvw : v = w
  · subst w; rfl
  · simp [hvw, Ne.symm hvw]

/-- Coefficient homomorphisms preserve the left regular Hecke matrix. -/
theorem map_heckeLeftMatrix {S : Type*} [CommRing S] (f : R →+* S)
    (s : R) (i : B) :
    (heckeLeftMatrix cs s i).map f = heckeLeftMatrix cs (f s) i := by
  classical
  ext v w
  simp [heckeLeftMatrix, apply_ite f]

/-- Coefficient homomorphisms preserve the right regular Hecke matrix. -/
theorem map_heckeRightMatrix {S : Type*} [CommRing S] (f : R →+* S)
    (s : R) (i : B) :
    (heckeRightMatrix cs s i).map f = heckeRightMatrix cs (f s) i := by
  classical
  ext v w
  simp [heckeRightMatrix, apply_ite f]

section Operators

variable [Fintype W] (q : Rˣ)

/-- At a unit parameter the left matrix represents the rescaled regular Hecke operator. -/
theorem heckeLeftMatrix_eq_toMatrix_heckeLeftMul [DecidableEq W] (i : B) :
    heckeLeftMatrix cs (q : R) i =
      LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
        ((q : R) • cs.heckeLeftMul ((q : R) - ↑q⁻¹) i) := by
  classical
  ext v w
  by_cases h : cs.IsLeftDescent w i <;> by_cases hvw : v = w <;>
    simp [LinearMap.toMatrix_apply, heckeLeftMatrix, h, hvw, Finsupp.single_apply,
      eq_comm, mul_sub, sq, add_comm]

/-- At a unit parameter the right matrix represents the rescaled regular Hecke operator. -/
theorem heckeRightMatrix_eq_toMatrix_heckeRightMul [DecidableEq W] (i : B) :
    heckeRightMatrix cs (q : R) i =
      LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
        ((q : R) • cs.heckeRightMul ((q : R) - ↑q⁻¹) i) := by
  classical
  ext v w
  by_cases h : cs.IsRightDescent w i <;> by_cases hvw : v = w <;>
    simp [LinearMap.toMatrix_apply, heckeRightMatrix, h, hvw, Finsupp.single_apply,
      eq_comm, mul_sub, sq, add_comm]

end Operators

section Relations

-- Embed polynomial entries into Laurent polynomials, where the indeterminate is a unit.
-- Injectivity gives the identities over R[X], and evaluation gives every scalar parameter.
variable [Fintype W] (s : R)

/-- Left and right regular Hecke matrices commute, including at nonunit parameters. -/
theorem commute_heckeLeftMatrix_heckeRightMatrix (i j : B) :
    Commute (heckeLeftMatrix cs s i) (heckeRightMatrix cs s j) := by
  classical
  let L := heckeLeftMatrix cs (Polynomial.X : Polynomial R) i
  let N := heckeRightMatrix cs (Polynomial.X : Polynomial R) j
  have hx : (Polynomial.evalRingHom s) Polynomial.X = s := Polynomial.eval_X
  suffices h : L * N = N * L by
    simpa only [L, N, Matrix.map_mul, map_heckeLeftMatrix, map_heckeRightMatrix,
      hx, commute_iff_eq] using
      congrArg (fun A ↦ A.map (Polynomial.evalRingHom s)) h
  apply Matrix.map_injective Polynomial.toLaurent_injective
  obtain ⟨q, hq⟩ := LaurentPolynomial.isUnit_T (R := R) 1
  simp only [L, N, Matrix.map_mul, map_heckeLeftMatrix, map_heckeRightMatrix,
    Polynomial.toLaurent_X, ← hq, heckeLeftMatrix_eq_toMatrix_heckeLeftMul,
    heckeRightMatrix_eq_toMatrix_heckeRightMul]
  exact (((cs.commute_heckeLeftMul_heckeRightMul _ i j).smul_left
    (q : LaurentPolynomial R)).smul_right (q : LaurentPolynomial R)).map
      (LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne) |>.eq

open Classical in
/-- The rescaled left regular Hecke matrix satisfies `(g_i + 1)(g_i - s²) = 0`
even when `s` is not a unit. -/
theorem heckeLeftMatrix_mul_self [DecidableEq W] (i : B) :
    heckeLeftMatrix cs s i * heckeLeftMatrix cs s i =
      (s ^ 2 - 1) • heckeLeftMatrix cs s i + s ^ 2 • 1 := by
  classical
  let L := heckeLeftMatrix cs (Polynomial.X : Polynomial R) i
  have hx : (Polynomial.evalRingHom s) Polynomial.X = s := Polynomial.eval_X
  suffices h : L * L = ((Polynomial.X : Polynomial R) ^ 2 - 1) • L +
      (Polynomial.X : Polynomial R) ^ 2 • 1 by
    simpa only [L, Matrix.map_mul, Matrix.map_add _ (map_add _),
      Matrix.map_smul' _ _ _ (map_mul _), map_sub, map_pow, map_one,
      Matrix.map_one _ (map_zero _) (map_one _), map_heckeLeftMatrix, hx] using
      congrArg (fun A ↦ A.map (Polynomial.evalRingHom s)) h
  apply Matrix.map_injective Polynomial.toLaurent_injective
  obtain ⟨q, hq⟩ := LaurentPolynomial.isUnit_T (R := R) 1
  simp only [L, Matrix.map_mul, Matrix.map_add _ (map_add _),
    Matrix.map_smul' _ _ _ (map_mul _), map_sub, map_pow, map_one,
    map_heckeLeftMatrix, Polynomial.toLaurent_X, ← hq,
    Matrix.map_one _ (map_zero _) (map_one _), heckeLeftMatrix_eq_toMatrix_heckeLeftMul,
    ← LinearMap.toMatrix_mul, ← map_smul]
  simp [cs.heckeLeftMul_mul_self, smul_add, smul_smul, mul_sub, sub_mul, sq,
    mul_assoc]

open Classical in
/-- The rescaled right regular Hecke matrix satisfies `(g_i + 1)(g_i - s²) = 0`
even when `s` is not a unit. -/
theorem heckeRightMatrix_mul_self [DecidableEq W] (i : B) :
    heckeRightMatrix cs s i * heckeRightMatrix cs s i =
      (s ^ 2 - 1) • heckeRightMatrix cs s i + s ^ 2 • 1 := by
  classical
  let N := heckeRightMatrix cs (Polynomial.X : Polynomial R) i
  have hx : (Polynomial.evalRingHom s) Polynomial.X = s := Polynomial.eval_X
  suffices h : N * N = ((Polynomial.X : Polynomial R) ^ 2 - 1) • N +
      (Polynomial.X : Polynomial R) ^ 2 • 1 by
    simpa only [N, Matrix.map_mul, Matrix.map_add _ (map_add _),
      Matrix.map_smul' _ _ _ (map_mul _), map_sub, map_pow, map_one,
      Matrix.map_one _ (map_zero _) (map_one _), map_heckeRightMatrix, hx] using
      congrArg (fun A ↦ A.map (Polynomial.evalRingHom s)) h
  apply Matrix.map_injective Polynomial.toLaurent_injective
  obtain ⟨q, hq⟩ := LaurentPolynomial.isUnit_T (R := R) 1
  simp only [N, Matrix.map_mul, Matrix.map_add _ (map_add _),
    Matrix.map_smul' _ _ _ (map_mul _), map_sub, map_pow, map_one,
    map_heckeRightMatrix, Polynomial.toLaurent_X, ← hq,
    Matrix.map_one _ (map_zero _) (map_one _), heckeRightMatrix_eq_toMatrix_heckeRightMul,
    ← LinearMap.toMatrix_mul, ← map_smul]
  have hquad : cs.heckeRightMul ((q : LaurentPolynomial R) - ↑q⁻¹) i *
      cs.heckeRightMul ((q : LaurentPolynomial R) - ↑q⁻¹) i =
      ((q : LaurentPolynomial R) - ↑q⁻¹) •
        cs.heckeRightMul ((q : LaurentPolynomial R) - ↑q⁻¹) i + 1 := by
    refine Finsupp.lhom_ext fun w r ↦ ?_
    simp only [mul_apply_eq_comp, LinearMap.add_apply, LinearMap.smul_apply,
      one_apply_eq_self]
    by_cases h : cs.IsRightDescent w i
    · have h' := cs.isRightDescent_iff_not_isRightDescent_mul.mp h
      simp [h, h', map_add]
    · have h' : cs.IsRightDescent (w * cs.simple i) i := by
        rwa [cs.isRightDescent_iff_not_isRightDescent_mul,
          cs.simple_mul_simple_cancel_right]
      simp [h, h']
  simp [hquad, smul_add, smul_smul, mul_sub, sub_mul, sq, mul_assoc]

end Relations

section Multiplication

variable {n : ℕ} (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
variable [Fintype W] (q : Rˣ)

open Classical in
/-- The explicit left matrix is the matrix of multiplication by `g_i = q T_i` in the
PBW basis. For a star-fixed real or complex parameter this basis is orthonormal for the
regular trace form. -/
theorem heckeLeftMatrix_eq_leftMulMatrix [DecidableEq W] (i : Fin (n - 1)) :
    heckeLeftMatrix cs (q : R) i =
      Algebra.leftMulMatrix (basisTw q cs) ((q : R) • T q i) := by
  ext v w
  rw [Algebra.leftMulMatrix_eq_repr_mul, coe_basisTw, smul_mul_assoc]
  by_cases h : cs.IsLeftDescent w i
  · rw [T_mul_Tw_of_isLeftDescent cs h]
    by_cases hvw : v = w <;>
      simp [heckeLeftMatrix_apply, h, ← coe_basisTw, Finsupp.single_apply, eq_comm,
        smul_add, smul_smul, mul_sub, sq, add_comm, hvw]
  · rw [T_mul_Tw_of_not_isLeftDescent cs h]
    simp [heckeLeftMatrix_apply, h, ← coe_basisTw, Finsupp.single_apply, eq_comm]

open Classical in
/-- The explicit right matrix is the matrix of right multiplication by `g_i = q T_i`
in the PBW basis. -/
theorem heckeRightMatrix_eq_toMatrix [DecidableEq W] (i : Fin (n - 1)) :
    heckeRightMatrix cs (q : R) i = LinearMap.toMatrix (basisTw q cs) (basisTw q cs)
      (LinearMap.mulRight R ((q : R) • T q i)) := by
  ext v w
  rw [LinearMap.toMatrix_apply, coe_basisTw, LinearMap.mulRight_apply, mul_smul_comm]
  by_cases h : cs.IsRightDescent w i
  · rw [Tw_mul_T_of_isRightDescent cs h]
    by_cases hvw : v = w <;>
      simp [heckeRightMatrix_apply, h, ← coe_basisTw, Finsupp.single_apply, eq_comm,
        smul_add, smul_smul, mul_sub, sq, add_comm, hvw]
  · rw [Tw_mul_T_of_not_isRightDescent cs h]
    simp [heckeRightMatrix_apply, h, ← coe_basisTw, Finsupp.single_apply, eq_comm]

/-- The fixed-coordinate left action agrees with multiplication on every vector. -/
theorem heckeLeftMatrix_mulVec_repr (i : Fin (n - 1))
    (x : TypeAHeckeAlgebra R q n) :
    heckeLeftMatrix cs (q : R) i *ᵥ (basisTw q cs).repr x =
      (basisTw q cs).repr (((q : R) • T q i) * x) := by
  classical
  rw [heckeLeftMatrix_eq_leftMulMatrix, Algebra.leftMulMatrix_mulVec_repr]

/-- The fixed-coordinate right action agrees with multiplication on every vector. -/
theorem heckeRightMatrix_mulVec_repr (i : Fin (n - 1))
    (x : TypeAHeckeAlgebra R q n) :
    heckeRightMatrix cs (q : R) i *ᵥ (basisTw q cs).repr x =
      (basisTw q cs).repr (x * ((q : R) • T q i)) := by
  classical
  rw [heckeRightMatrix_eq_toMatrix, LinearMap.toMatrix_mulVec_repr,
    LinearMap.mulRight_apply]

end Multiplication

section TypeARelations

variable {n : ℕ} (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
variable [Fintype W] (s : R)

/-- The left regular Hecke matrices satisfy the adjacent braid relation. -/
theorem heckeLeftMatrix_braid {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    heckeLeftMatrix cs s i * heckeLeftMatrix cs s j * heckeLeftMatrix cs s i =
      heckeLeftMatrix cs s j * heckeLeftMatrix cs s i * heckeLeftMatrix cs s j := by
  classical
  let L := heckeLeftMatrix cs (Polynomial.X : Polynomial R) i
  let N := heckeLeftMatrix cs (Polynomial.X : Polynomial R) j
  have hx : (Polynomial.evalRingHom s) Polynomial.X = s := Polynomial.eval_X
  suffices h : L * N * L = N * L * N by
    simpa only [L, N, Matrix.map_mul, map_heckeLeftMatrix, hx] using
      congrArg (fun A ↦ A.map (Polynomial.evalRingHom s)) h
  apply Matrix.map_injective Polynomial.toLaurent_injective
  obtain ⟨q, hq⟩ := LaurentPolynomial.isUnit_T (R := R) 1
  simp only [L, N, Matrix.map_mul, map_heckeLeftMatrix, Polynomial.toLaurent_X, ← hq]
  simp only [heckeLeftMatrix_eq_leftMulMatrix, ← map_mul, smul_mul_smul, T_braid h]

/-- The right regular Hecke matrices satisfy the adjacent braid relation. -/
theorem heckeRightMatrix_braid {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    heckeRightMatrix cs s i * heckeRightMatrix cs s j * heckeRightMatrix cs s i =
      heckeRightMatrix cs s j * heckeRightMatrix cs s i * heckeRightMatrix cs s j := by
  classical
  let L := heckeRightMatrix cs (Polynomial.X : Polynomial R) i
  let N := heckeRightMatrix cs (Polynomial.X : Polynomial R) j
  have hx : (Polynomial.evalRingHom s) Polynomial.X = s := Polynomial.eval_X
  suffices h : L * N * L = N * L * N by
    simpa only [L, N, Matrix.map_mul, map_heckeRightMatrix, hx] using
      congrArg (fun A ↦ A.map (Polynomial.evalRingHom s)) h
  apply Matrix.map_injective Polynomial.toLaurent_injective
  obtain ⟨q, hq⟩ := LaurentPolynomial.isUnit_T (R := R) 1
  simp only [L, N, Matrix.map_mul, map_heckeRightMatrix, Polynomial.toLaurent_X, ← hq]
  simp only [heckeRightMatrix_eq_toMatrix, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  simp only [mul_apply_eq_comp, LinearMap.mulRight_apply]
  have hb : ((q : LaurentPolynomial R) • T q i) * ((q : LaurentPolynomial R) • T q j) *
      ((q : LaurentPolynomial R) • T q i) =
      ((q : LaurentPolynomial R) • T q j) * ((q : LaurentPolynomial R) • T q i) *
        ((q : LaurentPolynomial R) • T q j) := by
    simp only [smul_mul_smul, T_braid h]
  simpa only [mul_assoc] using congrArg (fun a ↦ x * a) hb

/-- Distant left regular Hecke matrices commute. -/
theorem commute_heckeLeftMatrix {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (heckeLeftMatrix cs s i) (heckeLeftMatrix cs s j) := by
  classical
  let L := heckeLeftMatrix cs (Polynomial.X : Polynomial R) i
  let N := heckeLeftMatrix cs (Polynomial.X : Polynomial R) j
  have hx : (Polynomial.evalRingHom s) Polynomial.X = s := Polynomial.eval_X
  suffices h : L * N = N * L by
    simpa only [L, N, Matrix.map_mul, map_heckeLeftMatrix, hx, commute_iff_eq] using
      congrArg (fun A ↦ A.map (Polynomial.evalRingHom s)) h
  apply Matrix.map_injective Polynomial.toLaurent_injective
  obtain ⟨q, hq⟩ := LaurentPolynomial.isUnit_T (R := R) 1
  simp only [L, N, Matrix.map_mul, map_heckeLeftMatrix, Polynomial.toLaurent_X, ← hq]
  rw [← commute_iff_eq, heckeLeftMatrix_eq_leftMulMatrix, heckeLeftMatrix_eq_leftMulMatrix]
  exact (((commute_T h).smul_left (q : LaurentPolynomial R)).smul_right
    (q : LaurentPolynomial R)).map _

/-- Distant right regular Hecke matrices commute. -/
theorem commute_heckeRightMatrix {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (heckeRightMatrix cs s i) (heckeRightMatrix cs s j) := by
  classical
  let L := heckeRightMatrix cs (Polynomial.X : Polynomial R) i
  let N := heckeRightMatrix cs (Polynomial.X : Polynomial R) j
  have hx : (Polynomial.evalRingHom s) Polynomial.X = s := Polynomial.eval_X
  suffices h : L * N = N * L by
    simpa only [L, N, Matrix.map_mul, map_heckeRightMatrix, hx, commute_iff_eq] using
      congrArg (fun A ↦ A.map (Polynomial.evalRingHom s)) h
  apply Matrix.map_injective Polynomial.toLaurent_injective
  obtain ⟨q, hq⟩ := LaurentPolynomial.isUnit_T (R := R) 1
  simp only [L, N, Matrix.map_mul, map_heckeRightMatrix, Polynomial.toLaurent_X, ← hq]
  rw [heckeRightMatrix_eq_toMatrix, heckeRightMatrix_eq_toMatrix,
    ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  simp [smul_smul, mul_assoc, (commute_T (q := q) h).eq]

end TypeARelations

section Continuity

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- On the fixed PBW coordinate carrier, the left regular Hecke matrices vary
continuously with the square-root parameter, without any invertibility restriction. -/
@[fun_prop]
theorem continuous_heckeLeftMatrix (i : B) :
    Continuous (fun s : R ↦ heckeLeftMatrix cs s i) := by
  classical
  refine continuous_pi fun v ↦ continuous_pi fun w ↦ ?_
  simp only [heckeLeftMatrix_apply]
  exact (continuous_if_const _ (fun _ ↦ continuous_id) (fun _ ↦ continuous_const)).add
    (continuous_if_const _ (fun _ ↦ (continuous_id.pow 2).sub continuous_const)
      (fun _ ↦ continuous_const))

/-- On the fixed PBW coordinate carrier, the right regular Hecke matrices vary
continuously with the square-root parameter, without any invertibility restriction. -/
@[fun_prop]
theorem continuous_heckeRightMatrix (i : B) :
    Continuous (fun s : R ↦ heckeRightMatrix cs s i) := by
  classical
  refine continuous_pi fun v ↦ continuous_pi fun w ↦ ?_
  simp only [heckeRightMatrix_apply]
  exact (continuous_if_const _ (fun _ ↦ continuous_id) (fun _ ↦ continuous_const)).add
    (continuous_if_const _ (fun _ ↦ (continuous_id.pow 2).sub continuous_const)
      (fun _ ↦ continuous_const))

/-- Left multiplication by `g_i` in the orthonormal regular carrier is continuous in
`Q > 0`, and through `Q = 1`, when `q = √Q`. The entry formula extends continuously to
all real `Q`; its interpretation as a Hecke module requires `Q > 0`. -/
@[fun_prop]
theorem continuous_heckeLeftMatrix_sqrt (i : B) :
    Continuous (fun Q : ℝ ↦ heckeLeftMatrix cs (Real.sqrt Q) i) :=
  (continuous_heckeLeftMatrix cs i).comp Real.continuous_sqrt

/-- Right multiplication by `g_i` in the orthonormal regular carrier is continuous in
`Q > 0`, and through `Q = 1`, when `q = √Q`. -/
@[fun_prop]
theorem continuous_heckeRightMatrix_sqrt (i : B) :
    Continuous (fun Q : ℝ ↦ heckeRightMatrix cs (Real.sqrt Q) i) :=
  (continuous_heckeRightMatrix cs i).comp Real.continuous_sqrt

end Continuity

end CoxeterSystem

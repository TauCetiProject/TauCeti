/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Hecke.Operator
public import TauCeti.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.Matrix

/-!
# Regular Hecke matrices on a fixed carrier

For any Coxeter system, we define the matrices of the rescaled regular Hecke generators
without using a parameter-dependent quotient as their carrier. Their off-diagonal entries
are `s`, their descent diagonal entries are `s² - 1`, and all other entries are zero.
Both matrices are symmetric, commute with the opposite action, and satisfy the quadratic
and braid relations, even at nonunit parameters. The relations follow from the regular operators in
`TauCeti.GroupTheory.Coxeter.Hecke.Operator` by polynomial specialization.

At `s = √Q` their entries depend continuously on `Q`, including at `Q = 1`. For positive
real parameters these are the regular Hecke matrices in orthonormal PBW coordinates.
The type-A multiplication comparisons are in
`TauCeti.Algebra.TypeAHeckeAlgebra.Regular.Matrix`; the orthonormality statement is in
`TauCeti.Algebra.TypeAHeckeAlgebra.Regular.Form`. This fixed-carrier realization permits
continuous finite-dimensional spectral projection and rank arguments.

## References

* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

open Matrix

namespace CoxeterSystem

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

/-- Inverting both carrier indices turns the left regular Hecke matrix into the right one. -/
theorem heckeRightMatrix_eq_submatrix (s : R) (i : B) :
    heckeRightMatrix cs s i = (heckeLeftMatrix cs s i).submatrix (·⁻¹) (·⁻¹) := by
  classical
  ext v w
  have h : v⁻¹ = cs.simple i * w⁻¹ ↔ v = w * cs.simple i := by
    rw [inv_eq_iff_eq_inv, _root_.mul_inv_rev, inv_inv, cs.inv_simple]
  simp [Matrix.submatrix_apply, h, cs.isLeftDescent_inv_iff]

section Relations

variable [Fintype W] (s : R)

/-- Left and right regular Hecke matrices commute, including at nonunit parameters. -/
theorem commute_heckeLeftMatrix_heckeRightMatrix (i j : B) :
    Commute (heckeLeftMatrix cs s i) (heckeRightMatrix cs s j) := by
  classical
  rw [commute_iff_eq]
  refine Matrix.identity_of_units
    (fun _ _ t ↦ heckeLeftMatrix cs t i * heckeRightMatrix cs t j)
    (fun _ _ t ↦ heckeRightMatrix cs t j * heckeLeftMatrix cs t i)
    (by intros; simp [Matrix.map_mul, map_heckeLeftMatrix, map_heckeRightMatrix])
    (by intros; simp [Matrix.map_mul, map_heckeLeftMatrix, map_heckeRightMatrix]) ?_ s
  intro q
  rw [heckeLeftMatrix_eq_toMatrix_heckeLeftMul, heckeRightMatrix_eq_toMatrix_heckeRightMul]
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
  refine Matrix.identity_of_units
    (fun _ _ t ↦ heckeLeftMatrix cs t i * heckeLeftMatrix cs t i)
    (fun _ _ t ↦ (t ^ 2 - 1) • heckeLeftMatrix cs t i + t ^ 2 • 1)
    (by intros; simp [Matrix.map_mul, map_heckeLeftMatrix])
    (by intros; simp [Matrix.map_add, Matrix.map_smul' _ _ _ (map_mul _),
      Matrix.map_one _ (map_zero _) (map_one _), map_heckeLeftMatrix]) ?_ s
  intro q
  simp only [heckeLeftMatrix_eq_toMatrix_heckeLeftMul, ← LinearMap.toMatrix_mul,
    ← map_smul]
  simp [cs.heckeLeftMul_mul_self, smul_add, smul_smul, mul_sub, sub_mul, sq, mul_assoc]

open Classical in
/-- The rescaled right regular Hecke matrix satisfies `(g_i + 1)(g_i - s²) = 0`
even when `s` is not a unit. -/
theorem heckeRightMatrix_mul_self [DecidableEq W] (i : B) :
    heckeRightMatrix cs s i * heckeRightMatrix cs s i =
      (s ^ 2 - 1) • heckeRightMatrix cs s i + s ^ 2 • 1 := by
  classical
  refine Matrix.identity_of_units
    (fun _ _ t ↦ heckeRightMatrix cs t i * heckeRightMatrix cs t i)
    (fun _ _ t ↦ (t ^ 2 - 1) • heckeRightMatrix cs t i + t ^ 2 • 1)
    (by intros; simp [Matrix.map_mul, map_heckeRightMatrix])
    (by intros; simp [Matrix.map_add, Matrix.map_smul' _ _ _ (map_mul _),
      Matrix.map_one _ (map_zero _) (map_one _), map_heckeRightMatrix]) ?_ s
  intro q
  simp only [heckeRightMatrix_eq_toMatrix_heckeRightMul, ← LinearMap.toMatrix_mul,
    ← map_smul]
  simp [cs.heckeRightMul_mul_self, smul_add, smul_smul, mul_sub, sub_mul, sq, mul_assoc]

open Classical in
/-- Products of left regular Hecke matrices satisfy every Coxeter braid relation,
including at nonunit parameters. -/
theorem prod_map_heckeLeftMatrix_braidWord (i j : B) :
    ((braidWord M i j).map (heckeLeftMatrix cs s)).prod =
      ((braidWord M j i).map (heckeLeftMatrix cs s)).prod := by
  classical
  refine Matrix.identity_of_units
    (fun _ _ t ↦ ((braidWord M i j).map (heckeLeftMatrix cs t)).prod)
    (fun _ _ t ↦ ((braidWord M j i).map (heckeLeftMatrix cs t)).prod)
    (by
      intros
      rw [← RingHom.mapMatrix_apply, map_list_prod]
      simp only [List.map_map, Function.comp_def, RingHom.mapMatrix_apply,
        map_heckeLeftMatrix])
    (by
      intros
      rw [← RingHom.mapMatrix_apply, map_list_prod]
      simp only [List.map_map, Function.comp_def, RingHom.mapMatrix_apply,
        map_heckeLeftMatrix]) ?_ s
  intro q
  have hp (ω : List B) :
      (ω.map (heckeLeftMatrix cs (q : LaurentPolynomial R))).prod =
        LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
          ((q : LaurentPolynomial R) ^ ω.length •
            (ω.map (cs.heckeLeftMul ((q : LaurentPolynomial R) - ↑q⁻¹))).prod) := by
    induction ω with
    | nil => simp
    | cons k ω ih =>
      simp [ih, heckeLeftMatrix_eq_toMatrix_heckeLeftMul, ← LinearMap.toMatrix_mul,
        smul_smul, mul_comm, pow_succ']
  rw [hp, hp, length_alternatingWord, length_alternatingWord, M.symmetric i j,
    cs.prod_map_heckeLeftMul_braidWord]

open Classical in
/-- Products of right regular Hecke matrices satisfy every Coxeter braid relation,
including at nonunit parameters. -/
theorem prod_map_heckeRightMatrix_braidWord (i j : B) :
    ((braidWord M i j).map (heckeRightMatrix cs s)).prod =
      ((braidWord M j i).map (heckeRightMatrix cs s)).prod := by
  classical
  simpa only [map_list_prod, List.map_map, Matrix.coe_reindexAlgEquiv,
    Function.comp_def, Matrix.reindex_apply, Equiv.inv_symm, Equiv.inv_apply,
    ← heckeRightMatrix_eq_submatrix] using
    congrArg (Matrix.reindexAlgEquiv R R (Equiv.inv W))
      (prod_map_heckeLeftMatrix_braidWord cs s i j)

end Relations

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

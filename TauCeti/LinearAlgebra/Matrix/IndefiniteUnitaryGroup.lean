/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The indefinite unitary group `U(p, q)`

Let `R` be a commutative ring with an involution `star`. For a square matrix `A` over `R`, the
**unitary group of `A`**, `Matrix.unitaryGroupOf A`, is the subgroup of `GL n R` of the
matrices `g` with `star g * A * g = A`: the invertible matrices preserving the sesquilinear form
`⟨z, w⟩ = star z ⬝ᵥ A *ᵥ w` of Gram matrix `A`, conjugate-linear in the first slot.

For `J = LieAlgebra.Orthogonal.indefiniteDiagonal p q R = diag(1, …, 1, -1, …, -1)`, the Gram
matrix of the Hermitian form
`⟨z, w⟩ = star z ⬝ᵥ J *ᵥ w = Σ_{i ∈ p} star zᵢ wᵢ - Σ_{j ∈ q} star zⱼ wⱼ` on `p ⊕ q → R`, this is
the **indefinite unitary group** `TauCeti.Matrix.indefiniteUnitaryGroup p q R`. Over `ℂ` this is
`U(p, q)`, and `U(1, n)`, for `p = Fin 1` and `q = Fin n`, is the group acting on complex
hyperbolic `n`-space. Over `ℝ`, where the star is trivial, it is the indefinite orthogonal group
`O(p, q)`.

The basic structure of these groups is recorded here.

* Its determinant-one elements form the special isometry group
  `Matrix.specialIsometryGroup A (starRingEnd R)` of the same form, whose defining equation is
  written `(g.map σ)ᵀ * A * g = A`.
* Membership in `unitaryGroupOf A` is equivalent to the preservation `⟨g z, g w⟩ = ⟨z, w⟩` of the
  form and, for invertible `A`, to `g * A⁻¹ * star g = A⁻¹`, that is to `star g` lying in
  `unitaryGroupOf A⁻¹`. For `J`, which is its own inverse, `U(p, q)` is stable under `star`.
  (Over `ℝ` or `ℂ` and for Hermitian `A`, membership is also equivalent, by polarization, to the
  preservation of the values `⟨z, z⟩` alone; that statement, with the topological facts, is in
  `TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup`.)
* For invertible `A`, every matrix preserving the form is invertible, with inverse
  `A⁻¹ * star g * A` (`Matrix.unitaryGroupOf.ofMatrix`), and its determinant is a unitary
  scalar. For `U(p, q)` the inverse is `J * star g * J`.
* The block-diagonal matrices `diag(A, D)` with `A ∈ U(p)` and `D ∈ U(q)` form a subgroup of
  `U(p, q)` isomorphic to `U(p) × U(q)` (`TauCeti.Matrix.indefiniteUnitaryGroup.fromBlocksHom`). It
  is the stabilizer of the coordinate subspace `p → R` spanned by the positive basis vectors: an
  element of `U(p, q)` preserves that subspace, that is has vanishing lower-left block, exactly
  when it is block diagonal. For `U(1, n)` this is the stabilizer `U(1) × U(n)` of the positive
  line spanned by the first basis vector.
* Over a field of characteristic zero, the centre of `U(p, q)` is the group of unit scalars
  `λ • 1` with `star λ * λ = 1`. The proof uses the reflections
  `1 - (2 / ⟨v, v⟩) • vecMulVec v (star v ᵥ* A)` in the non-isotropic vectors `v`, which lie in
  `unitaryGroupOf A` for every Hermitian invertible `A` (`Matrix.unitaryGroupOf.reflection`): a
  central element commutes with the rank-one matrices `vecMulVec v (star v ᵥ* A)`, and for `A = J`
  testing this on the vectors `eₖ` and `eᵢ + 2 eₖ` forces it to be scalar.

## Main definitions

* `Matrix.unitaryGroupOf A`: the group of invertible matrices preserving the sesquilinear
  form of Gram matrix `A`.
* `Matrix.unitaryGroupOf.ofMatrix`: the element of `unitaryGroupOf A` defined by a matrix
  preserving the form, for invertible `A`.
* `Matrix.unitaryGroupOf.scalarHom`: the embedding `λ ↦ λ • 1` of the unitary scalars.
* `Matrix.unitaryGroupOf.reflection`: the reflection in a non-isotropic vector, for a Hermitian
  invertible Gram matrix `A`.
* `TauCeti.Matrix.indefiniteUnitaryGroup p q R`: the group `U(p, q)` of invertible matrices
  preserving the Hermitian form of Gram matrix `diag(1, …, 1, -1, …, -1)`.
* `TauCeti.Matrix.indefiniteUnitaryGroup.fromBlocksHom`: the block-diagonal embedding of
  `U(p) × U(q)`.

## Main results

* `Matrix.mem_unitaryGroupOf_iff_forall_dotProduct`: membership as preservation of the
  form.
* `Matrix.specialIsometryGroup_starRingEnd_eq_comap_unitaryGroupOf`: the determinant-one elements
  of `unitaryGroupOf A` are the special isometry group of the form.
* `Matrix.mem_unitaryGroupOf_iff'`: membership as the equation `g * A⁻¹ * star g = A⁻¹`.
* `Matrix.val_inv_of_mem_unitaryGroupOf`: the inverse of `g` is `A⁻¹ * star g * A`.
* `Matrix.det_mem_unitary_of_mem_unitaryGroupOf`: `star (det g) * det g = 1`.
* `Matrix.unitaryGroupOf.scalarHom_injective`: the embedding of the unitary scalars is
  injective.
* `TauCeti.Matrix.mem_indefiniteUnitaryGroup_iff'`: membership in `U(p, q)` as the equation
  `g * J * star g = J`.
* `TauCeti.Matrix.val_inv_of_mem_indefiniteUnitaryGroup`: the inverse of `g ∈ U(p, q)` is
  `J * star g * J`.
* `TauCeti.Matrix.star_diagonal_mul_indefiniteDiagonal_mul_diagonal_eq_iff`: a diagonal matrix
  preserves the form of `J` exactly when its diagonal entries are unitary.
* `TauCeti.Matrix.star_mem_indefiniteUnitaryGroup_iff`: `U(p, q)` is stable under conjugate
  transposition.
* `TauCeti.Matrix.indefiniteUnitaryGroup.mem_range_fromBlocksHom_iff`: the image of
  `U(p) × U(q)` is the subgroup of elements with vanishing lower-left block.
* `TauCeti.Matrix.indefiniteUnitaryGroup.center_eq_range_scalarHom`: over a field of
  characteristic zero, the centre of `U(p, q)` is the group of unit scalars.

## References

* W. M. Goldman, *Complex Hyperbolic Geometry*, Oxford Mathematical Monographs, Oxford University
  Press (1999), Chapter 3.
* G. Baldi and E. Ullmo, *Special subvarieties of non-arithmetic ball quotients and Hodge theory*,
  Ann. of Math. 197 (2023), Section 2, for the matrix description of `U(1, n)`.
-/

public section

open LieAlgebra.Orthogonal Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R] [StarRing R]

/-- The **unitary group of a sesquilinear form**: the invertible matrices `g` with
`star g * A * g = A`, that is the invertible matrices preserving the form
`⟨z, w⟩ = star z ⬝ᵥ A *ᵥ w` of Gram matrix `A`. For `A = 1` this is the unitary group, and for
`A = diag(1, …, 1, -1, …, -1)` it is the indefinite unitary group
`TauCeti.Matrix.indefiniteUnitaryGroup`. -/
def unitaryGroupOf (A : Matrix n n R) : Subgroup (GL n R) where
  carrier := {g | star (g : Matrix n n R) * A * g = A}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, star_mul] at *
    calc _ = star (b : Matrix n n R) * (star (a : Matrix n n R) * A * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc _ = star (↑a⁻¹ : Matrix n n R) * (star (a : Matrix n n R) * A * a) * ↑a⁻¹ := by
          rw [ha]
      _ = star ((a : Matrix n n R) * ↑a⁻¹) * A * ((a : Matrix n n R) * ↑a⁻¹) := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = _ := by simp

variable {A : Matrix n n R}

/-- Membership in `unitaryGroupOf A` is the equation `star g * A * g = A`. -/
theorem mem_unitaryGroupOf_iff {g : GL n R} :
    g ∈ unitaryGroupOf A ↔ star (g : Matrix n n R) * A * g = A :=
  Iff.rfl

/-- Two elements of `unitaryGroupOf A` are equal when their matrices are. -/
@[ext]
theorem unitaryGroupOf.ext {g h : unitaryGroupOf A}
    (H : ((g : GL n R) : Matrix n n R) = ((h : GL n R) : Matrix n n R)) : g = h :=
  Subtype.ext <| Units.ext H

/-- **`unitaryGroupOf A` is the group of isometries of the form**: `g ∈ unitaryGroupOf A` exactly
when `⟨g x, g y⟩ = ⟨x, y⟩` for all `x` and `y`, where `⟨x, y⟩ = star x ⬝ᵥ A *ᵥ y`. -/
theorem mem_unitaryGroupOf_iff_forall_dotProduct {g : GL n R} :
    g ∈ unitaryGroupOf A ↔ ∀ x y : n → R,
      star ((g : Matrix n n R) *ᵥ x) ⬝ᵥ A *ᵥ (g *ᵥ y) = star x ⬝ᵥ A *ᵥ y := by
  refine ⟨fun h => comp_mulVec_dotProduct_mulVec_mulVec (σ := starRingEnd R) h, fun h => ?_⟩
  simp only [← star_dotProduct_conjTranspose_mul_mul_mulVec, ← star_eq_conjTranspose] at h
  ext i j
  simpa [mulVec_single_one, Pi.star_single] using h (Pi.single i 1) (Pi.single j 1)

/-- The determinant-one elements of `unitaryGroupOf A` form Tau Ceti's special isometry group
`Matrix.specialIsometryGroup A (starRingEnd R)` of the `star`-sesquilinear form: the two defining
equations agree, since `star g = (g.map star)ᵀ`. -/
theorem specialIsometryGroup_starRingEnd_eq_comap_unitaryGroupOf :
    A.specialIsometryGroup (starRingEnd R) =
      (unitaryGroupOf A).comap SpecialLinearGroup.toGL :=
  Subgroup.ext fun g => by
    have h : ((g : Matrix n n R).map (starRingEnd R))ᵀ = star (g : Matrix n n R) := by
      ext; simp [starRingEnd_apply]
    rw [mem_specialIsometryGroup_iff, Subgroup.mem_comap, mem_unitaryGroupOf_iff,
      SpecialLinearGroup.coe_GL_coe_matrix, h]

/-- **The inverse of an element of `unitaryGroupOf A`**, for invertible `A`, is
`A⁻¹ * star g * A`. -/
theorem val_inv_of_mem_unitaryGroupOf (hA : IsUnit A) {g : GL n R} (hg : g ∈ unitaryGroupOf A) :
    (↑g⁻¹ : Matrix n n R) = A⁻¹ * star (g : Matrix n n R) * A :=
  Units.inv_eq_of_mul_eq_one_left <| by
    have h := mem_unitaryGroupOf_iff.mp hg
    simp only [Matrix.mul_assoc] at h ⊢
    rw [h, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA)]

/-- For invertible `A`, membership in `unitaryGroupOf A` is equivalent to the equation
`g * A⁻¹ * star g = A⁻¹`. -/
theorem mem_unitaryGroupOf_iff' (hA : IsUnit A) {g : GL n R} :
    g ∈ unitaryGroupOf A ↔ (g : Matrix n n R) * A⁻¹ * star (g : Matrix n n R) = A⁻¹ := by
  -- Both equations say that `A⁻¹ * star g * A` is an inverse of `g`, on the left and on the right.
  set M : Matrix n n R := (g : Matrix n n R)
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA
  have hA' : IsUnit A⁻¹ := (isUnit_nonsing_inv_iff).mpr hA
  calc g ∈ unitaryGroupOf A ↔ A⁻¹ * (star M * A * M) = A⁻¹ * A := hA'.mul_right_inj.symm
    _ ↔ A⁻¹ * star M * A * M = 1 := by simp only [nonsing_inv_mul _ hd, Matrix.mul_assoc]
    _ ↔ M * (A⁻¹ * star M * A) = 1 := mul_eq_one_comm
    _ ↔ M * A⁻¹ * star M * A = A⁻¹ * A := by simp only [nonsing_inv_mul _ hd, Matrix.mul_assoc]
    _ ↔ _ := hA.mul_left_inj

/-- For invertible `A`, conjugate transposition maps `unitaryGroupOf A` onto
`unitaryGroupOf A⁻¹`. -/
theorem star_mem_unitaryGroupOf_inv_iff (hA : IsUnit A) {g : GL n R} :
    star g ∈ unitaryGroupOf A⁻¹ ↔ g ∈ unitaryGroupOf A := by
  rw [mem_unitaryGroupOf_iff, mem_unitaryGroupOf_iff' hA, Units.coe_star, star_star]

/-- **The determinant of an element of `unitaryGroupOf A` is a unitary scalar**, for invertible
`A`: `star (det g) * det g = 1`. Over `ℂ` this says `|det g| = 1`. -/
theorem det_mem_unitary_of_mem_unitaryGroupOf (hA : IsUnit A) {g : GL n R}
    (hg : g ∈ unitaryGroupOf A) : (g : Matrix n n R).det ∈ unitary R := by
  have h := congrArg det (mem_unitaryGroupOf_iff.mp hg)
  rw [det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, mul_right_comm] at h
  rw [Unitary.mem_iff_star_mul_self]
  exact ((isUnit_iff_isUnit_det A).mp hA).mul_eq_right.mp h

namespace unitaryGroupOf

/-- A matrix preserving the form of an invertible Gram matrix `A` is invertible, with inverse
`A⁻¹ * star M * A`: this is the element of `unitaryGroupOf A` it defines. -/
noncomputable def ofMatrix (hA : IsUnit A) (M : Matrix n n R) (hM : star M * A * M = A) :
    unitaryGroupOf A :=
  have h : A⁻¹ * star M * A * M = 1 := by
    simp only [Matrix.mul_assoc] at hM ⊢
    rw [hM, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA)]
  ⟨⟨M, A⁻¹ * star M * A, mul_eq_one_comm.mp h, h⟩, hM⟩

@[simp]
theorem val_ofMatrix (hA : IsUnit A) (M : Matrix n n R) (hM : star M * A * M = A) :
    ((ofMatrix hA M hM : GL n R) : Matrix n n R) = M :=
  (rfl)

variable (A) in
/-- The embedding `λ ↦ λ • 1` of the unitary scalars in `unitaryGroupOf A`. For the indefinite
unitary group over a field of characteristic zero its image is the centre
(`TauCeti.Matrix.indefiniteUnitaryGroup.center_eq_range_scalarHom`). -/
def scalarHom : unitary R →* unitaryGroupOf A :=
  ((GeneralLinearGroup.scalar n).comp Unitary.toUnits).codRestrict _ fun u => by
    rw [mem_unitaryGroupOf_iff]
    ext i j
    simp [star_eq_conjTranspose, mul_diagonal, diagonal_mul, mul_right_comm,
      Unitary.star_mul_self_of_mem u.property]

@[simp]
theorem val_scalarHom (u : unitary R) :
    ((scalarHom A u : GL n R) : Matrix n n R) = scalar n (u : R) :=
  GeneralLinearGroup.coe_scalar _

/-- The embedding of the unitary scalars in `unitaryGroupOf A` is injective for nonempty `n`. -/
theorem scalarHom_injective [Nonempty n] : Function.Injective (scalarHom A) := fun u v h => by
  rw [unitaryGroupOf.ext_iff, val_scalarHom, val_scalarHom] at h
  exact Subtype.ext (scalar_inj.mp h)

end unitaryGroupOf

end CommRing

section Field

variable {K : Type*} [Field K] [StarRing K] {A : Matrix n n K}

/-- For Hermitian `A`, the reflection matrix `1 - (2 / ⟨v, v⟩) • v (star v ᵥ* A)` preserves the
form. -/
private theorem star_reflectionMatrix_mul_mul (hA : A.IsHermitian) {v : n → K}
    (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) :
    star (1 - (2 / (star v ⬝ᵥ A *ᵥ v)) • vecMulVec v (star v ᵥ* A)) * A *
      (1 - (2 / (star v ⬝ᵥ A *ᵥ v)) • vecMulVec v (star v ᵥ* A)) = A := by
  set c := star v ⬝ᵥ A *ᵥ v
  set S := vecMulVec (A *ᵥ v) (star v ᵥ* A)
  have hstar : star (vecMulVec v (star v ᵥ* A)) = vecMulVec (A *ᵥ v) (star v) := by
    rw [star_eq_conjTranspose, conjTranspose_vecMulVec, star_vecMul, star_star, hA.eq]
  have ha : star (2 / c) = 2 / c := by
    rw [star_div₀, star_ofNat, hA.star_dotProduct_mulVec_comm]
  have hNS : star (vecMulVec v (star v ᵥ* A)) * A = S := by
    rw [hstar, vecMulVec_mul]
  have hSN : A * vecMulVec v (star v ᵥ* A) = S := by
    rw [mul_vecMulVec]
  have hSNN : S * vecMulVec v (star v ᵥ* A) = c • S := by
    rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, vecMulVec_smul]
  rw [star_sub, star_one, star_smul, ha]
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hNS, hSN, hSNN, smul_smul]
  have h2 : 2 / c * (2 / c * c) = 2 / c + 2 / c := by
    field_simp
    ring
  rw [h2, add_smul]
  abel

namespace unitaryGroupOf

/-- **The reflection in a non-isotropic vector**, for a Hermitian invertible Gram matrix `A`. For
`v` with `⟨v, v⟩ ≠ 0`, the element `1 - (2 / ⟨v, v⟩) • v (star v ᵥ* A)` of `unitaryGroupOf A`,
which sends `v` to `-v` (`reflection_mulVec_self`) and fixes the vectors orthogonal to `v` for the
form (`reflection_mulVec_of_dotProduct_eq_zero`). -/
noncomputable def reflection (hA : A.IsHermitian) (hA' : IsUnit A) (v : n → K)
    (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) : unitaryGroupOf A :=
  ofMatrix hA' _ (star_reflectionMatrix_mul_mul hA hv)

@[simp]
theorem val_reflection (hA : A.IsHermitian) (hA' : IsUnit A) (v : n → K)
    (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) :
    ((reflection hA hA' v hv : GL n K) : Matrix n n K) =
      1 - (2 / (star v ⬝ᵥ A *ᵥ v)) • vecMulVec v (star v ᵥ* A) :=
  (rfl)

/-- The reflection in `v` sends `v` to `-v`. -/
theorem reflection_mulVec_self (hA : A.IsHermitian) (hA' : IsUnit A) (v : n → K)
    (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) :
    ((reflection hA hA' v hv : GL n K) : Matrix n n K) *ᵥ v = -v := by
  simp [sub_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec, smul_smul,
    div_mul_cancel₀ _ hv, two_smul]

/-- The reflection in `v` fixes every vector `w` orthogonal to `v` for the form. -/
theorem reflection_mulVec_of_dotProduct_eq_zero (hA : A.IsHermitian) (hA' : IsUnit A) (v : n → K)
    (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) {w : n → K} (hw : star v ⬝ᵥ A *ᵥ w = 0) :
    ((reflection hA hA' v hv : GL n K) : Matrix n n K) *ᵥ w = w := by
  simp [sub_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec, hw]

/-- For a Hermitian invertible Gram matrix `A`, an element of the centre of `unitaryGroupOf A`
commutes with the rank-one matrix `v (star v ᵥ* A)` of every non-isotropic vector `v`, since it
commutes with the reflection in `v`. -/
private theorem mul_vecMulVec_eq_of_mem_center [NeZero (2 : K)] (hA : A.IsHermitian)
    (hA' : IsUnit A) {g : unitaryGroupOf A} (hg : g ∈ Subgroup.center (unitaryGroupOf A))
    {v : n → K} (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) :
    ((g : GL n K) : Matrix n n K) * vecMulVec v (star v ᵥ* A) =
      vecMulVec v (star v ᵥ* A) * (g : GL n K) := by
  have h := congrArg (fun x : unitaryGroupOf A => ((x : GL n K) : Matrix n n K))
    (Subgroup.mem_center_iff.mp hg (reflection hA hA' v hv))
  simp only [Subgroup.coe_mul, Units.val_mul, val_reflection, sub_mul, mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, sub_right_inj] at h
  exact (smul_right_injective _ (div_ne_zero two_ne_zero hv) h).symm

/-- The entry `(i, k)` of `g * v (star v ᵥ* A) = v (star v ᵥ* A) * g`. -/
private theorem mulVec_apply_mul_eq_of_mem_center [NeZero (2 : K)] (hA : A.IsHermitian)
    (hA' : IsUnit A) {g : unitaryGroupOf A} (hg : g ∈ Subgroup.center (unitaryGroupOf A))
    {v : n → K} (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) (i k : n) :
    (((g : GL n K) : Matrix n n K) *ᵥ v) i * (star v ᵥ* A) k =
      v i * (star v ᵥ* A ᵥ* ((g : GL n K) : Matrix n n K)) k := by
  simpa [mul_vecMulVec, vecMulVec_mul, vecMulVec_apply] using
    congrFun (congrFun (mul_vecMulVec_eq_of_mem_center hA hA' hg hv) i) k

end unitaryGroupOf

end Field

end Matrix

namespace TauCeti

namespace Matrix

variable (p q R : Type*) [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

section CommRing

variable [CommRing R] [StarRing R]

/-- The **indefinite unitary group** `U(p, q)`: the invertible matrices `g` on `p ⊕ q → R` with
`star g * J * g = J`, where `J = diag(1, …, 1, -1, …, -1)` is
`LieAlgebra.Orthogonal.indefiniteDiagonal p q R`, the Gram matrix of the Hermitian form
`⟨z, w⟩ = star z ⬝ᵥ J *ᵥ w` of signature `(p, q)`. It is `unitaryGroupOf J`, whose general API
applies to it. -/
abbrev indefiniteUnitaryGroup : Subgroup (GL (p ⊕ q) R) :=
  unitaryGroupOf (indefiniteDiagonal p q R)

variable {p q R}

/-- **The inverse of an element of `U(p, q)`** is `J * star g * J`. -/
theorem val_inv_of_mem_indefiniteUnitaryGroup {g : GL (p ⊕ q) R}
    (hg : g ∈ indefiniteUnitaryGroup p q R) :
    (↑g⁻¹ : Matrix (p ⊕ q) (p ⊕ q) R) =
      indefiniteDiagonal p q R * star (g : Matrix (p ⊕ q) (p ⊕ q) R) *
        indefiniteDiagonal p q R := by
  rw [val_inv_of_mem_unitaryGroupOf isUnit_indefiniteDiagonal hg, inv_indefiniteDiagonal]

/-- Membership in `U(p, q)` is equivalent to the equation `g * J * star g = J`. -/
theorem mem_indefiniteUnitaryGroup_iff' {g : GL (p ⊕ q) R} :
    g ∈ indefiniteUnitaryGroup p q R ↔
      (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * star (g : Matrix _ _ R) =
        indefiniteDiagonal p q R := by
  rw [mem_unitaryGroupOf_iff' isUnit_indefiniteDiagonal, inv_indefiniteDiagonal]

/-- **`U(p, q)` is stable under conjugate transposition.** -/
@[simp]
theorem star_mem_indefiniteUnitaryGroup_iff {g : GL (p ⊕ q) R} :
    star g ∈ indefiniteUnitaryGroup p q R ↔ g ∈ indefiniteUnitaryGroup p q R := by
  simpa only [inv_indefiniteDiagonal] using
    star_mem_unitaryGroupOf_inv_iff (A := indefiniteDiagonal p q R) isUnit_indefiniteDiagonal

/-- A diagonal matrix `diag(d)` satisfies `star (diag d) * J * diag d = J` exactly when every
diagonal entry is unitary. -/
theorem star_diagonal_mul_indefiniteDiagonal_mul_diagonal_eq_iff {d : p ⊕ q → R} :
    star (diagonal d) * indefiniteDiagonal p q R * diagonal d = indefiniteDiagonal p q R ↔
      ∀ i, star (d i) * d i = 1 := by
  rw [indefiniteDiagonal, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    diagonal_mul_diagonal, diagonal_eq_diagonal_iff]
  refine forall_congr' fun i => ?_
  rcases i with i | i <;> simp [neg_eq_iff_eq_neg]

namespace indefiniteUnitaryGroup

variable (p q R) in
/-- The **block-diagonal embedding** `(A, D) ↦ diag(A, D)` of `U(p) × U(q)` in `U(p, q)`. Its
image is the stabilizer of the positive coordinate subspace (`mem_range_fromBlocksHom_iff`); for
`U(1, n)` it is the stabilizer `U(1) × U(n)` of the positive line spanned by the first basis
vector. -/
def fromBlocksHom : unitaryGroup p R × unitaryGroup q R →* indefiniteUnitaryGroup p q R :=
  (Unitary.toUnits.comp UnitaryGroup.sum).codRestrict _ fun x => by
    rw [mem_unitaryGroupOf_iff, MonoidHom.comp_apply, Unitary.val_toUnits_apply,
      UnitaryGroup.coe_sum, indefiniteDiagonal_eq_fromBlocks, star_eq_conjTranspose,
      fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [← star_eq_conjTranspose]

@[simp]
theorem val_fromBlocksHom (x : unitaryGroup p R × unitaryGroup q R) :
    ((fromBlocksHom p q R x : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) =
      fromBlocks (x.1 : Matrix p p R) 0 0 (x.2 : Matrix q q R) := by
  simp [fromBlocksHom]

/-- The block-diagonal embedding of `U(p) × U(q)` in `U(p, q)` is injective. -/
theorem fromBlocksHom_injective : Function.Injective (fromBlocksHom p q R) := fun x y h =>
  UnitaryGroup.sum_injective <| Subtype.ext <| by
    simpa using congrArg (fun g : indefiniteUnitaryGroup p q R =>
      ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R)) h

/-- **The stabilizer of the positive coordinate subspace.** An element of `U(p, q)` lies in the
image of `U(p) × U(q)` exactly when its lower-left block vanishes, that is when it maps the
subspace spanned by the positive basis vectors `eᵢ`, `i ∈ p`, into itself. -/
theorem mem_range_fromBlocksHom_iff {g : indefiniteUnitaryGroup p q R} :
    g ∈ (fromBlocksHom p q R).range ↔
      ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R).toBlocks₂₁ = 0 := by
  refine ⟨fun ⟨x, hx⟩ => by rw [← hx, val_fromBlocksHom, toBlocks_fromBlocks₂₁], fun hC => ?_⟩
  set M : Matrix (p ⊕ q) (p ⊕ q) R := ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R)
  have hM : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hC, fromBlocks_toBlocks]
  have h : star M * indefiniteDiagonal p q R * M = indefiniteDiagonal p q R :=
    mem_unitaryGroupOf_iff.mp g.property
  rw [hM, indefiniteDiagonal_eq_fromBlocks, star_eq_conjTranspose, fromBlocks_conjTranspose,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  simp only [conjTranspose_zero, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul,
    Matrix.mul_neg, Matrix.neg_mul, zero_add, neg_zero] at h
  obtain ⟨hA, hB, -, hD⟩ := h
  have hAu : M.toBlocks₁₁ ∈ unitaryGroup p R := by
    rwa [mem_unitaryGroup_iff', star_eq_conjTranspose]
  have hB0 : M.toBlocks₁₂ = 0 := by
    rw [← Matrix.one_mul M.toBlocks₁₂, ← mem_unitaryGroup_iff.mp hAu, Matrix.mul_assoc,
      star_eq_conjTranspose, hB, Matrix.mul_zero]
  have hDu : M.toBlocks₂₂ ∈ unitaryGroup q R := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    simpa [hB0] using hD
  refine ⟨(⟨_, hAu⟩, ⟨_, hDu⟩), unitaryGroupOf.ext ?_⟩
  rw [val_fromBlocksHom]
  exact (hB0 ▸ hM).symm

end indefiniteUnitaryGroup

end CommRing

section Field

variable {p q} {K : Type*} [Field K] [StarRing K]

namespace indefiniteUnitaryGroup

variable [CharZero K]

/-- The off-diagonal entries of a central element of `U(p, q)` vanish: test its commutation with
the rank-one matrix of the basis vector `eₖ`. -/
private theorem apply_eq_zero_of_mem_center {g : indefiniteUnitaryGroup p q K}
    (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K)) {i k : p ⊕ q} (hik : i ≠ k) :
    ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) i k = 0 := by
  have hv :
      star (Pi.single k 1 : p ⊕ q → K) ⬝ᵥ indefiniteDiagonal p q K *ᵥ Pi.single k 1 ≠ 0 := by
    simpa [Pi.single_star, mulVec_single_one, single_one_dotProduct] using
      indefiniteDiagonal_apply_self_ne_zero k
  have h := unitaryGroupOf.mulVec_apply_mul_eq_of_mem_center isHermitian_indefiniteDiagonal
    isUnit_indefiniteDiagonal hg hv i k
  simp only [mulVec_single, MulOpposite.op_one, Pi.smul_apply, col_apply, one_smul,
    Pi.star_single, star_one, single_vecMul, row_apply, smul_eq_mul, one_mul, ne_eq, hik,
    not_false_eq_true, Pi.single_eq_of_ne, zero_mul, mul_eq_zero] at h
  exact h.resolve_right (indefiniteDiagonal_apply_self_ne_zero k)

/-- The matrix of a central element of `U(p, q)` is diagonal. -/
private theorem eq_diagonal_of_mem_center {g : indefiniteUnitaryGroup p q K}
    (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K)) :
    ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) =
      diagonal fun i => ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) i i := by
  ext a b
  rcases eq_or_ne a b with rfl | hab
  · simp
  · simp [apply_eq_zero_of_mem_center hg hab, hab]

/-- The diagonal entries of a central element of `U(p, q)` agree: test its commutation with the
rank-one matrix of the non-isotropic vector `eᵢ + 2 eₖ`, whose value `J i i + 4 J k k` is one of
`±3`, `±5`. -/
private theorem apply_self_eq_of_mem_center {g : indefiniteUnitaryGroup p q K}
    (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K)) (i k : p ⊕ q) :
    ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) i i =
      ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) k k := by
  rcases eq_or_ne i k with rfl | hik
  · rfl
  set v : p ⊕ q → K := Pi.single i 1 + Pi.single k 2 with hv_def
  have hvi : v i = 1 := by simp [v, hik]
  have hvk : v k = 2 := by simp [v, hik.symm]
  have hsv : star v = v := by simp [v]
  have hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0 := by
    have hc : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v =
        indefiniteDiagonal p q K i i + 4 * indefiniteDiagonal p q K k k := by
      nth_rw 1 [hsv, hv_def]
      rw [add_dotProduct, single_dotProduct, single_dotProduct, indefiniteDiagonal_mulVec_apply,
        indefiniteDiagonal_mulVec_apply, hvi, hvk]
      ring
    rw [hc]
    rcases indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one (p := p) (q := q) (R := K) i
      with h1 | h1 <;>
    rcases indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one (p := p) (q := q) (R := K) k
      with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have h := unitaryGroupOf.mulVec_apply_mul_eq_of_mem_center isHermitian_indefiniteDiagonal
    isUnit_indefiniteDiagonal hg hv i k
  rw [eq_diagonal_of_mem_center hg, mulVec_diagonal, vecMul_diagonal, hsv,
    vecMul_indefiniteDiagonal_apply, hvi, hvk] at h
  apply mul_right_cancel₀ (mul_ne_zero two_ne_zero (indefiniteDiagonal_apply_self_ne_zero k))
  linear_combination h

/-- **The centre of `U(p, q)`**: over a field of characteristic zero, the elements of `U(p, q)`
commuting with all of `U(p, q)` are the unit scalars `λ • 1` with `star λ * λ = 1`. Over `ℂ`
these are the scalars of modulus one, and `PU(p, q)` is the quotient by them. -/
theorem center_eq_range_scalarHom :
    Subgroup.center (indefiniteUnitaryGroup p q K) =
      (unitaryGroupOf.scalarHom (indefiniteDiagonal p q K)).range := by
  refine le_antisymm (fun g hg => ?_) fun _ ⟨u, hu⟩ => hu ▸ Subgroup.mem_center_iff.mpr fun h =>
    unitaryGroupOf.ext <| by
      simp only [Subgroup.coe_mul, Units.val_mul, unitaryGroupOf.val_scalarHom]
      exact (scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm
  rcases isEmpty_or_nonempty (p ⊕ q) with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, unitaryGroupOf.ext <| Subsingleton.elim _ _⟩
  set M : Matrix (p ⊕ q) (p ⊕ q) K := ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) with hMdef
  -- `M` is the scalar matrix of its corner entry `λ = M i₀ i₀`, and `star λ * λ = 1`.
  have hMs : M = scalar (p ⊕ q) (M i₀ i₀) := by
    rw [hMdef, eq_diagonal_of_mem_center hg, scalar_apply]
    exact congrArg diagonal (funext fun a => by simp [apply_self_eq_of_mem_center hg a i₀])
  have hu : M i₀ i₀ ∈ unitary K := by
    have h := congrFun (congrFun (mem_unitaryGroupOf_iff.mp g.property) i₀) i₀
    rw [← hMdef, hMs] at h
    simp only [scalar_apply, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal,
      diagonal_mul, Pi.star_apply] at h
    rw [Unitary.mem_iff_star_mul_self]
    exact mul_right_cancel₀ (indefiniteDiagonal_apply_self_ne_zero i₀) (by linear_combination h)
  exact ⟨⟨_, hu⟩, unitaryGroupOf.ext <| by rw [unitaryGroupOf.val_scalarHom]; exact hMs.symm⟩

end indefiniteUnitaryGroup

end Field

end Matrix

end TauCeti

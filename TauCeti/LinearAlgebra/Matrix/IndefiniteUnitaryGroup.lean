/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# The indefinite unitary group `U(p, q)`

Let `R` be a commutative ring with an involution `star`, and let
`J = LieAlgebra.Orthogonal.indefiniteDiagonal p q R = diag(1, …, 1, -1, …, -1)` be the Gram matrix
of the Hermitian form `⟨z, w⟩ = star z ⬝ᵥ J *ᵥ w = Σ_{i ∈ p} star zᵢ wᵢ - Σ_{j ∈ q} star zⱼ wⱼ` on
`p ⊕ q → R`, conjugate-linear in the first slot. The **indefinite unitary group**
`Matrix.indefiniteUnitaryGroup p q R` is the subgroup of `GL (p ⊕ q) R` of the matrices `g` with
`star g * J * g = J`: the invertible matrices preserving the form. Over `ℂ` this is `U(p, q)`, and
`U(1, n)`, for `p = Fin 1` and `q = Fin n`, is the group acting on complex hyperbolic `n`-space.
Over `ℝ`, where the star is trivial, it is the indefinite orthogonal group `O(p, q)`.

The basic structure of this group is recorded here.

* Membership is equivalent to `g * J * star g = J`, to `star g` lying in the group, and to the
  preservation `⟨g z, g w⟩ = ⟨z, w⟩` of the form. (Over `ℝ` or `ℂ` it is also equivalent, by
  polarization, to the preservation of the values `⟨z, z⟩` alone; that statement, with the
  topological facts about `U(p, q)`, is in `TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup`.)
* Every matrix preserving the form is invertible, with inverse `J * star g * J`
  (`Matrix.indefiniteUnitaryGroup.ofMatrix`), and its determinant is a unitary scalar.
* The block-diagonal matrices `diag(A, D)` with `A ∈ U(p)` and `D ∈ U(q)` form a subgroup
  isomorphic to `U(p) × U(q)` (`Matrix.indefiniteUnitaryGroup.fromBlocksHom`). It is the stabilizer
  of the coordinate subspace `p → R` spanned by the positive basis vectors: an element of `U(p, q)`
  preserves that subspace, that is has vanishing lower-left block, exactly when it is block
  diagonal. For `U(1, n)` this is the stabilizer `U(1) × U(n)` of the positive line spanned by the
  first basis vector.
* Over a field of characteristic zero, the centre of `U(p, q)` is the group of unit scalars
  `λ • 1` with `star λ * λ = 1`. The proof uses the reflections
  `1 - (2 / ⟨v, v⟩) • vecMulVec v (star v ᵥ* J)` in the non-isotropic vectors `v`, which lie in
  `U(p, q)` (`Matrix.indefiniteUnitaryGroup.reflection`): a central element commutes with the
  rank-one matrices `vecMulVec v (star v ᵥ* J)`, and testing this on the vectors `eₖ` and
  `eᵢ + 2 eₖ` forces it to be scalar.

## Main definitions

* `Matrix.indefiniteUnitaryGroup p q R`: the group `U(p, q)` of invertible matrices preserving the
  Hermitian form of Gram matrix `diag(1, …, 1, -1, …, -1)`.
* `Matrix.indefiniteUnitaryGroup.ofMatrix`: the element of `U(p, q)` defined by a matrix preserving
  the form.
* `Matrix.indefiniteUnitaryGroup.fromBlocksHom`: the block-diagonal embedding of `U(p) × U(q)`.
* `Matrix.indefiniteUnitaryGroup.scalarHom`: the embedding `λ ↦ λ • 1` of the unitary scalars.
* `Matrix.indefiniteUnitaryGroup.reflection`: the reflection in a non-isotropic vector.

## Main results

* `Matrix.mem_indefiniteUnitaryGroup_iff'`: membership as the equation `g * J * star g = J`.
* `Matrix.mem_indefiniteUnitaryGroup_iff_forall_dotProduct`: membership as preservation of the
  form.
* `Matrix.val_inv_of_mem_indefiniteUnitaryGroup`: the inverse of `g ∈ U(p, q)` is `J * star g * J`.
* `Matrix.star_mem_indefiniteUnitaryGroup_iff`: `U(p, q)` is stable under conjugate transposition.
* `Matrix.det_mem_unitary_of_mem_indefiniteUnitaryGroup`: `star (det g) * det g = 1`.
* `Matrix.indefiniteUnitaryGroup.mem_range_fromBlocksHom_iff`: the image of `U(p) × U(q)` is the
  subgroup of elements with vanishing lower-left block.
* `Matrix.indefiniteUnitaryGroup.center_eq_range_scalarHom`: over a field of characteristic zero,
  the centre of `U(p, q)` is the group of unit scalars.

## References

* W. M. Goldman, *Complex Hyperbolic Geometry*, Oxford Mathematical Monographs, Oxford University
  Press (1999), Chapter 3.
* G. Baldi and E. Ullmo, *Special subvarieties of non-arithmetic ball quotients and Hodge theory*,
  Ann. of Math. 197 (2023), Section 2, for the matrix description of `U(1, n)`.
-/

public section

open LieAlgebra.Orthogonal

namespace Matrix

variable (p q R : Type*) [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

section CommRing

variable [CommRing R] [StarRing R]

/-- The **indefinite unitary group** `U(p, q)`: the invertible matrices `g` on `p ⊕ q → R` with
`star g * J * g = J`, where `J = diag(1, …, 1, -1, …, -1)` is
`LieAlgebra.Orthogonal.indefiniteDiagonal p q R`, the Gram matrix of the Hermitian form
`⟨z, w⟩ = star z ⬝ᵥ J *ᵥ w` of signature `(p, q)`. -/
def indefiniteUnitaryGroup : Subgroup (GL (p ⊕ q) R) where
  carrier := {g | star (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * g =
    indefiniteDiagonal p q R}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, star_mul] at *
    calc _ = star (b : Matrix (p ⊕ q) (p ⊕ q) R) *
          (star (a : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc _ = star (↑a⁻¹ : Matrix (p ⊕ q) (p ⊕ q) R) *
          (star (a : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * a) * ↑a⁻¹ := by
          rw [ha]
      _ = star ((a : Matrix (p ⊕ q) (p ⊕ q) R) * ↑a⁻¹) * indefiniteDiagonal p q R *
          ((a : Matrix (p ⊕ q) (p ⊕ q) R) * ↑a⁻¹) := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = _ := by simp

variable {p q R}

/-- Membership in `U(p, q)` is the equation `star g * J * g = J`. -/
theorem mem_indefiniteUnitaryGroup_iff {g : GL (p ⊕ q) R} :
    g ∈ indefiniteUnitaryGroup p q R ↔
      star (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * g =
        indefiniteDiagonal p q R :=
  Iff.rfl

/-- **The inverse of an element of `U(p, q)`** is `J * star g * J`. -/
theorem val_inv_of_mem_indefiniteUnitaryGroup {g : GL (p ⊕ q) R}
    (hg : g ∈ indefiniteUnitaryGroup p q R) :
    (↑g⁻¹ : Matrix (p ⊕ q) (p ⊕ q) R) =
      indefiniteDiagonal p q R * star (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R :=
  Units.inv_eq_of_mul_eq_one_left <| by
    have h := mem_indefiniteUnitaryGroup_iff.mp hg
    simp only [Matrix.mul_assoc] at h ⊢
    rw [h, indefiniteDiagonal_mul_indefiniteDiagonal]

/-- Membership in `U(p, q)` is equivalent to the equation `g * J * star g = J`. -/
theorem mem_indefiniteUnitaryGroup_iff' {g : GL (p ⊕ q) R} :
    g ∈ indefiniteUnitaryGroup p q R ↔
      (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * star (g : Matrix _ _ R) =
        indefiniteDiagonal p q R := by
  -- Both equations say that `J * star g * J` is an inverse of `g`, on the left and on the right.
  set M : Matrix (p ⊕ q) (p ⊕ q) R := (g : Matrix (p ⊕ q) (p ⊕ q) R)
  have hJ : IsUnit (indefiniteDiagonal p q R) := isUnit_indefiniteDiagonal
  calc g ∈ indefiniteUnitaryGroup p q R
      ↔ indefiniteDiagonal p q R * (star M * indefiniteDiagonal p q R * M) =
          indefiniteDiagonal p q R * indefiniteDiagonal p q R :=
        hJ.mul_right_inj.symm
    _ ↔ indefiniteDiagonal p q R * star M * indefiniteDiagonal p q R * M = 1 := by
        simp only [indefiniteDiagonal_mul_indefiniteDiagonal, Matrix.mul_assoc]
    _ ↔ M * (indefiniteDiagonal p q R * star M * indefiniteDiagonal p q R) = 1 := mul_eq_one_comm
    _ ↔ M * indefiniteDiagonal p q R * star M * indefiniteDiagonal p q R =
          indefiniteDiagonal p q R * indefiniteDiagonal p q R := by
        simp only [indefiniteDiagonal_mul_indefiniteDiagonal, Matrix.mul_assoc]
    _ ↔ _ := hJ.mul_left_inj

/-- **`U(p, q)` is stable under conjugate transposition.** -/
@[simp]
theorem star_mem_indefiniteUnitaryGroup_iff {g : GL (p ⊕ q) R} :
    star g ∈ indefiniteUnitaryGroup p q R ↔ g ∈ indefiniteUnitaryGroup p q R := by
  rw [mem_indefiniteUnitaryGroup_iff, mem_indefiniteUnitaryGroup_iff', Units.coe_star, star_star]

/-- **`U(p, q)` is the group of isometries of the Hermitian form**: `g ∈ U(p, q)` exactly when
`⟨g x, g y⟩ = ⟨x, y⟩` for all `x` and `y`, where `⟨x, y⟩ = star x ⬝ᵥ J *ᵥ y`. -/
theorem mem_indefiniteUnitaryGroup_iff_forall_dotProduct {g : GL (p ⊕ q) R} :
    g ∈ indefiniteUnitaryGroup p q R ↔ ∀ x y : p ⊕ q → R,
      star ((g : Matrix (p ⊕ q) (p ⊕ q) R) *ᵥ x) ⬝ᵥ indefiniteDiagonal p q R *ᵥ (g *ᵥ y) =
        star x ⬝ᵥ indefiniteDiagonal p q R *ᵥ y := by
  simp only [← star_dotProduct_conjTranspose_mul_mul_mulVec, ← star_eq_conjTranspose]
  refine ⟨fun h x y => by rw [mem_indefiniteUnitaryGroup_iff.mp h], fun h => ?_⟩
  ext i j
  simpa [mulVec_single_one, Pi.star_single] using h (Pi.single i 1) (Pi.single j 1)

/-- A matrix preserving the form is invertible, with inverse `J * star M * J`: this is the element
of `U(p, q)` it defines. -/
def indefiniteUnitaryGroup.ofMatrix (M : Matrix (p ⊕ q) (p ⊕ q) R)
    (hM : star M * indefiniteDiagonal p q R * M = indefiniteDiagonal p q R) :
    indefiniteUnitaryGroup p q R :=
  have h : indefiniteDiagonal p q R * star M * indefiniteDiagonal p q R * M = 1 := by
    simp only [Matrix.mul_assoc] at hM ⊢
    rw [hM, indefiniteDiagonal_mul_indefiniteDiagonal]
  ⟨⟨M, indefiniteDiagonal p q R * star M * indefiniteDiagonal p q R, mul_eq_one_comm.mp h, h⟩, hM⟩

@[simp]
theorem indefiniteUnitaryGroup.val_ofMatrix (M : Matrix (p ⊕ q) (p ⊕ q) R)
    (hM : star M * indefiniteDiagonal p q R * M = indefiniteDiagonal p q R) :
    ((ofMatrix M hM : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) = M :=
  (rfl)

/-- **The determinant of an element of `U(p, q)` is a unitary scalar**: `star (det g) * det g = 1`.
Over `ℂ` this says `|det g| = 1`. -/
theorem det_mem_unitary_of_mem_indefiniteUnitaryGroup {g : GL (p ⊕ q) R}
    (hg : g ∈ indefiniteUnitaryGroup p q R) :
    (g : Matrix (p ⊕ q) (p ⊕ q) R).det ∈ unitary R := by
  have h := congrArg det (mem_indefiniteUnitaryGroup_iff.mp hg)
  rw [det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, mul_right_comm] at h
  rw [Unitary.mem_iff_star_mul_self]
  exact (isUnit_det_of_left_inverse indefiniteDiagonal_mul_indefiniteDiagonal).mul_eq_right.mp h

namespace indefiniteUnitaryGroup

variable (p q R) in
/-- The **block-diagonal embedding** `(A, D) ↦ diag(A, D)` of `U(p) × U(q)` in `U(p, q)`. Its
image is the stabilizer of the positive coordinate subspace (`mem_range_fromBlocksHom_iff`); for
`U(1, n)` it is the stabilizer `U(1) × U(n)` of the positive line spanned by the first basis
vector. -/
def fromBlocksHom : unitaryGroup p R × unitaryGroup q R →* indefiniteUnitaryGroup p q R :=
  (Unitary.toUnits.comp UnitaryGroup.sum).codRestrict _ fun x => by
    rw [mem_indefiniteUnitaryGroup_iff, MonoidHom.comp_apply, Unitary.val_toUnits_apply,
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
  have h : star M * indefiniteDiagonal p q R * M = indefiniteDiagonal p q R := g.2
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
  refine ⟨(⟨_, hAu⟩, ⟨_, hDu⟩), Subtype.ext <| Units.ext ?_⟩
  rw [val_fromBlocksHom]
  exact (hB0 ▸ hM).symm

variable (p q R) in
/-- The embedding `λ ↦ λ • 1` of the unitary scalars in `U(p, q)`. Over a field of characteristic
zero its image is the centre of `U(p, q)` (`center_eq_range_scalarHom`). -/
def scalarHom : unitary R →* indefiniteUnitaryGroup p q R :=
  ((GeneralLinearGroup.scalar (p ⊕ q)).comp Unitary.toUnits).codRestrict _ fun u => by
    rw [mem_indefiniteUnitaryGroup_iff, MonoidHom.comp_apply]
    simp only [GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_ofClass,
      Unitary.val_toUnits_apply, RingHom.toMonoidHom_eq_coe, scalar_apply]
    rw [star_eq_conjTranspose, diagonal_conjTranspose, indefiniteDiagonal, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    ext i
    simp only [Pi.star_apply]
    rw [mul_right_comm, Unitary.star_mul_self_of_mem u.2, one_mul]

@[simp]
theorem val_scalarHom (u : unitary R) :
    ((scalarHom p q R u : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) = scalar (p ⊕ q) (u : R) :=
  (rfl)

end indefiniteUnitaryGroup

end CommRing

section Field

variable {p q} {K : Type*} [Field K] [StarRing K]

/-- The reflection matrix `1 - (2 / ⟨v, v⟩) • v (star v ᵥ* J)` preserves the form. -/
private theorem star_reflectionMatrix_mul_mul {v : p ⊕ q → K}
    (hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0) :
    star (1 - (2 / (star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v)) •
        vecMulVec v (star v ᵥ* indefiniteDiagonal p q K)) * indefiniteDiagonal p q K *
      (1 - (2 / (star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v)) •
        vecMulVec v (star v ᵥ* indefiniteDiagonal p q K)) = indefiniteDiagonal p q K := by
  set c := star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v
  set S := vecMulVec (indefiniteDiagonal p q K *ᵥ v) (star v ᵥ* indefiniteDiagonal p q K)
  have hstar : star (vecMulVec v (star v ᵥ* indefiniteDiagonal p q K)) =
      vecMulVec (indefiniteDiagonal p q K *ᵥ v) (star v) := by
    rw [star_eq_conjTranspose, conjTranspose_vecMulVec, star_vecMul, star_star,
      isHermitian_indefiniteDiagonal.eq]
  have ha : star (2 / c) = 2 / c := by
    rw [star_div₀, star_ofNat, isHermitian_indefiniteDiagonal.star_dotProduct_mulVec_comm]
  have hNS : star (vecMulVec v (star v ᵥ* indefiniteDiagonal p q K)) * indefiniteDiagonal p q K =
      S := by
    rw [hstar, vecMulVec_mul]
  have hSN : indefiniteDiagonal p q K * vecMulVec v (star v ᵥ* indefiniteDiagonal p q K) = S := by
    rw [mul_vecMulVec]
  have hSNN : S * vecMulVec v (star v ᵥ* indefiniteDiagonal p q K) = c • S := by
    rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, vecMulVec_smul]
  rw [star_sub, star_one, star_smul, ha]
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hNS, hSN, hSNN, smul_smul]
  have h2 : 2 / c * (2 / c * c) = 2 / c + 2 / c := by
    field_simp
    ring
  rw [h2, add_smul]
  abel

namespace indefiniteUnitaryGroup

/-- **The reflection in a non-isotropic vector.** For `v` with `⟨v, v⟩ ≠ 0`, the element
`1 - (2 / ⟨v, v⟩) • v (star v ᵥ* J)` of `U(p, q)`, which sends `v` to `-v`
(`reflection_mulVec_self`) and fixes the vectors orthogonal to `v` for the form
(`reflection_mulVec_of_dotProduct_eq_zero`). -/
def reflection (v : p ⊕ q → K) (hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0) :
    indefiniteUnitaryGroup p q K :=
  ofMatrix _ (star_reflectionMatrix_mul_mul hv)

@[simp]
theorem val_reflection (v : p ⊕ q → K) (hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0) :
    ((reflection v hv : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) =
      1 - (2 / (star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v)) •
        vecMulVec v (star v ᵥ* indefiniteDiagonal p q K) :=
  (rfl)

/-- The reflection in `v` sends `v` to `-v`. -/
theorem reflection_mulVec_self (v : p ⊕ q → K)
    (hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0) :
    ((reflection v hv : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) *ᵥ v = -v := by
  rw [val_reflection, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
    op_smul_eq_smul, smul_smul, div_mul_cancel₀ _ hv, two_smul, sub_add_cancel_left]

/-- The reflection in `v` fixes every vector `w` orthogonal to `v` for the form. -/
theorem reflection_mulVec_of_dotProduct_eq_zero (v : p ⊕ q → K)
    (hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0) {w : p ⊕ q → K}
    (hw : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ w = 0) :
    ((reflection v hv : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) *ᵥ w = w := by
  rw [val_reflection, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
    hw, op_smul_eq_smul, zero_smul, smul_zero, sub_zero]

/-- An element of the centre of `U(p, q)` commutes with the rank-one matrix `v (star v ᵥ* J)` of
every non-isotropic vector `v`, since it commutes with the reflection in `v`. -/
private theorem mul_vecMulVec_eq_of_mem_center [NeZero (2 : K)] {g : indefiniteUnitaryGroup p q K}
    (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K)) {v : p ⊕ q → K}
    (hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0) :
    ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) *
        vecMulVec v (star v ᵥ* indefiniteDiagonal p q K) =
      vecMulVec v (star v ᵥ* indefiniteDiagonal p q K) * (g : GL (p ⊕ q) K) := by
  have h := congrArg (fun x : indefiniteUnitaryGroup p q K => ((x : GL (p ⊕ q) K) :
    Matrix (p ⊕ q) (p ⊕ q) K)) (Subgroup.mem_center_iff.mp hg (reflection v hv))
  simp only [Subgroup.coe_mul, Units.val_mul, val_reflection, sub_mul, mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, sub_right_inj] at h
  exact (smul_right_injective _ (div_ne_zero two_ne_zero hv) h).symm

/-- The entry `(i, k)` of `g * v (star v ᵥ* J) = v (star v ᵥ* J) * g`. -/
private theorem mulVec_apply_mul_eq_of_mem_center [NeZero (2 : K)]
    {g : indefiniteUnitaryGroup p q K} (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K))
    {v : p ⊕ q → K} (hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0) (i k : p ⊕ q) :
    (((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) *ᵥ v) i *
        (star v ᵥ* indefiniteDiagonal p q K) k =
      v i * (star v ᵥ* indefiniteDiagonal p q K ᵥ* ((g : GL (p ⊕ q) K) :
        Matrix (p ⊕ q) (p ⊕ q) K)) k := by
  simpa [mul_vecMulVec, vecMulVec_mul, vecMulVec_apply] using
    congrFun (congrFun (mul_vecMulVec_eq_of_mem_center hg hv) i) k

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
  have h := mulVec_apply_mul_eq_of_mem_center hg hv i k
  simp only [mulVec_single, MulOpposite.op_one, Pi.smul_apply, col_apply, one_smul,
    Pi.star_single, star_one, single_vecMul, row_apply, smul_eq_mul, one_mul, ne_eq, hik,
    not_false_eq_true, Pi.single_eq_of_ne, zero_mul, mul_eq_zero] at h
  exact h.resolve_right (indefiniteDiagonal_apply_self_ne_zero k)

/-- The diagonal entries of a central element of `U(p, q)` agree: test its commutation with the
rank-one matrix of the non-isotropic vector `eᵢ + 2 eₖ`, whose value `J i i + 4 J k k` is one of
`±3`, `±5`. -/
private theorem apply_self_eq_of_mem_center {g : indefiniteUnitaryGroup p q K}
    (hg : g ∈ Subgroup.center (indefiniteUnitaryGroup p q K)) (i k : p ⊕ q) :
    ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) i i =
      ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) k k := by
  rcases eq_or_ne i k with rfl | hik
  · rfl
  set M : Matrix (p ⊕ q) (p ⊕ q) K := ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) with hMdef
  have hMd : M = diagonal fun i => M i i := by
    ext a b
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [apply_eq_zero_of_mem_center hg hab, hab, M]
  have hJv (v : p ⊕ q → K) :
      indefiniteDiagonal p q K *ᵥ v = fun l => indefiniteDiagonal p q K l l * v l := by
    ext l
    simp [indefiniteDiagonal, mulVec_diagonal]
  have hvJ (v : p ⊕ q → K) :
      v ᵥ* indefiniteDiagonal p q K = fun l => v l * indefiniteDiagonal p q K l l := by
    ext l
    simp [indefiniteDiagonal, vecMul_diagonal]
  set v : p ⊕ q → K := Pi.single i 1 + Pi.single k 2 with hv_def
  have hvi : v i = 1 := by simp [v, hik]
  have hvk : v k = 2 := by simp [v, hik.symm]
  have hsv : star v = v := by simp [v]
  have hv : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v ≠ 0 := by
    have hc : star v ⬝ᵥ indefiniteDiagonal p q K *ᵥ v =
        indefiniteDiagonal p q K i i + 4 * indefiniteDiagonal p q K k k := by
      rw [hsv, hJv]
      nth_rw 1 [hv_def]
      rw [add_dotProduct, single_dotProduct, single_dotProduct, hvi, hvk]
      ring
    rw [hc]
    rcases indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one (p := p) (q := q) (R := K) i
      with h1 | h1 <;>
    rcases indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one (p := p) (q := q) (R := K) k
      with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have h := mulVec_apply_mul_eq_of_mem_center hg hv i k
  rw [← hMdef, hMd, mulVec_diagonal, vecMul_diagonal, hsv, hvJ, hvi] at h
  simp only [hvk] at h
  apply mul_right_cancel₀ (mul_ne_zero two_ne_zero (indefiniteDiagonal_apply_self_ne_zero k))
  linear_combination h

/-- **The centre of `U(p, q)`**: over a field of characteristic zero, the elements of `U(p, q)`
commuting with all of `U(p, q)` are the unit scalars `λ • 1` with `star λ * λ = 1`. Over `ℂ`
these are the scalars of modulus one, and `PU(p, q)` is the quotient by them. -/
theorem center_eq_range_scalarHom :
    Subgroup.center (indefiniteUnitaryGroup p q K) = (scalarHom p q K).range := by
  refine le_antisymm (fun g hg => ?_) fun _ ⟨u, hu⟩ => hu ▸ Subgroup.mem_center_iff.mpr fun h =>
    Subtype.ext <| Units.ext <| by
      simp only [Subgroup.coe_mul, Units.val_mul, val_scalarHom]
      exact (scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm
  rcases isEmpty_or_nonempty (p ⊕ q) with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, Subtype.ext <| Units.ext <| Subsingleton.elim _ _⟩
  set M : Matrix (p ⊕ q) (p ⊕ q) K := ((g : GL (p ⊕ q) K) : Matrix (p ⊕ q) (p ⊕ q) K) with hMdef
  -- `M` is the scalar matrix of its corner entry `λ = M i₀ i₀`, and `star λ * λ = 1`.
  have hMs : M = scalar (p ⊕ q) (M i₀ i₀) := by
    ext a b
    rcases eq_or_ne a b with rfl | hab
    · simp [apply_self_eq_of_mem_center hg a i₀, M]
    · simp [apply_eq_zero_of_mem_center hg hab, hab, M]
  have hu : M i₀ i₀ ∈ unitary K := by
    have h := congrFun (congrFun (mem_indefiniteUnitaryGroup_iff.mp g.2) i₀) i₀
    rw [← hMdef, hMs] at h
    simp only [scalar_apply, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal,
      diagonal_mul, Pi.star_apply] at h
    rw [Unitary.mem_iff_star_mul_self]
    exact mul_right_cancel₀ (indefiniteDiagonal_apply_self_ne_zero i₀) (by linear_combination h)
  exact ⟨⟨_, hu⟩, Subtype.ext <| Units.ext <| by rw [val_scalarHom]; exact hMs.symm⟩

end indefiniteUnitaryGroup

end Field

end Matrix

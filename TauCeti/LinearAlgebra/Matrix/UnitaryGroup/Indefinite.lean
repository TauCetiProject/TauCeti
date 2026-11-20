/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.DotProduct
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
import Mathlib.Tactic.LinearCombination

/-!
# The indefinite unitary group `U(p, q)`

Let `R` be a commutative star ring and `J = diag(1, …, 1, -1, …, -1)` the Gram matrix
`LieAlgebra.Orthogonal.indefiniteDiagonal p q R` on `p ⊕ q`, with `p` ones and `q` minus ones. It
defines the Hermitian form `⟨z, w⟩ = star z ⬝ᵥ (J *ᵥ w)`, conjugate-linear in the first slot; over
`ℂ` with `p` a singleton this is the form `conj(z₀) w₀ - Σ conj(zᵢ) wᵢ` of signature `(1, n)`. The
**indefinite unitary group** `U(p, q)` is the subgroup of `GL (p ⊕ q) R` of the matrices `g` with
`star g * J * g = J`, the invertible matrices preserving this form. With the topology of `GL`, it is
the group whose quotient by its centre `PU(1, n)` acts on complex hyperbolic space, the unit ball of
`ℂⁿ`, by fractional linear maps.

This file develops the algebraic structure of `U(p, q)`:

* membership is preservation of the form, `⟨g z, g w⟩ = ⟨z, w⟩` for all `z` and `w`;
* the inverse of `g ∈ U(p, q)` is `J * star g * J`, and `star g ∈ U(p, q)` exactly when
  `g ∈ U(p, q)`, so `U(p, q)` is stable under `g ↦ (star g)⁻¹`;
* the determinant of `g ∈ U(p, q)` is unitary, `star (det g) * det g = 1`;
* the block-diagonal matrices `diag(A, B)` with `A ∈ U(p)` and `B ∈ U(q)` form a subgroup isomorphic
  to `U(p) × U(q)`, and an element of `U(p, q)` lies in it as soon as its lower left block
  vanishes; for `p` a singleton, these are the elements fixing the line spanned by the first
  basis vector;
* over a field of characteristic zero the centre of `U(p, q)` consists of the unit scalars
  `c • 1` with `star c * c = 1`.

## Main definitions

* `Matrix.indefiniteUnitaryGroup p q R`: the group `U(p, q)`.
* `Matrix.IndefiniteUnitaryGroup.mk`: the element of `U(p, q)` given by a matrix `M` with
  `star M * J * M = J`, which is automatically invertible.
* `Matrix.IndefiniteUnitaryGroup.ofUnitaryProd`: the block-diagonal embedding of `U(p) × U(q)`.
* `Matrix.IndefiniteUnitaryGroup.reflection`: over a field, the `J`-reflection in a vector `v`
  with `⟨v, v⟩ ≠ 0`.

## Main results

* `Matrix.mem_indefiniteUnitaryGroup_iff_forall_dotProduct`: membership as preservation of the
  Hermitian form.
* `Matrix.coe_inv_of_mem_indefiniteUnitaryGroup`: the inverse is `J * star g * J`.
* `Matrix.star_mem_indefiniteUnitaryGroup_iff`: stability under the conjugate transpose.
* `Matrix.det_of_mem_indefiniteUnitaryGroup`: the determinant is unitary.
* `Matrix.IndefiniteUnitaryGroup.mem_range_ofUnitaryProd_iff`: the image of `U(p) × U(q)` is the
  set of elements with vanishing lower left block.
* `Matrix.IndefiniteUnitaryGroup.mem_center_iff`: the centre is the group of unit scalars.

## References

* W. M. Goldman, *Complex Hyperbolic Geometry*, Oxford University Press (1999), Chapter 3.
-/

public section

open LieAlgebra.Orthogonal

namespace Matrix

variable {p q R : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

section CommRing

variable [CommRing R] [StarRing R]

omit [DecidableEq p] [DecidableEq q] in
/-- Congruence by a product: `(X Y)ᴴ M (X Y) = Yᴴ (Xᴴ M X) Y`. -/
private theorem star_mul_mul_mul_eq (X Y M : Matrix (p ⊕ q) (p ⊕ q) R) :
    star (X * Y) * M * (X * Y) = star Y * (star X * M * X) * Y := by
  simp only [star_mul, Matrix.mul_assoc]

variable (p q R) in
/-- **The indefinite unitary group** `U(p, q)`: the invertible matrices `g` on `p ⊕ q` with
`star g * J * g = J`, where `J = diag(1, …, 1, -1, …, -1)` is
`LieAlgebra.Orthogonal.indefiniteDiagonal p q R`. These are the invertible matrices preserving
the Hermitian form `⟨z, w⟩ = star z ⬝ᵥ (J *ᵥ w)`
(`Matrix.mem_indefiniteUnitaryGroup_iff_forall_dotProduct`). -/
def indefiniteUnitaryGroup : Subgroup (GL (p ⊕ q) R) where
  carrier := {g | star (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * g =
    indefiniteDiagonal p q R}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at ha hb ⊢
    rw [star_mul_mul_mul_eq, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← star_mul_mul_mul_eq, ← Units.val_mul, mul_inv_cancel, Units.val_one, star_one,
      Matrix.one_mul, Matrix.mul_one]

/-- An invertible matrix lies in `U(p, q)` exactly when `star g * J * g = J`. -/
theorem mem_indefiniteUnitaryGroup_iff {g : GL (p ⊕ q) R} :
    g ∈ indefiniteUnitaryGroup p q R ↔
      star (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * g =
        indefiniteDiagonal p q R :=
  Iff.rfl

/-- **`U(p, q)` is the group of the Hermitian form.** An invertible matrix lies in `U(p, q)`
exactly when it preserves `⟨z, w⟩ = star z ⬝ᵥ (J *ᵥ w)`. -/
theorem mem_indefiniteUnitaryGroup_iff_forall_dotProduct {g : GL (p ⊕ q) R} :
    g ∈ indefiniteUnitaryGroup p q R ↔
      ∀ z w : p ⊕ q → R, star (g *ᵥ z) ⬝ᵥ (indefiniteDiagonal p q R *ᵥ (g *ᵥ w)) =
        star z ⬝ᵥ (indefiniteDiagonal p q R *ᵥ w) := by
  simp_rw [← star_dotProduct_conjTranspose_mul_mul_mulVec, ← star_eq_conjTranspose,
    mem_indefiniteUnitaryGroup_iff]
  refine ⟨fun h z w => by rw [h], fun h => ?_⟩
  ext i j
  simpa [Pi.single_star, mulVec_single] using h (Pi.single i 1) (Pi.single j 1)

/-- A matrix `M` with `star M * J * M = J` has left inverse `J * star M * J`. -/
theorem indefiniteDiagonal_mul_star_mul_indefiniteDiagonal_mul_eq_one
    {M : Matrix (p ⊕ q) (p ⊕ q) R}
    (hM : star M * indefiniteDiagonal p q R * M = indefiniteDiagonal p q R) :
    indefiniteDiagonal p q R * star M * indefiniteDiagonal p q R * M = 1 := by
  rw [Matrix.mul_assoc _ (indefiniteDiagonal p q R), Matrix.mul_assoc, ← Matrix.mul_assoc _ _ M,
    hM, indefiniteDiagonal_mul_indefiniteDiagonal]

/-- **The inverse of an element of `U(p, q)`** is `J * star g * J`. -/
theorem coe_inv_of_mem_indefiniteUnitaryGroup {g : GL (p ⊕ q) R}
    (hg : g ∈ indefiniteUnitaryGroup p q R) :
    ((g⁻¹ : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) =
      indefiniteDiagonal p q R * star (g : Matrix (p ⊕ q) (p ⊕ q) R) *
        indefiniteDiagonal p q R :=
  Units.inv_eq_of_mul_eq_one_left <|
    indefiniteDiagonal_mul_star_mul_indefiniteDiagonal_mul_eq_one
      (mem_indefiniteUnitaryGroup_iff.mp hg)

/-- **`U(p, q)` is stable under the conjugate transpose**, hence under `g ↦ (star g)⁻¹`. -/
@[simp]
theorem star_mem_indefiniteUnitaryGroup_iff {g : GL (p ⊕ q) R} :
    star g ∈ indefiniteUnitaryGroup p q R ↔ g ∈ indefiniteUnitaryGroup p q R := by
  suffices h : ∀ g : GL (p ⊕ q) R, g ∈ indefiniteUnitaryGroup p q R →
      star g ∈ indefiniteUnitaryGroup p q R from
    ⟨fun hg => star_star g ▸ h _ hg, h g⟩
  intro g hg
  have h := g.mul_inv
  rw [coe_inv_of_mem_indefiniteUnitaryGroup hg] at h
  rw [mem_indefiniteUnitaryGroup_iff, Units.coe_star, star_star]
  calc (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * star (g : Matrix _ _ R) =
        (g : Matrix (p ⊕ q) (p ⊕ q) R) * (indefiniteDiagonal p q R * star (g : Matrix _ _ R) *
          indefiniteDiagonal p q R) * indefiniteDiagonal p q R := by
        simp [Matrix.mul_assoc]
    _ = indefiniteDiagonal p q R := by rw [h, Matrix.one_mul]

/-- **The determinant of an element of `U(p, q)` is unitary**: `star (det g) * det g = 1`. -/
theorem det_of_mem_indefiniteUnitaryGroup {g : GL (p ⊕ q) R}
    (hg : g ∈ indefiniteUnitaryGroup p q R) :
    (g : Matrix (p ⊕ q) (p ⊕ q) R).det ∈ unitary R := by
  have hJ : (indefiniteDiagonal p q R).det * (indefiniteDiagonal p q R).det = 1 := by
    rw [← det_mul, indefiniteDiagonal_mul_indefiniteDiagonal, det_one]
  have h := congrArg det (mem_indefiniteUnitaryGroup_iff.mp hg)
  rw [det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose] at h
  rw [Unitary.mem_iff_star_mul_self]
  linear_combination (indefiniteDiagonal p q R).det * h +
    (1 - star (g : Matrix (p ⊕ q) (p ⊕ q) R).det * (g : Matrix (p ⊕ q) (p ⊕ q) R).det) * hJ

/-- A diagonal matrix `diag(d)` satisfies `star (diag d) * J * diag d = J` exactly when every
diagonal entry is unitary. -/
theorem star_diagonal_mul_indefiniteDiagonal_mul_diagonal_eq_iff {d : p ⊕ q → R} :
    star (diagonal d) * indefiniteDiagonal p q R * diagonal d = indefiniteDiagonal p q R ↔
      ∀ i, star (d i) * d i = 1 := by
  rw [indefiniteDiagonal, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    diagonal_mul_diagonal, diagonal_eq_diagonal_iff]
  refine forall_congr' fun i => ?_
  rcases i with i | i <;> simp [neg_eq_iff_eq_neg]

namespace IndefiniteUnitaryGroup

/-- Two elements of `U(p, q)` are equal when their underlying matrices are equal. -/
@[ext]
theorem ext {g h : indefiniteUnitaryGroup p q R}
    (H : ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) = ((h : GL (p ⊕ q) R) : Matrix _ _ R)) :
    g = h :=
  Subtype.ext <| Units.ext H

/-- The element of `U(p, q)` given by a matrix `M` with `star M * J * M = J`. Such a matrix is
invertible, with inverse `J * star M * J`. -/
def mk (M : Matrix (p ⊕ q) (p ⊕ q) R)
    (hM : star M * indefiniteDiagonal p q R * M = indefiniteDiagonal p q R) :
    indefiniteUnitaryGroup p q R :=
  have h := indefiniteDiagonal_mul_star_mul_indefiniteDiagonal_mul_eq_one hM
  ⟨⟨M, _, mul_eq_one_comm.mp h, h⟩, hM⟩

@[simp]
theorem coe_mk (M : Matrix (p ⊕ q) (p ⊕ q) R)
    (hM : star M * indefiniteDiagonal p q R * M = indefiniteDiagonal p q R) :
    ((mk M hM : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) = M :=
  (rfl)

/-- The block-diagonal matrix `diag(A, B)` with `A` and `B` unitary lies in `U(p, q)`. -/
private theorem star_fromBlocks_mul_indefiniteDiagonal_mul_fromBlocks
    (AB : unitaryGroup p R × unitaryGroup q R) :
    star (fromBlocks (AB.1 : Matrix p p R) 0 0 (AB.2 : Matrix q q R)) *
        indefiniteDiagonal p q R * fromBlocks (AB.1 : Matrix p p R) 0 0 AB.2 =
      indefiniteDiagonal p q R := by
  rw [indefiniteDiagonal_eq_fromBlocks, star_eq_conjTranspose, fromBlocks_conjTranspose]
  simp [fromBlocks_multiply, ← star_eq_conjTranspose]

variable (p q R) in
/-- **The block-diagonal embedding** `(A, B) ↦ diag(A, B)` of `U(p) × U(q)` in `U(p, q)`, the
block-diagonal sum `Matrix.UnitaryGroup.sum` viewed in `U(p, q)`. Its image is the set of elements
of `U(p, q)` whose lower left block vanishes
(`Matrix.IndefiniteUnitaryGroup.mem_range_ofUnitaryProd_iff`). -/
def ofUnitaryProd : unitaryGroup p R × unitaryGroup q R →* indefiniteUnitaryGroup p q R where
  toFun AB := mk (UnitaryGroup.sum AB) <| by
    rw [UnitaryGroup.coe_sum]
    exact star_fromBlocks_mul_indefiniteDiagonal_mul_fromBlocks AB
  map_one' := ext <| by simp [-UnitaryGroup.coe_sum]
  map_mul' AB AB' := ext <| by simp [-UnitaryGroup.coe_sum]

@[simp]
theorem coe_ofUnitaryProd (AB : unitaryGroup p R × unitaryGroup q R) :
    ((ofUnitaryProd p q R AB : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) =
      fromBlocks (AB.1 : Matrix p p R) 0 0 (AB.2 : Matrix q q R) :=
  UnitaryGroup.coe_sum AB

theorem ofUnitaryProd_injective : Function.Injective (ofUnitaryProd p q R) := fun _ _ h =>
  UnitaryGroup.sum_injective <| Subtype.ext <| IndefiniteUnitaryGroup.ext_iff.mp h

/-- **The image of `U(p) × U(q)`.** An element of `U(p, q)` is block diagonal, with unitary
blocks, as soon as its lower left block vanishes. For `p` a singleton, these are the elements
of `U(p, q)` fixing the line spanned by the first basis vector. -/
theorem mem_range_ofUnitaryProd_iff {g : indefiniteUnitaryGroup p q R} :
    g ∈ (ofUnitaryProd p q R).range ↔
      ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R).toBlocks₂₁ = 0 := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨AB, rfl⟩
    simp
  have hM := mem_indefiniteUnitaryGroup_iff.mp g.2
  set M := ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R)
  rw [← fromBlocks_toBlocks M, h, indefiniteDiagonal_eq_fromBlocks, star_eq_conjTranspose,
    fromBlocks_conjTranspose] at hM
  simp only [fromBlocks_multiply, conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_zero, add_zero, zero_add,
    fromBlocks_inj] at hM
  obtain ⟨hA, hB, -, hD⟩ := hM
  have hAu : M.toBlocks₁₁ ∈ unitaryGroup p R := mem_unitaryGroup_iff'.mpr hA
  have hB0 : M.toBlocks₁₂ = 0 := by
    rw [← Matrix.one_mul M.toBlocks₁₂, ← mem_unitaryGroup_iff.mp hAu, Matrix.mul_assoc,
      star_eq_conjTranspose, hB, Matrix.mul_zero]
  rw [hB0, conjTranspose_zero, Matrix.zero_mul, zero_add, neg_inj] at hD
  refine ⟨(⟨_, hAu⟩, ⟨_, mem_unitaryGroup_iff'.mpr hD⟩), ext ?_⟩
  rw [coe_ofUnitaryProd, ← h, ← hB0]
  exact fromBlocks_toBlocks M

end IndefiniteUnitaryGroup

end CommRing

section Field

variable [Field R] [StarRing R]

namespace IndefiniteUnitaryGroup

/-- **The `J`-reflection in a vector `v`.** For a vector `v` whose value `s = ⟨v, v⟩` under the
indefinite Hermitian form is nonzero, the reflection `1 - (2 / s) • v (star v ᵥ* J)` in the
`J`-orthogonal complement of `v`, as an element of `U(p, q)`. -/
def reflection (v : p ⊕ q → R) (hs : star v ⬝ᵥ (indefiniteDiagonal p q R *ᵥ v) ≠ 0) :
    indefiniteUnitaryGroup p q R :=
  mk (1 - (2 / (star v ⬝ᵥ (indefiniteDiagonal p q R *ᵥ v))) •
      vecMulVec v (star v ᵥ* indefiniteDiagonal p q R)) <| by
    set J := indefiniteDiagonal p q R
    set s := star v ⬝ᵥ (J *ᵥ v)
    set P := vecMulVec v (star v ᵥ* J)
    set c := 2 / s
    have hss : star s = s := isHermitian_indefiniteDiagonal.star_dotProduct_mulVec_comm v v
    have hc : star c = c := by simp [c, hss]
    have hPJ : star P * J = J * P := by
      simp [P, J, star_eq_conjTranspose, conjTranspose_vecMulVec, star_vecMul, vecMulVec_mul,
        mul_vecMulVec, isHermitian_indefiniteDiagonal.eq]
    have hPP : P * P = s • P := by
      rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, vecMulVec_smul]
    have hcs : c * c * s = 2 * c := by
      simp only [c]
      field_simp
    have hHJ : star (1 - c • P) * J = J * (1 - c • P) := by simp [sub_mul, mul_sub, hc, hPJ]
    calc star (1 - c • P) * J * (1 - c • P) = J * ((1 - c • P) * (1 - c • P)) := by
          rw [hHJ, Matrix.mul_assoc]
      _ = J * (1 - (2 * c - c * c * s) • P) := by
          congr 1
          simp only [sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul, smul_mul_smul_comm, hPP,
            smul_smul]
          module
      _ = J := by rw [hcs, sub_self, zero_smul, sub_zero, Matrix.mul_one]

@[simp]
theorem coe_reflection (v : p ⊕ q → R) (hs : star v ⬝ᵥ (indefiniteDiagonal p q R *ᵥ v) ≠ 0) :
    ((reflection v hs : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) =
      1 - (2 / (star v ⬝ᵥ (indefiniteDiagonal p q R *ᵥ v))) •
        vecMulVec v (star v ᵥ* indefiniteDiagonal p q R) :=
  (rfl)

variable [CharZero R]

/-- A matrix commuting with every element of `U(p, q)` is diagonal: it commutes with the sign
change of each coordinate. -/
private theorem eq_diagonal_of_forall_commute {M : Matrix (p ⊕ q) (p ⊕ q) R}
    (comm : ∀ h : indefiniteUnitaryGroup p q R,
      ((h : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) * M =
        M * ((h : GL (p ⊕ q) R) : Matrix _ _ R)) :
    M = diagonal fun i => M i i := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  have h := congrFun (congrFun (comm (mk (diagonal (Function.update 1 i (-1)))
    (star_diagonal_mul_indefiniteDiagonal_mul_diagonal_eq_iff.mpr fun k => by
      by_cases hk : k = i <;> simp [hk]))) i) j
  simp only [coe_mk, diagonal_mul, mul_diagonal, Function.update_self,
    Function.update_of_ne hij.symm, Pi.one_apply, mul_one, neg_one_mul] at h
  rw [diagonal_apply_ne _ hij]
  exact neg_eq_self.mp h

/-- A diagonal matrix commuting with every element of `U(p, q)` has constant diagonal: it commutes
with the reflection in `eᵢ + 2 eⱼ`, whose `(i, j)` entry is nonzero. -/
private theorem apply_self_eq_of_forall_commute {d : p ⊕ q → R}
    (comm : ∀ h : indefiniteUnitaryGroup p q R,
      ((h : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) * diagonal d =
        diagonal d * ((h : GL (p ⊕ q) R) : Matrix _ _ R))
    (i j : p ⊕ q) :
    d i = d j := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  set e : p ⊕ q → R := Sum.elim (fun _ => 1) fun _ => -1
  set v : p ⊕ q → R := Pi.single i 1 + Pi.single j 2
  have hs : star v ⬝ᵥ (indefiniteDiagonal p q R *ᵥ v) = e i + 4 * e j := by
    simp [indefiniteDiagonal, v, mulVec_add, dotProduct_add, hij, hij.symm, e]
    ring
  have he (k : p ⊕ q) : e k = 1 ∨ e k = -1 := by rcases k with k | k <;> simp [e]
  have hs0 : e i + 4 * e j ≠ 0 := by
    rcases he i with h1 | h1 <;> rcases he j with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have h := congrFun (congrFun (comm (reflection v (hs ▸ hs0))) i) j
  rw [coe_reflection, hs, mul_diagonal, diagonal_mul, mul_comm (d i)] at h
  refine (mul_left_cancel₀ ?_ h).symm
  have hej : e j ≠ 0 := by rcases he j with h2 | h2 <;> simp [h2]
  simp [indefiniteDiagonal, vecMulVec_apply, vecMul_diagonal, v, hij, hij.symm, hs0, hej, e]

/-- **The centre of `U(p, q)`** over a field of characteristic zero consists of the unit
scalars `c • 1` with `star c * c = 1`. -/
theorem mem_center_iff {g : indefiniteUnitaryGroup p q R} :
    g ∈ Subgroup.center (indefiniteUnitaryGroup p q R) ↔
      ∃ c ∈ unitary R, ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) = scalar (p ⊕ q) c := by
  refine ⟨fun hg => ?_, fun ⟨c, _, hc⟩ => Subgroup.mem_center_iff.mpr fun h => ?_⟩
  swap
  · ext1
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hc]
    exact ((scalar_commute c (fun _ => Commute.all _ _) _).eq).symm
  have hg' := mem_indefiniteUnitaryGroup_iff.mp g.2
  set M := ((g : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R)
  have comm (h : indefiniteUnitaryGroup p q R) :
      ((h : GL (p ⊕ q) R) : Matrix (p ⊕ q) (p ⊕ q) R) * M =
        M * ((h : GL (p ⊕ q) R) : Matrix _ _ R) :=
    IndefiniteUnitaryGroup.ext_iff.mp (Subgroup.mem_center_iff.mp hg h)
  have hdiag := eq_diagonal_of_forall_commute comm
  rcases isEmpty_or_nonempty (p ⊕ q) with hne | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_mem _, Subsingleton.elim _ _⟩
  have hM : M = diagonal fun _ => M i₀ i₀ := hdiag.trans <| congrArg diagonal <| funext fun i =>
    apply_self_eq_of_forall_commute (d := fun i => M i i) (fun h => hdiag ▸ comm h) i i₀
  refine ⟨M i₀ i₀, Unitary.mem_iff_star_mul_self.mpr ?_, by rw [scalar_apply]; exact hM⟩
  rw [hM] at hg'
  exact star_diagonal_mul_indefiniteDiagonal_mul_diagonal_eq_iff.mp hg' i₀

end IndefiniteUnitaryGroup

end Field

end Matrix

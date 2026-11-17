/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.UnitaryGroup
import TauCeti.Algebra.Star.Unitary
import TauCeti.GroupTheory.Commutator

/-!
# Coordinate action of unitary matrices and algebraic identities in `SU(n)`

`Matrix.UnitaryGroup.toLinearEquiv_apply` describes the linear equivalence associated to a unitary
matrix by its matrix-vector action, and `Matrix.permMatrix_mem_unitary` records that
permutation matrices over a possibly noncommutative star semiring are unitary. Accordingly
`Matrix.permutationUnitary` is `Matrix.permMatrixHom` with values in the unitary matrices.

`Matrix.conjTranspose_mul_mul_mem_unitary` transfers unitarity along a possibly rectangular
matrix whose conjugate transpose is a two-sided inverse.

`Matrix.diagonal_update_one_mem_unitary_iff` says that a diagonal matrix with all diagonal entries
`1` except one is unitary exactly when that entry is. For `Matrix.specialUnitaryGroup`, this file
records basic inverse coercions (`coe_inv`, `coe_mul_coe_inv`, `coe_inv_mul_coe`), subsingleton
triviality on subsingleton index types (`subsingleton_of_subsingleton`), centrality of scalar
matrices (`mem_center_of_coe_eq_scalar`), scalar-rescaling invariance of commutators
(`coe_commutatorElement_of_eq_smul`), and algebraic identities for the twisted commutator relation
`⁅A, B⁆ = ζ • 1` (`coe_commutatorElement_eq_smul_one_iff`, `commutator_conj_eq_smul_one`,
`commute_mul_inv_of_commutator_eq_smul_one`, `conj_pow_eq_star_pow_smul`,
`conj_pow_eq_inv_pow_smul`).
-/

public section

universe u v

namespace Matrix.UnitaryGroup

variable {R : Type u} [CommRing R] [StarRing R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The linear equivalence associated to a unitary matrix acts by matrix-vector
multiplication. -/
@[simp]
theorem toLinearEquiv_apply (U : Matrix.unitaryGroup n R) (x : n → R) :
    Matrix.UnitaryGroup.toLinearEquiv U x = Matrix.toLin' (U : Matrix n n R) x := rfl

end Matrix.UnitaryGroup

namespace Matrix

/-- Conjugation by a possibly rectangular matrix with conjugate-transpose inverse preserves
unitarity over a possibly noncommutative star semiring. -/
theorem conjTranspose_mul_mul_mem_unitary
    {R m n : Type*} [Semiring R] [StarRing R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : Matrix m n R) (hP : Pᴴ * P = 1) (hP' : P * Pᴴ = 1)
    {X : Matrix m m R} (hX : X ∈ unitary (Matrix m m R)) :
    Pᴴ * X * P ∈ unitary (Matrix n n R) := by
  have hcancel (Y Z : Matrix m m R) :
      (Pᴴ * Y * P) * (Pᴴ * Z * P) = Pᴴ * (Y * Z) * P := by
    calc
      _ = Pᴴ * (Y * (P * Pᴴ) * Z) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP', Matrix.mul_one]
  rw [Unitary.mem_iff, star_eq_conjTranspose] at hX ⊢
  constructor <;>
    simp only [conjTranspose_mul, conjTranspose_conjTranspose,
      ← Matrix.mul_assoc Pᴴ Xᴴ P, hcancel, hX.1, hX.2, Matrix.mul_one, hP]

/-- A diagonal matrix whose diagonal entries are all `1` except the `i`-th one is unitary exactly
when its `i`-th diagonal entry is unitary. -/
theorem diagonal_update_one_mem_unitary_iff {n α : Type*} [Fintype n] [DecidableEq n]
    [Semiring α] [StarRing α] {a : α} {i : n} :
    diagonal (Function.update (1 : n → α) i a) ∈ unitary (Matrix n n α) ↔ a ∈ unitary α := by
  simp [Pi.mem_unitary_iff, Function.forall_update_iff]

variable {R : Type u} [Semiring R] [StarRing R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- A permutation matrix is unitary: its conjugate transpose is the permutation matrix of the
inverse permutation. -/
@[simp]
theorem permMatrix_mem_unitary (σ : Equiv.Perm n) :
    σ.permMatrix R ∈ unitary (Matrix n n R) := by
  simp [Unitary.mem_iff, star_eq_conjTranspose, ← permMatrix_mul]

/-- A permutation as a unitary matrix: `permutationUnitary σ` is the permutation matrix of `σ⁻¹`,
which makes this a homomorphism with Mathlib's convention for multiplication in `Equiv.Perm`. -/
def permutationUnitary : Equiv.Perm n →* unitary (Matrix n n R) :=
  (permMatrixHom (R := R)).codRestrict _ fun σ => by
    rw [permMatrixHom_apply]
    exact permMatrix_mem_unitary σ⁻¹

/-- The matrix underlying `permutationUnitary σ` is the permutation matrix of `σ⁻¹`. -/
@[simp]
theorem coe_permutationUnitary (σ : Equiv.Perm n) :
    (permutationUnitary (R := R) σ : Matrix n n R) = σ⁻¹.permMatrix R :=
  (rfl)

namespace specialUnitaryGroup

section CommRing

variable {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]

/-- The matrix underlying the inverse of a special unitary matrix is its conjugate transpose. -/
theorem coe_inv (g : specialUnitaryGroup n α) :
    ((g⁻¹ : specialUnitaryGroup n α) : Matrix n n α) = star (g : Matrix n n α) :=
  (rfl)

/-- Multiplying the matrix underlying `g ∈ SU(n)` on the right by the matrix underlying `g⁻¹`
gives `1`. -/
@[simp]
theorem coe_mul_coe_inv (g : specialUnitaryGroup n α) :
    (g : Matrix n n α) * ((g⁻¹ : specialUnitaryGroup n α) : Matrix n n α) = 1 := by
  rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]

/-- Multiplying the matrix underlying `g ∈ SU(n)` on the left by the matrix underlying `g⁻¹`
gives `1`. -/
@[simp]
theorem coe_inv_mul_coe (g : specialUnitaryGroup n α) :
    ((g⁻¹ : specialUnitaryGroup n α) : Matrix n n α) * (g : Matrix n n α) = 1 := by
  rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]

/-- For a subsingleton index type `n`, `specialUnitaryGroup n α` has at most one element: the
determinant-one condition forces the unique entry (if any) to be `1`. -/
instance subsingleton_of_subsingleton [Subsingleton n] :
    Subsingleton (specialUnitaryGroup n α) := by
  refine ⟨fun A B => Subtype.ext <| Matrix.ext fun i j => ?_⟩
  have hAdet := (mem_specialUnitaryGroup_iff.mp A.2).2
  have hBdet := (mem_specialUnitaryGroup_iff.mp B.2).2
  rw [det_eq_elem_of_subsingleton _ i] at hAdet hBdet
  rw [Subsingleton.elim j i, hAdet, hBdet]

/-- Any special unitary matrix equal to a scalar matrix lies in the center of the special unitary
group. -/
theorem mem_center_of_coe_eq_scalar {g : specialUnitaryGroup n α} {c : α}
    (hg : (g : Matrix n n α) = scalar n c) :
    g ∈ Subgroup.center (specialUnitaryGroup n α) :=
  Subgroup.mem_center_iff.mpr fun h => Subtype.ext <| by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, hg,
      (scalar_commute c (Commute.all c) (h : Matrix n n α)).eq]

open scoped commutatorElement in
/-- Rescaling two matrices by unitary scalars into `specialUnitaryGroup n α` leaves their
commutator `U * V * star U * star V` unchanged. -/
theorem coe_commutatorElement_of_eq_smul {c₁ c₂ : α} (hc₁ : c₁ ∈ unitary α)
    (hc₂ : c₂ ∈ unitary α) {U V : Matrix n n α} {A B : specialUnitaryGroup n α}
    (hA : (A : Matrix n n α) = c₁ • U) (hB : (B : Matrix n n α) = c₂ • V) :
    (↑⁅A, B⁆ : Matrix n n α) = U * V * star U * star V := by
  rw [commutatorElement_def, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    coe_inv, coe_inv, hA, hB,
    Unitary.smul_mul_mul_star_smul hc₁,
    Matrix.mul_assoc U, Matrix.mul_assoc U,
    Unitary.smul_mul_mul_star_smul hc₂,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]

open scoped commutatorElement in
/-- In `specialUnitaryGroup n α`, the commutator equation `⁅A, B⁆ = ζ • 1` is equivalent to the
twisted commutation relation `A * B = ζ • (B * A)`. -/
theorem coe_commutatorElement_eq_smul_one_iff {ζ : α} {A B : specialUnitaryGroup n α} :
    (↑⁅A, B⁆ : Matrix n n α) = ζ • 1 ↔
      (A : Matrix n n α) * (B : Matrix n n α) = ζ • ((B : Matrix n n α) * A) := by
  constructor
  · intro h
    calc (A : Matrix n n α) * B
        = (↑⁅A, B⁆ : Matrix n n α) * (B : Matrix n n α) * A := by
          simp only [commutatorElement_def, ← Submonoid.coe_mul, inv_mul_cancel_right]
      _ = ζ • ((B : Matrix n n α) * A) := by
          rw [h, Matrix.smul_mul, Matrix.one_mul, smul_mul_assoc]
  · intro h
    calc (↑⁅A, B⁆ : Matrix n n α)
        = (A : Matrix n n α) * B * ((A⁻¹ : specialUnitaryGroup n α) : Matrix n n α) *
            ((B⁻¹ : specialUnitaryGroup n α) : Matrix n n α) := by
          rw [commutatorElement_def, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
      _ = ζ • ((B : Matrix n n α) * ((A : Matrix n n α) *
            ((A⁻¹ : specialUnitaryGroup n α) : Matrix n n α)) *
            ((B⁻¹ : specialUnitaryGroup n α) : Matrix n n α)) := by
          rw [h, smul_mul_assoc, smul_mul_assoc, Matrix.mul_assoc (B : Matrix n n α)]
      _ = ζ • 1 := by
          rw [coe_mul_coe_inv, Matrix.mul_one, coe_mul_coe_inv]

open scoped commutatorElement in
/-- Simultaneous conjugation in `specialUnitaryGroup n α` preserves the twisted commutator
relation `⁅A, B⁆ = ζ • 1`. -/
theorem commutator_conj_eq_smul_one {ζ : α} {A B : specialUnitaryGroup n α}
    (hAB : (↑⁅A, B⁆ : Matrix n n α) = ζ • 1) (u : specialUnitaryGroup n α) :
    (↑⁅u * A * u⁻¹, u * B * u⁻¹⁆ : Matrix n n α) = ζ • 1 := by
  have h : ⁅u * A * u⁻¹, u * B * u⁻¹⁆ = u * ⁅A, B⁆ * u⁻¹ := by
    rw [← MulAut.conj_apply u A, ← MulAut.conj_apply u B, ← MulAut.conj_apply u ⁅A, B⁆,
      ← map_commutatorElement]
  rw [h, Submonoid.coe_mul, Submonoid.coe_mul, hAB, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, coe_mul_coe_inv]

open scoped commutatorElement in
/-- If `B₀` and `B` both satisfy `⁅A₀, -⁆ = ζ • 1` in `specialUnitaryGroup n α`, then `A₀`
commutes with `B * B₀⁻¹`. -/
theorem commute_mul_inv_of_commutator_eq_smul_one {ζ : α} {A₀ B₀ B : specialUnitaryGroup n α}
    (hrel₀ : (↑⁅A₀, B₀⁆ : Matrix n n α) = ζ • 1)
    (hrel : (↑⁅A₀, B⁆ : Matrix n n α) = ζ • 1) :
    Commute A₀ (B * B₀⁻¹) := by
  have hcen : ⁅A₀, B₀⁆ ∈ Subgroup.center (specialUnitaryGroup n α) :=
    mem_center_of_coe_eq_scalar (by rw [hrel₀, scalar_apply, smul_one_eq_diagonal])
  exact TauCeti.commute_mul_inv_of_commutatorElement_eq (Subtype.ext (hrel.trans hrel₀.symm))
    (Subgroup.mem_center_iff.mp hcen B₀) (Subgroup.mem_center_iff.mp hcen B)

open scoped commutatorElement in
/-- If `⁅A, B⁆ = ζ • 1` in `specialUnitaryGroup n α`, then conjugating `A` by `B ^ m` scales `A` by
`(star ζ) ^ m`. -/
theorem conj_pow_eq_star_pow_smul {ζ : α} {A B : specialUnitaryGroup n α}
    (hAB : (↑⁅A, B⁆ : Matrix n n α) = ζ • 1) (m : ℕ) :
    ((B ^ m * A * (B ^ m)⁻¹ : specialUnitaryGroup n α) : Matrix n n α) =
      (star ζ) ^ m • (A : Matrix n n α) := by
  have hBA : (↑⁅B, A⁆ : Matrix n n α) = (star ζ) • 1 := by
    rw [← commutatorElement_inv, coe_inv, hAB, star_smul, star_one]
  have hcen : ⁅B, A⁆ ∈ Subgroup.center (specialUnitaryGroup n α) :=
    mem_center_of_coe_eq_scalar (by rw [hBA, scalar_apply, smul_one_eq_diagonal])
  rw [Commute.pow_mul_mul_inv_pow_eq_commutatorElement_pow_mul
    (Subgroup.mem_center_iff.mp hcen B) m, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    hBA, smul_pow, one_pow, Matrix.smul_mul, Matrix.one_mul]

end CommRing

open scoped commutatorElement in
/-- Over a star field, if `⁅A, B⁆ = ζ • 1` in `specialUnitaryGroup n α`, then conjugating `A` by
`B ^ m` scales `A` by `(ζ⁻¹) ^ m`. No `ζ ≠ 0` hypothesis is needed: if `n` is empty both sides
are the unique `0 × 0` matrix, and otherwise unitarity of `ζ • 1` gives `ζ * star ζ = 1`. -/
theorem conj_pow_eq_inv_pow_smul {n α : Type*} [Fintype n] [DecidableEq n] [Field α] [StarRing α]
    {ζ : α} {A B : specialUnitaryGroup n α}
    (hAB : (↑⁅A, B⁆ : Matrix n n α) = ζ • 1) (m : ℕ) :
    ((B ^ m * A * (B ^ m)⁻¹ : specialUnitaryGroup n α) : Matrix n n α) =
      (ζ⁻¹) ^ m • (A : Matrix n n α) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact Subsingleton.elim _ _
  have hstar : star ζ = ζ⁻¹ := by
    have hunit := (Unitary.mem_iff.mp (specialUnitaryGroup_le_unitaryGroup ⁅A, B⁆.2)).2
    have h0 := congr_fun₂ hunit i₀ i₀
    rw [hAB, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, smul_eq_mul,
      mul_one] at h0
    exact eq_inv_of_mul_eq_one_right h0
  rw [conj_pow_eq_star_pow_smul hAB m, hstar]

end specialUnitaryGroup

end Matrix

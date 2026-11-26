/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.IdealEntries

-- Non-public: `noncomm_ring` normalises the conjugation identities below, the Schur complement
-- evaluates `det J`, positive definiteness shows `1 + A Aᵀ` is invertible, `Fintype.equivFin`
-- supplies an auxiliary linear order, and `Matrix.subTransposeEqEquiv` builds the correction in
-- the proof of `exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero`, but no statement
-- mentions any of them.
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Fintype.EquivFin
import TauCeti.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.NoncommRing

/-!
# The canonical skew-symmetric matrix as a unit, and block matrices in the symplectic group

Mathlib's `Matrix.J` satisfies `J * J = -1`, so it is a unit with inverse `-J`, and its
determinant is `1`. This file records that unit and the conjugation cancellation it supports —
`X = J * Y * J⁻¹` iff `X * J = J * Y` — and solves the symplectic inverse formula
`SymplecticGroup.inv_eq_symplectic_inv` for the transpose, `Aᵀ = J * A⁻¹ * J⁻¹`.
Conjugation by `J` is the shape the matrix exponential consumes:
the exponential does not interact with `Aᵀ * J = J * (-A)`, but it does turn `Aᵀ = J * (-A) * J⁻¹`
into `(exp A)ᵀ = J * (exp A)⁻¹ * J⁻¹`.

Read entrywise, `Jᵀ = -J` and `J * Jᵀ = 1` become the antisymmetry of the entries and the pairing
of a row of `J` with itself; summing the latter over all rows contracts `J` against itself to
`2 * card l`, the loop value of the symplectic Brauer diagrams up to sign. Read entrywise in the
same way, `Jᵀ * J = 1` is the orthonormality of the columns of `J`.

It also records membership in `Matrix.symplecticGroup` of three families of block matrices, each a
specialisation of `SymplecticGroup.fromBlocks_mem_iff`.

## Main definitions

* `TauCeti.Symplectic.coordSign`: the sign of a native coordinate, `-1` on the `e`-coordinates
  and `1` on the `f`-coordinates.

## Main results

* `Matrix.J_mul_neg_J`, `Matrix.neg_J_mul_J` and `Matrix.isUnit_J`: the canonical skew-symmetric
  matrix is a unit, with inverse `-J`.
* `Matrix.J_mul_fromBlocks_zero₁₂_zero₂₁`: left multiplication by `J` turns a block diagonal
  matrix `[[A, 0], [0, D]]` into the antidiagonal matrix `[[0, -D], [A, 0]]`.
* `Matrix.det_J`: its determinant is `1`.
* `Matrix.star_J` and `Matrix.J_mem_unitaryGroup`: over any star ring its adjoint is `-J`, so
  it is unitary (orthogonal over `ℝ`).
* `Matrix.reindex_sumCongr_J`: reindexing both halves of `J` along an equivalence preserves `J`.
* `Matrix.J_apply_swap` and `Matrix.sum_J_mul_J`: the two entrywise identities for `J`, its
  antisymmetry and the pairing of a row with itself; `Matrix.sum_sum_J_mul_J` is the double sum of
  the latter, `tr (J * Jᵀ) = 2 * card l`.
* `Matrix.J_apply_eq_zero_of_ne_swap` and `Matrix.J_apply_swap_ne_zero`: the nonzero entries of
  `J` are exactly those at the pairs `(x, x.swap)`.
* `Matrix.J_apply_eq_ite`: the entry of `J` at `(a, a.swap)` is the sign
  `TauCeti.Symplectic.coordSign a` of the coordinate `a`, `-1` on `inl i` and `1` on `inr i`.
* `Matrix.sum_J_apply`: the row sums of `J` are its single nonzero entries.
* `Matrix.sum_J_mul_J_eq_ite`: the columns of `J` are orthonormal, `Jᵀ * J = 1` read entrywise.
* `Matrix.eq_J_conj_iff_mul_J_eq`: cancelling a conjugation by `J`.
* `Matrix.J_mul_mul_J_mul_J`: sandwiching twice by `J` is the identity.
* `Matrix.J_mul_transpose_single_mul_J`: the involution `X ↦ J Xᵀ J` sends the matrix unit
  `E_ab` to `-sgn(a) sgn(b) E_(b', a')`.
* `Matrix.transpose_mul_J_mul_transpose` and `Matrix.mul_J_mul_transpose_apply_self`: the
  congruence transform `C * J * Cᵀ` of `J` by a rectangular matrix is alternating, that is
  antisymmetric with zero diagonal, in every characteristic;
  `Matrix.transpose_mul_J_mul_transpose_sub_J` and `Matrix.mul_J_mul_transpose_sub_J_apply_self`
  say the same of the defect `M * J * Mᵀ - J` of a square matrix `M`.
* `Matrix.transpose_transpose_mul_J_sub_J_mul`: the matrix `Ψᵀ * J - J * Ψ` is symmetric, and
  `Matrix.transpose_J_mul_mul_J_sub_J_mul_J_mul` evaluates it on `J * S` for symmetric `S` as
  `2 • S`. For symplectic `Ψ` it factors as `(Ψ + 1)ᵀ * -(J * (Ψ - 1))`
  (`Matrix.transpose_mul_J_sub_J_mul_eq_transpose_mul_neg_J_mul`), so away from the eigenvalue
  `-1` its kernel is the space of fixed vectors of `Ψ`
  (`Matrix.ker_mulVecLin_transpose_mul_J_sub_J_mul`). On every vector its quadratic form is twice
  that of `-(J * Ψ)` (`Matrix.dotProduct_transpose_mul_J_sub_J_mul_mulVec`).
* `Matrix.IsSymm.transpose_mul_mul_add_transpose_mul_J_mul`: if `S` is symmetric and
  `G'ᵀ * J * G + Gᵀ * J * G' = 0`, then `Gᵀ * S * G + Gᵀ * J * G'` is symmetric.
* `Matrix.exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero`: the linearized symplectic
  equation `E + X * J + J * Xᵀ = 0` is solvable with entries of `X` in an ideal `I` for every
  alternating `E` with entries in `I`, without dividing by two.
* `Matrix.one_add_mul_mul_J_mul_transpose_sub_J`: correcting `M` by such an `X` leaves the
  defect `X * E + E * Xᵀ + X * J * Xᵀ + X * E * Xᵀ`, quadratic in `X` and `E`.
* `Matrix.mul_J_mul_transpose_sub_J_mem_of_sub_mem`: a matrix congruent modulo an ideal `𝔞` to
  one whose defect has entries in `𝔞` has defect with entries in `𝔞`.
* `Matrix.one_add_mul_mem_symplecticGroup`: over a square-zero ideal `I`, correcting `M` by
  `1 + X`, where `X` has entries in `I` and `E + X * J + J * Xᵀ = 0`, gives a symplectic matrix
  when `M * J * Mᵀ - J = E`.
* `SymplecticGroup.transpose_eq_J_conj_inv`: the transpose of a symplectic matrix is the
  `J`-conjugate of its inverse; `SymplecticGroup.mem_of_J_conj_eq_transpose` is its converse, a
  matrix whose `J`-conjugate is its inverse transpose is symplectic.
* `SymplecticGroup.mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one`: the symplectic matrices are the
  unitary elements for the symplectic adjoint `A ↦ -(J * Aᵀ * J)`.
* `SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute` and
  `SymplecticGroup.commute_J_of_mem_orthogonalGroup`: among the matrices commuting with `J`, the
  symplectic ones are exactly the orthogonal ones, and an orthogonal symplectic matrix commutes
  with `J`. Any two of the three conditions symplectic, orthogonal and commuting with `J` imply the
  third.
* `SymplecticGroup.mem_iff_toBlocks`: a matrix is symplectic exactly when its blocks satisfy the
  relations `Aᵀ C = Cᵀ A`, `Bᵀ D = Dᵀ B` and `Aᵀ D - Cᵀ B = 1`.
* `SymplecticGroup.fromBlocks_upper_mem`: `fromBlocks 1 B 0 1` for symmetric `B`;
* `SymplecticGroup.fromBlocks_lower_mem`: `fromBlocks 1 0 C 1` for symmetric `C`;
* `SymplecticGroup.fromBlocks_diagonal_mem`: `fromBlocks A 0 0 D` when `Aᵀ * D = 1`.
* `SymplecticGroup.isUnit_det_mul_J_add_J_mul`: for a real symplectic matrix `A`, the matrix
  `A J + J A` is invertible.
-/

public section

open Matrix

namespace TauCeti.Symplectic

variable {l : Type*}

/-- **The sign of a native coordinate** of the standard symplectic space `(l ⊕ l) → R`: `-1` on
the `e`-coordinates `inl i` and `1` on the `f`-coordinates `inr i`. It is the sign of the nonzero
entry of `Matrix.J` in the row of the coordinate (`Matrix.J_apply_eq_ite`), and the sign of the
signed index in Molev's signed indexing of the coordinates. -/
def coordSign : l ⊕ l → ℤ :=
  Sum.elim (fun _ => -1) fun _ => 1

@[simp]
theorem coordSign_inl (i : l) : coordSign (Sum.inl i : l ⊕ l) = -1 :=
  (rfl)

@[simp]
theorem coordSign_inr (i : l) : coordSign (Sum.inr i : l ⊕ l) = 1 :=
  (rfl)

/-- Passing to the paired coordinate changes the sign. -/
@[simp]
theorem coordSign_swap (a : l ⊕ l) : coordSign a.swap = -coordSign a := by
  cases a <;> simp

theorem coordSign_mul_self (a : l ⊕ l) : coordSign a * coordSign a = 1 := by
  cases a <;> simp

end TauCeti.Symplectic

open TauCeti.Symplectic

namespace Matrix

variable (l : Type*) [DecidableEq l] [Fintype l] (R : Type*) [CommRing R]

/-- `J * (-J) = 1`: the companion of `Matrix.J_squared` in the form the conjugation arguments
below use. -/
theorem J_mul_neg_J : J l R * (-J l R) = 1 := by
  rw [mul_neg, J_squared, neg_neg]

/-- `(-J) * J = 1`, the other one-sided inverse identity for `Matrix.J`. -/
theorem neg_J_mul_J : (-J l R) * J l R = 1 := by
  rw [neg_mul, J_squared, neg_neg]

/-- The canonical skew-symmetric matrix is a unit, with inverse `-J`, because `J * J = -1`. -/
theorem isUnit_J : IsUnit (J l R) :=
  ⟨⟨J l R, -J l R, J_mul_neg_J l R, neg_J_mul_J l R⟩, rfl⟩

/-- Left multiplication by `J` turns a block diagonal matrix into an antidiagonal one:
`J * [[A, 0], [0, D]] = [[0, -D], [A, 0]]`. -/
theorem J_mul_fromBlocks_zero₁₂_zero₂₁ (A D : Matrix l l R) :
    J l R * fromBlocks A 0 0 D = fromBlocks 0 (-D) A 0 := by
  simp [J, fromBlocks_multiply]

/-- The canonical skew-symmetric matrix has determinant one. Mathlib records only
`det J * det J = 1` (`Matrix.J_det_mul_J_det`), which leaves the sign open. -/
@[simp]
theorem det_J : (J l R).det = 1 := by
  -- Multiplying by a unipotent block matrix moves the identity block into the corner, where
  -- `Matrix.det_fromBlocks_one₂₂` evaluates the determinant.
  have hJ : J l R * fromBlocks 1 1 0 1 = fromBlocks 0 (-1) 1 1 := by
    simp [J, fromBlocks_multiply]
  simpa [det_fromBlocks_zero₂₁, det_fromBlocks_one₂₂] using congrArg det hJ

omit [Fintype l] in
/-- The adjoint of the canonical skew-symmetric matrix is `-J`: its entries are `0` and `±1`, which
every star ring fixes, so its adjoint is its transpose. -/
@[simp]
theorem star_J [StarRing R] : star (J l R) = -J l R := by
  simp [star_eq_conjTranspose, J, fromBlocks_conjTranspose, fromBlocks_neg]

/-- The canonical skew-symmetric matrix is unitary, orthogonal over `ℝ`: its adjoint is
`-J = J⁻¹`. -/
theorem J_mem_unitaryGroup [StarRing R] : J l R ∈ unitaryGroup (l ⊕ l) R := by
  rw [mem_unitaryGroup_iff', star_J]
  exact neg_J_mul_J l R

/-- Reindexing both halves of the canonical skew-symmetric matrix `Matrix.J` along an equivalence
`e : l₁ ≃ l₂` gives `Matrix.J l₂ R`. -/
theorem reindex_sumCongr_J {l₁ l₂ : Type*} [DecidableEq l₁] [DecidableEq l₂] (e : l₁ ≃ l₂) :
    Matrix.reindex (Equiv.sumCongr e e) (Equiv.sumCongr e e) (J l₁ R) = J l₂ R := by
  ext (i | i) (j | j) <;> simp [Matrix.J, Matrix.one_apply, e.symm.injective.eq_iff]

omit [Fintype l] in
/-- `J` is antisymmetric, entrywise: `Jᵀ = -J` read at a pair of indices. -/
theorem J_apply_swap (x y : l ⊕ l) : J l R y x = -J l R x y := by
  have h := congrFun (congrFun (J_transpose l R) x) y
  simpa only [transpose_apply, Matrix.neg_apply] using h

omit [Fintype l] in
/-- An entry of `J` vanishes unless its two indices are the two members `x` and `x.swap` of one
pair. -/
theorem J_apply_eq_zero_of_ne_swap {x y : l ⊕ l} (h : y ≠ x.swap) : J l R x y = 0 := by
  rcases x with i | i <;> rcases y with j | j <;> simp_all [Matrix.J, eq_comm]

omit [Fintype l] in
/-- The entries of `J` at the two members `x` and `x.swap` of a pair are `-1` or `1`, in
particular nonzero. -/
theorem J_apply_swap_ne_zero [Nontrivial R] (x : l ⊕ l) : J l R x x.swap ≠ 0 := by
  rcases x with i | i <;> simp [Matrix.J]

omit [Fintype l] in
/-- **The standard form in signed terms**: `J a b` is the sign `TauCeti.Symplectic.coordSign a`
when `b` is the coordinate paired with `a`, and vanishes otherwise. -/
theorem J_apply_eq_ite (a b : l ⊕ l) :
    J l R a b = if b = a.swap then (coordSign a : R) else 0 := by
  split_ifs with h
  · subst h
    cases a <;> simp [J]
  · exact J_apply_eq_zero_of_ne_swap l R h

/-- The row sums of `J` are its single nonzero entries: `∑ y, J x y = J x x.swap`. -/
theorem sum_J_apply (x : l ⊕ l) : ∑ y : l ⊕ l, J l R x y = J l R x x.swap :=
  Finset.sum_eq_single x.swap (fun _ _ hy ↦ J_apply_eq_zero_of_ne_swap l R hy) (by simp)

/-- Each row of `J` pairs with itself to `1`, because `J * Jᵀ = 1`. -/
theorem sum_J_mul_J (x : l ⊕ l) : ∑ y : l ⊕ l, J l R x y * J l R x y = 1 := by
  have hJ : J l R * (J l R)ᵀ = 1 := by
    rw [J_transpose]
    exact J_mul_neg_J l R
  have h := congrFun (congrFun hJ x) x
  simpa only [Matrix.mul_apply, one_apply_eq, transpose_apply] using h

/-- The columns of `J` are orthonormal for the standard coordinate dot product, because
`Jᵀ * J = 1`. -/
theorem sum_J_mul_J_eq_ite (y p : l ⊕ l) :
    ∑ x : l ⊕ l, J l R x y * J l R x p = if y = p then 1 else 0 := by
  have hJ : (J l R)ᵀ * J l R = 1 := by
    rw [J_transpose]
    exact neg_J_mul_J l R
  have h := congrFun (congrFun hJ y) p
  simpa only [Matrix.mul_apply, Matrix.one_apply, transpose_apply] using h

/-- **`J` contracted against itself** is `tr (J * Jᵀ) = tr 1 = 2 * card l`: the double sum of
`Matrix.sum_J_mul_J` over the `2 * card l` rows. -/
theorem sum_sum_J_mul_J :
    ∑ x : l ⊕ l, ∑ y : l ⊕ l, J l R x y * J l R x y = (2 * Fintype.card l : R) := by
  rw [Finset.sum_congr rfl fun x _ => sum_J_mul_J l R x, Finset.sum_const, Finset.card_univ,
    Fintype.card_sum, nsmul_eq_mul, mul_one, Nat.cast_add, two_mul]

variable {l R}

/-- **Cancelling a conjugation by `J`**: since `J` is a unit, `X` is the `J`-conjugate of `Y`
exactly when `X * J = J * Y`. This is Mathlib's `Matrix.mul_inv_eq_iff_eq_mul_of_invertible` with
the invertibility of `J` supplied; every identity below that moves a matrix past `J` is an instance
of it. -/
theorem eq_J_conj_iff_mul_J_eq (X Y : Matrix (l ⊕ l) (l ⊕ l) R) :
    X = J l R * Y * (J l R)⁻¹ ↔ X * J l R = J l R * Y := by
  have : Invertible (J l R) := ⟨-J l R, neg_J_mul_J l R, J_mul_neg_J l R⟩
  rw [eq_comm, mul_inv_eq_iff_eq_mul_of_invertible, eq_comm]

/-- Sandwiching twice by the standard symplectic matrix is the identity:
`J * (J * M * J) * J = M`, since `J * J = -1`. -/
theorem J_mul_mul_J_mul_J (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    J l R * (J l R * M * J l R) * J l R = M := by
  calc J l R * (J l R * M * J l R) * J l R = (J l R * J l R) * M * (J l R * J l R) := by
        noncomm_ring
    _ = M := by simp [J_squared]

/-- **The involution `X ↦ J Xᵀ J` on a matrix unit**: it sends `E_ab` to
`-sgn(a) sgn(b) E_(b', a')`, where `b'` and `a'` are the coordinates paired with `b` and `a` and
the signs are those of `TauCeti.Symplectic.coordSign`. -/
theorem J_mul_transpose_single_mul_J (a b : l ⊕ l) :
    J l R * (single a b (1 : R))ᵀ * J l R =
      -(((coordSign a * coordSign b : ℤ) : R) • single b.swap a.swap 1) := by
  have hinv : Function.Involutive (@Sum.swap l l) := Sum.swap_swap
  ext x y
  have hcol (w : l ⊕ l) :
      (J l R * single b a (1 : R)) x w = if w = a then J l R x b else 0 := by
    split_ifs with hw
    · rw [hw, mul_single_apply_same, mul_one]
    · exact mul_single_apply_of_ne (hbj := hw) ..
  rw [transpose_single, Matrix.mul_apply,
    Fintype.sum_congr _ _ fun w => by rw [hcol, ite_mul, zero_mul],
    Fintype.sum_ite_eq' a, J_apply_eq_ite, J_apply_eq_ite,
    Matrix.neg_apply, Matrix.smul_apply, single_apply]
  clear hcol
  by_cases hx : x = b.swap
  · subst hx
    by_cases hy : y = a.swap
    · subst hy
      simp [mul_comm]
    · simp [hy, Ne.symm hy]
  · have h₁ : b ≠ x.swap := fun h => hx (by rw [h, hinv])
    simp [h₁, Ne.symm hx]

/-- The congruence transform `C * J * Cᵀ` of `J` by a rectangular matrix `C` is antisymmetric. -/
theorem transpose_mul_J_mul_transpose {m : Type*} (C : Matrix m (l ⊕ l) R) :
    (C * J l R * Cᵀ)ᵀ = -(C * J l R * Cᵀ) := by
  simp [transpose_mul, Matrix.mul_assoc]

/-- The congruence transform `C * J * Cᵀ` of `J` has zero diagonal, in every characteristic: its
entries are the values of the standard alternating form on pairs of rows of `C`. -/
@[simp]
theorem mul_J_mul_transpose_apply_self {m : Type*} (C : Matrix m (l ⊕ l) R) (i : m) :
    (C * J l R * Cᵀ) i i = 0 := by
  simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, mul_comm]

/-- The defect `M * J * Mᵀ - J` of a matrix is antisymmetric. -/
theorem transpose_mul_J_mul_transpose_sub_J (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    (M * J l R * Mᵀ - J l R)ᵀ = -(M * J l R * Mᵀ - J l R) := by
  rw [transpose_sub, transpose_mul_J_mul_transpose, J_transpose, neg_sub_neg, neg_sub]

/-- For any square matrix `Ψ`, the matrix `Ψᵀ * J - J * Ψ` is symmetric. When `Ψ` is symplectic
it is `(Ψ + 1)ᵀ * (-J * (Ψ - 1))`, the numerator of the Cayley transform of `Ψ`. -/
theorem transpose_transpose_mul_J_sub_J_mul (Ψ : Matrix (l ⊕ l) (l ⊕ l) R) :
    (Ψᵀ * J l R - J l R * Ψ)ᵀ = Ψᵀ * J l R - J l R * Ψ := by
  simp only [transpose_sub, transpose_mul, transpose_transpose, J_transpose, Matrix.neg_mul,
    Matrix.mul_neg]
  abel

/-- For a symplectic matrix `Ψ`, the symmetric matrix `Ψᵀ * J - J * Ψ` factors as
`(Ψ + 1)ᵀ * -(J * (Ψ - 1))`, the numerator of the Cayley transform of `Ψ`. -/
theorem transpose_mul_J_sub_J_mul_eq_transpose_mul_neg_J_mul {Ψ : Matrix (l ⊕ l) (l ⊕ l) R}
    (hΨ : Ψ ∈ symplecticGroup l R) :
    Ψᵀ * J l R - J l R * Ψ = (Ψ + 1)ᵀ * -(J l R * (Ψ - 1)) := by
  rw [transpose_add, transpose_one]
  simp only [Matrix.add_mul, Matrix.mul_neg, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    ← Matrix.mul_assoc, SymplecticGroup.mem_iff'.1 hΨ]
  abel

/-- **The kernel of `Ψᵀ * J - J * Ψ`.** For a symplectic matrix `Ψ` without the eigenvalue `-1`,
the kernel of the symmetric matrix `Ψᵀ * J - J * Ψ` is the space of fixed vectors of `Ψ`. -/
theorem ker_mulVecLin_transpose_mul_J_sub_J_mul {Ψ : Matrix (l ⊕ l) (l ⊕ l) R}
    (hΨ : Ψ ∈ symplecticGroup l R) (h : IsUnit (Ψ + 1).det) :
    LinearMap.ker (Ψᵀ * J l R - J l R * Ψ).mulVecLin = LinearMap.ker (Ψ - 1).mulVecLin := by
  have hinj : Function.Injective ((Ψ + 1)ᵀ * J l R).mulVec := by
    refine mulVec_injective_of_det_mem_nonZeroDivisors (IsUnit.mem_nonZeroDivisors ?_)
    rw [det_mul, det_transpose]
    exact h.mul (isUnit_det_J l R)
  ext v
  simp only [LinearMap.mem_ker, mulVecLin_apply, Matrix.mul_neg, ← Matrix.mul_assoc, neg_mulVec,
    neg_eq_zero, transpose_mul_J_sub_J_mul_eq_transpose_mul_neg_J_mul hΨ]
  rw [← mulVec_mulVec]
  exact ⟨fun hv ↦ hinj (hv.trans (mulVec_zero _).symm), fun hv ↦ by rw [hv, mulVec_zero]⟩

/-- On every vector, the quadratic form of `Bᵀ * J - J * B` is twice the quadratic form of
`-(J * B)`. -/
theorem dotProduct_transpose_mul_J_sub_J_mul_mulVec (B : Matrix (l ⊕ l) (l ⊕ l) R)
    (v : l ⊕ l → R) :
    v ⬝ᵥ (Bᵀ * J l R - J l R * B) *ᵥ v = 2 * (v ⬝ᵥ (-(J l R * B)) *ᵥ v) := by
  have h : v ⬝ᵥ (Bᵀ * J l R) *ᵥ v = -(v ⬝ᵥ (J l R * B) *ᵥ v) := by
    rw [← dotProduct_transpose_mulVec, transpose_mul, transpose_transpose, J_transpose,
      Matrix.neg_mul, neg_mulVec, dotProduct_neg]
  rw [sub_mulVec, dotProduct_sub, h, neg_mulVec, dotProduct_neg]
  ring

/-- For a symmetric `S` and `K = J * S`, the matrix `Kᵀ * J - J * K` is `2 • S`. This is the
linearization at `Ψ = 1` of `Ψᵀ * J - J * Ψ` along `Ψ = 1 + K`. -/
theorem transpose_J_mul_mul_J_sub_J_mul_J_mul {S : Matrix (l ⊕ l) (l ⊕ l) R} (hS : S.IsSymm) :
    (J l R * S)ᵀ * J l R - J l R * (J l R * S) = (2 : R) • S := by
  rw [transpose_mul, J_transpose, hS.eq, ← Matrix.mul_assoc, Matrix.mul_assoc, Matrix.neg_mul,
    J_squared]
  simp only [Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, neg_neg, two_smul, sub_neg_eq_add]

/-- If `S` is symmetric and `G'ᵀ * J * G + Gᵀ * J * G' = 0`, as for the derivative `G'` of a path
`G` of symplectic matrices, then `Gᵀ * S * G + Gᵀ * J * G'` is symmetric. This is the matrix of
the equation `Ψ' = J * S * Ψ` after a change of frame by `G`. -/
theorem IsSymm.transpose_mul_mul_add_transpose_mul_J_mul {S G G' : Matrix (l ⊕ l) (l ⊕ l) R}
    (hS : S.IsSymm) (h : G'ᵀ * J l R * G + Gᵀ * J l R * G' = 0) :
    (Gᵀ * S * G + Gᵀ * J l R * G').IsSymm := by
  simp only [IsSymm, transpose_add, transpose_mul, transpose_transpose, hS.eq, J_transpose,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_right_inj, neg_eq_iff_eq_neg]
  simpa only [Matrix.mul_assoc] using eq_neg_of_add_eq_zero_left h

/-- The defect `M * J * Mᵀ - J` of a matrix has zero diagonal. -/
theorem mul_J_mul_transpose_sub_J_apply_self (M : Matrix (l ⊕ l) (l ⊕ l) R) (i : l ⊕ l) :
    (M * J l R * Mᵀ - J l R) i i = 0 := by
  rw [Matrix.sub_apply, mul_J_mul_transpose_apply_self]
  simpa using mul_J_mul_transpose_apply_self (1 : Matrix (l ⊕ l) (l ⊕ l) R) i

/-- **The linearized symplectic equation is solvable over an ideal.** An alternating matrix `E`
with entries in an ideal `I` is minus the linearized symplectic defect `X * J + J * Xᵀ` of a
matrix `X` with entries in `I`. No division by two is needed, so this holds in every
characteristic. -/
theorem exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero (I : Ideal R)
    (E : Matrix (l ⊕ l) (l ⊕ l) R) (hE_mem : ∀ i j, E i j ∈ I) (hE_transpose : Eᵀ = -E)
    (hE_diag : ∀ i, E i i = 0) :
    ∃ X : Matrix (l ⊕ l) (l ⊕ l) R, (∀ i j, X i j ∈ I) ∧ E + X * J l R + J l R * Xᵀ = 0 := by
  -- The matrix `X` is built from `Matrix.subTransposeEqEquiv`, which avoids division by two.
  let _ : LinearOrder (l ⊕ l) := (Fintype.equivFin (l ⊕ l)).linearOrder
  have hQ : (-E)ᵀ = -(-E) := by rw [transpose_neg, hE_transpose]
  have hQd : ∀ i, (-E) i i = 0 := fun i => by simp [hE_diag]
  let Y : Matrix (l ⊕ l) (l ⊕ l) R := ((subTransposeEqEquiv hQ hQd).symm 0).val
  have hY_mem : ∀ i j, Y i j ∈ I := fun i j => by
    simp only [Y, coe_subTransposeEqEquiv_symm_apply, Pi.zero_apply, zero_add]
    split_ifs
    · exact I.neg_mem (hE_mem i j)
    · exact I.zero_mem
  have hY_sub : Y - Yᵀ = -E := ((subTransposeEqEquiv hQ hQd).symm 0).property
  have hX_mul_J : -(Y * J l R) * J l R = Y := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, J_squared]
    simp
  have hJ_mul_Xt : J l R * (-(Y * J l R))ᵀ = -Yᵀ := by
    simp [transpose_mul, J_transpose, ← Matrix.mul_assoc, J_squared]
  refine ⟨-(Y * J l R), fun i j => ?_, ?_⟩
  · simpa using I.neg_mem (by simpa using mul_mul_apply_mem hY_mem 1 (J l R) i j)
  · rw [hX_mul_J, hJ_mul_Xt]
    calc
      E + Y + -Yᵀ = E + (Y - Yᵀ) := by abel
      _ = 0 := by rw [hY_sub, add_neg_cancel]

/-- **The symplectic defect after a linearized correction.** If `M * J * Mᵀ - J = E` and
`E + X * J + J * Xᵀ = 0`, the defect of `(1 + X) * M` is the sum of the terms quadratic in `X`
and `E`. -/
theorem one_add_mul_mul_J_mul_transpose_sub_J {M E X : Matrix (l ⊕ l) (l ⊕ l) R}
    (hM : M * J l R * Mᵀ - J l R = E) (hX : E + X * J l R + J l R * Xᵀ = 0) :
    (1 + X) * M * J l R * ((1 + X) * M)ᵀ - J l R =
      X * E + E * Xᵀ + X * J l R * Xᵀ + X * E * Xᵀ := by
  calc
    (1 + X) * M * J l R * ((1 + X) * M)ᵀ - J l R =
        (1 + X) * (M * J l R * Mᵀ) * (1 + Xᵀ) - J l R := by
          rw [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
          noncomm_ring
    _ = (1 + X) * (J l R + E) * (1 + Xᵀ) - J l R := by rw [← hM, add_sub_cancel]
    _ = (E + X * J l R + J l R * Xᵀ) +
          (X * E + E * Xᵀ + X * J l R * Xᵀ + X * E * Xᵀ) := by
        noncomm_ring
    _ = _ := by rw [hX, zero_add]

/-- **The symplectic defect modulo an ideal.** If `L` is congruent entrywise to `M` modulo `𝔞`
and the defect `M * J * Mᵀ - J` has entries in `𝔞`, so does the defect of `L`. -/
theorem mul_J_mul_transpose_sub_J_mem_of_sub_mem {𝔞 : Ideal R}
    {L M : Matrix (l ⊕ l) (l ⊕ l) R} (hLM : ∀ i j, (L - M) i j ∈ 𝔞)
    (hM : ∀ i j, (M * J l R * Mᵀ - J l R) i j ∈ 𝔞) (i j : l ⊕ l) :
    (L * J l R * Lᵀ - J l R) i j ∈ 𝔞 := by
  set D := L - M
  have hL : L = M + D := by simp [D]
  have hD : ∀ i j, (D * J l R) i j ∈ 𝔞 := mul_apply_mem_right hLM (J l R)
  have hDt : ∀ i j, Dᵀ i j ∈ 𝔞 := fun i j ↦ hLM j i
  have h : L * J l R * Lᵀ - J l R = (M * J l R * Mᵀ - J l R) + D * J l R * Mᵀ +
      M * J l R * Dᵀ + D * J l R * Dᵀ := by
    rw [hL, Matrix.transpose_add]
    noncomm_ring
  rw [h]
  simp only [Matrix.add_apply]
  exact 𝔞.add_mem (𝔞.add_mem (𝔞.add_mem (hM i j)
    (mul_apply_mem_right hD Mᵀ i j)) (mul_apply_mem_left hDt (M * J l R) i j))
    (mul_apply_mem_left hDt (D * J l R) i j)

/-- Correcting a matrix `M` with `M * J * Mᵀ - J = E` by `1 + X`, where `X` has entries in a
square-zero ideal and `E + X * J + J * Xᵀ = 0`, gives a symplectic matrix. -/
theorem one_add_mul_mem_symplecticGroup {I : Ideal R} (hI : I ^ 2 = (⊥ : Ideal R))
    {M E X : Matrix (l ⊕ l) (l ⊕ l) R}
    (hM : M * J l R * Mᵀ - J l R = E) (hX_mem : ∀ i j, X i j ∈ I)
    (hX : E + X * J l R + J l R * Xᵀ = 0) :
    (1 + X) * M ∈ symplecticGroup l R := by
  have hXt_mem : ∀ i j, Xᵀ i j ∈ I := fun i j => hX_mem j i
  have hXJ_mem : ∀ i j, (X * J l R) i j ∈ I := fun i j => by
    simpa using mul_mul_apply_mem hX_mem 1 (J l R) i j
  -- The entries of `E = -(X * J + J * Xᵀ)` lie in `I`.
  have hE_mem : ∀ i j, E i j ∈ I := fun i j => by
    have hE : E = -(X * J l R + J l R * Xᵀ) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]
      exact hX
    rw [hE, Matrix.neg_apply, Matrix.add_apply]
    exact I.neg_mem (I.add_mem (hXJ_mem i j)
      (by simpa using mul_mul_apply_mem hXt_mem (J l R) 1 i j))
  have hX_mul_E : X * E = 0 := mul_eq_zero_of_mul_eq_bot (sq I ▸ hI) hX_mem hE_mem
  have hE_mul_Xt : E * Xᵀ = 0 := mul_eq_zero_of_mul_eq_bot (sq I ▸ hI) hE_mem hXt_mem
  have hXJ_mul_Xt : X * J l R * Xᵀ = 0 :=
    mul_eq_zero_of_mul_eq_bot (sq I ▸ hI) hXJ_mem hXt_mem
  rw [SymplecticGroup.mem_iff, ← sub_eq_zero, one_add_mul_mul_J_mul_transpose_sub_J hM hX,
    hX_mul_E, hE_mul_Xt, hXJ_mul_Xt]
  simp

end Matrix

namespace SymplecticGroup

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

/-- **The transpose of a symplectic matrix is the `J`-conjugate of its inverse.** Mathlib's
`SymplecticGroup.inv_eq_symplectic_inv` computes the inverse as `-J * Aᵀ * J`; cancelling the
conjugation by `J` solves that identity for `Aᵀ` instead. -/
theorem transpose_eq_J_conj_inv {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ Matrix.symplecticGroup l R) : Aᵀ = J l R * A⁻¹ * (J l R)⁻¹ := by
  rw [eq_J_conj_iff_mul_J_eq, inv_eq_symplectic_inv A hA]
  calc Aᵀ * J l R = J l R * (-J l R) * (Aᵀ * J l R) := by rw [J_mul_neg_J, one_mul]
    _ = J l R * (-J l R * Aᵀ * J l R) := by noncomm_ring

/-- **A matrix whose `J`-conjugate is its inverse transpose is symplectic.** If `Y * X = 1` and
`J * X * J⁻¹ = Yᵀ`, that is `(X⁻¹)ᵀ = J * X * J⁻¹`, then `X` is symplectic. This is a converse of
`SymplecticGroup.transpose_eq_J_conj_inv`, with the left inverse `Y` supplied explicitly. -/
theorem mem_of_J_conj_eq_transpose {X Y : Matrix (l ⊕ l) (l ⊕ l) R} (hYX : Y * X = 1)
    (h : J l R * X * (J l R)⁻¹ = Yᵀ) : X ∈ symplecticGroup l R := by
  have hJ : Yᵀ * J l R = J l R * X := (eq_J_conj_iff_mul_J_eq _ _).1 h.symm
  rw [mem_iff', Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, ← transpose_mul, hYX, transpose_one,
    Matrix.one_mul]

/-- **Symplectic matrices are the unitary elements for the symplectic adjoint**
`A ↦ J⁻¹ * Aᵀ * J = -(J * Aᵀ * J)`: a matrix is symplectic exactly when its adjoint is a left
inverse. Mathlib's `SymplecticGroup.inv_left_mul_aux` is the forward direction. -/
theorem mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one {A : Matrix (l ⊕ l) (l ⊕ l) R} :
    A ∈ symplecticGroup l R ↔ -(J l R * Aᵀ * J l R * A) = 1 := by
  refine ⟨inv_left_mul_aux, fun h => mem_iff'.mpr ?_⟩
  calc Aᵀ * J l R * A = -J l R * J l R * (Aᵀ * J l R * A) := by rw [neg_J_mul_J, one_mul]
    _ = J l R * -(J l R * Aᵀ * J l R * A) := by noncomm_ring
    _ = J l R := by rw [h, mul_one]

/-- **For a matrix commuting with `J`, symplectic means orthogonal**: if `A * J = J * A` then
`A * J * Aᵀ = J * (A * Aᵀ)`, which is `J` exactly when `A * Aᵀ = 1`, since `J` is a unit. -/
theorem mem_iff_mem_orthogonalGroup_of_commute {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (h : Commute (J l R) A) : A ∈ symplecticGroup l R ↔ A ∈ orthogonalGroup (l ⊕ l) R := by
  rw [mem_iff, mem_orthogonalGroup_iff, ← h.eq, Matrix.mul_assoc, (isUnit_J l R).mul_eq_left]

/-- **An orthogonal symplectic matrix commutes with `J`**: from `A * J * Aᵀ = J` and
`Aᵀ * A = 1`, multiplying on the right by `A` gives `A * J = J * A`. -/
theorem commute_J_of_mem_orthogonalGroup {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hS : A ∈ symplecticGroup l R) (hO : A ∈ orthogonalGroup (l ⊕ l) R) :
    Commute (J l R) A := by
  rw [mem_iff] at hS
  rw [mem_orthogonalGroup_iff'] at hO
  calc J l R * A = A * J l R * Aᵀ * A := by rw [hS]
    _ = A * J l R := by rw [Matrix.mul_assoc, hO, Matrix.mul_one]

/-- **The block relations of a symplectic matrix.** A matrix `M = [[A, B], [C, D]]` is symplectic
exactly when `Aᵀ C = Cᵀ A`, `Bᵀ D = Dᵀ B` and `Aᵀ D - Cᵀ B = 1`; this is
`SymplecticGroup.fromBlocks_mem_iff` stated for the blocks `M.toBlocksᵢⱼ` of an arbitrary `M`. -/
theorem mem_iff_toBlocks {M : Matrix (l ⊕ l) (l ⊕ l) R} :
    M ∈ symplecticGroup l R ↔
      M.toBlocks₁₁ᵀ * M.toBlocks₂₁ = M.toBlocks₂₁ᵀ * M.toBlocks₁₁ ∧
        M.toBlocks₁₂ᵀ * M.toBlocks₂₂ = M.toBlocks₂₂ᵀ * M.toBlocks₁₂ ∧
        M.toBlocks₁₁ᵀ * M.toBlocks₂₂ - M.toBlocks₂₁ᵀ * M.toBlocks₁₂ = 1 := by
  conv_lhs => rw [← M.fromBlocks_toBlocks]
  exact fromBlocks_mem_iff

/-- An upper unitriangular block matrix is symplectic when its upper-right block is symmetric. -/
theorem fromBlocks_upper_mem {B : Matrix l l R} (hB : Bᵀ = B) :
    fromBlocks 1 B 0 1 ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hB]

/-- A lower unitriangular block matrix is symplectic when its lower-left block is symmetric. -/
theorem fromBlocks_lower_mem {C : Matrix l l R} (hC : Cᵀ = C) :
    fromBlocks 1 0 C 1 ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hC]

/-- A block-diagonal matrix is symplectic when its diagonal blocks satisfy the defining inverse
transpose relation. -/
theorem fromBlocks_diagonal_mem {A D : Matrix l l R} (hAD : Aᵀ * D = 1) :
    fromBlocks A 0 0 D ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hAD]

/-- **For a real symplectic matrix `A`, the matrix `A J + J A` is invertible**:
`(A J + J A) Aᵀ = J (1 + A Aᵀ)` and `1 + A Aᵀ` is positive definite. -/
theorem isUnit_det_mul_J_add_J_mul {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ symplecticGroup l ℝ) : IsUnit (A * J l ℝ + J l ℝ * A).det := by
  have hsymp : A * J l ℝ * Aᵀ = J l ℝ := mem_iff.1 hA
  have hkey : (A * J l ℝ + J l ℝ * A) * Aᵀ = J l ℝ * (1 + A * Aᵀ) := by
    rw [add_mul, hsymp, mul_add, mul_one, Matrix.mul_assoc]
  have hpos : (1 + A * Aᵀ).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posDef_one_add_mul_conjTranspose A
  have h := congrArg Matrix.det hkey
  rw [det_mul, det_mul] at h
  have hne : (J l ℝ).det * (1 + A * Aᵀ).det ≠ 0 :=
    mul_ne_zero (isUnit_det_J l ℝ).ne_zero hpos.det_pos.ne'
  rw [← h] at hne
  exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hne)

/-- For a symplectic matrix with invertible upper-left block `A` with inverse `A⁻¹`, the blocks
`C A⁻¹` and `A⁻¹ B` are symmetric, and `D = (C A⁻¹) A (A⁻¹ B) + A⁻ᵀ`. -/
theorem symm_and_toBlocks₂₂_of_mem_symplecticGroup {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] {M : Matrix (n ⊕ n) (n ⊕ n) R} (hM : M ∈ Matrix.symplecticGroup n R)
    {Ainv : Matrix n n R} (hright : M.toBlocks₁₁ * Ainv = 1) :
    (M.toBlocks₂₁ * Ainv).IsSymm ∧ (Ainv * M.toBlocks₁₂).IsSymm ∧
      M.toBlocks₂₂ = M.toBlocks₂₁ * Ainv * M.toBlocks₁₁ * (Ainv * M.toBlocks₁₂) + Ainvᵀ := by
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  have hleft : Ainv * A = 1 := mul_eq_one_comm.mp hright
  have hMblocks : Matrix.fromBlocks A B C D = M := M.fromBlocks_toBlocks
  have hblocks : Aᵀ * C = Cᵀ * A ∧ Bᵀ * D = Dᵀ * B ∧ Aᵀ * D - Cᵀ * B = 1 :=
    (SymplecticGroup.fromBlocks_mem_iff).mp (hMblocks ▸ hM)
  have hS : (C * Ainv).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_mul]
    calc
      Ainvᵀ * Cᵀ = Ainvᵀ * Cᵀ * (A * Ainv) := by rw [hright, mul_one]
      _ = Ainvᵀ * (Cᵀ * A) * Ainv := by simp only [mul_assoc]
      _ = Ainvᵀ * (Aᵀ * C) * Ainv := by rw [hblocks.1]
      _ = (Ainvᵀ * Aᵀ) * C * Ainv := by simp only [mul_assoc]
      _ = C * Ainv := by rw [← Matrix.transpose_mul, hright, Matrix.transpose_one, one_mul]
  have hdual : A * Bᵀ = B * Aᵀ := by
    have hMt : Matrix.fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ ∈ Matrix.symplecticGroup n R := by
      rw [← Matrix.fromBlocks_transpose, hMblocks]
      exact SymplecticGroup.transpose_mem hM
    simpa only [Matrix.transpose_transpose] using
      (SymplecticGroup.fromBlocks_mem_iff.mp hMt).1
  refine ⟨hS, ?_, ?_⟩
  · rw [Matrix.IsSymm, Matrix.transpose_mul]
    calc
      Bᵀ * Ainvᵀ = (Ainv * A) * Bᵀ * Ainvᵀ := by rw [hleft, one_mul]
      _ = Ainv * (A * Bᵀ) * Ainvᵀ := by simp only [mul_assoc]
      _ = Ainv * (B * Aᵀ) * Ainvᵀ := by rw [hdual]
      _ = Ainv * B * (Aᵀ * Ainvᵀ) := by simp only [mul_assoc]
      _ = Ainv * B := by rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one, mul_one]
  · have hAD : Aᵀ * D = 1 + Cᵀ * B := sub_eq_iff_eq_add.mp hblocks.2.2
    have hAinvC : Ainvᵀ * Cᵀ = C * Ainv := by
      calc
        Ainvᵀ * Cᵀ = (C * Ainv)ᵀ := by simp only [Matrix.transpose_mul]
        _ = C * Ainv := hS.eq
    calc
      D = (Ainvᵀ * Aᵀ) * D := by rw [← Matrix.transpose_mul, hright,
        Matrix.transpose_one, one_mul]
      _ = Ainvᵀ * (Aᵀ * D) := by rw [mul_assoc]
      _ = Ainvᵀ * (1 + Cᵀ * B) := by rw [hAD]
      _ = Ainvᵀ + (Ainvᵀ * Cᵀ) * B := by noncomm_ring
      _ = Ainvᵀ + C * Ainv * B := by rw [hAinvC]
      _ = Ainvᵀ + C * Ainv * A * (Ainv * B) := by
        rw [← mul_assoc (C * Ainv * A) Ainv B, mul_assoc (C * Ainv) A Ainv, hright, mul_one]
      _ = C * Ainv * A * (Ainv * B) + Ainvᵀ := add_comm _ _

end SymplecticGroup

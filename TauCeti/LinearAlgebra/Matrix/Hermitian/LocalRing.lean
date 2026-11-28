/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Orthonormal bases of unimodular hermitian forms over a local ring

Let `R` be a commutative local ring with an involution `star`, and `b` an invertible hermitian
matrix over `R`, the Gram matrix of the unimodular hermitian form `(u, v) ↦ star u ⬝ᵥ b *ᵥ v`.
This file proves that `b` has an orthonormal basis, that is `kᴴ * b * k = 1` for some invertible
`k`, as soon as

* every unit `u` of `R` with `star u = u` is a norm `star y * y`, and
* `t + star t = 1` for some `t ∈ R`.

The second condition holds when `2` is a unit (`t = 1/2`), and also for the ring of integers of an
unramified quadratic extension of local fields, of any residue characteristic. Neither condition
can be dropped: over `𝔽₂` with the trivial involution every unit is a norm, but the form
`[[0, 1], [1, 0]]` is alternating, so it takes no unit value; over `ℝ` with the trivial involution,
`t = 1/2`, and the `1 × 1` form `-1` has no orthonormal basis.

The proof is the Gram–Schmidt process. Since `b` is invertible, some entry `b i j` is a unit. If a
diagonal entry is a unit, the corresponding basis vector `v` has `star v ⬝ᵥ b *ᵥ v` a unit.
Otherwise `i ≠ j`, and `v = eᵢ + λ eⱼ` with `λ = t / b i j` has
`star v ⬝ᵥ b *ᵥ v ≡ t + star t = 1` modulo the maximal ideal. Dividing `v` by `y`, where
`star v ⬝ᵥ b *ᵥ v = star y * y`, gives a vector of length one. It has a unit coordinate `v p`, so
replacing the `p`-th basis vector by `v` is a change of basis, and the orthogonal complement of
`v` has an invertible hermitian Gram matrix of smaller size, the Schur complement.

## Main results

* `Matrix.exists_isUnit_star_dotProduct_mulVec_self`: an invertible hermitian matrix over a local
  ring with `t + star t = 1` has a vector `v` with `star v ⬝ᵥ b *ᵥ v` a unit, and
  `Matrix.exists_star_dotProduct_mulVec_self_eq_one`: one with `star v ⬝ᵥ b *ᵥ v = 1` when
  conjugation-fixed units are norms.
* `Matrix.fromBlocks_conjTranspose_mul_fromBlocks_mul_fromBlocks`: clearing the off-diagonal blocks
  of a hermitian block matrix with top left block `1` leaves the Schur complement.
* `Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_one`: an invertible hermitian matrix `b` over
  such a local ring satisfies `kᴴ * b * k = 1` for some `k ∈ GL n R`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §92 (unimodular lattices over local rings).
* U. First, *Witt's extension theorem for quadratic spaces over semiperfect rings*, J. Pure Appl.
  Algebra 219 (2015), Corollary 4.9 and §4.
-/

public section

open IsLocalRing

namespace Matrix

section CommSemiring

variable {R n : Type*} [CommSemiring R] [Fintype n]

/-- **A vector with a unit inner product has a unit coordinate.** Over a local semiring, if
`x ⬝ᵥ v` is a unit then so is some coordinate `v p`. -/
theorem exists_isUnit_apply_of_isUnit_dotProduct [IsLocalRing R] {x v : n → R}
    (h : IsUnit (x ⬝ᵥ v)) : ∃ p, IsUnit (v p) := by
  obtain ⟨p, -, hp⟩ := IsLocalRing.exists_of_isUnit_sum h
  exact ⟨p, isUnit_of_mul_isUnit_right hp⟩

/-- The value of the sesquilinear form of `b` at `a • eᵢ + c • eⱼ`. -/
theorem star_dotProduct_mulVec_single_add_single [DecidableEq n] [StarRing R] (b : Matrix n n R)
    (i j : n) (a c : R) :
    star (Pi.single i a + Pi.single j c : n → R) ⬝ᵥ b *ᵥ (Pi.single i a + Pi.single j c) =
      star a * b i i * a + star a * b i j * c + star c * b j i * a + star c * b j j * c := by
  simp only [star_add, Pi.star_single, mulVec_add, mulVec_single, add_dotProduct, dotProduct_add,
    single_dotProduct, dotProduct_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    col_apply]
  ring

end CommSemiring

/-- **The Schur complement of a pivot `1`.** For a hermitian matrix in block form with top left
block `1`, clearing the top right block by the unipotent change of basis `[[1, -B], [0, 1]]` leaves
the block diagonal matrix with blocks `1` and the Schur complement `D - Bᴴ * B`. -/
theorem fromBlocks_conjTranspose_mul_fromBlocks_mul_fromBlocks {α l m : Type*} [Ring α]
    [StarRing α] [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m] (B : Matrix l m α)
    (D : Matrix m m α) :
    (fromBlocks 1 (-B) 0 1)ᴴ * fromBlocks 1 B Bᴴ D * fromBlocks 1 (-B) 0 1 =
      fromBlocks 1 0 0 (D - Bᴴ * B) := by
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one, conjTranspose_zero,
    conjTranspose_neg]
  simp [Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg]
  abel

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **An invertible matrix over a local ring has a unit entry**, when its index type is
nonempty. -/
theorem exists_isUnit_apply_of_isUnit [IsLocalRing R] [Nonempty n] {b : Matrix n n R}
    (hb : IsUnit b) : ∃ i j, IsUnit (b i j) := by
  -- modulo the maximal ideal, `b` becomes an invertible, hence nonzero, matrix
  have hne : (residue R).mapMatrix b ≠ 0 := (hb.map _).ne_zero
  by_contra! h
  refine hne (Matrix.ext fun i j ↦ ?_)
  rw [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply]
  exact (residue_eq_zero_iff _).2 (h i j)

variable [StarRing R]

/-- **A unimodular hermitian form over a local ring represents a unit.** Let `R` be a local ring
with an involution and `t + star t = 1` for some `t`. Every invertible hermitian matrix `b` over
`R` with nonempty index type has a vector `v` with `star v ⬝ᵥ b *ᵥ v` a unit. -/
theorem exists_isUnit_star_dotProduct_mulVec_self [IsLocalRing R] [Nonempty n] {t : R}
    (ht : t + star t = 1) {b : Matrix n n R} (hb : b.IsHermitian) (hu : IsUnit b) :
    ∃ v : n → R, IsUnit (star v ⬝ᵥ b *ᵥ v) := by
  have hdiag (i : n) : star (Pi.single i 1 : n → R) ⬝ᵥ b *ᵥ Pi.single i 1 = b i i := by simp
  obtain ⟨i, j, hij⟩ := exists_isUnit_apply_of_isUnit hu
  -- a unit diagonal entry is the value at a basis vector
  by_cases hi : IsUnit (b i i)
  · exact ⟨Pi.single i 1, by rwa [hdiag]⟩
  by_cases hj : IsUnit (b j j)
  · exact ⟨Pi.single j 1, by rwa [hdiag]⟩
  -- otherwise, the value at `eᵢ + λ eⱼ` with `b i j * λ = t` is `1` modulo the maximal ideal
  set l := t * ↑hij.unit⁻¹ with hl
  refine ⟨Pi.single i 1 + Pi.single j l, ?_⟩
  have hlam : b i j * l = t := by
    rw [hl, mul_left_comm, IsUnit.mul_val_inv, mul_one]
  have hs : star l * b j i = star t := by
    rw [← hb.apply j i, ← star_mul, hlam]
  have hval : star (Pi.single i 1 + Pi.single j l : n → R) ⬝ᵥ b *ᵥ (Pi.single i 1 + Pi.single j l) =
      1 + (b i i + star l * b j j * l) := by
    rw [star_dotProduct_mulVec_single_add_single, star_one, one_mul, one_mul, mul_one, mul_one]
    linear_combination hlam + hs + ht
  have hm : b i i + star l * b j j * l ∈ maximalIdeal R :=
    add_mem ((mem_maximalIdeal _).2 hi)
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).2 hj)))
  rw [hval, ← sub_neg_eq_add]
  exact isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).1 (neg_mem hm))

/-- **A unimodular hermitian form over a local ring represents `1`.** Let `R` be a local ring with
an involution in which every unit `u` with `star u = u` is a norm `star y * y`, and
`t + star t = 1` for some `t`. Every invertible hermitian matrix `b` over `R` with nonempty index
type has a vector `v` with `star v ⬝ᵥ b *ᵥ v = 1`. -/
theorem exists_star_dotProduct_mulVec_self_eq_one [IsLocalRing R] [Nonempty n]
    (hnorm : ∀ u : R, IsUnit u → star u = u → ∃ y, star y * y = u) {t : R}
    (ht : t + star t = 1) {b : Matrix n n R} (hb : b.IsHermitian) (hu : IsUnit b) :
    ∃ v : n → R, star v ⬝ᵥ b *ᵥ v = 1 := by
  obtain ⟨v, hv⟩ := exists_isUnit_star_dotProduct_mulVec_self ht hb hu
  -- the value `u` at `v` is fixed by `star`, so `u = star y * y`; divide `v` by `y`
  have hstar : star (star v ⬝ᵥ b *ᵥ v) = star v ⬝ᵥ b *ᵥ v := by
    rw [← star_dotProduct_star, star_mulVec, star_star, ← dotProduct_mulVec, hb.eq]
  obtain ⟨y, hy⟩ := hnorm _ hv hstar
  have hyu : IsUnit y := isUnit_of_mul_isUnit_right (hy ▸ hv)
  refine ⟨(↑hyu.unit⁻¹ : R) • v, ?_⟩
  have h₁ : ↑hyu.unit⁻¹ * y = 1 := IsUnit.val_inv_mul hyu
  have h₂ : star (↑hyu.unit⁻¹ : R) * star y = 1 := by rw [← star_mul, mul_comm, h₁, star_one]
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hy]
  linear_combination (↑hyu.unit⁻¹ * y) * h₂ + h₁

/-- **Pivoting at a vector of length one.** Over a local ring, if `star v ⬝ᵥ b *ᵥ v = 1`, then
some coordinate `v p` is a unit, and replacing the `p`-th standard basis vector by `v` is a change
of basis `P` in which the Gram matrix of `b` has `1` at `(p, p)`. -/
private theorem exists_isUnit_conjTranspose_mul_mul_apply_self_eq_one [IsLocalRing R]
    {b : Matrix n n R} {v : n → R} (hv : star v ⬝ᵥ b *ᵥ v = 1) :
    ∃ (p : n) (P : Matrix n n R), IsUnit P ∧ (Pᴴ * b * P) p p = 1 := by
  obtain ⟨p, hp⟩ := exists_isUnit_apply_of_isUnit_dotProduct (x := star v ᵥ* b) (v := v)
    (by rw [← dotProduct_mulVec, hv]; exact isUnit_one)
  refine ⟨p, (1 : Matrix n n R).updateCol p v, ?_, ?_⟩
  · -- the determinant of `1` with its `p`-th column replaced by `v` is `v p`
    have hcol : (fun k ↦ ∑ i, v i • (1 : Matrix n n R) k i) = v := by
      ext k
      simp [Matrix.one_apply, mul_ite]
    rw [isUnit_iff_isUnit_det, ← hcol, det_updateCol_sum, det_one, smul_eq_mul, mul_one]
    exact hp
  · have hcol : ((1 : Matrix n n R).updateCol p v).col p = v := funext fun _ ↦ updateCol_self
    rw [conjTranspose_mul_mul_apply, hcol, hv]

/-- **Splitting off a pivot `1`.** Let `c` be an invertible hermitian matrix with `c p p = 1`. Its
Schur complement `D'` along `{p}`, indexed by the other indices, is invertible and hermitian, and
an orthonormal basis of `D'` extends to one of `c`. -/
private theorem exists_schurComplement {c : Matrix n n R} (hc : c.IsHermitian) (hu : IsUnit c)
    {p : n} (hp : c p p = 1) :
    ∃ D' : Matrix {q // ¬q = p} {q // ¬q = p} R, D'.IsHermitian ∧ IsUnit D' ∧
      ∀ k', k'ᴴ * D' * k' = 1 → ∃ k : Matrix n n R, kᴴ * c * k = 1 := by
  -- `c` in block form along `{p}` and its complement
  set e := Equiv.sumCompl (· = p)
  set c' := c.submatrix e e
  have hc' : c'.IsHermitian := hc.submatrix e
  set B := c'.toBlocks₁₂
  set D := c'.toBlocks₂₂
  obtain ⟨-, hBC, -, hD⟩ := isHermitian_fromBlocks_iff.1 (c'.fromBlocks_toBlocks.symm ▸ hc')
  have h₁₁ : c'.toBlocks₁₁ = 1 := by
    ext ⟨q, rfl⟩ ⟨q', rfl⟩
    simp [c', e, toBlocks₁₁, hp]
  have hcB : c' = fromBlocks 1 B Bᴴ D := by
    rw [← h₁₁, hBC, fromBlocks_toBlocks]
  -- clearing `B` leaves the blocks `1` and the Schur complement `D'`
  set Q : Matrix ({q // q = p} ⊕ {q // ¬q = p}) ({q // q = p} ⊕ {q // ¬q = p}) R :=
    fromBlocks 1 (-B) 0 1
  have hQ : Qᴴ * c' * Q = fromBlocks 1 0 0 (D - Bᴴ * B) := by
    rw [hcB]
    exact fromBlocks_conjTranspose_mul_fromBlocks_mul_fromBlocks B D
  refine ⟨D - Bᴴ * B, hD.sub (isHermitian_conjTranspose_mul_self B), ?_, fun k' hk' ↦ ?_⟩
  · have hQu : IsUnit Q := isUnit_fromBlocks_zero₂₁.2 ⟨isUnit_one, isUnit_one⟩
    have h : IsUnit (Qᴴ * c' * Q) := by
      rw [← star_eq_conjTranspose]
      exact (hQu.star.mul ((isUnit_submatrix_equiv e e).2 hu)).mul hQu
    rw [hQ] at h
    exact (isUnit_fromBlocks_zero₂₁.1 h).2
  -- the change of basis `Q * [[1, 0], [0, k']]`, read back along `e`
  set X := Q * fromBlocks 1 0 0 k'
  have hX : Xᴴ * c' * X = 1 := by
    have hXQ : Xᴴ * c' * X = (fromBlocks 1 0 0 k')ᴴ * (Qᴴ * c' * Q) * fromBlocks 1 0 0 k' := by
      simp only [X, conjTranspose_mul, Matrix.mul_assoc]
    rw [hXQ, hQ]
    simp [fromBlocks_conjTranspose, fromBlocks_multiply, hk']
  refine ⟨X.submatrix e.symm e.symm, ?_⟩
  have hcc : c = c'.submatrix e.symm e.symm := by
    rw [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  rw [hcc, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hX,
    submatrix_one_equiv]

/-- **Orthonormal bases of unimodular hermitian forms over a local ring.** Let `R` be a commutative
local ring with an involution in which every unit `u` with `star u = u` is a norm `star y * y`,
and `t + star t = 1` for some `t`. Then every invertible hermitian matrix `b` over `R` satisfies
`kᴴ * b * k = 1` for some invertible `k`. -/
theorem IsHermitian.exists_conjTranspose_mul_mul_eq_one [IsLocalRing R]
    (hnorm : ∀ u : R, IsUnit u → star u = u → ∃ y, star y * y = u) {t : R}
    (ht : t + star t = 1) {b : Matrix n n R} (hb : b.IsHermitian) (hu : IsUnit b) :
    ∃ k : GL n R, (k : Matrix n n R)ᴴ * b * k = 1 := by
  -- it suffices to find `k` with `kᴴ * b * k = 1`, which is then invertible
  suffices h : ∃ k : Matrix n n R, kᴴ * b * k = 1 by
    obtain ⟨k, hk⟩ := h
    have hku : IsUnit k := (isUnit_iff_isUnit_det k).2 (isUnit_det_of_left_inverse hk)
    exact ⟨hku.unit, hk⟩
  -- strong induction on the size of the index type
  induction hN : Fintype.card n using Nat.strong_induction_on generalizing n with
  | _ N ih =>
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, Subsingleton.elim _ _⟩
  -- a vector `v` of length one, with a unit coordinate `p`, gives a basis with `1` at `(p, p)`
  obtain ⟨v, hv⟩ := exists_star_dotProduct_mulVec_self_eq_one hnorm ht hb hu
  obtain ⟨p, P, hP, hPp⟩ := exists_isUnit_conjTranspose_mul_mul_apply_self_eq_one hv
  -- split off that `1`, and apply the induction hypothesis to the Schur complement
  obtain ⟨D', hD', hD'u, hext⟩ := exists_schurComplement
    (isHermitian_conjTranspose_mul_mul P hb) ((hP.star.mul hu).mul hP) hPp
  have hcard : Fintype.card {q // ¬q = p} < N := by
    rw [← hN]
    exact Fintype.card_subtype_lt (not_not.2 rfl)
  obtain ⟨k', hk'⟩ := ih _ hcard hD' hD'u rfl
  obtain ⟨k, hk⟩ := hext k' hk'
  exact ⟨P * k, by simpa only [conjTranspose_mul, Matrix.mul_assoc] using hk⟩

end Matrix

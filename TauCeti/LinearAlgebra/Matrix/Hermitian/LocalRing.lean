/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.Star.Pi
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.RowCol
import TauCeti.LinearAlgebra.Matrix.SchurComplement
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Orthonormal bases of unimodular hermitian matrices over a local ring

Let `R` be a commutative local ring with an involution `star`. A hermitian matrix `b` over `R`
whose determinant is a unit is the Gram matrix of a *unimodular* hermitian form on `R^n`. This
file shows that such a form has an orthonormal basis, `kᴴ * b * k = 1`, as soon as

* some trace `s + star s` is a unit (for instance `s = 1` when `2` is a unit), and
* every unit `u` with `star u = u` is a norm `star y * y`.

Both conditions are necessary. Over `ℤ_[2]` with the trivial involution every `s + star s = 2 * s`
lies in the maximal ideal, and the hyperbolic plane `!![0, 1; 1, 0]` represents no unit, while an
orthonormal basis would make it represent `1`. Over `ℝ` with the trivial involution `-1` is not a
norm, and the `1 × 1` matrix `!![-1]` is not congruent to `1`.

The proof is Gram–Schmidt. A unimodular form represents a unit by a vector with a coordinate equal
to `1` (`Matrix.IsHermitian.exists_isUnit_star_dotProduct_mulVec`): a row of `b` contains a unit,
and if no diagonal entry of the two rows involved is a unit, the trace condition produces a vector
of unit norm in the plane they span. That unit is a norm, so the vector may be scaled to norm `1`,
and the orthogonal complement is split off by the Schur complement.

The integral finite adeles of a CM field are not local, but they are a product of local rings and
of pairs of rings exchanged by the involution, and the statement here is the local case of the
existence of orthonormal bases of unimodular hermitian forms over them.

## Main results

* `Matrix.IsHermitian.exists_isUnit_star_dotProduct_mulVec`: over a local ring with a unit trace,
  a unimodular hermitian form represents a unit, by a vector with a coordinate equal to `1`.
* `Matrix.conjTranspose_mul_fromBlocks_one₂₂_mul`: a block-diagonal congruence
  identity leaving the Schur complement; the multiplier is invertible when `kS` is invertible.
* `Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_one`: over a local ring with a unit trace
  whose conjugation-fixed units are norms, a unimodular hermitian matrix `b` satisfies
  `kᴴ * b * k = 1` for some `k`, which is then invertible.

## References

* R. Jacobowitz, *Hermitian forms over local fields*, Amer. J. Math. 84 (1962), 441–465, for
  unimodular hermitian lattices over local rings of integers.
* M.-A. Knus, *Quadratic and Hermitian Forms over Rings*, Springer, 1991, for hermitian forms
  over local rings.
* `grh-lean`, https://github.com/lsernau/grh-lean, file `src/Lib/Adelic/Witt/WittTheorem.lean`
  (declaration `New.exists_orthonormal_Ô`); Apache 2.0, Copyright 2026 Anthropic, PBC. That
  declaration states the result over the integral finite adeles of a CM field; the local
  statement and its proof here are independent of that code.
-/

public section

open Matrix

namespace Matrix

variable {R : Type*} [CommRing R] [StarRing R] {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **A hermitian form with a unit entry over a local ring represents a unit.**
Let `R` be a local ring with an involution in which some trace `s + star s` is a unit. A
hermitian matrix `b` with a unit entry takes a unit value `star v ⬝ᵥ b *ᵥ v` at a vector `v`
with a coordinate equal to `1`. -/
theorem IsHermitian.exists_isUnit_star_dotProduct_mulVec [IsLocalRing R]
    {b : Matrix n n R} (hb : b.IsHermitian) (hentry : ∃ i j, IsUnit (b i j)) {s : R}
    (hs : IsUnit (s + star s)) :
    ∃ i v, v i = 1 ∧ IsUnit (star v ⬝ᵥ b *ᵥ v) := by
  classical
  -- the value at a basis vector is a diagonal entry
  have hsingle (j : n) : star (Pi.single j 1 : n → R) ⬝ᵥ b *ᵥ Pi.single j 1 = b j j := by
    rw [Pi.star_single, star_one, single_one_dotProduct, mulVec_single_one, col_apply]
  obtain ⟨i, j, hij⟩ := hentry
  by_cases hii : IsUnit (b i i)
  · exact ⟨i, Pi.single i 1, Pi.single_eq_same i 1, by rwa [hsingle]⟩
  by_cases hjj : IsUnit (b j j)
  · exact ⟨j, Pi.single j 1, Pi.single_eq_same j 1, by rwa [hsingle]⟩
  have hne : j ≠ i := by rintro rfl; exact hii hij
  -- in the plane of `e_i` and `e_j`, the vector `e_i + t e_j` with `b i j * t = s`
  set t : R := ↑hij.unit⁻¹ * s with ht
  have hts : b i j * t = s := by rw [ht, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hval : star (Pi.single i 1 + Pi.single j t : n → R) ⬝ᵥ b *ᵥ (Pi.single i 1 + Pi.single j t) =
      (s + star s) + (b i i + star t * (b j j * t)) := by
    have hji : b j i = star (b i j) := by rw [← hb.apply i j, star_star]
    have hts' : star t * star (b i j) = star s := by rw [← star_mul', mul_comm, hts]
    -- expanding bilinearly: `b i i + star t * b j i + t * (b i j + star t * b j j)`
    simp only [star_add, Pi.star_single, star_one, mulVec_add, mulVec_single, MulOpposite.op_one,
      one_smul, op_smul_eq_smul, dotProduct_add, add_dotProduct, single_dotProduct, col_apply,
      one_mul, dotProduct_smul, smul_eq_mul, hji]
    linear_combination hts + hts'
  refine ⟨i, Pi.single i 1 + Pi.single j t, by simp [hne.symm], ?_⟩
  -- a unit plus a sum of two nonunits is a unit
  have hrest : ¬IsUnit (b i i + star t * (b j j * t)) := IsLocalRing.nonunits_add hii
    fun h ↦ hjj (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h))
  rw [hval]
  exact TauCeti.isUnit_add_of_isUnit_of_not_isUnit hs hrest

/-- **Normalizing a vector of unit norm.** If every conjugation-fixed unit is a norm, a vector `v`
with a unit coordinate `v i` and unit norm for a hermitian `b` yields an invertible change of
basis `P`
after which the `i`-th basis vector has norm `1`. -/
private theorem IsHermitian.exists_isUnit_det_and_conjTranspose_mul_mul_apply_self_eq_one
    {b : Matrix n n R} (hb : b.IsHermitian)
    (hnorm : ∀ u : R, IsUnit u → star u = u → ∃ y, star y * y = u) {i : n} {v : n → R}
    (hvi : IsUnit (v i)) (hv : IsUnit (star v ⬝ᵥ b *ᵥ v)) :
    ∃ P : Matrix n n R, IsUnit P.det ∧ (Pᴴ * b * P) i i = 1 := by
  obtain ⟨y, hy⟩ := hnorm _ hv (hb.star_dotProduct_mulVec_comm v v)
  have hyu : IsUnit y := isUnit_of_mul_isUnit_right (hy ▸ hv)
  set z : R := ↑hyu.unit⁻¹
  have hzy : z * y = 1 := IsUnit.val_inv_mul hyu
  -- the change of basis replacing the `i`-th basis vector by `z • v`
  refine ⟨updateCol 1 i (z • v), ?_, ?_⟩
  · have hdet : (updateCol (1 : Matrix n n R) i (z • v)).det = z * v i := by
      rw [← det_transpose, ← updateRow_transpose, transpose_one, det_updateRow_one]
      rfl
    rw [hdet]
    exact (hyu.unit⁻¹).isUnit.mul hvi
  · have hscale : star (z • v) ⬝ᵥ b *ᵥ (z • v) =
        (star z * z) * (star v ⬝ᵥ b *ᵥ v) := by
      rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      ac_rfl
    rw [conjTranspose_mul_mul_updateCol_one_apply_self, hscale, ← hy]
    have hzy' : star z * star y = 1 := by rw [← star_mul', hzy, star_one]
    calc
      (star z * z) * (star y * y) = (star z * star y) * (z * y) := by ac_rfl
      _ = 1 := by rw [hzy', hzy, mul_one]

/-- **The block step of Gram–Schmidt.** If the `i`-th basis vector has norm `1` for a unimodular
hermitian `b`, and the unimodular hermitian matrices on the complement of `i` have orthonormal
bases, then so does `b`. -/
private theorem IsHermitian.exists_conjTranspose_mul_mul_eq_one_of_apply_self_eq_one
    {b : Matrix n n R} (hb : b.IsHermitian) (hdet : IsUnit b.det) {i : n} (hi : b i i = 1)
    (ih : ∀ c : Matrix {j // j ≠ i} {j // j ≠ i} R, c.IsHermitian → IsUnit c.det →
      ∃ k, kᴴ * c * k = 1) :
    ∃ k : Matrix n n R, kᴴ * b * k = 1 := by
  -- order the basis as the complement of `i`, followed by `i`
  let e : {j // j ≠ i} ⊕ {j // j = i} ≃ n :=
    (Equiv.sumComm _ _).trans (Equiv.sumCompl (· = i))
  set c := b.submatrix e e with hc
  have hch :
      (Matrix.fromBlocks c.toBlocks₁₁ c.toBlocks₁₂ c.toBlocks₂₁ c.toBlocks₂₂).IsHermitian := by
    rw [fromBlocks_toBlocks]
    exact hb.submatrix e
  obtain ⟨hA, hBC, -, -⟩ := isHermitian_fromBlocks_iff.1 hch
  have h22 : c.toBlocks₂₂ = 1 := by
    ext ⟨a, ha⟩ ⟨a', ha'⟩
    subst ha ha'
    simp [c, e, toBlocks₂₂, hi]
  have hcb : c = Matrix.fromBlocks c.toBlocks₁₁ c.toBlocks₁₂ c.toBlocks₁₂ᴴ 1 := by
    rw [hBC, ← h22, fromBlocks_toBlocks]
  -- the Schur complement is again unimodular and hermitian
  have hSdet : IsUnit (c.toBlocks₁₁ - c.toBlocks₁₂ * c.toBlocks₁₂ᴴ).det := by
    rw [← det_fromBlocks_one₂₂, ← hcb, hc, det_submatrix_equiv_self]
    exact hdet
  obtain ⟨kS, hkS⟩ := ih _ (hA.sub (isHermitian_mul_conjTranspose_self _)) hSdet
  have hK := conjTranspose_mul_fromBlocks_one₂₂_mul c.toBlocks₁₁ c.toBlocks₁₂ kS
  rw [hkS, fromBlocks_one, ← hcb] at hK
  -- transport the orthonormal basis of `c` back along `e`
  refine ⟨(Matrix.fromBlocks kS 0 (-(c.toBlocks₁₂ᴴ * kS)) 1).submatrix e.symm e.symm, ?_⟩
  have hbc : b = c.submatrix e.symm e.symm := by
    rw [hc, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  rw [conjTranspose_submatrix, hbc, submatrix_mul_equiv, submatrix_mul_equiv, hK,
    submatrix_one_equiv]

/-- **Orthonormal bases of unimodular hermitian forms over a local ring.** Let `R` be a local
ring with an involution in which some trace `s + star s` is a unit and every unit `u` with
`star u = u` is a norm `star y * y`. Then every hermitian matrix `b` over `R` with unit
determinant is congruent to the identity: `kᴴ * b * k = 1` for some invertible `k`. -/
theorem IsHermitian.exists_conjTranspose_mul_mul_eq_one [IsLocalRing R] {b : Matrix n n R}
    (hb : b.IsHermitian) (hdet : IsUnit b.det) {s : R} (hs : IsUnit (s + star s))
    (hnorm : ∀ u : R, IsUnit u → star u = u → ∃ y, star y * y = u) :
    ∃ k : Matrix n n R, IsUnit k ∧ kᴴ * b * k = 1 := by
  suffices ∃ k : Matrix n n R, kᴴ * b * k = 1 by
    obtain ⟨k, hk⟩ := this
    exact ⟨k, IsUnit.of_mul_eq_one_right _ hk, hk⟩
  induction h : Fintype.card n using Nat.strong_induction_on generalizing n with
  | _ N ih =>
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, Subsingleton.elim _ _⟩
  obtain ⟨i₀⟩ := hn
  obtain ⟨j, -, hj⟩ := IsLocalRing.exists_of_isUnit_sum
    (Matrix.det_eq_sum_mul_adjugate_row b i₀ ▸ hdet)
  obtain ⟨i, v, hvi, hv⟩ := hb.exists_isUnit_star_dotProduct_mulVec
    ⟨i₀, j, isUnit_of_mul_isUnit_left hj⟩ hs
  obtain ⟨P, hP, hPi⟩ :=
    hb.exists_isUnit_det_and_conjTranspose_mul_mul_apply_self_eq_one hnorm
      (by rw [hvi]; exact isUnit_one) hv
  have hb₁ : (Pᴴ * b * P).IsHermitian := isHermitian_conjTranspose_mul_mul P hb
  have hdet₁ : IsUnit (Pᴴ * b * P).det := by
    rw [det_mul, det_mul, det_conjTranspose]
    exact (hP.star.mul hdet).mul hP
  obtain ⟨k, hk⟩ := hb₁.exists_conjTranspose_mul_mul_eq_one_of_apply_self_eq_one hdet₁ hPi
    fun c hc hcdet ↦ ih _ (h ▸ Fintype.card_subtype_lt (x := i) (by simp)) hc hcdet rfl
  exact ⟨P * k, by rw [conjTranspose_mul, ← hk]; simp only [Matrix.mul_assoc]⟩

end Matrix

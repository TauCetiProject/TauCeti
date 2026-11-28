/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.Matrix.FormAdjoint
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel
public import TauCeti.LinearAlgebra.Matrix.RaisesDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# Graded hermitian forms, the shift and the string map

Let `R` be a commutative ring with an involution, `X` a finite type, `s` a natural number and
`N`, `c` elements of `R` fixed by the involution. The space `R^(X ⊕ Fin s)` has the basis `x ∈ X`
and the *string* `e₀, …, e_{s-1}`. Its **graded Gram matrix** `TauCeti.gradedGram X s N` is the
identity on `X`, makes `X` orthogonal to the string, and pairs `e_a` with `e_{s-1-a}` to `1`,
except that the middle vector `e_{(s-1)/2}` of a string of odd length has norm `-N`. The **grade**
of a basis vector is `0` on `X` and `s - 1 - 2a` on `e_a`, so that the form pairs only opposite
grades. Forms of this shape, with the unipotent radical of the flag of the grades and the subgroup
`U(X)`, are the setting of Bessel periods of unitary groups and of their unfolding along a theta
correspondence. For a string of odd length `2ϱ + 1` the graded Gram matrix is the split form
`TauCeti.splitGram ϱ (TauCeti.middleGram N)` with its basis reordered
(`TauCeti.gradedGram_eq_submatrix_splitGram`); the order of the string used here is the one along
which the shift and the string map below move.

Two maps lower the grade.

* The **shift** `TauCeti.gradedShift X s N c` maps `e_a` to a multiple of `e_{a+1}` (by `-N c` at
  grade `0`, by `-N c²` at grade `1` and by `c` otherwise) and kills `X` and `e_{s-1}`; it lowers
  the grade by two.
* The **string map** `TauCeti.stringMap X X' s N c`, from `X ⊕ Fin (s + 1)` to `X' ⊕ Fin s`, kills
  `X` and the last string vector and maps `e_a` to a multiple of `e'_a`; it lowers the grade by
  one.

With the form adjoint `T† = J⁻¹ * Tᴴ * J'` of `Matrix.formAdjoint`, the shift factors through the
string map in both orders: for a self-adjoint unit `N` and a self-adjoint `c`, `T† * T` is the shift
of the longer string and `T * T†` that of the shorter one. The string itself is the orbit under the
shift of one vector: the **string powers** `𝔢^i = TauCeti.stringPower X s N c i` are multiples of
`e_i` with `𝔢 𝔢^i = 𝔢^(i+1)`. When `c` is a unit, the string map carries them to the string powers
of the shorter string, and, for self-adjoint `N` and `c`, all nonzero products `⟨𝔢^i, 𝔢^l⟩` (for
`i + l + 1 = s`) equal `-N`. When `N` and `c` are units, every vector orthogonal to `X` is a
combination of the string powers. All objects are defined over any ring and are compatible with
ring homomorphisms (the string powers when `c` is a unit), so that the statements over a field `E`
pass to vectors with coefficients in any `E`-algebra, such as the finite adeles.

## Main definitions

* `TauCeti.gradedGram X s N`: the graded Gram matrix.
* `TauCeti.gradedGrade X s`: the grade of a basis vector.
* `TauCeti.gradedShift X s N c`: the shift.
* `TauCeti.stringMap X X' s N c`: the string map from a string of length `s + 1` to one of length
  `s`.
* `TauCeti.stringPower X s N c i`: the string power `𝔢^i`, and `0` for `s ≤ i`.
* `TauCeti.gradedSplitEquiv X ϱ`: the reordering of `X ⊕ Fin (2ϱ + 1)` as the index set of the
  split form.

## Main results

* `TauCeti.isHermitian_gradedGram`, `TauCeti.inv_gradedGram`: for self-adjoint `N` the graded Gram
  matrix is hermitian, and for `N * N' = 1` its inverse is the graded Gram matrix of `N'`.
* `TauCeti.gradedGrade_inr_rev`, `TauCeti.gradedGrade_inr_lt_iff`: reversing the string negates
  the grade, and the grade strictly decreases along the string.
* `TauCeti.even_gradedGrade`: for a string of odd length every grade is even.
* `TauCeti.gradedGram_inr_inr_rev`: the pairing of a string vector with its partner.
* `TauCeti.gradedGram_mul_apply_inl`, `TauCeti.gradedGram_mul_apply_inr`: the rows of
  `gradedGram X s N * M`.
* `TauCeti.two_mul_splitLevel_gradedSplitEquiv`: along this reordering, the level of the split
  form is `ϱ - grade / 2`.
* `TauCeti.gradedGram_eq_of_even`: for even length the Gram matrix is independent of `N`,
  Hermitian and unimodular.
* `TauCeti.gradedGram_eq_submatrix_splitGram`, `TauCeti.reindex_gradedGram`: for odd length the
  graded Gram matrix is the split form `splitGram ϱ (middleGram N)`, reordered.
* `TauCeti.raisesDegree_gradedShift`, `TauCeti.stringMap_apply_eq_zero_of_ne`: the shift lowers
  the grade by two and the string map by one.
* `TauCeti.trace_gradedShift_mul_mul`: additivity of the trace against the shift on matrices
  whose differences from the identity raise the grade by degrees summing to more than two.
* `TauCeti.commute_gradedShift_fromBlocks`: the shift commutes with block diagonal matrices
  having identity string block.
* `TauCeti.conjTranspose_stringMap_mul_gradedGram_mul_stringMap`: `⟨T x, T y⟩ = ⟨x, 𝔢 y⟩`, for
  self-adjoint `N` and `c`.
* `TauCeti.stringMap_mul_gradedGram_mul_conjTranspose_stringMap`: the inverse-free form
  `T J⁻¹ Tᴴ = 𝔢' J'⁻¹` of `T * T† = 𝔢'`, stated with the graded Gram matrices of `N'` for
  `N * N' = 1` and self-adjoint `N` and `c`.
* `TauCeti.formAdjoint_stringMap_mul_stringMap`, `TauCeti.stringMap_mul_formAdjoint_stringMap`:
  `T† * T = 𝔢` and `T * T† = 𝔢'`, for a self-adjoint unit `N` and a self-adjoint `c`.
* `TauCeti.gradedShift_mulVec_stringPower`: `𝔢 𝔢^i = 𝔢^(i+1)`.
* `TauCeti.star_stringPower_dotProduct_gradedGram_mulVec_stringPower`: for a self-adjoint unit `c`
  and self-adjoint `N`, `⟨𝔢^i, 𝔢^l⟩ = -N` if `i + l + 1 = s`, and `0` otherwise.
* `TauCeti.stringMap_mulVec_stringPower`: `T 𝔢^i = 𝔢'^i`, for a unit `c`.
* `TauCeti.exists_eq_sum_smul_stringPower`: when `N` and `c` are units, the vectors orthogonal to
  `X` are the combinations of the string powers.
* `TauCeti.gradedGram_map`, `TauCeti.comp_stringPower`: compatibility with ring homomorphisms.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, files
  `src/Lib/Weil/Periods/Grading.lean` (declarations `New.gradedGram`, `New.Grading.gradeOf`,
  `New.Grading.stringMap`, `New.Grading.shift`, `New.Space.formAdjoint`,
  `New.Grading.hasDegreeGe_neg_one_stringMap`, `New.Grading.formAdjoint_stringMap`,
  `New.Grading.formAdjoint_stringMap_mul_stringMap`) and `src/Lib/Weil/Periods/StringPowers.lean`
  (`New.Grading.stringPower`, `New.Grading.shift_mulVec_stringPower`,
  `New.Grading.form_stringPower`, `New.Grading.stringMap_mulVec_stringPower`,
  `New.Grading.exists_stringSum_eq`, `New.Grading.stringMapFin_stringSum`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The statements corresponding to the listed declarations follow
  them, and the definitions here follow their conventions; the comparison with the split form
  (`TauCeti.gradedSplitEquiv`, `TauCeti.gradedGram_eq_submatrix_splitGram`,
  `TauCeti.reindex_gradedGram`) and the compatibility with ring homomorphisms are new here.
* The trace and commutation statements follow `New.Grading.trace_shift_mul` and
  `New.Grading.commute_shift_ratCoordMatrix_inclX` in `grh-lean`, file
  `src/Lib/Weil/Periods/Equivariant.lean`, under the same license and copyright above.
-/

public section

open Matrix
open scoped Ring

namespace TauCeti

variable {R : Type*} (X X' : Type*) (s : ℕ)

/-! ### Definitions -/

section Defs

/-- The **graded Gram matrix** on `X ⊕ Fin s`: the identity on `X`, `X` orthogonal to the
string `e₀, …, e_{s-1}`, and on the string the antidiagonal matrix pairing `e_a` with
`e_{s-1-a}` to `1`, except that the middle vector `e_a = e_{s-1-a}` of a string of odd length has
norm `-N`. -/
def gradedGram [Zero R] [One R] [Neg R] [DecidableEq X] (N : R) :
    Matrix (X ⊕ Fin s) (X ⊕ Fin s) R :=
  fromBlocks 1 0 0 (of fun a b ↦ if a.rev = b then if a = b then -N else 1 else 0)

/-- The **grade** of a basis vector of `X ⊕ Fin s`: `0` on `X` and `s - 1 - 2a` on `e_a`. -/
def gradedGrade : X ⊕ Fin s → ℤ :=
  Sum.elim 0 fun a ↦ (s : ℤ) - 1 - 2 * a

variable [Ring R]

/-- The factor by which the shift of a string of length `s` multiplies `e_a`: `-N c` if `e_a` has
grade `0`, `-N c²` if it has grade `1`, and `c` otherwise. -/
def gradedShiftCoeff (N c : R) (a : ℕ) : R :=
  if 2 * a + 1 = s then -N * c else if 2 * a + 2 = s then -N * c ^ 2 else c

/-- The **shift** `𝔢` of `X ⊕ Fin s` for the constants `N` and `c`: it kills `X` and the last
string vector `e_{s-1}`, and maps `e_a` to `gradedShiftCoeff s N c a • e_{a+1}`. -/
def gradedShift (N c : R) : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R :=
  fromBlocks 0 0 0 (of fun b a ↦ if (b : ℕ) = a + 1 then gradedShiftCoeff s N c a else 0)

/-- The factor by which the string map from a string of length `s + 1` multiplies `e_a`, according
to the grade `s - 2a` of `e_a`: for odd `s`, `c` in positive and `1` in negative grade; for even
`s`, `1`, `-N c` or `c` in positive, zero or negative grade. -/
def stringMapCoeff (N c : R) (a : ℕ) : R :=
  if Even s then (if 2 * a < s then 1 else if 2 * a = s then -N * c else c)
  else if 2 * a < s then c else 1

/-- The **string map** from `X ⊕ Fin (s + 1)` to `X' ⊕ Fin s`: it kills `X` and the last string
vector `e_s`, and maps `e_a` to `stringMapCoeff s N c a • e'_a` for `a < s`. -/
def stringMap (N c : R) : Matrix (X' ⊕ Fin s) (X ⊕ Fin (s + 1)) R :=
  fromBlocks 0 0 0 (of fun b a ↦ if a = b.castSucc then stringMapCoeff s N c a else 0)

/-- The scalar of the string power `𝔢^i` of a string of length `s`: `c⁻¹ ^ ⌊s/2⌋ * c ^ i` if
`2 i < s` (grade `≥ 0`) and `-N * c⁻¹ ^ ⌈s/2⌉ * c ^ (i + 1)` otherwise; for a unit `c` these are
`c ^ (i - ⌊s/2⌋)` and `-N c ^ (i + 1 - ⌈s/2⌉)`. -/
noncomputable def stringPowerCoeff (N c : R) (i : ℕ) : R :=
  if 2 * i < s then c⁻¹ʳ ^ (s / 2) * c ^ i else -N * c⁻¹ʳ ^ ((s + 1) / 2) * c ^ (i + 1)

/-- The **string power** `𝔢^i`: the multiple `stringPowerCoeff s N c i • e_i` of the string vector
`e_i`, and `0` if `s ≤ i`. -/
noncomputable def stringPower (N c : R) (i : ℕ) : X ⊕ Fin s → R :=
  Sum.elim 0 fun a ↦ if (a : ℕ) = i then stringPowerCoeff s N c i else 0

end Defs

variable {X X' s}

/-! ### Entries -/

section Entries

section Gram

variable [Zero R] [One R] [Neg R] [DecidableEq X] (N : R)

@[simp] lemma gradedGram_inl_inl (x y : X) :
    gradedGram X s N (.inl x) (.inl y) = (1 : Matrix X X R) x y := (rfl)
@[simp] lemma gradedGram_inl_inr (x : X) (b : Fin s) : gradedGram X s N (.inl x) (.inr b) = 0 :=
  (rfl)
@[simp] lemma gradedGram_inr_inl (a : Fin s) (y : X) : gradedGram X s N (.inr a) (.inl y) = 0 :=
  (rfl)
@[simp] lemma gradedGram_inr_inr (a b : Fin s) :
    gradedGram X s N (.inr a) (.inr b) = if a.rev = b then if a = b then -N else 1 else 0 := (rfl)

end Gram

@[simp] lemma gradedGrade_inl (x : X) : gradedGrade X s (.inl x) = 0 := (rfl)
@[simp] lemma gradedGrade_inr (a : Fin s) : gradedGrade X s (.inr a) = s - 1 - 2 * a := (rfl)

/-- Reversing the string negates the grade: `e_{s-1-a}` has the grade opposite to that of
`e_a`. -/
theorem gradedGrade_inr_rev (a : Fin s) :
    gradedGrade X s (.inr a.rev) = -gradedGrade X s (.inr a) := by
  simp only [gradedGrade_inr, Fin.val_rev]
  omega

/-- A string vector has grade `0` exactly when it is the middle vector of an odd string. -/
theorem gradedGrade_inr_eq_zero_iff {a : Fin s} : gradedGrade X s (.inr a) = 0 ↔ a = a.rev := by
  simp only [gradedGrade_inr, Fin.ext_iff, Fin.val_rev]
  omega

/-- A string vector has nonzero grade exactly when it differs from its reversed partner. -/
theorem gradedGrade_inr_ne_zero_iff {a : Fin s} :
    gradedGrade X s (.inr a) ≠ 0 ↔ a ≠ a.rev :=
  gradedGrade_inr_eq_zero_iff.not

/-- Reversing the string exchanges the two sides of a strict grade comparison. -/
theorem gradedGrade_inr_rev_lt_iff {a b : Fin s} :
    gradedGrade X s (.inr a.rev) < gradedGrade X s (.inr b) ↔
      gradedGrade X s (.inr b.rev) < gradedGrade X s (.inr a) := by
  simp only [gradedGrade_inr_rev, neg_lt]

/-- For a string of odd length every grade is even. -/
theorem even_gradedGrade (hs : Odd s) (k : X ⊕ Fin s) : Even (gradedGrade X s k) := by
  obtain ⟨m, rfl⟩ := hs
  rcases k with x | a
  · simp
  · exact ⟨m - a, by simp only [gradedGrade_inr]; push_cast; ring⟩

/-- The grade strictly decreases along the string. -/
theorem gradedGrade_inr_lt_iff {a b : Fin s} :
    gradedGrade X s (.inr b) < gradedGrade X s (.inr a) ↔ a < b := by
  simp only [gradedGrade_inr, Fin.lt_def]
  omega

variable [Ring R] (N c : R)

lemma gradedShiftCoeff_def (a : ℕ) : gradedShiftCoeff s N c a =
    if 2 * a + 1 = s then -N * c else if 2 * a + 2 = s then -N * c ^ 2 else c := (rfl)

lemma stringMapCoeff_def (a : ℕ) : stringMapCoeff s N c a =
    if Even s then (if 2 * a < s then 1 else if 2 * a = s then -N * c else c)
    else if 2 * a < s then c else 1 := (rfl)

lemma stringPowerCoeff_def (i : ℕ) : stringPowerCoeff s N c i =
    if 2 * i < s then c⁻¹ʳ ^ (s / 2) * c ^ i else -N * c⁻¹ʳ ^ ((s + 1) / 2) * c ^ (i + 1) := (rfl)

@[simp] lemma gradedShift_inl (x : X) (k : X ⊕ Fin s) : gradedShift X s N c (.inl x) k = 0 := by
  cases k <;> rfl
@[simp] lemma gradedShift_inr_inl (b : Fin s) (y : X) :
    gradedShift X s N c (.inr b) (.inl y) = 0 := (rfl)
@[simp] lemma gradedShift_inr_inr (a b : Fin s) :
    gradedShift X s N c (.inr b) (.inr a) =
      if (b : ℕ) = a + 1 then gradedShiftCoeff s N c a else 0 := (rfl)

@[simp] lemma stringMap_inl (x : X') (k : X ⊕ Fin (s + 1)) :
    stringMap X X' s N c (.inl x) k = 0 := by
  cases k <;> rfl
@[simp] lemma stringMap_inr_inl (b : Fin s) (y : X) :
    stringMap X X' s N c (.inr b) (.inl y) = 0 := (rfl)
@[simp] lemma stringMap_inr_inr (b : Fin s) (a : Fin (s + 1)) :
    stringMap X X' s N c (.inr b) (.inr a) =
      if a = b.castSucc then stringMapCoeff s N c a else 0 := (rfl)

@[simp] lemma stringPower_inl (i : ℕ) (x : X) : stringPower X s N c i (.inl x) = 0 := (rfl)
@[simp] lemma stringPower_inr (i : ℕ) (a : Fin s) :
    stringPower X s N c i (.inr a) = if (a : ℕ) = i then stringPowerCoeff s N c i else 0 := (rfl)

/-- The string power `𝔢^i` of a string of length `s > i` is a multiple of the basis vector
`e_i`. -/
theorem stringPower_eq_single [DecidableEq X] {i : ℕ} (hi : i < s) :
    stringPower X s N c i = Pi.single (.inr ⟨i, hi⟩) (stringPowerCoeff s N c i) := by
  ext (x | a)
  · simp
  · simp [Pi.single_apply, Fin.ext_iff, eq_comm]

/-- The string powers `𝔢^i` with `s ≤ i` vanish. -/
@[simp] theorem stringPower_eq_zero {i : ℕ} (hi : s ≤ i) : stringPower X s N c i = 0 := by
  ext (x | a)
  · simp
  · simp [show (a : ℕ) ≠ i by omega]

end Entries

/-! ### The graded Gram matrix is hermitian and invertible -/

section Gram

variable [DecidableEq X]

/-- The pairing of a string vector `e_a` with its partner `e_{s-1-a}` is `-N` for the middle
vector of an odd string and `1` otherwise. -/
theorem gradedGram_inr_inr_rev [Zero R] [One R] [Neg R] (N : R) (a : Fin s) :
    gradedGram X s N (.inr a) (.inr a.rev) = if a = a.rev then -N else 1 := by
  simp

/-- The graded Gram matrix pairs only basis vectors of opposite grades. -/
theorem gradedGram_apply_eq_zero_of_add_ne_zero [Zero R] [One R] [Neg R] (N : R)
    {k l : X ⊕ Fin s} (h : gradedGrade X s k + gradedGrade X s l ≠ 0) :
    gradedGram X s N k l = 0 := by
  rcases k with x | a <;> rcases l with y | b
  · simp at h
  · simp
  · simp
  · simp only [gradedGram_inr_inr, ite_eq_right_iff]
    rintro rfl
    simp [Fin.val_rev] at h
    omega

/-- The graded Gram matrix is block diagonal, with the identity on `X`. -/
theorem gradedGram_eq_fromBlocks [Zero R] [One R] [Neg R] (N : R) :
    gradedGram X s N = fromBlocks 1 0 0 (gradedGram X s N).toBlocks₂₂ := by
  ext (x | a) (y | b) <;> simp [Matrix.toBlocks₂₂]

/-- The graded Gram matrix acts as the identity on the rows indexed by `X`. -/
theorem gradedGram_mul_apply_inl [Fintype X] [NonAssocRing R] (N : R) {m : Type*}
    (M : Matrix (X ⊕ Fin s) m R) (x : X) (j : m) :
    (gradedGram X s N * M) (.inl x) j = M (.inl x) j := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- The graded Gram matrix moves the row of `e_{s-1-a}` to that of `e_a`, scaled by the entry
`⟨e_a, e_{s-1-a}⟩`. -/
theorem gradedGram_mul_apply_inr [Fintype X] [NonAssocRing R] (N : R) {m : Type*}
    (M : Matrix (X ⊕ Fin s) m R) (a : Fin s) (j : m) :
    (gradedGram X s N * M) (.inr a) j =
      gradedGram X s N (.inr a) (.inr a.rev) * M (.inr a.rev) j := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

/-- The graded Gram matrix is hermitian when `N` is self-adjoint. -/
theorem isHermitian_gradedGram [Ring R] [StarRing R] {N : R} (hN : star N = N) :
    (gradedGram X s N).IsHermitian := by
  ext (x | a) (y | b)
  · simp [(isHermitian_one (n := X) (α := R)).apply]
  · simp
  · simp
  · simp only [conjTranspose_apply, gradedGram_inr_inr]
    by_cases hab : a.rev = b
    · subst hab
      simp [eq_comm, apply_ite star, hN]
    · simp [hab, Fin.rev_eq_iff, Ne.symm hab]

variable [Fintype X]

/-- The graded Gram matrices of `N` and `N'` are inverse to each other when `N * N' = 1`. -/
theorem gradedGram_mul_gradedGram [Ring R] {N N' : R} (h : N * N' = 1) :
    gradedGram X s N * gradedGram X s N' = 1 := by
  ext (x | a) (y | b)
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · simp only [Matrix.mul_apply, Fintype.sum_sum_type, gradedGram_inr_inl, gradedGram_inr_inr,
      zero_mul, Finset.sum_const_zero, zero_add, ite_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, Matrix.one_apply, Sum.inr.injEq, Fin.rev_rev]
    rcases eq_or_ne a b with rfl | hab
    · by_cases ha : a = a.rev
      · simp [← ha, h]
      · simp [ha, Ne.symm ha]
    · simp [hab]

/-- The inverse of the graded Gram matrix of `N` is the graded Gram matrix of `N'` when
`N * N' = 1`. -/
theorem inv_gradedGram [CommRing R] {N N' : R} (h : N * N' = 1) :
    (gradedGram X s N)⁻¹ = gradedGram X s N' :=
  inv_eq_right_inv (gradedGram_mul_gradedGram h)

/-- The graded Gram matrix of a unit `N` is invertible. -/
theorem isUnit_det_gradedGram [CommRing R] {N : R} (hN : IsUnit N) :
    IsUnit (gradedGram X s N).det := by
  obtain ⟨u, rfl⟩ := hN
  exact isUnit_det_of_right_inverse (gradedGram_mul_gradedGram u.mul_inv)

end Gram

/-! ### Even strings -/

section Even

variable {X : Type*} {s : ℕ} [DecidableEq X]

/-- For an even string there is no middle coordinate, so the graded Gram matrix does not
depend on the middle parameter. -/
theorem gradedGram_eq_of_even [Zero R] [One R] [Neg R] (hs : Even s) (N N' : R) :
    gradedGram X s N = gradedGram X s N' := by
  obtain ⟨r, rfl⟩ := hs
  ext (x | i) (y | j)
  · simp
  · simp
  · simp
  · by_cases hij : i = j
    · subst j
      have hi : i.rev ≠ i := by grind
      simp [hi]
    · simp only [gradedGram_inr_inr, ite_eq_right hij]

/-- The graded Gram matrix of an even string is Hermitian for any middle parameter. -/
theorem isHermitian_gradedGram_of_even [Ring R] [StarRing R] (hs : Even s) (N : R) :
    (gradedGram X s N).IsHermitian := by
  rw [gradedGram_eq_of_even (X := X) hs N 1]
  exact isHermitian_gradedGram (star_one R)

/-- For an even string the graded Gram matrix is unimodular, with no unit hypothesis on
the unused middle parameter. -/
theorem isUnit_det_gradedGram_of_even [CommRing R] [Fintype X] (hs : Even s) (N : R) :
    IsUnit (gradedGram X s N).det := by
  rw [gradedGram_eq_of_even (X := X) hs N 1]
  exact isUnit_det_gradedGram isUnit_one

end Even

/-! ### Odd strings and the split form -/

section Split

/-- The reordering of the basis of `X ⊕ Fin (2ϱ + 1)` as the basis
`e₀, …, e_{ϱ-1}, x_i (i ∈ X), z, e*₀, …, e*_{ϱ-1}` of the split form: the string vectors `e_a` and
`e_{2ϱ-a}` with `a < ϱ` go to `e_a` and `e*_a`, the middle string vector `e_ϱ` goes to `z`, and
`X` goes to the middle block. -/
def gradedSplitEquiv (X : Type*) (ϱ : ℕ) : X ⊕ Fin (2 * ϱ + 1) ≃ SplitIndex ϱ (X ⊕ Unit) where
  toFun
    | .inl x => .inr (.inl (.inl x))
    | .inr a =>
      if h : (a : ℕ) < ϱ then .inl ⟨a, h⟩
      else if h' : (a : ℕ) = ϱ then .inr (.inl (.inr ()))
      else .inr (.inr ⟨2 * ϱ - a, by have := a.isLt; omega⟩)
  invFun
    | .inl a => .inr ⟨a, by omega⟩
    | .inr (.inl (.inl x)) => .inl x
    | .inr (.inl (.inr _)) => .inr ⟨ϱ, by omega⟩
    | .inr (.inr a) => .inr ⟨2 * ϱ - a, by omega⟩
  left_inv := by
    rintro (x | a)
    · rfl
    · have := a.isLt
      dsimp only
      split_ifs <;> simp only [Sum.inr.injEq, Fin.ext_iff] <;> omega
  right_inv := by
    rintro (a | (x | u) | a)
    · simp [a.isLt]
    · rfl
    · simp
    · have := a.isLt
      dsimp only
      rw [dite_eq_right (by omega), dite_eq_right (by omega)]
      simp only [Sum.inr.injEq, Fin.ext_iff]
      omega

@[simp] lemma gradedSplitEquiv_inl (ϱ : ℕ) (x : X) :
    gradedSplitEquiv X ϱ (.inl x) = .inr (.inl (.inl x)) := (rfl)

lemma gradedSplitEquiv_inr (ϱ : ℕ) (a : Fin (2 * ϱ + 1)) :
    gradedSplitEquiv X ϱ (.inr a) =
      if h : (a : ℕ) < ϱ then .inl ⟨a, h⟩
      else if h' : (a : ℕ) = ϱ then .inr (.inl (.inr ()))
      else .inr (.inr ⟨2 * ϱ - a, by have := a.isLt; omega⟩) := (rfl)

@[simp] lemma gradedSplitEquiv_symm_inl (ϱ : ℕ) (a : Fin ϱ) :
    (gradedSplitEquiv X ϱ).symm (.inl a) = .inr ⟨a, by omega⟩ := (rfl)

@[simp] lemma gradedSplitEquiv_symm_inr_inl_inl (ϱ : ℕ) (x : X) :
    (gradedSplitEquiv X ϱ).symm (.inr (.inl (.inl x))) = .inl x := (rfl)

@[simp] lemma gradedSplitEquiv_symm_inr_inl_inr (ϱ : ℕ) (u : Unit) :
    (gradedSplitEquiv X ϱ).symm (.inr (.inl (.inr u))) = .inr ⟨ϱ, by omega⟩ := (rfl)

@[simp] lemma gradedSplitEquiv_symm_inr_inr (ϱ : ℕ) (a : Fin ϱ) :
    (gradedSplitEquiv X ϱ).symm (.inr (.inr a)) = .inr ⟨2 * ϱ - a, by omega⟩ := (rfl)

variable [Zero R] [One R] [Neg R] [DecidableEq X]

/-- **For odd length the graded Gram matrix is the split form**: the graded Gram matrix of a string
of length `2ϱ + 1` is `splitGram ϱ (middleGram N)` read in the basis `gradedSplitEquiv X ϱ`. -/
theorem gradedGram_eq_submatrix_splitGram (ϱ : ℕ) (N : R) :
    gradedGram X (2 * ϱ + 1) N =
      (splitGram ϱ (middleGram N)).submatrix (gradedSplitEquiv X ϱ) (gradedSplitEquiv X ϱ) := by
  ext (x | a) (y | b)
  · simp
  · simp only [submatrix_apply, gradedSplitEquiv_inl, gradedSplitEquiv_inr, gradedGram_inl_inr]
    split_ifs <;> simp
  · simp only [submatrix_apply, gradedSplitEquiv_inl, gradedSplitEquiv_inr, gradedGram_inr_inl]
    split_ifs <;> simp
  · have := a.isLt
    have := b.isLt
    simp only [submatrix_apply, gradedSplitEquiv_inr, gradedGram_inr_inr, Fin.ext_iff,
      Fin.val_rev]
    -- Split `a` and `b` into the lower half, the middle and the upper half of the string.
    split_ifs <;> simp [Matrix.one_apply, Fin.ext_iff] <;> omega

/-- The split form `splitGram ϱ (middleGram N)` is the graded Gram matrix of a string of length
`2ϱ + 1`, reindexed along `gradedSplitEquiv X ϱ`. -/
theorem reindex_gradedGram (ϱ : ℕ) (N : R) :
    reindex (gradedSplitEquiv X ϱ) (gradedSplitEquiv X ϱ) (gradedGram X (2 * ϱ + 1) N) =
      splitGram ϱ (middleGram N) := by
  rw [gradedGram_eq_submatrix_splitGram, reindex_apply, submatrix_submatrix,
    Equiv.self_comp_symm, submatrix_id_id]

omit [Zero R] [One R] [Neg R] [DecidableEq X] in
/-- Along the reordering `gradedSplitEquiv X ϱ`, the level of the split form is determined by the
grade: `2 * level = 2ϱ - grade`, so the level increases exactly when the grade decreases. -/
theorem two_mul_splitLevel_gradedSplitEquiv (ϱ : ℕ) (k : X ⊕ Fin (2 * ϱ + 1)) :
    2 * (splitLevel (gradedSplitEquiv X ϱ k) : ℤ) = 2 * ϱ - gradedGrade X (2 * ϱ + 1) k := by
  rcases k with x | a
  · simp
  · have := a.isLt
    rw [gradedSplitEquiv_inr]
    split_ifs with h h'
    · simp
    · simp [h']
    · simp only [splitLevel_eStar, gradedGrade_inr]
      push_cast
      omega

end Split

/-! ### Grades -/

section Grades

variable [Ring R] (N c : R)

/-- The shift lowers the grade by exactly two. -/
theorem gradedShift_apply_eq_zero_of_ne {k l : X ⊕ Fin s}
    (h : gradedGrade X s k ≠ gradedGrade X s l - 2) : gradedShift X s N c k l = 0 := by
  rcases k with x | b <;> rcases l with y | a
  · simp
  · simp
  · simp
  · simp only [gradedShift_inr_inr, ite_eq_right_iff]
    intro hba
    simp only [gradedGrade_inr] at h
    omega

/-- The shift lowers the grade by two: it raises the grade by at least `-2`. -/
theorem raisesDegree_gradedShift : RaisesDegree (gradedGrade X s) (-2) (gradedShift X s N c) :=
  raisesDegree_iff.2 fun k l hkl ↦ by
    by_contra h
    exact hkl (gradedShift_apply_eq_zero_of_ne N c (by omega))

/-- The string map lowers the grade by exactly one; in particular it raises the grade by at
least `-1`. -/
theorem stringMap_apply_eq_zero_of_ne {k : X' ⊕ Fin s} {l : X ⊕ Fin (s + 1)}
    (h : gradedGrade X' s k ≠ gradedGrade X (s + 1) l - 1) : stringMap X X' s N c k l = 0 := by
  rcases k with x | b <;> rcases l with y | a
  · simp
  · simp
  · simp
  · simp only [stringMap_inr_inr, ite_eq_right_iff]
    rintro rfl
    simp at h
    omega

end Grades

/-! ### Traces against the shift -/

section Trace

variable [Ring R] [Fintype X] (N c : R)

/-- The shift has trace zero. -/
@[simp]
theorem trace_gradedShift : (gradedShift X s N c).trace = 0 :=
  Finset.sum_eq_zero fun k _ ↦ gradedShift_apply_eq_zero_of_ne N c (k := k) (l := k) (by omega)

/-- The trace of the shift times a matrix raising the grade by more than two vanishes. -/
theorem trace_gradedShift_mul_eq_zero {d : ℤ} (hd : 2 < d)
    {A : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R} (hA : RaisesDegree (gradedGrade X s) d A) :
    (gradedShift X s N c * A).trace = 0 :=
  ((raisesDegree_gradedShift N c).mul hA).trace_eq_zero (by omega)

/-- **Additivity of `A ↦ tr (𝔢 A)` on unipotent matrices.** If `A - 1` and `B - 1` raise the
grade by at least `d` and `d'` with `2 < d + d'`, then `tr (𝔢 (A B)) = tr (𝔢 A) + tr (𝔢 B)`. -/
theorem trace_gradedShift_mul_mul [DecidableEq X] {d d' : ℤ} (hdd' : 2 < d + d')
    {A B : Matrix (X ⊕ Fin s) (X ⊕ Fin s) R} (hA : RaisesDegree (gradedGrade X s) d (A - 1))
    (hB : RaisesDegree (gradedGrade X s) d' (B - 1)) :
    (gradedShift X s N c * (A * B)).trace =
      (gradedShift X s N c * A).trace + (gradedShift X s N c * B).trace := by
  have hAB : A * B = (A - 1) * (B - 1) + A + B - 1 := by noncomm_ring
  have hexpand : (gradedShift X s N c * (A * B)).trace =
      (gradedShift X s N c * ((A - 1) * (B - 1))).trace + (gradedShift X s N c * A).trace +
        (gradedShift X s N c * B).trace - (gradedShift X s N c).trace := by
    simp only [hAB, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, trace_sub, trace_add]
  rw [hexpand, trace_gradedShift_mul_eq_zero N c hdd' (hA.mul hB), trace_gradedShift, zero_add,
    sub_zero]

/-- The shift commutes with every matrix that is block diagonal with identity string block, such
as the image of `U(X)`. -/
theorem commute_gradedShift_fromBlocks (a : Matrix X X R) :
    Commute (gradedShift X s N c) (fromBlocks a 0 0 1) := by
  -- The shift is supported on the string block.
  have h : gradedShift X s N c = fromBlocks 0 0 0 (gradedShift X s N c).toBlocks₂₂ := by
    rw [← fromBlocks_toBlocks (gradedShift X s N c)]
    congr 1
  rw [commute_iff_eq, h]
  simp [fromBlocks_multiply]

end Trace

/-! ### The shift and the form adjoint of the string map -/

section Adjoint

variable [CommRing R] [StarRing R] {N c : R}

omit [StarRing R] in
/-- The coefficient identity behind `T† * T = 𝔢`. -/
private lemma stringMapCoeff_mul_stringMapCoeff {a b : ℕ} (hab : a + b + 1 = s) :
    stringMapCoeff s N c a * ((if a = s - (a + 1) then -N else 1) * stringMapCoeff s N c b) =
      (if a = s + 1 - (a + 1) then -N else 1) * gradedShiftCoeff (s + 1) N c b := by
  unfold stringMapCoeff gradedShiftCoeff
  simp only [Nat.even_iff]
  -- Each branch fixes the parity of `s` and the grades of `e_a` and `e_b`; `omega` refutes the
  -- inconsistent ones and the others are identities of polynomials in `N` and `c`.
  split_ifs <;> first
    | (exfalso; omega)
    | ring1

omit [StarRing R] in
/-- The coefficient identity behind `T * T† = 𝔢'`. -/
private lemma stringMapCoeff_mul_stringMapCoeff' {N' : R} (h : N * N' = 1) {a b : ℕ}
    (hab : a + b = s) (hb : b < s) :
    stringMapCoeff s N c a * (if a = b then -N' else 1) * stringMapCoeff s N c b =
      gradedShiftCoeff s N c (s - (b + 1)) * (if s - (b + 1) = b then -N' else 1) := by
  unfold stringMapCoeff gradedShiftCoeff
  simp only [Nat.even_iff]
  -- As above; in the two branches where `N'` occurs, it cancels against `N` by `N * N' = 1`.
  split_ifs <;> first
    | (exfalso; omega)
    | ring1
    | linear_combination (-N * c ^ 2) * h
    | linear_combination (-c) * h

private lemma star_stringMapCoeff (hN : star N = N) (hc : star c = c) (a : ℕ) :
    star (stringMapCoeff s N c a) = stringMapCoeff s N c a := by
  unfold stringMapCoeff
  split_ifs <;> simp [hN, hc]

variable [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']

/-- **The string map transports the form to the form of the shift**: `Tᴴ J' T = J 𝔢`, that is
`⟨T x, T y⟩' = ⟨x, 𝔢 y⟩` for the graded forms `J` of `X ⊕ Fin (s + 1)` and `J'` of
`X' ⊕ Fin s`. -/
theorem conjTranspose_stringMap_mul_gradedGram_mul_stringMap (hN : star N = N)
    (hc : star c = c) :
    (stringMap X X' s N c)ᴴ * gradedGram X' s N * stringMap X X' s N c =
      gradedGram X (s + 1) N * gradedShift X (s + 1) N c := by
  rw [Matrix.mul_assoc]
  ext (x | a) (y | b)
  · simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · simp only [Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply, stringMap_inl,
      stringMap_inr_inr, gradedGram_inr_inl, gradedGram_inr_inr,
      gradedShift_inr_inr, gradedShift_inl, star_zero, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add, ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    induction a using Fin.lastCases with
    | last => simp [Fin.castSucc_ne_last, eq_comm]
    | cast a =>
      simp only [Fin.castSucc_inj, apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      simp only [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, star_stringMapCoeff hN hc]
      by_cases hab : (a : ℕ) + b + 1 = s
      · rw [ite_eq_left (show (b : ℕ) = s - (a + 1) by omega),
          ite_eq_left (show s + 1 - (a + 1) = (b : ℕ) + 1 by omega)]
        simpa only [← ite_mul] using stringMapCoeff_mul_stringMapCoeff (N := N) (c := c) hab
      · rw [ite_eq_right (show (b : ℕ) ≠ s - (a + 1) by omega),
          ite_eq_right (show s + 1 - (a + 1) ≠ (b : ℕ) + 1 by omega)]
        simp

/-- **The inverse-free form of `T * T† = 𝔢'`**: `T J⁻¹ Tᴴ = 𝔢' J'⁻¹`. For `N * N' = 1`, the graded
Gram matrices of `N'` are the inverses `J⁻¹` and `J'⁻¹` of the graded forms `J` of
`X ⊕ Fin (s + 1)` and `J'` of `X' ⊕ Fin s` (`TauCeti.inv_gradedGram`), and no determinant needs
to be inverted. -/
theorem stringMap_mul_gradedGram_mul_conjTranspose_stringMap {N' : R} (h : N * N' = 1)
    (hN : star N = N) (hc : star c = c) :
    stringMap X X' s N c * gradedGram X (s + 1) N' * (stringMap X X' s N c)ᴴ =
      gradedShift X' s N c * gradedGram X' s N' := by
  ext (x | a) (y | b)
  · simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply]
  · simp only [Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply, stringMap_inr_inl,
      stringMap_inr_inr, gradedGram_inr_inl, gradedGram_inl_inr, gradedGram_inr_inr,
      gradedShift_inr_inr, gradedShift_inr_inl, star_zero, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add, ite_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      apply_ite star]
    rw [Fintype.sum_eq_single b.castSucc fun q hq ↦ by simp [hq],
      Fintype.sum_eq_single b.rev fun q hq ↦ by simp [Fin.rev_eq_iff, hq]]
    simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.val_castSucc,
      star_stringMapCoeff hN hc, ite_true]
    by_cases hab : (a : ℕ) + b = s
    · rw [ite_eq_left (show s + 1 - (a + 1) = (b : ℕ) by omega),
        ite_eq_left (show (a : ℕ) = s - (b + 1) + 1 by omega)]
      exact stringMapCoeff_mul_stringMapCoeff' h hab b.isLt
    · rw [ite_eq_right (show s + 1 - (a + 1) ≠ (b : ℕ) by omega),
        ite_eq_right (show (a : ℕ) ≠ s - (b + 1) + 1 by omega)]
      simp

/-- **`T† T = 𝔢`**: the form adjoint of the string map composed with the string map is the shift
of the longer string. -/
theorem formAdjoint_stringMap_mul_stringMap (hN : IsUnit N) (hN' : star N = N)
    (hc : star c = c) :
    formAdjoint (gradedGram X (s + 1) N) (gradedGram X' s N) (stringMap X X' s N c) *
      stringMap X X' s N c = gradedShift X (s + 1) N c := by
  rw [formAdjoint_def, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (gradedGram X' s N),
    conjTranspose_stringMap_mul_gradedGram_mul_stringMap hN' hc,
    nonsing_inv_mul_cancel_left _ _ (isUnit_det_gradedGram hN)]

/-- **`T T† = 𝔢'`**: the string map composed with its form adjoint is the shift of the shorter
string, for the same constants `N` and `c`. -/
theorem stringMap_mul_formAdjoint_stringMap (hN : IsUnit N) (hN' : star N = N)
    (hc : star c = c) :
    stringMap X X' s N c *
      formAdjoint (gradedGram X (s + 1) N) (gradedGram X' s N) (stringMap X X' s N c) =
      gradedShift X' s N c := by
  obtain ⟨u, rfl⟩ := hN
  rw [formAdjoint_def, inv_gradedGram u.mul_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    stringMap_mul_gradedGram_mul_conjTranspose_stringMap u.mul_inv hN' hc, Matrix.mul_assoc,
    gradedGram_mul_gradedGram u.inv_mul, Matrix.mul_one]

end Adjoint

/-! ### String powers -/

section StringPowers

variable [CommRing R] {N c : R}

/-- The coefficient identity behind `𝔢 𝔢^i = 𝔢^(i+1)`. -/
private lemma gradedShiftCoeff_mul_stringPowerCoeff {i : ℕ} (hi : i + 1 < s) :
    gradedShiftCoeff s N c i * stringPowerCoeff s N c i = stringPowerCoeff s N c (i + 1) := by
  by_cases hc : IsUnit c
  swap
  · -- For a nonunit `c` the inverse is `0`, and all string powers of a string of length `≥ 2`
    -- vanish.
    simp [stringPowerCoeff_def, Ring.inverse_non_unit c hc, zero_pow (show s / 2 ≠ 0 by omega),
      zero_pow (show (s + 1) / 2 ≠ 0 by omega)]
  replace hc := Ring.inverse_mul_cancel c hc
  unfold gradedShiftCoeff stringPowerCoeff
  -- Write `s = 2m` or `s = 2m + 1` and compare `i` with `m`; then the branches are decided by
  -- `omega` and the exponents agree up to one factor `c⁻¹ * c = 1`.
  obtain ⟨m, hs | hs⟩ := Nat.even_or_odd' s
  · rw [show s / 2 = m by omega, show (s + 1) / 2 = m by omega]
    rcases lt_trichotomy (i + 1) m with h | rfl | h <;> split_ifs <;> first
      | (exfalso; omega)
      | ring1
  · rw [show s / 2 = m by omega, show (s + 1) / 2 = m + 1 by omega]
    rcases lt_trichotomy i m with h | rfl | h <;> split_ifs <;> first
      | (exfalso; omega)
      | ring1
      | linear_combination (N * c⁻¹ʳ ^ i * c ^ (i + 1)) * hc

/-- The coefficient identity behind `⟨𝔢^i, 𝔢^l⟩ = -N`. -/
private lemma stringPowerCoeff_mul_stringPowerCoeff (hc : c⁻¹ʳ * c = 1) {i l : ℕ}
    (hil : i + l + 1 = s) :
    stringPowerCoeff s N c i *
      (if i = l then -N * stringPowerCoeff s N c l else 1 * stringPowerCoeff s N c l) = -N := by
  have key (k : ℕ) : c⁻¹ʳ ^ k * c ^ k = 1 := by rw [← mul_pow, hc, one_pow]
  unfold stringPowerCoeff
  split_ifs <;> try (exfalso; omega)
  · obtain rfl : i = l := by omega
    calc _ = -N * (c⁻¹ʳ ^ (s / 2 + s / 2) * c ^ (i + i)) := by ring
      _ = -N := by rw [show s / 2 + s / 2 = i + i by omega, key, mul_one]
  · calc _ = -N * (c⁻¹ʳ ^ (s / 2 + (s + 1) / 2) * c ^ (i + (l + 1))) := by ring
      _ = -N := by rw [show s / 2 + (s + 1) / 2 = i + (l + 1) by omega, key, mul_one]
  · calc _ = -N * (c⁻¹ʳ ^ (s / 2 + (s + 1) / 2) * c ^ (l + (i + 1))) := by ring
      _ = -N := by rw [show s / 2 + (s + 1) / 2 = l + (i + 1) by omega, key, mul_one]

/-- The coefficient identity behind `T 𝔢^i = 𝔢'^i`. -/
private lemma stringMapCoeff_mul_stringPowerCoeff (hc : c⁻¹ʳ * c = 1) (i : ℕ) :
    stringMapCoeff s N c i * stringPowerCoeff (s + 1) N c i = stringPowerCoeff s N c i := by
  unfold stringMapCoeff stringPowerCoeff
  simp only [Nat.even_iff]
  -- As for the shift: fix the parity of `s` and the position of `i` relative to `s / 2`.
  obtain ⟨m, hs | hs⟩ := Nat.even_or_odd' s
  · rw [show s / 2 = m by omega, show (s + 1) / 2 = m by omega,
      show (s + 1 + 1) / 2 = m + 1 by omega]
    rcases lt_trichotomy i m with h | rfl | h <;> split_ifs <;> first
      | (exfalso; omega)
      | ring1
      | linear_combination (-N * c⁻¹ʳ ^ m * c ^ (i + 1)) * hc
  · rw [show s / 2 = m by omega, show (s + 1) / 2 = m + 1 by omega,
      show (s + 1 + 1) / 2 = m + 1 by omega]
    rcases lt_trichotomy i m with h | rfl | h <;> split_ifs <;> first
      | (exfalso; omega)
      | ring1
      | linear_combination (c⁻¹ʳ ^ m * c ^ i) * hc
      | linear_combination (c⁻¹ʳ ^ i * c ^ i) * hc

/-- The scalars of the string powers are units when `N` and `c` are. -/
theorem isUnit_stringPowerCoeff (hN : IsUnit N) (hc : IsUnit c) (i : ℕ) :
    IsUnit (stringPowerCoeff s N c i) := by
  rw [stringPowerCoeff_def]
  split_ifs
  · exact (hc.ringInverse.pow _).mul (hc.pow _)
  · exact ((hN.neg.mul (hc.ringInverse.pow _))).mul (hc.pow _)

variable [Fintype X]

/-- **The shift moves the string powers along the string**: `𝔢 𝔢^i = 𝔢^(i+1)`; in particular
`𝔢 𝔢^(s-1) = 0`. -/
@[simp] theorem gradedShift_mulVec_stringPower (i : ℕ) :
    gradedShift X s N c *ᵥ stringPower X s N c i = stringPower X s N c (i + 1) := by
  classical
  rcases lt_or_ge i s with hi | hi
  · rw [stringPower_eq_single N c hi, mulVec_single]
    ext (x | b)
    · simp
    · simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, col_apply,
        gradedShift_inr_inr, stringPower_inr, ite_mul, zero_mul]
      split_ifs with h
      · exact gradedShiftCoeff_mul_stringPowerCoeff (by omega)
      · rfl
  · rw [stringPower_eq_zero N c hi, stringPower_eq_zero N c (by omega), mulVec_zero]

/-- The string power `𝔢^i` is the image of `𝔢^0` under the `i`-th power of the shift. -/
@[simp] theorem gradedShift_pow_mulVec_stringPower_zero [DecidableEq X] (i : ℕ) :
    gradedShift X s N c ^ i *ᵥ stringPower X s N c 0 = stringPower X s N c i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', ← mulVec_mulVec, ih, gradedShift_mulVec_stringPower]

/-- **The products of the string powers**: `⟨𝔢^i, 𝔢^l⟩ = -N` if `i + l + 1 = s`, and `0`
otherwise. -/
theorem star_stringPower_dotProduct_gradedGram_mulVec_stringPower [DecidableEq X] [StarRing R]
    (hN : star N = N) (hc : IsUnit c) (hc' : star c = c) (i l : ℕ) :
    star (stringPower X s N c i) ⬝ᵥ gradedGram X s N *ᵥ stringPower X s N c l =
      if i + l + 1 = s then -N else 0 := by
  rcases lt_or_ge i s with hi | hi
  · rcases lt_or_ge l s with hl | hl
    · rw [stringPower_eq_single N c hi, stringPower_eq_single N c hl, mulVec_single,
        Pi.star_single, single_dotProduct]
      simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, col_apply,
        gradedGram_inr_inr, Fin.ext_iff, Fin.val_rev, ite_mul, zero_mul]
      have hstar : star (stringPowerCoeff s N c i) = stringPowerCoeff s N c i := by
        rw [stringPowerCoeff_def]
        split_ifs <;> simp [hN, hc', ← Ring.inverse_star, mul_comm]
      by_cases hil : i + l + 1 = s
      · rw [ite_eq_left (show s - (i + 1) = l by omega), ite_eq_left hil, hstar]
        exact stringPowerCoeff_mul_stringPowerCoeff (Ring.inverse_mul_cancel c hc) hil
      · rw [ite_eq_right (show s - (i + 1) ≠ l by omega), ite_eq_right hil, mul_zero]
    · rw [stringPower_eq_zero N c hl, mulVec_zero, dotProduct_zero,
        ite_eq_right (show i + l + 1 ≠ s by omega)]
  · rw [stringPower_eq_zero N c hi, ite_eq_right (show i + l + 1 ≠ s by omega)]
    simp [dotProduct]

/-- **The string map carries string powers to string powers**: `T 𝔢^i = 𝔢'^i`, for the same
constants `N` and `c`; in particular `T 𝔢^s = 0`. -/
theorem stringMap_mulVec_stringPower (hc : IsUnit c) (i : ℕ) :
    stringMap X X' s N c *ᵥ stringPower X (s + 1) N c i = stringPower X' s N c i := by
  classical
  rcases lt_or_ge i (s + 1) with hi | hi
  · rw [stringPower_eq_single N c hi, mulVec_single]
    ext (x | b)
    · simp
    · simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, col_apply,
        stringMap_inr_inr, stringPower_inr, ite_mul, zero_mul, Fin.ext_iff, Fin.val_castSucc]
      split_ifs <;> first
        | exact stringMapCoeff_mul_stringPowerCoeff (Ring.inverse_mul_cancel c hc) i
        | rfl
        | (exfalso; omega)
  · rw [stringPower_eq_zero N c hi, stringPower_eq_zero N c (by omega), mulVec_zero]

omit [Fintype X] in
/-- The coordinates of a combination of the string powers. -/
theorem sum_smul_stringPower_inr (t : Fin s → R) (a : Fin s) :
    (∑ i : Fin s, t i • stringPower X s N c i) (.inr a) = t a * stringPowerCoeff s N c a := by
  simp only [Finset.sum_apply, Pi.smul_apply, stringPower_inr, smul_eq_mul, mul_ite, mul_zero]
  rw [Fintype.sum_eq_single a fun i hi ↦ by simp [Fin.val_ne_of_ne (Ne.symm hi)]]
  simp

omit [Fintype X] in
/-- **The string powers span the orthogonal complement of `X`**: when `N` and `c` are units,
every vector `v` of `R^(X ⊕ Fin s)` vanishing on `X` is a combination `∑ i, t i • 𝔢^i`. -/
theorem exists_eq_sum_smul_stringPower (hN : IsUnit N) (hc : IsUnit c) (v : X ⊕ Fin s → R)
    (hv : ∀ x, v (.inl x) = 0) : ∃ t : Fin s → R, v = ∑ i : Fin s, t i • stringPower X s N c i := by
  refine ⟨fun i ↦ v (.inr i) * (stringPowerCoeff s N c i)⁻¹ʳ, ?_⟩
  ext (x | a)
  · simp [hv]
  · rw [sum_smul_stringPower_inr, mul_assoc,
      Ring.inverse_mul_cancel _ (isUnit_stringPowerCoeff hN hc a), mul_one]

/-- The string map carries a combination of the string powers to the same combination of the
string powers of the shorter string. -/
theorem stringMap_mulVec_sum_smul_stringPower (hc : IsUnit c)
    (t : Fin (s + 1) → R) :
    stringMap X X' s N c *ᵥ ∑ i : Fin (s + 1), t i • stringPower X (s + 1) N c i =
      ∑ i : Fin (s + 1), t i • stringPower X' s N c i := by
  simp only [mulVec_sum, mulVec_smul, stringMap_mulVec_stringPower hc]

end StringPowers

/-! ### Change of rings -/

section Map

variable {S : Type*}

/-- The graded Gram matrix is compatible with ring homomorphisms. -/
@[simp] theorem gradedGram_map [Ring R] [Ring S] [DecidableEq X] (f : R →+* S) (N : R) :
    (gradedGram X s N).map f = gradedGram X s (f N) := by
  ext (x | a) (y | b) <;> simp [Matrix.one_apply, apply_ite f]

/-- The shift is compatible with ring homomorphisms. -/
@[simp] theorem gradedShift_map [Ring R] [Ring S] (f : R →+* S) (N c : R) :
    (gradedShift X s N c).map f = gradedShift X s (f N) (f c) := by
  ext (x | b) (y | a) <;> simp [gradedShiftCoeff_def, apply_ite f]

/-- The string map is compatible with ring homomorphisms. -/
@[simp] theorem stringMap_map [Ring R] [Ring S] (f : R →+* S) (N c : R) :
    (stringMap X X' s N c).map f = stringMap X X' s (f N) (f c) := by
  ext (x | b) (y | a) <;> simp [stringMapCoeff_def, apply_ite f]

/-- The string powers are compatible with ring homomorphisms, when `c` is a unit. -/
theorem comp_stringPower [CommRing R] [CommRing S] (f : R →+* S) {c : R} (hc : IsUnit c)
    (N : R) (i : ℕ) : f ∘ stringPower X s N c i = stringPower X s (f N) (f c) i := by
  have hinv : f c⁻¹ʳ = (f c)⁻¹ʳ := by
    obtain ⟨u, rfl⟩ := hc
    simpa using (Ring.inverse_unit (Units.map (f : R →* S) u)).symm
  ext (x | a) <;> simp [stringPowerCoeff_def, apply_ite f, hinv]

end Map

end TauCeti

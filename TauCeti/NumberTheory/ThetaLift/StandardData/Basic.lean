/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.LinearAlgebra.Matrix.Determinant.RowCompletion
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UnimodularFrame.Semilocal
import TauCeti.LinearAlgebra.Matrix.Submatrix

/-!
# Standard row and column data

For an integral matrix `s` with `b` rows and `b + a` columns, the standard row datum
at `x` is the inverse determinant character of the square matrix with rows `s, x`.
The standard column datum at `y` is the inverse determinant character of `s * y`.
Both are extended by zero from integral matrices to matrices over the ambient ring.
A multiplicative character of the integral subring already vanishes on nonunits.

These functions are partners: their values on the last rows of `k⁻¹` and the first
columns of `k` differ by the determinant character of `k`. Over a semilocal integral
subring, they are supported on blocks of invertible integral matrices. These
algebraic facts allow row data to be exchanged with column data in local theta integrals.

## References

The standard data and partner assertion follow [ShortProof], `lsernau/grh-lean` at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`,
[grh/src/Lib/SiegelWeil/Tower/LineGaussSums.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/SiegelWeil/Tower/LineGaussSums.lean)
(`New.stdRowDatum`, `New.stdColDatum`, `New.areMatched_stdRowDatum_stdColDatum`).
Its column-support input is `New.IsValuationPair.exists_firstCols_iff` in
[grh/src/Lib/General/LinearAlgebra/PartnerAlgebra.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/General/LinearAlgebra/PartnerAlgebra.lean).
The proofs here are independent.
-/

public section

noncomputable section

open Matrix

namespace Subring

variable {A C b a : Type*} [CommRing A] [CommGroupWithZero C]
  [Fintype b] [Fintype a] [DecidableEq b] [DecidableEq a]

/-- The standard row datum, extended by zero off integral matrices.
The first block of rows is `s`; its character is evaluated on the determinant of `s, x`. -/
def standardRowDatum (O : Subring A) (χ : MulChar O C) (s : Matrix b (b ⊕ a) O) :
    Matrix a (b ⊕ a) A → C :=
  Function.extend (fun M : Matrix a (b ⊕ a) O ↦ M.map Subtype.val)
    (fun x ↦ (χ (fromRows s x).det)⁻¹) 0

/-- The standard column datum, extended by zero off integral matrices.
The determinant character vanishes unless `s * y` is invertible over `O`. -/
def standardColDatum (O : Subring A) (χ : MulChar O C) (s : Matrix b (b ⊕ a) O) :
    Matrix (b ⊕ a) b A → C :=
  Function.extend (fun M : Matrix (b ⊕ a) b O ↦ M.map Subtype.val) (fun y ↦ (χ (s * y).det)⁻¹) 0

variable (O : Subring A) (χ : MulChar O C) (s : Matrix b (b ⊕ a) O)

/-- Unfold the standard row datum as extension by zero. -/
theorem standardRowDatum_def : O.standardRowDatum χ s =
    Function.extend (fun M : Matrix a (b ⊕ a) O ↦ M.map Subtype.val)
    (fun x ↦ (χ (fromRows s x).det)⁻¹) 0 :=
  (rfl)

omit [DecidableEq a] in
/-- Unfold the standard column datum as extension by zero. -/
theorem standardColDatum_def : O.standardColDatum χ s =
    Function.extend (fun M : Matrix (b ⊕ a) b O ↦ M.map Subtype.val)
      (fun y ↦ (χ (s * y).det)⁻¹) 0 :=
  (rfl)

@[simp]
theorem standardRowDatum_map (x : Matrix a (b ⊕ a) O) :
    O.standardRowDatum χ s (x.map Subtype.val) = (χ (fromRows s x).det)⁻¹ :=
  (Matrix.map_injective O.subtype_injective).extend_apply _ _ x

omit [DecidableEq a] in
@[simp]
theorem standardColDatum_map (y : Matrix (b ⊕ a) b O) :
    O.standardColDatum χ s (y.map Subtype.val) = (χ (s * y).det)⁻¹ :=
  (Matrix.map_injective O.subtype_injective).extend_apply _ _ y

/-- The row datum vanishes at a matrix with a nonintegral entry. -/
theorem standardRowDatum_eq_zero_of_not_integral {x : Matrix a (b ⊕ a) A}
    (hx : ¬ ∃ x₀ : Matrix a (b ⊕ a) O, x₀.map Subtype.val = x) :
    O.standardRowDatum χ s x = 0 :=
  Function.extend_apply' _ _ _ hx

omit [DecidableEq a] in
/-- The column datum vanishes at a matrix with a nonintegral entry. -/
theorem standardColDatum_eq_zero_of_not_integral {y : Matrix (b ⊕ a) b A}
    (hy : ¬ ∃ y₀ : Matrix (b ⊕ a) b O, y₀.map Subtype.val = y) :
    O.standardColDatum χ s y = 0 :=
  Function.extend_apply' _ _ _ hy

/-- Nonvanishing is precisely integrality and invertibility of the completed row matrix. -/
theorem standardRowDatum_ne_zero_iff {x : Matrix a (b ⊕ a) A} :
    O.standardRowDatum χ s x ≠ 0 ↔ ∃ x₀ : Matrix a (b ⊕ a) O,
      x₀.map Subtype.val = x ∧ IsUnit (fromRows s x₀).det := by
  constructor
  · intro hx
    obtain ⟨x₀, rfl⟩ := not_not.mp (mt
      (O.standardRowDatum_eq_zero_of_not_integral χ s) hx)
    rw [standardRowDatum_map, ne_eq, inv_eq_zero] at hx
    exact ⟨x₀, rfl, MulChar.apply_ne_zero_iff.mp hx⟩
  · rintro ⟨x₀, rfl, hx⟩
    rw [standardRowDatum_map, ne_eq, inv_eq_zero]
    exact MulChar.apply_ne_zero_iff.mpr hx

omit [DecidableEq a] in
/-- Nonvanishing is precisely integrality and invertibility of the pairing matrix. -/
theorem standardColDatum_ne_zero_iff {y : Matrix (b ⊕ a) b A} :
    O.standardColDatum χ s y ≠ 0 ↔ ∃ y₀ : Matrix (b ⊕ a) b O,
      y₀.map Subtype.val = y ∧ IsUnit (s * y₀).det := by
  constructor
  · intro hy
    obtain ⟨y₀, rfl⟩ := not_not.mp (mt
      (O.standardColDatum_eq_zero_of_not_integral χ s) hy)
    rw [standardColDatum_map, ne_eq, inv_eq_zero] at hy
    exact ⟨y₀, rfl, MulChar.apply_ne_zero_iff.mp hy⟩
  · rintro ⟨y₀, rfl, hy⟩
    rw [standardColDatum_map, ne_eq, inv_eq_zero]
    exact MulChar.apply_ne_zero_iff.mpr hy

omit [DecidableEq a] in
/-- A nonzero column datum has an integral left inverse. -/
theorem exists_leftInverse_of_standardColDatum_ne_zero {y : Matrix (b ⊕ a) b A}
    (hy : O.standardColDatum χ s y ≠ 0) :
    ∃ (y₀ : Matrix (b ⊕ a) b O) (t : Matrix b (b ⊕ a) O),
      y₀.map Subtype.val = y ∧ t * y₀ = 1 := by
  obtain ⟨y₀, hmap, hdet⟩ := (O.standardColDatum_ne_zero_iff χ s).mp hy
  exact ⟨y₀, (s * y₀)⁻¹ * s, hmap, by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hdet]⟩

/-- The standard row and column data satisfy the determinant matching identity. -/
theorem standardRowDatum_inv_rows_eq_mul_standardColDatum
    (k : GeneralLinearGroup (b ⊕ a) O) :
    O.standardRowDatum χ s (((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) O).toRows₂).map Subtype.val) =
    χ (k : Matrix (b ⊕ a) (b ⊕ a) O).det *
      O.standardColDatum χ s (((k : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁).map Subtype.val) := by
  rw [standardRowDatum_map, standardColDatum_map,
    ← det_fromRows_toRows₂_inv_mul_det s k, map_mul, _root_.mul_inv_rev]
  have hχ : χ (k : Matrix (b ⊕ a) (b ⊕ a) O).det ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr k.det.isUnit
  simp [hχ]

/-- Every point where the row datum is nonzero is the last rows of an integral inverse. -/
theorem exists_inv_rows_of_standardRowDatum_ne_zero {x : Matrix a (b ⊕ a) A}
    (hx : O.standardRowDatum χ s x ≠ 0) :
    ∃ k : GeneralLinearGroup (b ⊕ a) O,
      (((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) O).toRows₂).map Subtype.val) = x := by
  obtain ⟨x₀, hmap, hdet⟩ := (O.standardRowDatum_ne_zero_iff χ s).mp hx
  obtain ⟨g, hg⟩ := (isUnit_iff_isUnit_det (fromRows s x₀)).mpr hdet
  refine ⟨g⁻¹, ?_⟩
  simpa only [inv_inv, hg, toRows₂_fromRows] using hmap

/-- Over a semilocal ring every point where the column datum is nonzero is the first
columns of an integral invertible matrix. -/
theorem exists_cols_of_standardColDatum_ne_zero [Finite (MaximalSpectrum O)]
    {y : Matrix (b ⊕ a) b A} (hy : O.standardColDatum χ s y ≠ 0) :
    ∃ k : GeneralLinearGroup (b ⊕ a) O,
      (((k : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁).map Subtype.val) = y := by
  obtain ⟨y₀, t, hmap, ht⟩ := O.exists_leftInverse_of_standardColDatum_ne_zero χ s hy
  have hframe : y₀ ∈ TauCeti.unimodularFrames O (b ⊕ a) b :=
    TauCeti.mem_unimodularFrames_iff.mpr ⟨t, ht⟩
  rw [← TauCeti.orbit_submatrix_one Sum.inl_injective] at hframe
  obtain ⟨k, hk⟩ := hframe
  refine ⟨k, ?_⟩
  have hcols : (k : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁ = y₀ := by
    ext i j
    simpa [GeneralLinearGroup.smul_def, Matrix.mul_apply, Matrix.one_apply]
      using congrFun₂ hk i j
  exact (congrArg (fun M ↦ M.map Subtype.val) hcols).trans hmap

/-- Simultaneous right multiplication of the fixed and varying rows scales the datum
by the inverse determinant character. No invertibility hypothesis is needed. -/
theorem standardRowDatum_mul_right (x : Matrix a (b ⊕ a) O)
    (k : Matrix (b ⊕ a) (b ⊕ a) O) :
    O.standardRowDatum χ (s * k) ((x * k).map Subtype.val) =
      (χ k.det)⁻¹ * O.standardRowDatum χ s (x.map Subtype.val) := by
  simp only [standardRowDatum_map, ← fromRows_mul, det_mul, map_mul, _root_.mul_inv_rev]

omit [DecidableEq a] in
/-- Right multiplication of the column frame scales the datum by the inverse
determinant character. No invertibility hypothesis is needed. -/
theorem standardColDatum_mul_right (y : Matrix (b ⊕ a) b O) (t : Matrix b b O) :
    O.standardColDatum χ s ((y * t).map Subtype.val) =
      (χ t.det)⁻¹ * O.standardColDatum χ s (y.map Subtype.val) := by
  simp only [standardColDatum_map, ← Matrix.mul_assoc, det_mul, map_mul, _root_.mul_inv_rev]

omit s in
/-- The row datum of the standard first rows takes value one on the standard last rows. -/
theorem standardRowDatum_one :
    O.standardRowDatum χ ((1 : Matrix (b ⊕ a) (b ⊕ a) O).toRows₁)
      (((1 : Matrix (b ⊕ a) (b ⊕ a) O).toRows₂).map Subtype.val) = 1 := by
  rw [standardRowDatum_map, fromRows_toRows, det_one, map_one, inv_one]

omit s in
/-- The column datum of the standard first rows takes value one on the standard first columns. -/
@[simp high] -- No simp lemma reduces the product of these two blocks of the identity.
theorem standardColDatum_one :
    O.standardColDatum χ ((1 : Matrix (b ⊕ a) (b ⊕ a) O).toRows₁)
      (((1 : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁).map Subtype.val) = 1 := by
  have hcols : (1 : Matrix (b ⊕ a) (b ⊕ a) O).toRows₁ *
      (1 : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁ = 1 :=
    submatrix_one_mul_submatrix_one ⟨Sum.inl, Sum.inl_injective⟩
  rw [standardColDatum_map, hcols, det_one, map_one, inv_one]

/-- Partners have support on complementary blocks of integral invertible matrices and
satisfy the determinant matching identity there. The coordinate order is `b ⊕ a`. -/
structure AreMatrixPartners (Φ : Matrix a (b ⊕ a) A → C) (Ψ : Matrix (b ⊕ a) b A → C) : Prop where
  /-- The row datum is supported on last rows of integral inverses. -/
  row_support : ∀ x, Φ x ≠ 0 → ∃ k : GeneralLinearGroup (b ⊕ a) O,
    (((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) O).toRows₂).map Subtype.val) = x
  /-- The column datum is supported on first columns of integral units. -/
  col_support : ∀ y, Ψ y ≠ 0 → ∃ k : GeneralLinearGroup (b ⊕ a) O,
    (((k : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁).map Subtype.val) = y
  /-- Values on complementary blocks satisfy the determinant identity. -/
  apply_inv_rows_eq : ∀ k : GeneralLinearGroup (b ⊕ a) O,
    Φ (((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) O).toRows₂).map Subtype.val) =
      χ (k : Matrix (b ⊕ a) (b ⊕ a) O).det *
        Ψ (((k : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁).map Subtype.val)

omit s in
/-- The support conditions and value identity characterizing partners. -/
theorem areMatrixPartners_iff (Φ : Matrix a (b ⊕ a) A → C)
    (Ψ : Matrix (b ⊕ a) b A → C) : O.AreMatrixPartners χ Φ Ψ ↔
    (∀ x, Φ x ≠ 0 → ∃ k : GeneralLinearGroup (b ⊕ a) O,
      (((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) O).toRows₂).map Subtype.val) = x) ∧
    (∀ y, Ψ y ≠ 0 → ∃ k : GeneralLinearGroup (b ⊕ a) O,
      (((k : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁).map Subtype.val) = y) ∧
    ∀ k : GeneralLinearGroup (b ⊕ a) O,
      Φ (((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) O).toRows₂).map Subtype.val) =
        χ (k : Matrix (b ⊕ a) (b ⊕ a) O).det *
          Ψ (((k : Matrix (b ⊕ a) (b ⊕ a) O).toCols₁).map Subtype.val) :=
  ⟨fun h ↦ ⟨h.row_support, h.col_support, h.apply_inv_rows_eq⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Standard row and column data are partners over a semilocal integral subring. -/
theorem areMatrixPartners_standardData [Finite (MaximalSpectrum O)] :
    O.AreMatrixPartners χ (O.standardRowDatum χ s) (O.standardColDatum χ s) :=
  ⟨fun _ ↦ O.exists_inv_rows_of_standardRowDatum_ne_zero χ s,
    (fun _ ↦ O.exists_cols_of_standardColDatum_ne_zero χ s),
    O.standardRowDatum_inv_rows_eq_mul_standardColDatum χ s⟩

variable {O χ}

omit s in
/-- Multiplying both data by the same constant preserves their partnership. -/
theorem AreMatrixPartners.const_mul {Φ : Matrix a (b ⊕ a) A → C}
    {Ψ : Matrix (b ⊕ a) b A → C} (h : O.AreMatrixPartners χ Φ Ψ) (c : C) :
    O.AreMatrixPartners χ (fun x ↦ c * Φ x) (fun y ↦ c * Ψ y) := by
  refine ⟨fun x hx ↦ h.row_support x (mul_ne_zero_iff.mp hx).2,
    (fun y hy ↦ h.col_support y (mul_ne_zero_iff.mp hy).2), fun k ↦ ?_⟩
  rw [h.apply_inv_rows_eq k]
  exact mul_left_comm _ _ _

omit s in
/-- A column datum has at most one row partner. -/
theorem AreMatrixPartners.row_eq {Φ Φ' : Matrix a (b ⊕ a) A → C}
    {Ψ : Matrix (b ⊕ a) b A → C} (h : O.AreMatrixPartners χ Φ Ψ)
    (h' : O.AreMatrixPartners χ Φ' Ψ) : Φ = Φ' := by
  funext x
  by_cases hx : Φ x = 0
  · by_cases hx' : Φ' x = 0
    · exact hx.trans hx'.symm
    · obtain ⟨k, rfl⟩ := h'.row_support x hx'
      exact (h.apply_inv_rows_eq k).trans (h'.apply_inv_rows_eq k).symm
  · obtain ⟨k, rfl⟩ := h.row_support x hx
    exact (h.apply_inv_rows_eq k).trans (h'.apply_inv_rows_eq k).symm

omit s in
/-- A row datum has at most one column partner. -/
theorem AreMatrixPartners.col_eq {Φ : Matrix a (b ⊕ a) A → C}
    {Ψ Ψ' : Matrix (b ⊕ a) b A → C} (h : O.AreMatrixPartners χ Φ Ψ)
    (h' : O.AreMatrixPartners χ Φ Ψ') : Ψ = Ψ' := by
  have heq (k : GeneralLinearGroup (b ⊕ a) O) :=
    mul_left_cancel₀ (MulChar.apply_ne_zero_iff.mpr k.det.isUnit :
      χ (k : Matrix (b ⊕ a) (b ⊕ a) O).det ≠ 0)
      ((h.apply_inv_rows_eq k).symm.trans (h'.apply_inv_rows_eq k))
  funext y
  by_cases hy : Ψ y = 0
  · by_cases hy' : Ψ' y = 0
    · exact hy.trans hy'.symm
    · obtain ⟨k, rfl⟩ := h'.col_support y hy'
      exact heq k
  · obtain ⟨k, rfl⟩ := h.col_support y hy
    exact heq k

end Subring

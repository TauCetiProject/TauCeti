/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.MvPolynomial

/-!
# Entry heights of matrices

Over a field `K` with admissible absolute values, the entry height `Matrix.mulHeight A` of a
matrix `A` with finite row and column index types is the projective multiplicative height
`Height.mulHeight` of the tuple of its entries, indexed by pairs of a row and a column, and
`Matrix.logHeight A` is its logarithm. Like every projective height, it is unchanged by nonzero
scalar multiplication, and the zero matrix, in particular every matrix with an empty row or
column index type, has entry height one. It is unchanged by transposition and by reindexing rows
and columns, and it does not increase on passing to a submatrix. Over number fields it is
relative: in an extension `L / K` the entry height of `A` is raised to the degree `[L : K]`.

The entry height of a product is at most `(#n) ^ totalWeight K` times the product of the entry
heights of the factors, where `n` is the inner index type
(`Matrix.mulHeight_mul_le`). The factor `#n` is paid only at the archimedean places, and the
bound needs `n` nonempty: a product over an empty inner index type is the zero matrix, of entry
height one, while `(#n) ^ totalWeight ℚ = 0`. Over `ℚ` the constant is attained by
`[1 1] * [[1, 0], [1, 1]] = [2 1]`, whose factors have entry height one and whose product has
entry height `2`. The Arakelov height, whose archimedean local factors are Euclidean norms, obeys
the same product bound with constant one (`Matrix.arakelovMulHeight_mul_le`).

The entry height of a matrix is a different object from the height of its row space, which is
computed from its maximal minors (`Submodule.relativeSubspaceHeight`).

## Main definitions

* `Matrix.mulHeight A`, `Matrix.logHeight A`: the multiplicative and logarithmic entry heights.

## Main results

* `Matrix.mulHeight_smul`, `Matrix.mulHeight_transpose`, `Matrix.mulHeight_submatrix_equiv` and
  `Matrix.mulHeight_submatrix_le`: projectivity and behaviour under reindexing.
* `Matrix.mulHeight_mul_le` and `Matrix.logHeight_mul_le`: the entry height of a product.
* `Matrix.mulHeight_map_algebraMap`: over number fields, the entry height in an extension
  `L / K` is the `[L : K]`-th power of the entry height over `K`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press,
  2006, §1.6 and §2.8.

The product bound is reduced to Mathlib's bound for linear maps,
`Height.mulHeight_linearMap_apply_le`, and its bound for pointwise products,
`Height.mulHeight_mul_le`.
-/

public section

open Height

namespace Matrix

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {m n p m' n' : Type*}

/-- The multiplicative entry height of a matrix: the projective multiplicative height of the
tuple of its entries, indexed by pairs of a row and a column. -/
noncomputable def mulHeight (A : Matrix m n K) : ℝ :=
  Height.mulHeight fun q : m × n ↦ A q.1 q.2

/-- The logarithmic entry height of a matrix, the logarithm of `Matrix.mulHeight`. -/
noncomputable def logHeight (A : Matrix m n K) : ℝ := Real.log A.mulHeight

theorem mulHeight_def (A : Matrix m n K) :
    A.mulHeight = Height.mulHeight fun q : m × n ↦ A q.1 q.2 := (rfl)

theorem logHeight_eq_log_mulHeight (A : Matrix m n K) : A.logHeight = Real.log A.mulHeight :=
  (rfl)

/-- The logarithmic entry height is the logarithmic height of the tuple of entries. -/
theorem logHeight_def (A : Matrix m n K) :
    A.logHeight = Height.logHeight fun q : m × n ↦ A q.1 q.2 := (rfl)

@[simp]
theorem mulHeight_zero : (0 : Matrix m n K).mulHeight = 1 :=
  Height.mulHeight_zero

@[simp]
theorem logHeight_zero : (0 : Matrix m n K).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_neg (A : Matrix m n K) : (-A).mulHeight = A.mulHeight :=
  Height.mulHeight_neg (fun q : m × n ↦ A q.1 q.2)

@[simp]
theorem logHeight_neg (A : Matrix m n K) : (-A).logHeight = A.logHeight := by
  simp [logHeight_eq_log_mulHeight]

/-- The entry height does not change under reindexing the rows and the columns along
equivalences, in particular under `Matrix.reindex`. -/
@[simp]
theorem mulHeight_submatrix_equiv (A : Matrix m n K) (e₁ : m' ≃ m) (e₂ : n' ≃ n) :
    (A.submatrix e₁ e₂).mulHeight = A.mulHeight :=
  mulHeight_comp_equiv (e₁.prodCongr e₂) (fun q : m × n ↦ A q.1 q.2)

@[simp]
theorem logHeight_submatrix_equiv (A : Matrix m n K) (e₁ : m' ≃ m) (e₂ : n' ≃ n) :
    (A.submatrix e₁ e₂).logHeight = A.logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_submatrix_equiv, logHeight_eq_log_mulHeight]

/-- The entry height does not change under transposition. -/
@[simp]
theorem mulHeight_transpose (A : Matrix m n K) : Aᵀ.mulHeight = A.mulHeight :=
  mulHeight_comp_equiv (Equiv.prodComm n m) (fun q : m × n ↦ A q.1 q.2)

@[simp]
theorem logHeight_transpose (A : Matrix m n K) : Aᵀ.logHeight = A.logHeight := by
  simp [logHeight_eq_log_mulHeight]

variable [Finite m] [Finite n]

theorem one_le_mulHeight (A : Matrix m n K) : 1 ≤ A.mulHeight :=
  Height.one_le_mulHeight _

theorem mulHeight_pos (A : Matrix m n K) : 0 < A.mulHeight :=
  Height.mulHeight_pos _

theorem mulHeight_ne_zero (A : Matrix m n K) : A.mulHeight ≠ 0 :=
  Height.mulHeight_ne_zero _

theorem logHeight_nonneg (A : Matrix m n K) : 0 ≤ A.logHeight :=
  Real.log_nonneg A.one_le_mulHeight

/-- Entry heights are projective: scaling by a nonzero constant does not change them. -/
@[simp]
theorem mulHeight_smul (A : Matrix m n K) {c : K} (hc : c ≠ 0) :
    (c • A).mulHeight = A.mulHeight :=
  mulHeight_smul_eq_mulHeight (fun q : m × n ↦ A q.1 q.2) hc

@[simp]
theorem logHeight_smul (A : Matrix m n K) {c : K} (hc : c ≠ 0) :
    (c • A).logHeight = A.logHeight := by
  simp [logHeight_eq_log_mulHeight, hc]

/-- The entry height of a submatrix is at most the entry height of the matrix. Rows and columns
may be repeated or omitted. -/
theorem mulHeight_submatrix_le [Finite m'] [Finite n'] (A : Matrix m n K) (f : m' → m)
    (g : n' → n) : (A.submatrix f g).mulHeight ≤ A.mulHeight :=
  mulHeight_comp_le (Prod.map f g) (fun q : m × n ↦ A q.1 q.2)

theorem logHeight_submatrix_le [Finite m'] [Finite n'] (A : Matrix m n K) (f : m' → m)
    (g : n' → n) : (A.submatrix f g).logHeight ≤ A.logHeight :=
  Real.log_le_log (mulHeight_pos _) (A.mulHeight_submatrix_le f g)

/-! ### Products -/

omit [AdmissibleAbsValues K] [Finite m] [Finite n] in
/-- The entries of `A * B` are the values at the all-ones vector of the linear map with
coefficients `A i j * B j k`, the pointwise product of two subtuples of the entries of `A` and of
`B`. -/
private theorem mul_entries_eq_linearMap_apply [Fintype n] (A : Matrix m n K)
    (B : Matrix n p K) :
    (fun q : m × p ↦ (A * B) q.1 q.2) = fun q ↦ ∑ j,
      ((fun q : (m × p) × n ↦ A q.1.1 q.2) * fun q : (m × p) × n ↦ B q.2 q.1.2) (q, j) *
        (1 : n → K) j := by
  ext q
  simp [mul_apply]

/-- The pointwise product of the subtuples of the entries of `A` and of `B` appearing in
`mul_entries_eq_linearMap_apply` has height at most the product of the entry heights of `A` and
`B`. -/
private theorem mulHeight_mul_entries_le [Finite p] (A : Matrix m n K)
    (B : Matrix n p K) :
    Height.mulHeight ((fun q : (m × p) × n ↦ A q.1.1 q.2) * fun q : (m × p) × n ↦ B q.2 q.1.2) ≤
      A.mulHeight * B.mulHeight :=
  (Height.mulHeight_mul_le _ _).trans <| mul_le_mul
    (mulHeight_comp_le (fun q : (m × p) × n ↦ (q.1.1, q.2)) fun q : m × n ↦ A q.1 q.2)
    (mulHeight_comp_le (fun q : (m × p) × n ↦ (q.2, q.1.2)) fun q : n × p ↦ B q.1 q.2)
    (Height.mulHeight_pos _).le A.mulHeight_pos.le

omit [Finite n] in
/-- **The entry height of a matrix product.** For a nonempty inner index type `n`, the entry
height of `A * B` is at most `(#n) ^ totalWeight K` times the product of the entry heights of `A`
and `B`. -/
theorem mulHeight_mul_le [Fintype n] [Nonempty n] [Finite p] (A : Matrix m n K)
    (B : Matrix n p K) :
    (A * B).mulHeight ≤ Nat.card n ^ totalWeight K * A.mulHeight * B.mulHeight := by
  have hpos : 0 ≤ (Nat.card n : ℝ) ^ totalWeight K := by positivity
  let x : (m × p) × n → K := fun q ↦ A q.1.1 q.2
  let y : (m × p) × n → K := fun q ↦ B q.2 q.1.2
  have hc : Height.mulHeight (x * y) ≤ A.mulHeight * B.mulHeight := mulHeight_mul_entries_le A B
  calc (A * B).mulHeight
      ≤ Nat.card n ^ totalWeight K * Height.mulHeight (x * y) * Height.mulHeight (1 : n → K) := by
        rw [mulHeight_def, mul_entries_eq_linearMap_apply]
        exact mulHeight_linearMap_apply_le (x * y) 1
    _ ≤ Nat.card n ^ totalWeight K * A.mulHeight * B.mulHeight := by
        rw [Height.mulHeight_one, mul_one, mul_assoc]
        exact mul_le_mul_of_nonneg_left hc hpos

omit [Finite n] in
/-- The logarithmic form of `Matrix.mulHeight_mul_le`. It needs no nonemptiness hypothesis,
because `Real.log 0 = 0`. -/
theorem logHeight_mul_le [Fintype n] [Finite p] (A : Matrix m n K) (B : Matrix n p K) :
    (A * B).logHeight ≤ totalWeight K * Real.log (Nat.card n) + A.logHeight + B.logHeight := by
  let x : (m × p) × n → K := fun q ↦ A q.1.1 q.2
  let y : (m × p) × n → K := fun q ↦ B q.2 q.1.2
  have hc : Height.logHeight (x * y) ≤ A.logHeight + B.logHeight := by
    rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
      Height.logHeight_eq_log_mulHeight, ← Real.log_mul A.mulHeight_ne_zero B.mulHeight_ne_zero]
    exact Real.log_le_log (Height.mulHeight_pos _) (mulHeight_mul_entries_le A B)
  calc (A * B).logHeight
      ≤ totalWeight K * Real.log (Nat.card n) + Height.logHeight (x * y) +
          Height.logHeight (1 : n → K) := by
        rw [logHeight_def, mul_entries_eq_linearMap_apply]
        exact logHeight_linearMap_apply_le (x * y) 1
    _ ≤ totalWeight K * Real.log (Nat.card n) + A.logHeight + B.logHeight := by
        rw [Height.logHeight_one, add_zero, add_assoc]
        exact add_le_add le_rfl hc

/-! ### Extensions of number fields -/

section NumberField

variable {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]

/-- **Entry heights in an extension.** For an extension of number fields `L / F`, the entry
height of a matrix over `F`, computed over `L`, is its entry height over `F` raised to the degree
`[L : F]`. -/
@[simp]
theorem mulHeight_map_algebraMap (A : Matrix m n F) :
    (A.map (algebraMap F L)).mulHeight = A.mulHeight ^ Module.finrank F L :=
  NumberField.mulHeight_algebraMap (fun q : m × n ↦ A q.1 q.2)

@[simp]
theorem logHeight_map_algebraMap (A : Matrix m n F) :
    (A.map (algebraMap F L)).logHeight = Module.finrank F L * A.logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_map_algebraMap, Real.log_pow,
    logHeight_eq_log_mulHeight]

end NumberField

/-! ### Examples -/

omit [Finite m] [Finite n] in
/-- Over `ℚ`, a matrix with coprime integer entries has entry height the largest absolute value
`M` of its entries, given as a bound `hle` on every entry attained at the entry `(i, j)`. -/
private theorem mulHeight_map_intCast_eq [Fintype m] [Fintype n] {A : Matrix m n ℤ}
    (hA : Finset.univ.gcd (fun q : m × n ↦ A q.1 q.2) = 1) {M : ℤ} (hle : ∀ i j, |A i j| ≤ M)
    (i : m) (j : n) (hM : |A i j| = M) : (A.map ((↑) : ℤ → ℚ)).mulHeight = M := by
  have : Nonempty (m × n) := ⟨(i, j)⟩
  change Height.mulHeight (((↑) : ℤ → ℚ) ∘ fun q : m × n ↦ A q.1 q.2) = M
  rw [Rat.mulHeight_eq_max_abs_of_gcd_eq_one hA]
  exact_mod_cast le_antisymm (ciSup_le fun q ↦ hle q.1 q.2)
    (le_ciSup_of_le (Finite.bddAbove_range _) (i, j) hM.ge)

-- A matrix with an empty index type is zero, so it has entry height one.
example (A : Matrix (Fin 0) (Fin 3) ℚ) : A.mulHeight = 1 := by
  rw [Subsingleton.elim A 0, mulHeight_zero]

-- Over an empty inner index type the product bound fails: `A * B = 0` has entry height one, while
-- `(#n) ^ totalWeight ℚ = 0 ^ 1 = 0`.
example (A : Matrix (Fin 1) (Fin 0) ℚ) (B : Matrix (Fin 0) (Fin 1) ℚ) :
    ¬ (A * B).mulHeight ≤ Nat.card (Fin 0) ^ totalWeight ℚ * A.mulHeight * B.mulHeight := by
  have hAB : A * B = 0 := by ext i k; simp [mul_apply]
  simp [hAB, NumberField.totalWeight_eq_finrank]

-- The row `[1 2]` has entry height `2` over `ℚ`, and `2 ^ [L : ℚ]` over a number field `L`, for
-- instance `4` over `ℚ(i)`.
example (L : Type*) [Field L] [NumberField L] :
    (!![(1 : ℚ), 2].map (algebraMap ℚ L)).mulHeight = 2 ^ Module.finrank ℚ L := by
  have h : !![(1 : ℚ), 2] = !![(1 : ℤ), 2].map (↑) := by
    ext i j; fin_cases i; fin_cases j <;> simp
  have h2 : !![(1 : ℚ), 2].mulHeight = 2 := by
    rw [h, mulHeight_map_intCast_eq (M := 2) (by decide) (by decide) 0 1 (by decide)]
    norm_num
  rw [mulHeight_map_algebraMap, h2]

/-- **The constant of `Matrix.mulHeight_mul_le` is attained.** Over `ℚ`, the matrices `[1 1]`
and `[[1, 0], [1, 1]]` have entry height `1`, and their product `[2 1]` has entry height
`2 = 2 ^ totalWeight ℚ`. -/
example : !![(1 : ℚ), 1].mulHeight = 1 ∧ !![(1 : ℚ), 0; 1, 1].mulHeight = 1 ∧
    (!![(1 : ℚ), 1] * !![(1 : ℚ), 0; 1, 1]).mulHeight =
      Nat.card (Fin 2) ^ totalWeight ℚ * !![(1 : ℚ), 1].mulHeight *
        !![(1 : ℚ), 0; 1, 1].mulHeight := by
  have hA : !![(1 : ℚ), 1].mulHeight = 1 := by
    have h : (fun q : Fin 1 × Fin 2 ↦ !![(1 : ℚ), 1] q.1 q.2) = 1 := by
      ext q; fin_cases q <;> rfl
    rw [mulHeight_def, h, Height.mulHeight_one]
  have hB : !![(1 : ℚ), 0; 1, 1].mulHeight = 1 := by
    have h : !![(1 : ℚ), 0; 1, 1] = !![(1 : ℤ), 0; 1, 1].map (↑) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [h, mulHeight_map_intCast_eq (M := 1) (by decide) (by decide) 0 0 (by decide)]
    norm_num
  have hAB : (!![(1 : ℚ), 1] * !![(1 : ℚ), 0; 1, 1]).mulHeight = 2 := by
    have h : !![(1 : ℚ), 1] * !![(1 : ℚ), 0; 1, 1] = !![(2 : ℤ), 1].map (↑) := by
      ext i j; fin_cases i; fin_cases j <;> norm_num [mul_apply, Fin.sum_univ_two]
    rw [h, mulHeight_map_intCast_eq (M := 2) (by decide) (by decide) 0 0 (by decide)]
    norm_num
  refine ⟨hA, hB, ?_⟩
  rw [hA, hB, hAB]
  simp [NumberField.totalWeight_eq_finrank]

end Matrix

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Diagram
public import TauCeti.LinearAlgebra.Vandermonde
public import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# The Weyl dimension formula for `Sp 2n`

The irreducible representations of the symplectic group `Sp 2n` are indexed by the partitions
`λ₁ ≥ ⋯ ≥ λₙ ≥ 0` with at most `n` parts.  The positive roots of type `Cₙ` are `eᵢ ± eⱼ` for
`i < j` and `2eᵢ`, and the half-sum of the positive roots is `ρ = (n, n - 1, …, 1)`, so with
`xᵢ = λᵢ + n - i` the entries of `λ + ρ` (indexing from `0`), the Weyl dimension formula reads

`dim V_λ = ∏_{i < n} xᵢ / (n - i) · ∏_{i < j < n} (xᵢ² - xⱼ²) / ((n - i)² - (n - j)²)`.

This file builds the right-hand side as a natural number.  As for `GL n`
(`TauCeti.weylDimension`), that is a step in its own right: the factors are rational, and
neither the integrality nor the positivity of the product is visible from the formula.

The numerator `TauCeti.symplecticWeylDimensionNumerator` is the odd Vandermonde product
`∏ᵢ xᵢ · ∏_{i < j} (xᵢ² - xⱼ²)`, and the denominator is its value at `λ = 0`, which is
`1! · 3! ⋯ (2n - 1)!` (`TauCeti.symplecticWeylDimensionNumerator_bot`).  Integrality is
`TauCeti.prod_factorial_dvd_prod_mul_prod_sq_sub_sq`: in the Vandermonde determinant of the squares
`xᵢ²`, weighted by the `xᵢ`, the column of `x^{2k+1}` may be replaced by the column of the odd
polynomial `x (x² - 1²) ⋯ (x² - k²)`, a product of `2k + 1` consecutive integers.  The same
polynomial evaluates each row of the numerator once the rows below it are those of `ρ`, which
computes the denominator and the one-row weights.

A Young diagram `μ` is read through its first `n` rows
(`TauCeti.symplecticWeylDimension_congr`).  When `μ` has at most `n` rows it is a
dominant weight of `Sp 2n`, and the value is the dimension of the corresponding irreducible
representation; the identification with that dimension is downstream of the highest-weight
classification.

## Main definitions

* `TauCeti.symplecticRhoShift`: the entries `μᵢ + n - i` of `μ + ρ`.
* `TauCeti.symplecticWeylDimensionNumerator`: the product `∏ᵢ xᵢ · ∏_{i < j} (xᵢ² - xⱼ²)`.
* `TauCeti.symplecticWeylDimension`: the dimension predicted by the Weyl dimension formula.

## Main results

* `TauCeti.symplecticWeylDimension_mul_prod_factorial`: the defining identity, division-free.
* `TauCeti.symplecticWeylDimension_eq_prod_prod_div`: the product form of the formula, over `ℚ`.
* `TauCeti.symplecticWeylDimension_pos`: the dimension is positive.
* `TauCeti.symplecticWeylDimension_congr`: the dimension reads only the first `n` rows.
* `TauCeti.symplecticWeylDimension_eq_choose_of_colLen_le_one`: for `Sp (2n + 2)`, a one-row
  weight `(d, 0, …, 0)` has dimension `(d + 2n + 1).choose (2n + 1)`, that of the symmetric power
  `Symᵈ` of the standard representation; in particular `TauCeti.symplecticWeylDimension_bot`, the
  trivial representation has dimension `1`.
* `TauCeti.symplecticWeylDimension_one_eq_rowLen_add_one`: for `Sp 2 = SL 2` the formula reads
  `d + 1`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §24.2.
-/

public section

namespace TauCeti

open Finset

variable (n : ℕ) (μ : YoungDiagram)

/-- The entries `μᵢ + n - i` of `μ + ρ` for `Sp 2n`, where `ρ = (n, n - 1, …, 1)` is the half-sum
of the positive roots of type `Cₙ`.  Only the indices `i < n` are used. -/
def symplecticRhoShift (i : ℕ) : ℤ := μ.rowLen i + n - i

/-- The defining equation of `TauCeti.symplecticRhoShift`. -/
@[simp]
theorem symplecticRhoShift_apply (i : ℕ) :
    symplecticRhoShift n μ i = μ.rowLen i + n - i := (rfl)

variable {n μ} in
/-- The entries of `μ + ρ` are positive below `n`. -/
theorem symplecticRhoShift_pos {i : ℕ} (hi : i < n) : 0 < symplecticRhoShift n μ i := by
  rw [symplecticRhoShift_apply]
  omega

/-- Adding the strictly decreasing `ρ` to the weakly decreasing row lengths gives a strictly
decreasing sequence, which makes every factor of `TauCeti.symplecticWeylDimensionNumerator`
positive. -/
theorem symplecticRhoShift_strictAnti : StrictAnti (symplecticRhoShift n μ) := by
  intro i j hij
  have := μ.rowLen_anti i j hij.le
  simp only [symplecticRhoShift_apply]
  omega

/-- The **numerator of the symplectic Weyl dimension formula**: with `xᵢ = μᵢ + n - i`, the
product `∏_{i < n} xᵢ · ∏_{i < j < n} (xᵢ² - xⱼ²)` of the pairings of `μ + ρ` with the positive
roots `2eᵢ` and `eᵢ ± eⱼ` of type `Cₙ`, the factors `2` of the long roots being dropped since they
cancel against the denominator. -/
def symplecticWeylDimensionNumerator : ℤ :=
  ∏ i ∈ range n, symplecticRhoShift n μ i *
    ∏ j ∈ Ico (i + 1) n, (symplecticRhoShift n μ i ^ 2 - symplecticRhoShift n μ j ^ 2)

/-- **The numerator as a double product**: the defining equation of
`TauCeti.symplecticWeylDimensionNumerator`, the form every computation with it starts from. -/
theorem symplecticWeylDimensionNumerator_eq_prod_prod :
    symplecticWeylDimensionNumerator n μ =
      ∏ i ∈ range n, symplecticRhoShift n μ i *
        ∏ j ∈ Ico (i + 1) n, (symplecticRhoShift n μ i ^ 2 - symplecticRhoShift n μ j ^ 2) :=
  (rfl)

/-- Every factor of the numerator is positive. -/
theorem symplecticWeylDimensionNumerator_pos : 0 < symplecticWeylDimensionNumerator n μ := by
  rw [symplecticWeylDimensionNumerator_eq_prod_prod]
  refine prod_pos fun i hi => mul_pos (symplecticRhoShift_pos (mem_range.1 hi)) <|
    prod_pos fun j hj => ?_
  have hij := symplecticRhoShift_strictAnti n μ (mem_Ico.1 hj).1
  have hj0 := symplecticRhoShift_pos (μ := μ) (mem_Ico.1 hj).2
  exact sub_pos.2 (pow_lt_pow_left₀ hij hj0.le two_ne_zero)

/-- **Integrality of the symplectic Weyl dimension formula**: `1! · 3! ⋯ (2n - 1)!` divides the
numerator. -/
theorem prod_factorial_dvd_symplecticWeylDimensionNumerator :
    (∏ k ∈ range n, ((2 * k + 1).factorial : ℤ)) ∣ symplecticWeylDimensionNumerator n μ :=
  prod_factorial_dvd_prod_mul_prod_sq_sub_sq n _

/-- A row of the numerator, all of whose lower rows are empty.  Below row `i` the entries of
`μ + ρ` are then those of `ρ`, namely `1, 2, …, k` with `k = n - 1 - i`, so the row is
`xᵢ (xᵢ² - 1²) ⋯ (xᵢ² - k²)`, the falling factorial of degree `2k + 1` at `xᵢ + k`.  For `i ≥ n`
both sides are `xᵢ`. -/
private theorem symplecticWeylDimensionNumerator_row {i : ℕ}
    (h : ∀ j, i < j → μ.rowLen j = 0) :
    symplecticRhoShift n μ i *
        ∏ j ∈ Ico (i + 1) n, (symplecticRhoShift n μ i ^ 2 - symplecticRhoShift n μ j ^ 2)
      = (descPochhammer ℤ (2 * (n - 1 - i) + 1)).eval
          (symplecticRhoShift n μ i + (n - 1 - i : ℕ)) := by
  set x := symplecticRhoShift n μ i
  have hrow : ∀ j ∈ Ico (i + 1) n,
      x ^ 2 - symplecticRhoShift n μ j ^ 2 = (fun c : ℕ => x ^ 2 - (c : ℤ) ^ 2) (n - j) := by
    intro j hj
    have hj := mem_Ico.1 hj
    simp only [symplecticRhoShift_apply, h j (by omega), Nat.cast_zero, zero_add,
      Nat.cast_sub hj.2.le]
  have hlen : n + 1 - (i + 1) - (n + 1 - n) = n - 1 - i := by omega
  have hstart : n + 1 - n = 1 := by omega
  rw [prod_congr rfl hrow,
    prod_Ico_reflect (fun c : ℕ => x ^ 2 - (c : ℤ) ^ 2) (i + 1) (Nat.le_succ n),
    prod_Ico_eq_prod_range, hlen, ← mul_prod_sq_sub_sq_eq_descPochhammer_eval]
  simp only [hstart, Nat.cast_add, Nat.cast_one, add_comm (1 : ℤ)]

/-- The numerator of a weight with at most one row, of length `d`: below the first row the
entries of `μ + ρ` are those of `ρ`, so the rows `1, …, n` contribute `1! · 3! ⋯ (2n - 1)!`, and
the first row is the falling factorial of degree `2n + 1` at `d + 2n + 1`. -/
private theorem symplecticWeylDimensionNumerator_succ_of_colLen_le_one
    (h : μ.colLen 0 ≤ 1) :
    symplecticWeylDimensionNumerator (n + 1) μ
      = (∏ k ∈ range n, ((2 * k + 1).factorial : ℤ))
        * ((μ.rowLen 0 + 2 * n + 1).descFactorial (2 * n + 1) : ℤ) := by
  have h' : ∀ j, 0 < j → μ.rowLen j = 0 := fun j hj =>
    YoungDiagram.rowLen_eq_zero_of_colLen_le (h.trans hj)
  rw [symplecticWeylDimensionNumerator_eq_prod_prod, prod_range_succ',
    ← prod_range_reflect (fun k => ((2 * k + 1).factorial : ℤ)) n]
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    have hi := mem_range.1 hi
    have hk : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
    have hx : symplecticRhoShift (n + 1) μ (i + 1) + ((n - 1 - i : ℕ) : ℤ)
        = ((2 * (n - 1 - i) + 1 : ℕ) : ℤ) := by
      rw [symplecticRhoShift_apply, h' _ (by omega)]
      omega
    rw [symplecticWeylDimensionNumerator_row (n + 1) μ fun j hj => h' j (by omega), hk, hx,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self]
  · have hk : n + 1 - 1 - 0 = n := by omega
    have hx : symplecticRhoShift (n + 1) μ 0 + ((n : ℕ) : ℤ)
        = ((μ.rowLen 0 + 2 * n + 1 : ℕ) : ℤ) := by
      rw [symplecticRhoShift_apply]
      push_cast
      ring
    rw [symplecticWeylDimensionNumerator_row (n + 1) μ fun j hj => h' j hj, hk, hx,
      descPochhammer_eval_eq_descFactorial]

/-- The value of the numerator at `μ = 0`, the denominator of the Weyl dimension formula: at
`ρ = (n, …, 1)` the row `i` is `(2k + 1)!` with `k = n - 1 - i`, so the numerator is
`1! · 3! ⋯ (2n - 1)!`. -/
@[simp]
theorem symplecticWeylDimensionNumerator_bot :
    symplecticWeylDimensionNumerator n ⊥ = ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) := by
  cases n with
  | zero => simp [symplecticWeylDimensionNumerator_eq_prod_prod]
  | succ n =>
    rw [symplecticWeylDimensionNumerator_succ_of_colLen_le_one n ⊥
        (by simp only [YoungDiagram.colLen_bot, zero_le]),
      YoungDiagram.rowLen_bot, zero_add, Nat.descFactorial_self, prod_range_succ]

/-- **The symplectic Weyl dimension** of a Young diagram `μ`, read through its first `n` rows: the
value

`∏_{i < n} xᵢ / (n - i) · ∏_{i < j < n} (xᵢ² - xⱼ²) / ((n - i)² - (n - j)²)`,  `xᵢ = μᵢ + n - i`,

of the Weyl dimension formula for `Sp 2n`.  For `μ` with at most `n` rows it is the dimension of
the irreducible representation of `Sp 2n` with highest weight `μ`.  The quotient is taken once,
of `TauCeti.symplecticWeylDimensionNumerator` by `1! · 3! ⋯ (2n - 1)!`;
`TauCeti.symplecticWeylDimension_eq_prod_prod_div` recovers the term-by-term form over `ℚ`. -/
def symplecticWeylDimension : ℕ :=
  (symplecticWeylDimensionNumerator n μ / ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ)).toNat

/-- **The defining identity of `TauCeti.symplecticWeylDimension`**, in division-free form: the
dimension times `1! · 3! ⋯ (2n - 1)!` is the numerator. -/
theorem symplecticWeylDimension_mul_prod_factorial :
    (symplecticWeylDimension n μ : ℤ) * ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ)
      = symplecticWeylDimensionNumerator n μ := by
  rw [symplecticWeylDimension, Int.toNat_of_nonneg (Int.ediv_nonneg
      (symplecticWeylDimensionNumerator_pos n μ).le (prod_factorial_two_mul_add_one_pos n).le),
    Int.ediv_mul_cancel (prod_factorial_dvd_symplecticWeylDimensionNumerator n μ)]

/-- **The symplectic Weyl dimension is positive**. -/
theorem symplecticWeylDimension_pos : 0 < symplecticWeylDimension n μ := by
  have h := symplecticWeylDimension_mul_prod_factorial n μ
  have h0 := symplecticWeylDimensionNumerator_pos n μ
  rw [← h] at h0
  exact_mod_cast pos_of_mul_pos_left h0 (prod_factorial_two_mul_add_one_pos n).le

/-- **The Weyl dimension formula for `Sp 2n` in its product form**: over `ℚ`, with
`xᵢ = μᵢ + n - i`, the dimension is

`∏_{i < n} xᵢ / (n - i) · ∏_{i < j < n} (xᵢ² - xⱼ²) / ((n - i)² - (n - j)²)`. -/
theorem symplecticWeylDimension_eq_prod_prod_div :
    (symplecticWeylDimension n μ : ℚ) =
      ∏ i ∈ range n, ((symplecticRhoShift n μ i : ℚ) / ((n : ℚ) - i) *
        ∏ j ∈ Ico (i + 1) n, (((symplecticRhoShift n μ i : ℚ) ^ 2 - (symplecticRhoShift n μ j) ^ 2)
          / (((n : ℚ) - i) ^ 2 - ((n : ℚ) - j) ^ 2))) := by
  have hnum : ((symplecticWeylDimensionNumerator n μ : ℤ) : ℚ) =
      ∏ i ∈ range n, ((symplecticRhoShift n μ i : ℚ) * ∏ j ∈ Ico (i + 1) n,
        ((symplecticRhoShift n μ i : ℚ) ^ 2 - (symplecticRhoShift n μ j) ^ 2)) := by
    simp [symplecticWeylDimensionNumerator_eq_prod_prod]
  have hden : ((∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) : ℤ) : ℚ) =
      ∏ i ∈ range n,
        (((n : ℚ) - i) * ∏ j ∈ Ico (i + 1) n, (((n : ℚ) - i) ^ 2 - ((n : ℚ) - j) ^ 2)) := by
    rw [← symplecticWeylDimensionNumerator_bot]
    simp [symplecticWeylDimensionNumerator_eq_prod_prod]
  have hden0 : ((∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (prod_factorial_two_mul_add_one_pos n).ne'
  simp only [prod_div_distrib, div_mul_div_comm]
  rw [← hnum, ← hden, eq_div_iff hden0]
  exact_mod_cast symplecticWeylDimension_mul_prod_factorial n μ

variable {n μ} in
/-- **The numerator reads only the first `n` rows**: two diagrams whose rows `0, …, n - 1` have
the same lengths have the same numerator. -/
theorem symplecticWeylDimensionNumerator_congr {ν : YoungDiagram}
    (h : ∀ i < n, μ.rowLen i = ν.rowLen i) :
    symplecticWeylDimensionNumerator n μ = symplecticWeylDimensionNumerator n ν := by
  have hx : ∀ i < n, symplecticRhoShift n μ i = symplecticRhoShift n ν i := fun i hi => by
    simp only [symplecticRhoShift_apply, h i hi]
  rw [symplecticWeylDimensionNumerator_eq_prod_prod, symplecticWeylDimensionNumerator_eq_prod_prod]
  refine prod_congr rfl fun i hi => ?_
  rw [hx i (mem_range.1 hi)]
  exact congrArg _ <| prod_congr rfl fun j hj => by rw [hx j (mem_Ico.1 hj).2]

variable {n μ} in
/-- **The symplectic Weyl dimension reads only the first `n` rows**: two diagrams whose rows
`0, …, n - 1` have the same lengths have the same dimension. -/
theorem symplecticWeylDimension_congr {ν : YoungDiagram}
    (h : ∀ i < n, μ.rowLen i = ν.rowLen i) :
    symplecticWeylDimension n μ = symplecticWeylDimension n ν := by
  -- Cancel `1! · 3! ⋯ (2n - 1)!` to reduce to the numerator.
  have h1 : (symplecticWeylDimension n μ : ℤ) * ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) =
      (symplecticWeylDimension n ν : ℤ) * ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) :=
    (symplecticWeylDimension_mul_prod_factorial n μ).trans
      ((symplecticWeylDimensionNumerator_congr h).trans
        (symplecticWeylDimension_mul_prod_factorial n ν).symm)
  exact_mod_cast mul_right_cancel₀ (prod_factorial_two_mul_add_one_pos n).ne' h1

/-- **One-row weights**: if `μ` has at most one row, of length `d`, then the symplectic Weyl
dimension for `Sp (2n + 2)` is `(d + 2n + 1).choose (2n + 1)`, the dimension of the symmetric power
`Symᵈ` of the standard representation, which is irreducible for the symplectic group. -/
theorem symplecticWeylDimension_eq_choose_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    symplecticWeylDimension (n + 1) μ = (μ.rowLen 0 + 2 * n + 1).choose (2 * n + 1) := by
  have hdim := symplecticWeylDimension_mul_prod_factorial (n + 1) μ
  rw [symplecticWeylDimensionNumerator_succ_of_colLen_le_one n μ h, prod_range_succ,
    Nat.descFactorial_eq_factorial_mul_choose] at hdim
  have hpos : (0 : ℤ) < (∏ k ∈ range n, ((2 * k + 1).factorial : ℤ)) * (2 * n + 1).factorial :=
    mul_pos (prod_factorial_two_mul_add_one_pos n) (mod_cast (2 * n + 1).factorial_pos)
  have hchoose : (symplecticWeylDimension (n + 1) μ : ℤ)
      = ((μ.rowLen 0 + 2 * n + 1).choose (2 * n + 1) : ℕ) := by
    refine mul_right_cancel₀ hpos.ne' ?_
    rw [hdim]
    push_cast
    ring
  exact_mod_cast hchoose

/-- The symplectic group `Sp 0` is trivial, and so is the formula: an empty product. -/
@[simp]
theorem symplecticWeylDimension_zero : symplecticWeylDimension 0 μ = 1 := by
  have h := symplecticWeylDimension_mul_prod_factorial 0 μ
  simp only [range_zero, prod_empty, mul_one, symplecticWeylDimensionNumerator_eq_prod_prod] at h
  exact_mod_cast h

/-- **The trivial representation**: the empty diagram has symplectic Weyl dimension `1`. -/
@[simp]
theorem symplecticWeylDimension_bot : symplecticWeylDimension n ⊥ = 1 := by
  cases n with
  | zero => exact symplecticWeylDimension_zero ⊥
  | succ n =>
    rw [symplecticWeylDimension_eq_choose_of_colLen_le_one n ⊥
        (by simp only [YoungDiagram.colLen_bot, zero_le]),
      YoungDiagram.rowLen_bot, zero_add, Nat.choose_self]

/-- **The `Sp 2 = SL 2` case**: the irreducible representation with highest weight `(d)` has
dimension `d + 1`.  The formula reads only the first row. -/
@[simp]
theorem symplecticWeylDimension_one_eq_rowLen_add_one :
    symplecticWeylDimension 1 μ = μ.rowLen 0 + 1 := by
  have h := symplecticWeylDimension_mul_prod_factorial 1 μ
  simp only [symplecticWeylDimensionNumerator_eq_prod_prod, prod_range_one, mul_zero, zero_add,
    Nat.factorial_one, Nat.cast_one, mul_one, Ico_self, prod_empty, symplecticRhoShift_apply,
    CharP.cast_eq_zero, sub_zero] at h
  exact_mod_cast h

end TauCeti

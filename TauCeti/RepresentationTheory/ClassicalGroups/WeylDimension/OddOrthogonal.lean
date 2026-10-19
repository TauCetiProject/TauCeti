/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Vandermonde
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension.Orthogonal
public import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# The Weyl dimension formula for `SO (2n + 1)`

The irreducible representations of the odd special orthogonal group `SO (2n + 1)` are indexed by
the partitions `λ₁ ≥ ⋯ ≥ λₙ ≥ 0` with at most `n` parts.  The positive roots of type `Bₙ` are
`eᵢ ± eⱼ` for `i < j` and `eᵢ`, and the half-sum of the positive roots is
`ρ = (n - 1/2, n - 3/2, …, 1/2)`, so with `lᵢ = λᵢ + n - i - 1/2` the entries of `λ + ρ` and
`rᵢ = n - i - 1/2` those of `ρ` (indexing from `0`), the Weyl dimension formula reads

`dim V_λ = ∏_{i < n} lᵢ / rᵢ · ∏_{i < j < n} (lᵢ² - lⱼ²) / (rᵢ² - rⱼ²)`.

This file builds the right-hand side as a natural number.  As for `Sp 2n`
(`TauCeti.symplecticWeylDimension`), that is a step in its own right: the factors are rational,
and neither the integrality nor the positivity of the product is visible from the formula.

The entries of `λ + ρ` are half-integers, so the file works with the integers
`xᵢ = λᵢ + n - 1 - i = lᵢ - 1/2`, the sequence `TauCeti.orthogonalRhoShift` it shares with
`SO (2n)`.  In these, `2lᵢ = 2xᵢ + 1` and
`lᵢ² - lⱼ² = (xᵢ - xⱼ)(xᵢ + xⱼ + 1)`, so the numerator
`TauCeti.oddOrthogonalWeylDimensionNumerator` is
`∏ᵢ (2xᵢ + 1) · ∏_{i < j} (xᵢ - xⱼ)(xᵢ + xⱼ + 1)`, the product of the pairings of `λ + ρ` with the
positive roots, each pairing with a short root `eᵢ` doubled.  The denominator is its value at
`λ = 0`, which is `1! · 3! ⋯ (2n - 1)!` (`TauCeti.oddOrthogonalWeylDimensionNumerator_bot`), the
same as for `Sp 2n`.  Integrality is
`TauCeti.prod_factorial_dvd_prod_two_mul_add_one_mul_prod_sub_mul_add_add_one`: the factors
`(xᵢ - xⱼ)(xᵢ + xⱼ + 1)` are the differences of the values `xᵢ (xᵢ + 1)`, and in their Vandermonde
determinant, weighted by the `2xᵢ + 1`, the column of `(x (x + 1))^k` may be replaced by the column
of `(2x + 1) ∏_{c < k} (x - c)(x + c + 1)`, a sum of two products of `2k + 1` consecutive integers.
The same polynomial evaluates each row of the numerator once the rows below it are those of
`ρ - 1/2`, which computes the denominator and the one-row weights.

A Young diagram `μ` is read through its first `n` rows
(`TauCeti.oddOrthogonalWeylDimension_congr`).  When `μ` has at most `n` rows it is a dominant
weight of `SO (2n + 1)`, and the value is the dimension of the corresponding irreducible
representation; the identification with that dimension is downstream of the highest-weight
classification.  The spin representations of `Spin (2n + 1)`, whose highest weights have
half-integral entries, are not indexed by Young diagrams and are not covered here.

## Main definitions

* `TauCeti.oddOrthogonalWeylDimensionNumerator`: the product
  `∏ᵢ (2xᵢ + 1) · ∏_{i < j} (xᵢ - xⱼ)(xᵢ + xⱼ + 1)`.
* `TauCeti.oddOrthogonalWeylDimension`: the dimension predicted by the Weyl dimension formula.

## Main results

* `TauCeti.oddOrthogonalWeylDimension_mul_prod_factorial`: the defining identity, division-free.
* `TauCeti.oddOrthogonalWeylDimension_eq_prod_prod_div`: the product form of the formula, over `ℚ`.
* `TauCeti.oddOrthogonalWeylDimension_pos`: the dimension is positive.
* `TauCeti.oddOrthogonalWeylDimension_congr`: the dimension reads only the first `n` rows.
* `TauCeti.oddOrthogonalWeylDimension_eq_choose_add_choose_of_colLen_le_one`: for `SO (2n + 3)`, a
  one-row weight `(d, 0, …, 0)` has dimension
  `(d + 2n + 1).choose (2n + 1) + (d + 2n).choose (2n + 1)`, that of the space of harmonic
  polynomials of degree `d` in `2n + 3` variables; in particular
  `TauCeti.oddOrthogonalWeylDimension_bot`, the trivial representation has dimension `1`.
* `TauCeti.oddOrthogonalWeylDimension_one_eq_two_mul_rowLen_add_one`: for `SO 3` the formula reads
  `2d + 1`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §24.2.
-/

public section

namespace TauCeti

open Finset

variable (n : ℕ) (μ : YoungDiagram)

/-- The **numerator of the odd orthogonal Weyl dimension formula**: with `xᵢ = μᵢ + n - 1 - i`,
the product `∏_{i < n} (2xᵢ + 1) · ∏_{i < j < n} (xᵢ - xⱼ)(xᵢ + xⱼ + 1)` of the pairings of `μ + ρ`
with the positive roots `eᵢ ± eⱼ` and `eᵢ` of type `Bₙ`, each pairing with a short root `eᵢ`
doubled to clear the half. -/
def oddOrthogonalWeylDimensionNumerator : ℤ :=
  ∏ i ∈ range n, (2 * orthogonalRhoShift n μ i + 1) *
    ∏ j ∈ Ico (i + 1) n, (orthogonalRhoShift n μ i - orthogonalRhoShift n μ j) *
      (orthogonalRhoShift n μ i + orthogonalRhoShift n μ j + 1)

/-- **The numerator as a double product**: the defining equation of
`TauCeti.oddOrthogonalWeylDimensionNumerator`, the form every computation with it starts from. -/
theorem oddOrthogonalWeylDimensionNumerator_eq_prod_prod :
    oddOrthogonalWeylDimensionNumerator n μ =
      ∏ i ∈ range n, (2 * orthogonalRhoShift n μ i + 1) *
        ∏ j ∈ Ico (i + 1) n, (orthogonalRhoShift n μ i - orthogonalRhoShift n μ j) *
          (orthogonalRhoShift n μ i + orthogonalRhoShift n μ j + 1) :=
  (rfl)

/-- Every factor of the numerator is positive. -/
theorem oddOrthogonalWeylDimensionNumerator_pos : 0 < oddOrthogonalWeylDimensionNumerator n μ := by
  rw [oddOrthogonalWeylDimensionNumerator_eq_prod_prod]
  refine prod_pos fun i hi => ?_
  have hi0 := orthogonalRhoShift_nonneg (μ := μ) (mem_range.1 hi)
  refine mul_pos (by omega) <| prod_pos fun j hj => ?_
  have hij := orthogonalRhoShift_strictAnti n μ (mem_Ico.1 hj).1
  have hj0 := orthogonalRhoShift_nonneg (μ := μ) (mem_Ico.1 hj).2
  exact mul_pos (sub_pos.2 hij) (by omega)

/-- **Integrality of the odd orthogonal Weyl dimension formula**: `1! · 3! ⋯ (2n - 1)!` divides the
numerator. -/
theorem prod_factorial_dvd_oddOrthogonalWeylDimensionNumerator :
    (∏ k ∈ range n, ((2 * k + 1).factorial : ℤ)) ∣ oddOrthogonalWeylDimensionNumerator n μ :=
  prod_factorial_dvd_prod_two_mul_add_one_mul_prod_sub_mul_add_add_one n _

/-- A row of the numerator, all of whose lower rows are empty.  Below row `i` the shifted entries
are then those of `ρ - 1/2`, namely `0, 1, …, k - 1` with `k = n - 1 - i`, so the row is
`(2xᵢ + 1) ∏_{c < k} (xᵢ - c)(xᵢ + c + 1)`, the sum of the falling factorials of degree `2k + 1`
at `xᵢ + k + 1` and at `xᵢ + k`.  For `i ≥ n` both sides are `2xᵢ + 1`. -/
private theorem oddOrthogonalWeylDimensionNumerator_row {i : ℕ}
    (h : ∀ j, i < j → μ.rowLen j = 0) :
    (2 * orthogonalRhoShift n μ i + 1) *
        ∏ j ∈ Ico (i + 1) n, (orthogonalRhoShift n μ i - orthogonalRhoShift n μ j) *
          (orthogonalRhoShift n μ i + orthogonalRhoShift n μ j + 1)
      = (descPochhammer ℤ (2 * (n - 1 - i) + 1)).eval
          (orthogonalRhoShift n μ i + (n - 1 - i : ℕ) + 1)
        + (descPochhammer ℤ (2 * (n - 1 - i) + 1)).eval
          (orthogonalRhoShift n μ i + (n - 1 - i : ℕ)) := by
  set x := orthogonalRhoShift n μ i
  have hrow : ∀ t ∈ range (n - (i + 1)),
      (x - orthogonalRhoShift n μ (i + 1 + t)) * (x + orthogonalRhoShift n μ (i + 1 + t) + 1)
        = (fun c : ℕ => (x - c) * (x + c + 1)) (n - 1 - i - 1 - t) := by
    intro t ht
    have ht := mem_range.1 ht
    simp only [orthogonalRhoShift_apply, h (i + 1 + t) (by omega), Nat.cast_zero, zero_add,
      Nat.cast_sub (by omega : 1 + i + 1 + t ≤ n), Nat.sub_sub, Nat.cast_add, Nat.cast_one]
    ring_nf
  have hlen : n - (i + 1) = n - 1 - i := by omega
  rw [prod_Ico_eq_prod_range, prod_congr rfl hrow, hlen,
    prod_range_reflect (fun c : ℕ => (x - c) * (x + c + 1)) (n - 1 - i),
    two_mul_add_one_mul_prod_sub_mul_add_add_one_eq]

/-- The numerator of a weight with at most one row, of length `d`: below the first row the shifted
entries are those of `ρ - 1/2`, so the rows `1, …, n` contribute `1! · 3! ⋯ (2n - 1)!`, and the
first row is the sum of the falling factorials of degree `2n + 1` at `d + 2n + 1` and at
`d + 2n`. -/
private theorem oddOrthogonalWeylDimensionNumerator_succ_of_colLen_le_one
    (h : μ.colLen 0 ≤ 1) :
    oddOrthogonalWeylDimensionNumerator (n + 1) μ
      = (∏ k ∈ range n, ((2 * k + 1).factorial : ℤ))
        * (((μ.rowLen 0 + 2 * n + 1).descFactorial (2 * n + 1)
          + (μ.rowLen 0 + 2 * n).descFactorial (2 * n + 1) : ℕ) : ℤ) := by
  have h' : ∀ j, 0 < j → μ.rowLen j = 0 := fun j hj =>
    YoungDiagram.rowLen_eq_zero_of_colLen_le (h.trans hj)
  rw [oddOrthogonalWeylDimensionNumerator_eq_prod_prod, prod_range_succ',
    ← prod_range_reflect (fun k => ((2 * k + 1).factorial : ℤ)) n]
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    have hi := mem_range.1 hi
    have hk : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
    have hx : orthogonalRhoShift (n + 1) μ (i + 1) + ((n - 1 - i : ℕ) : ℤ)
        = ((2 * (n - 1 - i) : ℕ) : ℤ) := by
      rw [orthogonalRhoShift_apply, h' _ (by omega)]
      omega
    rw [oddOrthogonalWeylDimensionNumerator_row (n + 1) μ fun j hj => h' j (by omega), hk, hx,
      ← Nat.cast_succ, descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_self, Nat.descFactorial_of_lt (by omega), Nat.cast_zero, add_zero]
  · have hk : n + 1 - 1 - 0 = n := by omega
    have hx : orthogonalRhoShift (n + 1) μ 0 + ((n : ℕ) : ℤ)
        = ((μ.rowLen 0 + 2 * n : ℕ) : ℤ) := by
      rw [orthogonalRhoShift_apply]
      push_cast
      ring
    rw [oddOrthogonalWeylDimensionNumerator_row (n + 1) μ fun j hj => h' j hj, hk, hx,
      ← Nat.cast_succ, descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial,
      Nat.cast_add]

/-- The value of the numerator at `μ = 0`, the denominator of the Weyl dimension formula: at
`ρ - 1/2 = (n - 1, …, 0)` the row `i` is `(2k + 1)!` with `k = n - 1 - i`, so the numerator is
`1! · 3! ⋯ (2n - 1)!`. -/
@[simp]
theorem oddOrthogonalWeylDimensionNumerator_bot :
    oddOrthogonalWeylDimensionNumerator n ⊥ = ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) := by
  cases n with
  | zero => simp [oddOrthogonalWeylDimensionNumerator_eq_prod_prod]
  | succ n =>
    rw [oddOrthogonalWeylDimensionNumerator_succ_of_colLen_le_one n ⊥
        (by simp only [YoungDiagram.colLen_bot, zero_le]),
      YoungDiagram.rowLen_bot, zero_add, Nat.descFactorial_self,
      Nat.descFactorial_of_lt (by omega), add_zero, prod_range_succ]

/-- **The odd orthogonal Weyl dimension** of a Young diagram `μ`, read through its first `n` rows:
the value

`∏_{i < n} lᵢ / rᵢ · ∏_{i < j < n} (lᵢ² - lⱼ²) / (rᵢ² - rⱼ²)`,
`lᵢ = μᵢ + n - i - 1/2`, `rᵢ = n - i - 1/2`,

of the Weyl dimension formula for `SO (2n + 1)`.  For `μ` with at most `n` rows it is the dimension
of the irreducible representation of `SO (2n + 1)` with highest weight `μ`.  The quotient is taken
once, of `TauCeti.oddOrthogonalWeylDimensionNumerator` by `1! · 3! ⋯ (2n - 1)!`;
`TauCeti.oddOrthogonalWeylDimension_eq_prod_prod_div` recovers the term-by-term form over `ℚ`. -/
def oddOrthogonalWeylDimension : ℕ :=
  (oddOrthogonalWeylDimensionNumerator n μ / ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ)).toNat

/-- **The defining identity of `TauCeti.oddOrthogonalWeylDimension`**, in division-free form: the
dimension times `1! · 3! ⋯ (2n - 1)!` is the numerator. -/
theorem oddOrthogonalWeylDimension_mul_prod_factorial :
    (oddOrthogonalWeylDimension n μ : ℤ) * ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ)
      = oddOrthogonalWeylDimensionNumerator n μ := by
  rw [oddOrthogonalWeylDimension, Int.toNat_of_nonneg (Int.ediv_nonneg
      (oddOrthogonalWeylDimensionNumerator_pos n μ).le (prod_factorial_two_mul_add_one_pos n).le),
    Int.ediv_mul_cancel (prod_factorial_dvd_oddOrthogonalWeylDimensionNumerator n μ)]

/-- **The odd orthogonal Weyl dimension is positive**. -/
theorem oddOrthogonalWeylDimension_pos : 0 < oddOrthogonalWeylDimension n μ := by
  have h := oddOrthogonalWeylDimension_mul_prod_factorial n μ
  have h0 := oddOrthogonalWeylDimensionNumerator_pos n μ
  rw [← h] at h0
  exact_mod_cast pos_of_mul_pos_left h0 (prod_factorial_two_mul_add_one_pos n).le

/-- The numerator over `ℚ`, in the half-integers `lᵢ = xᵢ + 1/2`: twice each pairing with a short
root, times the differences of the squares. -/
private theorem oddOrthogonalWeylDimensionNumerator_cast (ν : YoungDiagram) :
    ((oddOrthogonalWeylDimensionNumerator n ν : ℤ) : ℚ) =
      ∏ i ∈ range n, (2 * ((orthogonalRhoShift n ν i : ℚ) + 1 / 2) *
        ∏ j ∈ Ico (i + 1) n, (((orthogonalRhoShift n ν i : ℚ) + 1 / 2) ^ 2
          - ((orthogonalRhoShift n ν j : ℚ) + 1 / 2) ^ 2)) := by
  rw [oddOrthogonalWeylDimensionNumerator_eq_prod_prod]
  push_cast
  refine prod_congr rfl fun i _ => ?_
  rw [prod_congr rfl fun j _ => (by ring :
    ((orthogonalRhoShift n ν i : ℚ) - orthogonalRhoShift n ν j)
        * ((orthogonalRhoShift n ν i : ℚ) + orthogonalRhoShift n ν j + 1)
      = ((orthogonalRhoShift n ν i : ℚ) + 1 / 2) ^ 2
        - ((orthogonalRhoShift n ν j : ℚ) + 1 / 2) ^ 2)]
  ring

/-- **The Weyl dimension formula for `SO (2n + 1)` in its product form**: over `ℚ`, with
`lᵢ = μᵢ + n - i - 1/2` and `rᵢ = n - i - 1/2` the entries of `μ + ρ` and of `ρ`, the dimension is

`∏_{i < n} lᵢ / rᵢ · ∏_{i < j < n} (lᵢ² - lⱼ²) / (rᵢ² - rⱼ²)`. -/
theorem oddOrthogonalWeylDimension_eq_prod_prod_div :
    (oddOrthogonalWeylDimension n μ : ℚ) =
      ∏ i ∈ range n, (((μ.rowLen i : ℚ) + n - i - 1 / 2) / ((n : ℚ) - i - 1 / 2) *
        ∏ j ∈ Ico (i + 1) n, ((((μ.rowLen i : ℚ) + n - i - 1 / 2) ^ 2
            - ((μ.rowLen j : ℚ) + n - j - 1 / 2) ^ 2)
          / (((n : ℚ) - i - 1 / 2) ^ 2 - ((n : ℚ) - j - 1 / 2) ^ 2))) := by
  have hl : ∀ (ν : YoungDiagram) (i : ℕ),
      (orthogonalRhoShift n ν i : ℚ) + 1 / 2 = (ν.rowLen i : ℚ) + n - i - 1 / 2 := by
    intro ν i
    rw [orthogonalRhoShift_apply]
    push_cast
    ring
  have hnum := oddOrthogonalWeylDimensionNumerator_cast n μ
  have hden := oddOrthogonalWeylDimensionNumerator_cast n ⊥
  simp only [hl, YoungDiagram.rowLen_bot, Nat.cast_zero, zero_add] at hnum hden
  rw [oddOrthogonalWeylDimensionNumerator_bot] at hden
  have hden0 : ((∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (prod_factorial_two_mul_add_one_pos n).ne'
  have htwo : ∀ a b : ℚ, a / b = (2 * a) / (2 * b) := fun a b =>
    (mul_div_mul_left a b two_ne_zero).symm
  simp only [htwo ((μ.rowLen _ : ℚ) + n - _ - 1 / 2), prod_div_distrib, div_mul_div_comm]
  rw [← hnum, ← hden, eq_div_iff hden0]
  exact_mod_cast oddOrthogonalWeylDimension_mul_prod_factorial n μ

variable {n μ} in
/-- **The numerator reads only the first `n` rows**: two diagrams whose rows `0, …, n - 1` have
the same lengths have the same numerator. -/
theorem oddOrthogonalWeylDimensionNumerator_congr {ν : YoungDiagram}
    (h : ∀ i < n, μ.rowLen i = ν.rowLen i) :
    oddOrthogonalWeylDimensionNumerator n μ = oddOrthogonalWeylDimensionNumerator n ν := by
  have hx : ∀ i < n, orthogonalRhoShift n μ i = orthogonalRhoShift n ν i := fun i hi => by
    simp only [orthogonalRhoShift_apply, h i hi]
  rw [oddOrthogonalWeylDimensionNumerator_eq_prod_prod,
    oddOrthogonalWeylDimensionNumerator_eq_prod_prod]
  refine prod_congr rfl fun i hi => ?_
  rw [hx i (mem_range.1 hi)]
  exact congrArg _ <| prod_congr rfl fun j hj => by rw [hx j (mem_Ico.1 hj).2]

variable {n μ} in
/-- **The odd orthogonal Weyl dimension reads only the first `n` rows**: two diagrams whose rows
`0, …, n - 1` have the same lengths have the same dimension. -/
theorem oddOrthogonalWeylDimension_congr {ν : YoungDiagram}
    (h : ∀ i < n, μ.rowLen i = ν.rowLen i) :
    oddOrthogonalWeylDimension n μ = oddOrthogonalWeylDimension n ν := by
  -- Cancel `1! · 3! ⋯ (2n - 1)!` to reduce to the numerator.
  have h1 : (oddOrthogonalWeylDimension n μ : ℤ) * ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) =
      (oddOrthogonalWeylDimension n ν : ℤ) * ∏ k ∈ range n, ((2 * k + 1).factorial : ℤ) :=
    (oddOrthogonalWeylDimension_mul_prod_factorial n μ).trans
      ((oddOrthogonalWeylDimensionNumerator_congr h).trans
        (oddOrthogonalWeylDimension_mul_prod_factorial n ν).symm)
  exact_mod_cast mul_right_cancel₀ (prod_factorial_two_mul_add_one_pos n).ne' h1

/-- **One-row weights**: if `μ` has at most one row, of length `d`, then the odd orthogonal Weyl
dimension for `SO (2n + 3)` is `(d + 2n + 1).choose (2n + 1) + (d + 2n).choose (2n + 1)`, the
dimension of the space of harmonic polynomials of degree `d` in `2n + 3` variables, on which
`SO (2n + 3)` acts irreducibly. -/
theorem oddOrthogonalWeylDimension_eq_choose_add_choose_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    oddOrthogonalWeylDimension (n + 1) μ
      = (μ.rowLen 0 + 2 * n + 1).choose (2 * n + 1) + (μ.rowLen 0 + 2 * n).choose (2 * n + 1) := by
  have hdim := oddOrthogonalWeylDimension_mul_prod_factorial (n + 1) μ
  rw [oddOrthogonalWeylDimensionNumerator_succ_of_colLen_le_one n μ h, prod_range_succ,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hdim
  have hpos : (0 : ℤ) < (∏ k ∈ range n, ((2 * k + 1).factorial : ℤ)) * (2 * n + 1).factorial :=
    mul_pos (prod_factorial_two_mul_add_one_pos n) (mod_cast (2 * n + 1).factorial_pos)
  have hchoose : (oddOrthogonalWeylDimension (n + 1) μ : ℤ)
      = (((μ.rowLen 0 + 2 * n + 1).choose (2 * n + 1)
        + (μ.rowLen 0 + 2 * n).choose (2 * n + 1) : ℕ) : ℤ) := by
    refine mul_right_cancel₀ hpos.ne' ?_
    rw [hdim]
    push_cast
    ring
  exact_mod_cast hchoose

/-- The group `SO 1` is trivial, and so is the formula: an empty product. -/
@[simp]
theorem oddOrthogonalWeylDimension_zero : oddOrthogonalWeylDimension 0 μ = 1 := by
  have h := oddOrthogonalWeylDimension_mul_prod_factorial 0 μ
  simp only [range_zero, prod_empty, mul_one, oddOrthogonalWeylDimensionNumerator_eq_prod_prod] at h
  exact_mod_cast h

/-- **The trivial representation**: the empty diagram has odd orthogonal Weyl dimension `1`. -/
@[simp]
theorem oddOrthogonalWeylDimension_bot : oddOrthogonalWeylDimension n ⊥ = 1 := by
  cases n with
  | zero => exact oddOrthogonalWeylDimension_zero ⊥
  | succ n =>
    rw [oddOrthogonalWeylDimension_eq_choose_add_choose_of_colLen_le_one n ⊥
        (by simp only [YoungDiagram.colLen_bot, zero_le]),
      YoungDiagram.rowLen_bot, zero_add, Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega)]

/-- **The `SO 3` case**: the irreducible representation with highest weight `(d)` has dimension
`2d + 1`.  The formula reads only the first row. -/
@[simp]
theorem oddOrthogonalWeylDimension_one_eq_two_mul_rowLen_add_one :
    oddOrthogonalWeylDimension 1 μ = 2 * μ.rowLen 0 + 1 := by
  have h := oddOrthogonalWeylDimension_mul_prod_factorial 1 μ
  simp only [oddOrthogonalWeylDimensionNumerator_eq_prod_prod, prod_range_one, mul_zero, zero_add,
    Nat.factorial_one, Nat.cast_one, mul_one, Ico_self, prod_empty, orthogonalRhoShift_apply,
    CharP.cast_eq_zero, sub_zero, add_sub_cancel_right] at h
  exact_mod_cast h

end TauCeti

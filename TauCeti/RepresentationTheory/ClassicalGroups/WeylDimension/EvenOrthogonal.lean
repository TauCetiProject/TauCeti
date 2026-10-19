/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Vandermonde
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension.Orthogonal
public import TauCeti.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.LinearCombination

/-!
# The Weyl dimension formula for `SO (2n)`

The positive roots of type `Dₙ`, the root system of the even special orthogonal group `SO (2n)`,
are `eᵢ ± eⱼ` for `i < j`, and the half-sum of the positive roots is `ρ = (n - 1, n - 2, …, 0)`.
With `lᵢ = λᵢ + n - 1 - i` the entries of `λ + ρ` and `rᵢ = n - 1 - i` those of `ρ` (indexing from
`0`), the Weyl dimension formula reads

`dim V_λ = ∏_{i < j < n} (lᵢ² - lⱼ²) / (rᵢ² - rⱼ²)`.

This file builds the right-hand side as a natural number, as `TauCeti.symplecticWeylDimension` and
`TauCeti.oddOrthogonalWeylDimension` do for `Sp 2n` and `SO (2n + 1)`: the factors are rational,
and neither the integrality nor the positivity of the product is visible from the formula.

The entries of `λ + ρ` are the integers `TauCeti.orthogonalRhoShift n λ i = λᵢ + n - 1 - i`,
since the half-sum of the positive roots of type `Dₙ` is that of type `Bₙ` less `1/2` in every
coordinate.  The numerator `TauCeti.evenOrthogonalWeylDimensionNumerator` is the product
`∏_{i < j} (lᵢ - lⱼ)(lᵢ + lⱼ)` of the pairings of `λ + ρ` with the positive roots.  The
denominator is its value at `λ = 0`, which is `2!/2 · 4!/2 ⋯ (2n - 2)!/2`
(`TauCeti.evenOrthogonalWeylDimensionNumerator_bot`).  Integrality is
`TauCeti.prod_add_one_mul_factorial_dvd_prod_prod_sq_sub_sq`: the factors `lᵢ² - lⱼ²` are the
differences of the squares, and in their Vandermonde determinant the column of `(l²)^k` may be
replaced by the column of the degree-`2k` polynomial `∏_{c < k} (l² - c²)`, twice which is the
sum of the products of the `2k` consecutive integers ending at `l + k` and at `l + k - 1`
(`TauCeti.two_mul_prod_sq_sub_sq_eq`, stated for `∏_{c ≤ k}` and so with `2k + 2` factors).  The
same polynomial evaluates each row of the numerator once the rows below it are those of `ρ`, which
computes the denominator and the one-row weights.

A Young diagram `μ` is read through its first `n` rows
(`TauCeti.evenOrthogonalWeylDimension_congr`).  When `μ` has at most `n` rows it is a dominant
weight of `SO (2n)` with nonnegative last entry, and the value is the dimension of the
corresponding irreducible representation; the identification with that dimension is downstream of
the highest-weight classification.  The dominant weights of type
`Dₙ` are the `λ₁ ≥ ⋯ ≥ λₙ₋₁ ≥ |λₙ|`; the formula reads `λₙ` only through `lₙ₋₁² = λₙ²`, so the
weight with last entry `-λₙ` has the same value.  The half-spin representations of `Spin (2n)`,
whose highest weights have half-integral entries, are not indexed by Young diagrams and are not
covered here.

## Main definitions

* `TauCeti.evenOrthogonalWeylDimensionNumerator`: the product `∏_{i < j} (lᵢ - lⱼ)(lᵢ + lⱼ)`.
* `TauCeti.evenOrthogonalWeylDimension`: the dimension predicted by the Weyl dimension formula.

## Main results

* `TauCeti.evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial`: the defining identity,
  division-free.
* `TauCeti.evenOrthogonalWeylDimension_eq_prod_prod_div`: the product form of the formula, over
  `ℚ`.
* `TauCeti.evenOrthogonalWeylDimension_pos`: the dimension is positive.
* `TauCeti.evenOrthogonalWeylDimension_congr`: the dimension reads only the first `n` rows.
* `TauCeti.evenOrthogonalWeylDimension_eq_choose_add_choose_of_colLen_le_one`: for `SO (2n + 4)`, a
  one-row weight `(d, 0, …, 0)` has dimension
  `(d + 2n + 2).choose (2n + 2) + (d + 2n + 1).choose (2n + 2)`, that of the space of harmonic
  polynomials of degree `d` in `2n + 4` variables; and `TauCeti.evenOrthogonalWeylDimension_bot`,
  the trivial representation has dimension `1`.
* `TauCeti.evenOrthogonalWeylDimension_one`: the irreducible representations of the circle group
  `SO 2` are one-dimensional.
* `TauCeti.evenOrthogonalWeylDimension_two`: for `SO 4` the formula reads
  `(λ₁ - λ₂ + 1)(λ₁ + λ₂ + 1)`, the dimension of the exterior tensor product of the irreducible
  representations of dimensions `λ₁ - λ₂ + 1` and `λ₁ + λ₂ + 1` of the two factors of
  `Spin 4 ≅ SU 2 × SU 2`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §24.2.
-/

public section

namespace TauCeti

open Finset

variable (n : ℕ) (μ : YoungDiagram)

/-- The **numerator of the even orthogonal Weyl dimension formula**: with
`lᵢ = μᵢ + n - 1 - i` the entries of `μ + ρ` for the root system of type `Dₙ`, the product
`∏_{i < j < n} (lᵢ - lⱼ)(lᵢ + lⱼ)` of the pairings of `μ + ρ` with the positive roots `eᵢ ± eⱼ`. -/
def evenOrthogonalWeylDimensionNumerator : ℤ :=
  ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n,
    (orthogonalRhoShift n μ i - orthogonalRhoShift n μ j) *
      (orthogonalRhoShift n μ i + orthogonalRhoShift n μ j)

/-- **The numerator as a double product**: the defining equation of
`TauCeti.evenOrthogonalWeylDimensionNumerator`, the form every computation with it starts from. -/
theorem evenOrthogonalWeylDimensionNumerator_eq_prod_prod :
    evenOrthogonalWeylDimensionNumerator n μ =
      ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n,
        (orthogonalRhoShift n μ i - orthogonalRhoShift n μ j) *
          (orthogonalRhoShift n μ i + orthogonalRhoShift n μ j) :=
  (rfl)

/-- Every factor of the numerator is positive: the entries of `μ + ρ` are strictly decreasing and
nonnegative. -/
theorem evenOrthogonalWeylDimensionNumerator_pos :
    0 < evenOrthogonalWeylDimensionNumerator n μ := by
  rw [evenOrthogonalWeylDimensionNumerator_eq_prod_prod]
  refine prod_pos fun i _ => prod_pos fun j hj => ?_
  have hij := orthogonalRhoShift_strictAnti n μ (mem_Ico.1 hj).1
  have hj0 := orthogonalRhoShift_nonneg (μ := μ) (mem_Ico.1 hj).2
  exact mul_pos (sub_pos.2 hij) (by omega)

/-- **Integrality of the even orthogonal Weyl dimension formula**: `2!/2 · 4!/2 ⋯ (2n - 2)!/2`,
written `∏_{k < n - 1} (k + 1) (2k + 1)!`, divides the numerator. -/
theorem prod_dvd_evenOrthogonalWeylDimensionNumerator :
    (∏ k ∈ range (n - 1), ((k + 1) * (2 * k + 1).factorial : ℤ))
      ∣ evenOrthogonalWeylDimensionNumerator n μ := by
  rw [evenOrthogonalWeylDimensionNumerator_eq_prod_prod]
  convert prod_add_one_mul_factorial_dvd_prod_prod_sq_sub_sq n (orthogonalRhoShift n μ)
    using 2 with i _
  exact prod_congr rfl fun j _ => by ring

/-- A row of the numerator, all of whose lower rows are empty.  Below row `i` the entries of
`μ + ρ` are then those of `ρ`, namely `0, 1, …, k - 1` with `k = n - 1 - i`, so the row is
`∏_{c < k} (lᵢ² - c²)`. -/
private theorem evenOrthogonalWeylDimensionNumerator_row {i : ℕ}
    (h : ∀ j, i < j → μ.rowLen j = 0) :
    ∏ j ∈ Ico (i + 1) n, (orthogonalRhoShift n μ i - orthogonalRhoShift n μ j) *
        (orthogonalRhoShift n μ i + orthogonalRhoShift n μ j)
      = ∏ c ∈ range (n - 1 - i), (orthogonalRhoShift n μ i ^ 2 - (c : ℤ) ^ 2) := by
  set x := orthogonalRhoShift n μ i
  have hrow : ∀ t ∈ range (n - (i + 1)),
      (x - orthogonalRhoShift n μ (i + 1 + t)) * (x + orthogonalRhoShift n μ (i + 1 + t))
        = (fun c : ℕ => x ^ 2 - (c : ℤ) ^ 2) (n - 1 - i - 1 - t) := by
    intro t ht
    have ht := mem_range.1 ht
    have hc : ((n - 1 - i - 1 - t : ℕ) : ℤ) = n - 1 - (i + 1 + t : ℕ) := by omega
    simp only [hc]
    rw [orthogonalRhoShift_apply, h (i + 1 + t) (by omega), Nat.cast_zero, zero_add]
    ring
  have hlen : n - (i + 1) = n - 1 - i := by omega
  rw [prod_Ico_eq_prod_range, prod_congr rfl hrow, hlen,
    prod_range_reflect (fun c : ℕ => x ^ 2 - (c : ℤ) ^ 2) (n - 1 - i)]

/-- A row of the numerator, which with all the rows below it is empty: its entry of `μ + ρ` is
`k = n - 1 - i`, and the row is `∏_{c < k} (k² - c²)`. -/
private theorem evenOrthogonalWeylDimensionNumerator_row_of_rowLen_eq_zero {i : ℕ} (hi : i < n)
    (h : ∀ j, i ≤ j → μ.rowLen j = 0) :
    ∏ j ∈ Ico (i + 1) n, (orthogonalRhoShift n μ i - orthogonalRhoShift n μ j) *
        (orthogonalRhoShift n μ i + orthogonalRhoShift n μ j)
      = (fun k : ℕ => ∏ c ∈ range k, ((k : ℤ) ^ 2 - (c : ℤ) ^ 2)) (n - 1 - i) := by
  have hx : orthogonalRhoShift n μ i = ((n - 1 - i : ℕ) : ℤ) := by
    rw [orthogonalRhoShift_apply, h i le_rfl]
    omega
  rw [evenOrthogonalWeylDimensionNumerator_row n μ fun j hj => h j hj.le, hx]

/-- The value of the numerator at `μ = 0`, the denominator of the Weyl dimension formula: at
`ρ = (n - 1, …, 0)` the row `i` is `∏_{c < k} (k² - c²) = (2k)! / 2` with `k = n - 1 - i` (and `1`
for `k = 0`), so the numerator is `2!/2 · 4!/2 ⋯ (2n - 2)!/2`. -/
@[simp]
theorem evenOrthogonalWeylDimensionNumerator_bot :
    evenOrthogonalWeylDimensionNumerator n ⊥
      = ∏ k ∈ range (n - 1), ((k + 1) * (2 * k + 1).factorial : ℤ) := by
  rw [evenOrthogonalWeylDimensionNumerator_eq_prod_prod,
    prod_congr rfl fun i hi => evenOrthogonalWeylDimensionNumerator_row_of_rowLen_eq_zero n ⊥
      (mem_range.1 hi) fun j _ => YoungDiagram.rowLen_bot j,
    prod_range_reflect (fun k : ℕ => ∏ c ∈ range k, ((k : ℤ) ^ 2 - (c : ℤ) ^ 2)) n,
    prod_prod_sq_sub_sq_eq_prod_add_one_mul_factorial]

/-- **The even orthogonal Weyl dimension** of a Young diagram `μ`, read through its first `n` rows:
the value

`∏_{i < j < n} (lᵢ² - lⱼ²) / (rᵢ² - rⱼ²)`, `lᵢ = μᵢ + n - 1 - i`, `rᵢ = n - 1 - i`,

of the Weyl dimension formula for `SO (2n)`.  For `μ` with at most `n` rows it is the dimension of
the irreducible representation of `SO (2n)` with highest weight `μ`.  The quotient is taken once,
of `TauCeti.evenOrthogonalWeylDimensionNumerator` by its value `2!/2 · 4!/2 ⋯ (2n - 2)!/2` at
`μ = 0`, written `∏_{k < n - 1} (k + 1) (2k + 1)!`;
`TauCeti.evenOrthogonalWeylDimension_eq_prod_prod_div` recovers the term-by-term form over `ℚ`. -/
def evenOrthogonalWeylDimension : ℕ :=
  (evenOrthogonalWeylDimensionNumerator n μ /
    ∏ k ∈ range (n - 1), ((k + 1) * (2 * k + 1).factorial : ℤ)).toNat

/-- **The defining identity of `TauCeti.evenOrthogonalWeylDimension`**, in division-free form: the
dimension times `2!/2 · 4!/2 ⋯ (2n - 2)!/2` is the numerator. -/
theorem evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial :
    (evenOrthogonalWeylDimension n μ : ℤ) *
        ∏ k ∈ range (n - 1), ((k + 1) * (2 * k + 1).factorial : ℤ)
      = evenOrthogonalWeylDimensionNumerator n μ := by
  rw [evenOrthogonalWeylDimension, Int.toNat_of_nonneg (Int.ediv_nonneg
      (evenOrthogonalWeylDimensionNumerator_pos n μ).le
      (prod_add_one_mul_factorial_two_mul_add_one_pos _).le),
    Int.ediv_mul_cancel (prod_dvd_evenOrthogonalWeylDimensionNumerator n μ)]

/-- **The even orthogonal Weyl dimension is positive**. -/
theorem evenOrthogonalWeylDimension_pos : 0 < evenOrthogonalWeylDimension n μ := by
  have h := evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial n μ
  have h0 := evenOrthogonalWeylDimensionNumerator_pos n μ
  rw [← h] at h0
  exact_mod_cast pos_of_mul_pos_left h0 (prod_add_one_mul_factorial_two_mul_add_one_pos _).le

/-- The numerator over `ℚ`, as the product of the differences of the squares of the entries
`μᵢ + n - 1 - i` of `μ + ρ`. -/
private theorem evenOrthogonalWeylDimensionNumerator_cast (ν : YoungDiagram) :
    ((evenOrthogonalWeylDimensionNumerator n ν : ℤ) : ℚ) =
      ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n,
        (((ν.rowLen i : ℚ) + n - 1 - i) ^ 2 - ((ν.rowLen j : ℚ) + n - 1 - j) ^ 2) := by
  rw [evenOrthogonalWeylDimensionNumerator_eq_prod_prod]
  push_cast
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  simp only [orthogonalRhoShift_apply]
  push_cast
  ring

/-- **The Weyl dimension formula for `SO (2n)` in its product form**: over `ℚ`, with
`lᵢ = μᵢ + n - 1 - i` and `rᵢ = n - 1 - i` the entries of `μ + ρ` and of `ρ`, the dimension is

`∏_{i < j < n} (lᵢ² - lⱼ²) / (rᵢ² - rⱼ²)`. -/
theorem evenOrthogonalWeylDimension_eq_prod_prod_div :
    (evenOrthogonalWeylDimension n μ : ℚ) =
      ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n,
        ((((μ.rowLen i : ℚ) + n - 1 - i) ^ 2 - ((μ.rowLen j : ℚ) + n - 1 - j) ^ 2)
          / (((n : ℚ) - 1 - i) ^ 2 - ((n : ℚ) - 1 - j) ^ 2)) := by
  have hnum := evenOrthogonalWeylDimensionNumerator_cast n μ
  have hden := evenOrthogonalWeylDimensionNumerator_cast n ⊥
  simp only [YoungDiagram.rowLen_bot, Nat.cast_zero, zero_add] at hden
  rw [evenOrthogonalWeylDimensionNumerator_bot] at hden
  have hden0 : ((∏ k ∈ range (n - 1), ((k + 1) * (2 * k + 1).factorial : ℤ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (prod_add_one_mul_factorial_two_mul_add_one_pos _).ne'
  simp only [prod_div_distrib]
  rw [← hnum, ← hden, eq_div_iff hden0]
  exact_mod_cast evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial n μ

variable {n μ} in
/-- **The numerator reads only the first `n` rows**: two diagrams whose rows `0, …, n - 1` have
the same lengths have the same numerator. -/
theorem evenOrthogonalWeylDimensionNumerator_congr {ν : YoungDiagram}
    (h : ∀ i < n, μ.rowLen i = ν.rowLen i) :
    evenOrthogonalWeylDimensionNumerator n μ = evenOrthogonalWeylDimensionNumerator n ν := by
  have hx : ∀ i < n, orthogonalRhoShift n μ i = orthogonalRhoShift n ν i := fun i hi => by
    simp only [orthogonalRhoShift_apply, h i hi]
  rw [evenOrthogonalWeylDimensionNumerator_eq_prod_prod,
    evenOrthogonalWeylDimensionNumerator_eq_prod_prod]
  refine prod_congr rfl fun i hi => prod_congr rfl fun j hj => ?_
  rw [hx i (mem_range.1 hi), hx j (mem_Ico.1 hj).2]

variable {n μ} in
/-- **The even orthogonal Weyl dimension reads only the first `n` rows**: two diagrams whose rows
`0, …, n - 1` have the same lengths have the same dimension. -/
theorem evenOrthogonalWeylDimension_congr {ν : YoungDiagram}
    (h : ∀ i < n, μ.rowLen i = ν.rowLen i) :
    evenOrthogonalWeylDimension n μ = evenOrthogonalWeylDimension n ν := by
  -- Cancel the denominator to reduce to the numerator.
  have h1 : (evenOrthogonalWeylDimension n μ : ℤ) *
        ∏ k ∈ range (n - 1), ((k + 1) * (2 * k + 1).factorial : ℤ) =
      (evenOrthogonalWeylDimension n ν : ℤ) *
        ∏ k ∈ range (n - 1), ((k + 1) * (2 * k + 1).factorial : ℤ) :=
    (evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial n μ).trans
      ((evenOrthogonalWeylDimensionNumerator_congr h).trans
        (evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial n ν).symm)
  exact_mod_cast mul_right_cancel₀ (prod_add_one_mul_factorial_two_mul_add_one_pos _).ne' h1

/-- The numerator of a weight with at most one row, of length `d`, for `SO (2n + 4)`: below the
first row the entries of `μ + ρ` are those of `ρ`, so the rows `1, …, n + 1` contribute
`2!/2 · 4!/2 ⋯ (2n)!/2`, and the first row is `∏_{c ≤ n} ((d + n + 1)² - c²)`. -/
private theorem evenOrthogonalWeylDimensionNumerator_add_two_of_colLen_le_one
    (h : μ.colLen 0 ≤ 1) :
    evenOrthogonalWeylDimensionNumerator (n + 2) μ
      = (∏ k ∈ range n, ((k + 1) * (2 * k + 1).factorial : ℤ))
        * ∏ c ∈ range (n + 1), (((μ.rowLen 0 + n + 1 : ℕ) : ℤ) ^ 2 - (c : ℤ) ^ 2) := by
  have h' : ∀ j, 0 < j → μ.rowLen j = 0 := fun j hj =>
    YoungDiagram.rowLen_eq_zero_of_colLen_le (h.trans hj)
  rw [evenOrthogonalWeylDimensionNumerator_eq_prod_prod, prod_range_succ']
  congr 1
  · rw [prod_congr rfl fun i hi => evenOrthogonalWeylDimensionNumerator_row_of_rowLen_eq_zero
        (n + 2) μ (by have := mem_range.1 hi; omega) fun j hj => h' j (by omega)]
    have hk : ∀ i ∈ range (n + 1), (fun k : ℕ => ∏ c ∈ range k, ((k : ℤ) ^ 2 - (c : ℤ) ^ 2))
        (n + 2 - 1 - (i + 1)) = (fun k : ℕ => ∏ c ∈ range k, ((k : ℤ) ^ 2 - (c : ℤ) ^ 2))
          (n + 1 - 1 - i) := fun i hi => by
      have := mem_range.1 hi
      congr 1
      omega
    rw [prod_congr rfl hk,
      prod_range_reflect (fun k : ℕ => ∏ c ∈ range k, ((k : ℤ) ^ 2 - (c : ℤ) ^ 2)) (n + 1),
      prod_prod_sq_sub_sq_eq_prod_add_one_mul_factorial, Nat.add_sub_cancel]
  · have hx : orthogonalRhoShift (n + 2) μ 0 = ((μ.rowLen 0 + n + 1 : ℕ) : ℤ) := by
      rw [orthogonalRhoShift_apply]
      push_cast
      ring
    rw [evenOrthogonalWeylDimensionNumerator_row (n + 2) μ fun j hj => h' j hj, hx, Nat.sub_zero,
      Nat.add_succ_sub_one]

/-- **One-row weights**: if `μ` has at most one row, of length `d`, then the even orthogonal Weyl
dimension for `SO (2n + 4)` is `(d + 2n + 2).choose (2n + 2) + (d + 2n + 1).choose (2n + 2)`, the
dimension of the space of harmonic polynomials of degree `d` in `2n + 4` variables, on which
`SO (2n + 4)` acts irreducibly. -/
theorem evenOrthogonalWeylDimension_eq_choose_add_choose_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    evenOrthogonalWeylDimension (n + 2) μ
      = (μ.rowLen 0 + 2 * n + 2).choose (2 * n + 2)
        + (μ.rowLen 0 + 2 * n + 1).choose (2 * n + 2) := by
  have hdim := evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial (n + 2) μ
  rw [evenOrthogonalWeylDimensionNumerator_add_two_of_colLen_le_one n μ h,
    Nat.add_succ_sub_one, prod_range_succ, mul_comm, mul_assoc] at hdim
  have hP := (prod_add_one_mul_factorial_two_mul_add_one_pos n).ne'
  -- Cancel `2!/2 ⋯ (2n)!/2`, then double the first row into two falling factorials.
  have hrow := mul_left_cancel₀ hP hdim
  have h2 := two_mul_prod_sq_sub_sq_eq (R := ℤ) n ((μ.rowLen 0 + n + 1 : ℕ) : ℤ)
  have e1 : ((μ.rowLen 0 + n + 1 : ℕ) : ℤ) + n + 1 = ((μ.rowLen 0 + 2 * n + 2 : ℕ) : ℤ) := by
    push_cast
    ring
  have e2 : ((μ.rowLen 0 + n + 1 : ℕ) : ℤ) + n = ((μ.rowLen 0 + 2 * n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [e1, e2, descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    ← hrow] at h2
  have hfac : ((2 * n + 2).factorial : ℤ) = 2 * ((n + 1) * (2 * n + 1).factorial) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hpos : (0 : ℤ) < (2 * n + 2).factorial := mod_cast (2 * n + 2).factorial_pos
  have hchoose : (evenOrthogonalWeylDimension (n + 2) μ : ℤ)
      = (((μ.rowLen 0 + 2 * n + 2).choose (2 * n + 2)
        + (μ.rowLen 0 + 2 * n + 1).choose (2 * n + 2) : ℕ) : ℤ) := by
    refine mul_left_cancel₀ hpos.ne' ?_
    push_cast at h2 ⊢
    rw [hfac] at h2 ⊢
    linear_combination h2
  exact_mod_cast hchoose

/-- The group `SO 0` is trivial, and so is the formula: an empty product. -/
@[simp]
theorem evenOrthogonalWeylDimension_zero : evenOrthogonalWeylDimension 0 μ = 1 := by
  have h := evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial 0 μ
  simp only [evenOrthogonalWeylDimensionNumerator_eq_prod_prod, range_zero, prod_empty] at h
  exact_mod_cast h

/-- **The `SO 2` case**: the circle group is abelian, and the formula, an empty product, gives every
irreducible representation dimension `1`. -/
@[simp]
theorem evenOrthogonalWeylDimension_one : evenOrthogonalWeylDimension 1 μ = 1 := by
  have h := evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial 1 μ
  simp only [evenOrthogonalWeylDimensionNumerator_eq_prod_prod, range_one, prod_singleton,
    Ico_self, prod_empty, Nat.sub_self, range_zero, mul_one] at h
  exact_mod_cast h

/-- **The trivial representation**: the empty diagram has even orthogonal Weyl dimension `1`. -/
@[simp]
theorem evenOrthogonalWeylDimension_bot : evenOrthogonalWeylDimension n ⊥ = 1 := by
  have h := evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial n ⊥
  rw [evenOrthogonalWeylDimensionNumerator_bot] at h
  exact_mod_cast mul_right_cancel₀ (prod_add_one_mul_factorial_two_mul_add_one_pos _).ne'
    (h.trans (one_mul _).symm)

/-- **The `SO 4` case**: the irreducible representation with highest weight `(λ₁, λ₂)` has
dimension `(λ₁ - λ₂ + 1)(λ₁ + λ₂ + 1)`.  Under `Spin 4 ≅ SU 2 × SU 2` it is the exterior tensor
product of the irreducible representations of the two factors of dimensions `λ₁ - λ₂ + 1` and
`λ₁ + λ₂ + 1`.  The formula reads only the first two rows. -/
@[simp]
theorem evenOrthogonalWeylDimension_two :
    evenOrthogonalWeylDimension 2 μ
      = (μ.rowLen 0 - μ.rowLen 1 + 1) * (μ.rowLen 0 + μ.rowLen 1 + 1) := by
  have h := evenOrthogonalWeylDimension_mul_prod_add_one_mul_factorial 2 μ
  have hle := μ.rowLen_anti 0 1 zero_le_one
  simp only [evenOrthogonalWeylDimensionNumerator_eq_prod_prod, orthogonalRhoShift_apply,
    Nat.reduceSub, range_one, prod_singleton] at h
  rw [prod_range_succ, range_one, prod_singleton, Ico_self, prod_empty, mul_one,
    zero_add, Nat.Ico_succ_singleton, prod_singleton] at h
  norm_num at h
  zify [hle]
  linear_combination h

end TauCeti

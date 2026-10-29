/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.Young.YoungDiagram
import TauCeti.Combinatorics.Young.Diagram
import TauCeti.Combinatorics.Young.OfRowLens
import TauCeti.Data.Fin.StrictAnti

/-!
# Beta-numbers of a Young diagram

Fix a Young diagram `μ` and a bound `r` on its number of rows. The `i`-th **beta-number**
`YoungDiagram.betaNumber μ r i = μ.rowLen i + (r - 1 - i)` is the length of row `i` plus the number
`r - 1 - i` of rows of the bounding `r`-row strip that lie below it. Adding that shift to the weakly
decreasing row lengths makes the beta-numbers strictly decrease across the indices `i < j < r`
inside the bound, so those `r` numbers are pairwise distinct; that is the whole point of the
construction.  This file also records that the natural-number product of their differences casts
to the corresponding integer product.

Beta-numbers are the bookkeeping device behind the Frobenius determinant formula and the
Frame-Robinson-Thrall route to the hook-length formula. Their relation to hook lengths --- for the
exact row count `r = μ.colLen 0` the beta-numbers of the nonempty rows `i < μ.colLen 0` are the
hook lengths of the first column, and in general they describe a row of hook lengths --- needs the
hook-length API and is developed in `TauCeti/Combinatorics/Young/HookLength/BetaNumbers.lean`.

## Main definitions

* `YoungDiagram.betaNumber`: the beta-numbers of `μ` relative to a bound `r` on its number of rows.
* `YoungDiagram.complBetaNumber`: the complementary beta-numbers, `r + p` minus the length of
  column `p`; when `c` bounds the number of columns they fill the complement of the beta-set.

## Main results

* `YoungDiagram.betaNumber_lt_betaNumber`: the beta-numbers strictly decrease across the indices
  `i < j < r` inside the bound.
* `YoungDiagram.injOn_betaNumber`: the beta-numbers of the indices `i < r` are pairwise distinct.
* `YoungDiagram.strictAnti_betaNumber`: the beta-numbers relative to `r` are strictly antitone on
  `Fin r`, and `YoungDiagram.exists_eq_betaNumber_of_strictAnti`: conversely every strictly antitone
  `Fin r → ℕ` is the sequence of beta-numbers of a diagram with at most `r` rows.
* `YoungDiagram.eq_of_betaNumber_eq`: a Young diagram with at most `r` rows is determined by its
  beta-numbers of the indices `i < r`.
* `YoungDiagram.sum_betaNumber`: the beta-numbers of a diagram with at most `r` rows total its
  number of cells plus the staircase `∑_j (r - 1 - j)`.
* `YoungDiagram.cast_prod_betaNumber_sub`: casts the product of beta-number differences from
  `ℕ` to `ℤ`.
* `YoungDiagram.betaNumber_lt_add` and `YoungDiagram.complBetaNumber_lt`: the beta-numbers and
  complementary beta-numbers of a diagram stay inside the bounding strip `r + c`.
* `YoungDiagram.strictMono_complBetaNumber`: the complementary beta-numbers increase with their
  index.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  1, Example 1, for beta-numbers and the description of a row of hook lengths by them.
-/

public section

namespace YoungDiagram

variable {μ : YoungDiagram} {r i j : ℕ}

/-- The `i`-th **beta-number** of a Young diagram `μ`, relative to a bound `r` on its number of
rows: the length of row `i` plus the number `r - 1 - i` of rows of the bounding `r`-row strip that
lie below it. For `r = μ.colLen 0` and a nonempty row `i < μ.colLen 0` this is the hook length of
the first cell of row `i`; see `YoungDiagram.betaNumber_eq_hookLength`. -/
def betaNumber (μ : YoungDiagram) (r i : ℕ) : ℕ := μ.rowLen i + (r - 1 - i)

theorem betaNumber_def (μ : YoungDiagram) (r i : ℕ) :
    μ.betaNumber r i = μ.rowLen i + (r - 1 - i) := (rfl)

/-- The `p`-th **complementary beta-number** of a Young diagram `μ` with `r` rows: `r + p` minus
the length of column `p` of `μ`.  When `c` is at least the number of columns of `μ`, the `c`
numbers `μ.complBetaNumber r p` for `p < c` are the complement, inside `Fin (r + c)`, of the
beta-set `μ.betaNumber r i` for `i < r`. -/
def complBetaNumber (μ : YoungDiagram) (r p : ℕ) : ℕ := r + p - μ.transpose.rowLen p

/-- The complementary beta-numbers are the column lengths of the conjugate diagram, shifted. -/
theorem complBetaNumber_def (μ : YoungDiagram) (r p : ℕ) :
    μ.complBetaNumber r p = r + p - μ.transpose.rowLen p := (rfl)

/-- The beta-numbers strictly decrease along the rows, because the row lengths are weakly
decreasing while the shifts `r - 1 - i` strictly decrease. -/
theorem betaNumber_lt_betaNumber (μ : YoungDiagram) (hij : i < j) (hj : j < r) :
    μ.betaNumber r j < μ.betaNumber r i := by
  have := μ.rowLen_anti i j hij.le
  simp only [betaNumber_def]
  omega

-- The antecedents of `betaNumber_lt_betaNumber` mention no beta-number, so the `@[grind →]`
-- pattern does not exist; the useful trigger is a pair of beta-numbers sharing a bound, which is
-- what makes `grind` derive `βᵢ ≠ βⱼ` and `βᵢ - βⱼ ≠ 0` on its own.
grind_pattern betaNumber_lt_betaNumber => μ.betaNumber r i, μ.betaNumber r j

/-- The beta-numbers stay inside the bounding strip `r + c`. -/
theorem betaNumber_lt_add (μ : YoungDiagram) {r c : ℕ} (hc : μ.rowLen 0 ≤ c) {i : ℕ}
    (hi : i < r) : μ.betaNumber r i < r + c := by
  have h1 : μ.rowLen i ≤ c := (μ.rowLen_anti 0 i (Nat.zero_le i)).trans hc
  simp only [betaNumber_def]
  omega

/-- The complementary beta-numbers stay inside the bounding strip `r + c`. -/
theorem complBetaNumber_lt (μ : YoungDiagram) {r c p : ℕ} (hp : p < c) :
    μ.complBetaNumber r p < r + c := by
  simp only [complBetaNumber_def]
  omega

/-- The complementary beta-numbers increase with their index. -/
theorem strictMono_complBetaNumber (μ : YoungDiagram) {r c : ℕ} (hr : μ.colLen 0 ≤ r) :
    StrictMono fun p : Fin c => μ.complBetaNumber r p := by
  intro p q hpq
  have hpq' : (p : ℕ) < (q : ℕ) := hpq
  have h1 : μ.transpose.rowLen q ≤ μ.transpose.rowLen p := by
    rw [μ.rowLen_transpose, μ.rowLen_transpose]
    exact μ.colLen_anti (p : ℕ) (q : ℕ) hpq'.le
  have h2 : μ.transpose.rowLen p ≤ r := by
    rw [μ.rowLen_transpose]
    exact (μ.colLen_anti 0 (p : ℕ) (Nat.zero_le p)).trans hr
  simp only [complBetaNumber_def, Fin.lt_def] at hpq ⊢
  omega

/-- The beta-numbers of the rows inside the bound strictly decrease. -/
theorem strictAntiOn_betaNumber (μ : YoungDiagram) (r : ℕ) :
    StrictAntiOn (μ.betaNumber r) (Set.Iio r) :=
  fun _ _ _ hb hab => μ.betaNumber_lt_betaNumber hab (Set.mem_Iio.mp hb)

/-- The beta-numbers of the rows inside the bound are pairwise distinct. -/
theorem injOn_betaNumber (μ : YoungDiagram) (r : ℕ) :
    Set.InjOn (μ.betaNumber r) (Set.Iio r) :=
  (μ.strictAntiOn_betaNumber r).injOn

/-- **A Young diagram is determined by its beta-numbers**: two diagrams with at most `r` rows whose
beta-numbers relative to `r` agree at every index `i < r` are equal.  Inside the bound the row
lengths are recovered by subtracting the common shift `r - 1 - i`, and outside it both diagrams
have empty rows. -/
theorem eq_of_betaNumber_eq {ν : YoungDiagram} (hμ : μ.colLen 0 ≤ r) (hν : ν.colLen 0 ≤ r)
    (h : ∀ i < r, μ.betaNumber r i = ν.betaNumber r i) : μ = ν := by
  refine rowLen_injective (funext fun i => ?_)
  by_cases hi : i < r
  · have := h i hi
    rw [betaNumber_def, betaNumber_def] at this
    omega
  · rw [rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.not_lt.mp hi)),
      rowLen_eq_zero_of_colLen_le (hν.trans (Nat.not_lt.mp hi))]

/-- The beta-numbers relative to a bound `r` strictly decrease along the indices `Fin r`. -/
theorem strictAnti_betaNumber (μ : YoungDiagram) (r : ℕ) :
    StrictAnti fun j : Fin r => μ.betaNumber r j :=
  fun _ j hij => μ.betaNumber_lt_betaNumber (Fin.lt_def.mp hij) j.isLt

/-- **A strictly decreasing sequence of naturals is a sequence of beta-numbers.**  Every strictly
antitone `η : Fin r → ℕ` is the sequence of beta-numbers relative to `r` of a Young diagram with at
most `r` rows, unique by `YoungDiagram.eq_of_betaNumber_eq`.  Strict decrease is exactly what makes
the differences `η j - (r - 1 - j)` weakly decreasing and nonnegative, hence row lengths. -/
theorem exists_eq_betaNumber_of_strictAnti {r : ℕ} {η : Fin r → ℕ} (hη : StrictAnti η) :
    ∃ μ : YoungDiagram, μ.colLen 0 ≤ r ∧ ∀ j : Fin r, μ.betaNumber r j = η j := by
  have hshift : ∀ j : Fin r, r - 1 - (j : ℕ) ≤ η j := by
    intro j
    have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    set L : Fin r := ⟨r - 1, by omega⟩ with _hLdef
    have hLval : (L : ℕ) = r - 1 := rfl
    have hle : j ≤ L := Fin.le_def.mpr (by rw [hLval]; omega)
    have hgap := hη.add_sub_le_nat hle
    rw [hLval] at hgap
    omega
  have hanti : Antitone fun j : Fin r => η j - (r - 1 - (j : ℕ)) := by
    intro i j hij
    dsimp only
    have hgap := hη.add_sub_le_nat hij
    have hi := hshift i
    have hj := hshift j
    have _ : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
    have _ : (j : ℕ) < r := j.isLt
    omega
  refine ⟨ofRowLensFin _ hanti, colLen_zero_ofRowLensFin_le _ hanti, fun j => ?_⟩
  rw [betaNumber_def, rowLen_ofRowLensFin]
  have := hshift j
  omega


open Finset

/-- **The beta-numbers of a diagram total its size plus the staircase.**  For a diagram with at most
`r` rows the row lengths add up to the number of cells, and the shifts add up separately. -/
theorem sum_betaNumber (μ : YoungDiagram) {r : ℕ} (hμ : μ.colLen 0 ≤ r) :
    ∑ j : Fin r, μ.betaNumber r j = μ.card + ∑ j : Fin r, (r - 1 - (j : ℕ)) := by
  simp only [betaNumber_def]
  rw [Finset.sum_add_distrib, card_eq_sum_range_rowLen μ hμ,
    Fin.sum_univ_eq_sum_range (fun i => μ.rowLen i) r]

/-- The Vandermonde-style product of the differences of the beta-numbers is computed by the same
formula over `ℤ`, the differences being nonnegative. -/
theorem cast_prod_betaNumber_sub (μ : YoungDiagram) (r : ℕ) :
    ((∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r, (μ.betaNumber r k - μ.betaNumber r l) : ℕ) : ℤ)
      = ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r,
          ((μ.betaNumber r k : ℤ) - (μ.betaNumber r l : ℤ)) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [mem_Ico] at hl
  exact Nat.cast_sub (μ.betaNumber_lt_betaNumber (by omega) hl.2).le

end YoungDiagram

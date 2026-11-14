/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Charpoly
public import TauCeti.RepresentationTheory.FDRep.Basic

/-!
# Checks for characters and characteristic polynomials

These examples exercise Newton's identities for the traces of the powers of a matrix and their
character form.

* `d = 2`: with `c_1 = -tr A` and `c_2 = det A`, Newton's identity in degree two gives
  `2 det A = tr (A) ^ 2 - tr (A ^ 2)`.
* `d = 0`: `det (1 - X A) = 1`, and both sides of the recurrence vanish in every positive degree.
* A four-dimensional representation and an element with `g ^ 2 = 1`: the traces of the powers
  alternate between `χ (g)` and `4`, and `χ (g) = 2` forces the characteristic polynomial
  `(X - 1) ^ 3 * (X + 1)`.
* Adding a trivial summand of dimension `s` multiplies the characteristic polynomial by
  `(X - 1) ^ s` and adds `s` to every trace of a power, including for `s = 0`.
-/

public section

open Finset Module Polynomial Representation

namespace TauCeti.Examples.RepresentationTheory.CharacterTableCharpoly

/-! ### Matrices of size two and zero -/

/-- For a `2 × 2` matrix, Newton's identity in degree two reads `2 det A = tr (A) ^ 2 - tr (A ^ 2)`,
so `det A = (tr (A) ^ 2 - tr (A ^ 2)) / 2` over `ℚ`. -/
example (A : Matrix (Fin 2) (Fin 2) ℚ) : A.det = (A.trace ^ 2 - (A ^ 2).trace) / 2 := by
  have h1 : A.charpolyRev.coeff 1 = -A.trace := by simp
  have h2 := A.mul_coeff_charpolyRev_eq_neg_sum 2
  have hdet : A.charpolyRev.coeff 2 = A.det := by
    simpa using A.coeff_charpolyRev_card
  simp only [sum_range_succ, sum_range_zero, h1, hdet] at h2
  norm_num at h2
  linear_combination h2 / 2

/-- For a `0 × 0` matrix, `det (1 - X A) = 1` and both sides of the recurrence vanish. -/
example {R : Type*} [CommRing R] (A : Matrix (Fin 0) (Fin 0) R) {r : ℕ} (hr : 0 < r) :
    A.charpolyRev = 1 ∧ (r : R) * A.charpolyRev.coeff r = 0 ∧
      ∑ j ∈ range r, A.charpolyRev.coeff (r - (j + 1)) * (A ^ (j + 1)).trace = 0 :=
  ⟨Matrix.charpolyRev_isEmpty A, by simp [Matrix.charpolyRev_isEmpty, Polynomial.coeff_one, hr.ne'],
    by simp [Matrix.trace]⟩

/-! ### Representations -/

variable {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ρ : Representation k G V)

/-- For an element with `g ^ 2 = 1` of a four-dimensional representation, the traces of the powers
of `ρ g` alternate between `χ (g)` and `4`. -/
example (hV : finrank k V = 4) {g : G} (hg : g ^ 2 = 1) :
    LinearMap.trace k V (ρ g) = ρ.character g ∧ LinearMap.trace k V (ρ g ^ 2) = 4 ∧
      LinearMap.trace k V (ρ g ^ 3) = ρ.character g ∧ LinearMap.trace k V (ρ g ^ 4) = 4 := by
  have h3 : g ^ 3 = g := by rw [pow_succ, hg, one_mul]
  have h4 : g ^ 4 = 1 := by rw [show 4 = 2 * 2 by rfl, pow_mul, hg, one_pow]
  simp only [trace_pow_eq_character_pow, hg, h3, h4, char_one, hV]
  exact ⟨rfl, by norm_num, trivial, by norm_num⟩

/-- For an element with `g ^ 2 = 1` and `χ (g) = 2` of a four-dimensional representation, the
characteristic polynomial of `ρ g` is `(X - 1) ^ 3 * (X + 1)`. -/
example (hV : finrank k V = 4) {g : G} (hg : g ^ 2 = 1) (hχ : ρ.character g = 2) :
    (ρ g).charpoly = (X - 1) ^ 3 * (X + 1) := by
  rw [ρ.charpoly_apply_eq_of_sq_eq_one hg (a := 3) (b := 1) (by omega) (by rw [hχ]; norm_num),
    pow_one]

/-- Adding a trivial summand of dimension `s` multiplies the characteristic polynomial by
`(X - 1) ^ s`. -/
example (s : ℕ) (g : G) :
    (ρ.prod (trivial k G (Fin s → k)) g).charpoly = (ρ g).charpoly * (X - 1) ^ s := by
  have h1 : trivial k G (Fin s → k) g = 1 := by ext; simp
  rw [charpoly_prod_apply, h1, LinearMap.charpoly_one, finrank_fin_fun]

/-- Adding a trivial summand of dimension `s` adds `s` to every trace of a power. -/
example (s : ℕ) (g : G) (j : ℕ) :
    LinearMap.trace k _ (ρ.prod (trivial k G (Fin s → k)) g ^ j) =
      LinearMap.trace k V (ρ g ^ j) + s := by
  simp [trace_pow_eq_character_pow, char_trivial]

end TauCeti.Examples.RepresentationTheory.CharacterTableCharpoly

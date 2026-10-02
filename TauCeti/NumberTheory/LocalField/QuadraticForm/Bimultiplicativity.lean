/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.NormalizedValuation

import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.HilbertSymbol.SquareClassIndex
import TauCeti.NumberTheory.LocalField.FiniteExtension.SquareClass
import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass
import TauCeti.NumberTheory.LocalField.Squares

/-!
# The index theorem for quadratic norms, and bimultiplicativity of the local Hilbert symbol

Let `K` be a nonarchimedean local field with `2 ≠ 0`, in any residue characteristic. The norms
from `K(√a)`, that is the subgroup `N` of `Kˣ` consisting of the `b` of the form `x² - a y²` with
`x, y ∈ K`, form a subgroup of index two in `Kˣ` for every nonsquare radicand `a`.

The index is computed by counting square classes, uniformly in the residue characteristic and in
the quadratic defect of `a`. For `L = K(√a)`,
`TauCeti.two_mul_index_quadraticNormSubgroup_mul_card_squareClass` gives
`2 · (Kˣ : N) · #(Lˣ/(Lˣ)²) = #(Kˣ/(Kˣ)²)²` over any field with `2 ≠ 0`. Over a local field
`#(Kˣ/(Kˣ)²) = 4 q^{v_K(2)}`, with `q = #𝓀[K]`, and since `[L : K] = 2`,
`TauCeti.card_squareClass_eq_four_mul_pow_finrank` gives `#(Lˣ/(Lˣ)²) = 4 q^{2 v_K(2)}`. Hence
`(Kˣ : N) = 2`.

The sign indicator of an index-two subgroup is a character, so the local Hilbert symbol is
bimultiplicative in both arguments. The same index theorem gives nondegeneracy, and there that step
is purely group-theoretic: the sign indicator of a proper subgroup of index two is onto, so it takes
the value `-1` off the subgroup. The field-level statement is
`TauCeti.exists_hilbertSymbol_eq_neg_one_of_index_eq_two`, which asks only that the norm subgroup of
`a` have index two.

Nondegeneracy has two consequences for prescribing values of the symbol. Two distinct nontrivial
characters `(·, a)_K` and `(·, b)_K` of the group `Kˣ/(Kˣ)²` of exponent two take every pair of
values. And the norm group of `K(√a)` contains a nonsquare for every `a`: among a uniformizer, the
unramified unit and their product, three nonsquares, the symbols with `a` multiply to `1`.

The diagonal entry `(a, a)_K = (a, -1)_K` needs no arithmetic input and is stated for an arbitrary
field in `TauCeti.NumberTheory.HilbertSymbol.NormSubgroup`, as
`TauCeti.hilbertSymbol_self`.

## Main results

* `TauCeti.quadraticNormSubgroup_index_eq_two_of_not_isSquare`: the norm index of every nonsquare
  radicand.
* `TauCeti.hilbertSymbol_mul_right` and `TauCeti.hilbertSymbol_mul_left`: the Hilbert symbol is
  bilinear in both arguments.
* `TauCeti.hilbertSymbol_self_mul` and `TauCeti.hilbertSymbol_neg_self_mul`:
  `(a, ab)_K = (a, -b)_K` and `(a, -ab)_K = (a, b)_K`.
* `TauCeti.exists_hilbertSymbol_eq_neg_one`: for every nonsquare `a` there is a `b` with
  `(a, b)_K = -1`.
* `TauCeti.exists_hilbertSymbol_eq_and_hilbertSymbol_eq`: for nonsquares `a`, `b` with `ab` a
  nonsquare, the characters `(·, a)_K` and `(·, b)_K` take every pair of values.
* `TauCeti.exists_not_isSquare_hilbertSymbol_eq_one`: the norm group of `K(√a)` contains a
  nonsquare, for every `a`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter VI, §2.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 2.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The norm index of a nonsquare radicand.** If `2 ≠ 0` in `K`, the norms from `K(√a)` form
a subgroup of index two in `Kˣ` for every `a` that is not a square. -/
theorem quadraticNormSubgroup_index_eq_two_of_not_isSquare (h2 : (2 : K) ≠ 0) {a : Kˣ}
    (ha : ¬IsSquare a) : (quadraticNormSubgroup (a : K)).index = 2 := by
  have : Fact (¬IsSquare (a : K)) := ⟨isSquare_units_val_iff.not.mpr ha⟩
  have h := two_mul_index_quadraticNormSubgroup_mul_card_squareClass a h2
  rw [card_squareClass_eq_four_mul_pow_finrank h2, QuadraticAlgebra.finrank_eq_two,
    card_squareClass h2] at h
  -- `h` reads `2 · (Kˣ : N) · 4 Q² = (4 Q)²` with `Q = q ^ v_K(2) > 0`.
  have hq : 0 < Nat.card 𝓀[K] := Nat.card_pos
  have hQ : 0 < 8 * (Nat.card 𝓀[K] ^ natCastValuation K 2 h2) ^ 2 := by positivity
  refine Nat.eq_of_mul_eq_mul_right hQ ?_
  linear_combination h

/-- **Bimultiplicativity of the local Hilbert symbol in the second argument.** If `2 ≠ 0` in `K`,
then `(a, bc)_K = (a, b)_K (a, c)_K` for every `a`, `b` and `c`. -/
@[simp]
theorem hilbertSymbol_mul_right (h2 : (2 : K) ≠ 0) (a b c : Kˣ) :
    hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  by_cases ha : IsSquare a
  · simp [hilbertSymbol_eq_one_of_isSquare_left ha]
  · exact (hilbertSymbol_mul_iff_quadraticNormSubgroup_index_dvd_two a).mpr
      (quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 ha ▸ dvd_rfl) b c

/-- **Bimultiplicativity of the local Hilbert symbol in the first argument.** If `2 ≠ 0` in `K`,
then `(bc, a)_K = (b, a)_K (c, a)_K` for every `a`, `b` and `c`. -/
@[simp]
theorem hilbertSymbol_mul_left (h2 : (2 : K) ≠ 0) (a b c : Kˣ) :
    hilbertSymbol (b * c) a = hilbertSymbol b a * hilbertSymbol c a := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  -- the first-argument law is the second-argument law read through the symmetry of the symbol
  simp only [hilbertSymbol_comm _ a, hilbertSymbol_mul_right h2]

/-- If `2 ≠ 0` in `K`, then `(a, ab)_K = (a, -b)_K`: the two second arguments differ by the norm
`-a` from `K(√a)`. -/
theorem hilbertSymbol_self_mul (h2 : (2 : K) ≠ 0) (a b : Kˣ) :
    hilbertSymbol a (a * b) = hilbertSymbol a (-b) := by
  rw [← neg_mul_neg, hilbertSymbol_mul_right h2, hilbertSymbol_neg_self, one_mul]

/-- If `2 ≠ 0` in `K`, then `(a, -ab)_K = (a, b)_K`: the two second arguments differ by the norm
`-a` from `K(√a)`. -/
theorem hilbertSymbol_neg_self_mul (h2 : (2 : K) ≠ 0) (a b : Kˣ) :
    hilbertSymbol a (-(a * b)) = hilbertSymbol a b := by
  rw [← mul_neg, hilbertSymbol_self_mul h2, neg_neg]

/-- The Hilbert symbol is multiplicative on integer powers of its second argument. -/
@[simp]
theorem hilbertSymbol_zpow_right (h2 : (2 : K) ≠ 0)
    (a b : Kˣ) (n : ℤ) :
    hilbertSymbol a (b ^ n) = hilbertSymbol a b ^ n := by
  let f : Kˣ →* ℤˣ :=
    { toFun := hilbertSymbol a
      map_one' := hilbertSymbol_one_right a
      map_mul' := hilbertSymbol_mul_right h2 a }
  exact map_zpow f b n

/-- The Hilbert symbol is multiplicative on integer powers of its first argument. -/
@[simp]
theorem hilbertSymbol_zpow_left (h2 : (2 : K) ≠ 0)
    (a b : Kˣ) (n : ℤ) :
    hilbertSymbol (a ^ n) b = hilbertSymbol a b ^ n := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  rw [hilbertSymbol_comm, hilbertSymbol_zpow_right h2, hilbertSymbol_comm]

/-- **Nondegeneracy of the local Hilbert symbol.** If `2 ≠ 0` in `K`, then for every nonsquare `a`
there is a `b ∈ Kˣ` with `(a, b)_K = -1`. It is the field-level consequence
`TauCeti.exists_hilbertSymbol_eq_neg_one_of_index_eq_two` of the norm index theorem. -/
theorem exists_hilbertSymbol_eq_neg_one (h2 : (2 : K) ≠ 0) {a : Kˣ} (ha : ¬IsSquare a) :
    ∃ b : Kˣ, hilbertSymbol a b = -1 :=
  exists_hilbertSymbol_eq_neg_one_of_index_eq_two a
    (quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 ha)

/-! ### Prescribing values of the Hilbert symbol -/

/-- If `2 ≠ 0` in `K`, then for a nonsquare `a` and any `b` with `ab` a nonsquare, some `y ∈ Kˣ`
has `(y, a)_K = -1` and `(y, b)_K = 1`: the character `(·, a)_K` is nontrivial and differs from
`(·, b)_K`. -/
private theorem exists_hilbertSymbol_eq_neg_one_and_eq_one (h2 : (2 : K) ≠ 0) {a b : Kˣ}
    (ha : ¬IsSquare a) (hab : ¬IsSquare (a * b)) :
    ∃ y : Kˣ, hilbertSymbol y a = -1 ∧ hilbertSymbol y b = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨x₁, hx₁⟩ := exists_hilbertSymbol_eq_neg_one h2 ha
  obtain ⟨x₃, hx₃⟩ := exists_hilbertSymbol_eq_neg_one h2 hab
  rw [hilbertSymbol_comm] at hx₁ hx₃
  rw [hilbertSymbol_mul_right h2] at hx₃
  rcases Int.units_eq_one_or (hilbertSymbol x₁ b) with h₁ | h₁
  · exact ⟨x₁, hx₁, h₁⟩
  rcases Int.units_eq_one_or (hilbertSymbol x₃ a) with h₃ | h₃
  · rw [h₃, one_mul] at hx₃
    exact ⟨x₁ * x₃, by rw [hilbertSymbol_mul_left h2, hx₁, h₃, mul_one],
      by rw [hilbertSymbol_mul_left h2, h₁, hx₃]; decide⟩
  · rw [h₃, neg_one_mul, neg_inj] at hx₃
    exact ⟨x₃, h₃, hx₃⟩

/-- **Two distinct nontrivial characters take every pair of values.** If `2 ≠ 0` in `K`, then for
nonsquares `a`, `b` with `ab` a nonsquare, every pair of signs `(s, t)` is `((x, a)_K, (x, b)_K)`
for some `x ∈ Kˣ`. -/
theorem exists_hilbertSymbol_eq_and_hilbertSymbol_eq (h2 : (2 : K) ≠ 0) {a b : Kˣ}
    (ha : ¬IsSquare a) (hb : ¬IsSquare b) (hab : ¬IsSquare (a * b)) (s t : ℤˣ) :
    ∃ x : Kˣ, hilbertSymbol x a = s ∧ hilbertSymbol x b = t := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨y, hya, hyb⟩ := exists_hilbertSymbol_eq_neg_one_and_eq_one h2 ha hab
  obtain ⟨z, hzb, hza⟩ := exists_hilbertSymbol_eq_neg_one_and_eq_one h2 hb (mul_comm a b ▸ hab)
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · exact ⟨1, hilbertSymbol_one_left a, hilbertSymbol_one_left b⟩
  · exact ⟨z, hza, hzb⟩
  · exact ⟨y, hya, hyb⟩
  · exact ⟨y * z, by rw [hilbertSymbol_mul_left h2, hya, hza, mul_one],
      by rw [hilbertSymbol_mul_left h2, hyb, hzb, one_mul]⟩

/-- **The norm group of `K(√a)` contains a nonsquare.** If `2 ≠ 0` in `K`, then for every `a ∈ Kˣ`
there is a nonsquare `b` with `(b, a)_K = 1`: among a uniformizer `π`, the unramified unit `Δ` and
their product, three nonsquares, the symbols with `a` multiply to `1`, so one of them is `1`. -/
theorem exists_not_isSquare_hilbertSymbol_eq_one (h2 : (2 : K) ≠ 0) (a : Kˣ) :
    ∃ b : Kˣ, ¬IsSquare b ∧ hilbertSymbol b a = 1 := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  obtain ⟨Δ, hΔ, hΔv, -⟩ := exists_unramified_class h2
  by_cases hπa : hilbertSymbol π a = 1
  · exact ⟨π, not_isSquare_of_isUniformizer hπ, hπa⟩
  by_cases hΔa : hilbertSymbol Δ a = 1
  · exact ⟨Δ, hΔ, hΔa⟩
  refine ⟨π * Δ,
    not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation hπ (hΔv ▸ Even.zero), ?_⟩
  rw [hilbertSymbol_mul_left h2, Int.units_ne_iff_eq_neg.mp hπa, Int.units_ne_iff_eq_neg.mp hΔa]
  decide

end TauCeti

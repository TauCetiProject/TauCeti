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

The diagonal entry `(a, a)_K = (a, -1)_K` needs no arithmetic input and is stated for an arbitrary
field in `TauCeti.NumberTheory.HilbertSymbol.NormSubgroup`, as
`TauCeti.hilbertSymbol_self`.

## Main results

* `TauCeti.quadraticNormSubgroup_index_eq_two_of_not_isSquare`: the norm index of every nonsquare
  radicand.
* `TauCeti.hilbertSymbol_mul_right` and `TauCeti.hilbertSymbol_mul_left`: the Hilbert symbol is
  bilinear in both arguments.
* `TauCeti.exists_hilbertSymbol_eq_neg_one`: for every nonsquare `a` there is a `b` with
  `(a, b)_K = -1`.

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

end TauCeti

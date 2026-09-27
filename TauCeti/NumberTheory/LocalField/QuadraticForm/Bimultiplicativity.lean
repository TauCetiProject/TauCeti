/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.EvenValuation
public import TauCeti.NumberTheory.LocalField.QuadraticForm.OddValuation

import TauCeti.NumberTheory.LocalField.NatCastValuation

/-!
# The index theorem for quadratic norms, and bimultiplicativity of the local Hilbert symbol

Let `K` be a nonarchimedean local field whose residue characteristic is odd, that is with `2` a
unit of `𝒪[K]`. The norms from `K(√a)`, that is the subgroup of `Kˣ` consisting of the `b` of the
form `x² - a y²` with `x, y ∈ K`, form a subgroup of index two in `Kˣ` for every nonsquare radicand
`a`. A radicand of odd valuation is handled in
`TauCeti.NumberTheory.LocalField.QuadraticForm.OddValuation`, where the index is forced by the four
square classes, and a radicand of even valuation, which is square-equivalent to a unit of valuation
zero, in `TauCeti.NumberTheory.LocalField.QuadraticForm.EvenValuation`, where it is the unramified
class up to a square and so has the same norms, namely the elements of even normalized valuation.

The sign indicator of an index-two subgroup is a character, so the local Hilbert symbol is
bimultiplicative in both arguments. The same index theorem gives nondegeneracy, and there that step
is purely group-theoretic: the sign indicator of a proper subgroup of index two is onto, so it takes
the value `-1` off the subgroup. The field-level statement is
`TauCeti.exists_hilbertSymbol_eq_neg_one_of_index_eq_two`, which asks only that the norm subgroup of
`a` have index two, so the theorem here needs no case split on the valuation of `a`.

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
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 2.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The norm index of a nonsquare radicand.** Away from residue characteristic two, the norms
from `K(√a)` form a subgroup of index two in `Kˣ` for every `a` that is not a square. -/
theorem quadraticNormSubgroup_index_eq_two_of_not_isSquare (h2 : IsUnit (2 : 𝒪[K])) {a : Kˣ}
    (ha : ¬IsSquare a) : (quadraticNormSubgroup (a : K)).index = 2 := by
  by_cases hev : Even (normalizedValuation K a).toAdd
  · exact quadraticNormSubgroup_index_eq_two_of_even h2 hev ha
  · exact quadraticNormSubgroup_index_eq_two_of_odd h2 (Int.not_even_iff_odd.mp hev)

/-- **Bimultiplicativity of the local Hilbert symbol in the second argument.** Away from residue
characteristic two, `(a, bc)_K = (a, b)_K (a, c)_K` for every `a`, `b` and `c`. -/
@[simp]
theorem hilbertSymbol_mul_right (h2 : IsUnit (2 : 𝒪[K])) (a b c : Kˣ) :
    hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  by_cases ha : IsSquare a
  · simp [hilbertSymbol_eq_one_of_isSquare_left ha]
  · exact (hilbertSymbol_mul_iff_quadraticNormSubgroup_index_dvd_two a).mpr
      (quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 ha ▸ dvd_rfl) b c

/-- **Bimultiplicativity of the local Hilbert symbol in the first argument.** Away from residue
characteristic two, `(bc, a)_K = (b, a)_K (c, a)_K` for every `a`, `b` and `c`. -/
@[simp]
theorem hilbertSymbol_mul_left (h2 : IsUnit (2 : 𝒪[K])) (a b c : Kˣ) :
    hilbertSymbol (b * c) a = hilbertSymbol b a * hilbertSymbol c a := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  -- the first-argument law is the second-argument law read through the symmetry of the symbol
  simp only [hilbertSymbol_comm _ a, hilbertSymbol_mul_right h2]

/-- **Nondegeneracy of the local Hilbert symbol.** Away from residue characteristic two, for every
nonsquare `a` there is a `b ∈ Kˣ` with `(a, b)_K = -1`. It is the field-level consequence of
the norm index theorem, `TauCeti.exists_hilbertSymbol_eq_neg_one_of_index_eq_two`, and so needs
no case split on the valuation of `a`. -/
theorem exists_hilbertSymbol_eq_neg_one (h2 : IsUnit (2 : 𝒪[K])) {a : Kˣ} (ha : ¬IsSquare a) :
    ∃ b : Kˣ, hilbertSymbol a b = -1 :=
  exists_hilbertSymbol_eq_neg_one_of_index_eq_two a
    (quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 ha)

end TauCeti

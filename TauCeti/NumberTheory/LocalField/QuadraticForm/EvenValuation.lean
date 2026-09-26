/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.NormIndex

import TauCeti.NumberTheory.LocalField.NatCastValuation
import TauCeti.NumberTheory.LocalField.SquareClass

/-!
# Quadratic norms for a radicand of even valuation

Let `K` be a nonarchimedean local field whose residue characteristic is odd, that is with `2` a
unit of `𝒪[K]`, and let `a ∈ Kˣ`. The norms from `K(√a)`, that is the subgroup of `Kˣ` consisting
of the `b` of the form `x² - a y²` with `x, y ∈ K`, have index two in `Kˣ` as soon as `a` is not a
square.

`TauCeti.quadraticNormSubgroup_index_eq_two_of_odd` treats the radicands of odd valuation. This
file treats the radicands of even valuation, which are square-equivalent to a unit of valuation
zero, and it is the last case of the index theorem away from residue characteristic two. The
square-class group has four elements away from residue characteristic two: the two classes of odd
valuation are represented by a uniformizer, and the two classes of even valuation are represented
by `1` and by the unramified class. A nonsquare radicand of even valuation is therefore the
unramified class up to a square, and it has the same norms, namely the elements of even normalized
valuation.

Together with the odd valuation case this gives the index theorem in full, in
`TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity`, where it is also used to show
that the local Hilbert symbol is bimultiplicative and nondegenerate.

## Main results

* `TauCeti.exists_unramified_class_isSquare_mul_of_even_of_not_isSquare`: a nonsquare radicand of
  even valuation is the unramified class up to a square.
* `TauCeti.quadraticNormSubgroup_index_eq_two_of_even`: the norm index of a radicand of even
  valuation.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 2.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The unramified class in the square class of an even-valuation radicand.** Away from residue
characteristic two, if `v_K(a)` is even and `a` is not a square, there is a class `Δ` of valuation
zero, the unramified class, such that `a` and `Δ` differ by a square and the elements of even
normalized valuation are exactly the norms from `K(√Δ)`. -/
theorem exists_unramified_class_isSquare_mul_of_even_of_not_isSquare (h2 : IsUnit (2 : 𝒪[K]))
    {a : Kˣ} (ha : Even (normalizedValuation K a).toAdd) (ha' : ¬IsSquare a) :
    ∃ Δ : Kˣ, (normalizedValuation K Δ).toAdd = 0 ∧ IsSquare (a * Δ) ∧
      ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
        Even (normalizedValuation K b).toAdd := by
  obtain ⟨Δ, hΔ', hΔ0, hΔ⟩ := exists_unramified_class (two_ne_zero_of_isUnit_two h2)
  have hΔeven : Even (normalizedValuation K Δ).toAdd := by rw [hΔ0]; exact ⟨0, by simp⟩
  obtain hsq | hsq := isSquare_or_isSquare_mul_of_isUnit_two h2 hΔeven hΔ' ha
  · exact absurd hsq ha'
  exact ⟨Δ, hΔ0, hsq, hΔ⟩

/-- **The norm index for a radicand of even valuation.** Away from residue characteristic two, if
`v_K(a)` is even and `a` is not a square, the norms from `K(√a)` form a subgroup of index two. The
radicand is the unramified class up to a square, and it therefore has the same norm subgroup. -/
theorem quadraticNormSubgroup_index_eq_two_of_even (h2 : IsUnit (2 : 𝒪[K])) {a : Kˣ}
    (ha : Even (normalizedValuation K a).toAdd) (ha' : ¬IsSquare a) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  obtain ⟨Δ, -, hsq, hΔ⟩ := exists_unramified_class_isSquare_mul_of_even_of_not_isSquare h2 ha ha'
  rw [quadraticNormSubgroup_eq_of_isSquare_mul hsq]
  exact quadraticNormSubgroup_index_eq_two_of_unramified_class hΔ

end TauCeti

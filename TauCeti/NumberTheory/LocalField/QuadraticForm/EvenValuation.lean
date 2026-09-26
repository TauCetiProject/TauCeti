/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.NormIndex
public import TauCeti.NumberTheory.LocalField.QuadraticForm.OddValuation

import TauCeti.NumberTheory.LocalField.NatCastValuation
import TauCeti.NumberTheory.LocalField.SquareClass

/-!
# Quadratic norms for a radicand of even valuation, and the local Hilbert symbol

Let `K` be a nonarchimedean local field whose residue characteristic is odd, that is with `2` a
unit of `𝒪[K]`, and let `a ∈ Kˣ`. The norms from `K(√a)`, that is the subgroup of `Kˣ` consisting
of the `b` of the form `x² - a y²` with `x y ∈ K`, have index two in `Kˣ` as soon as `a` is not a
square.

`TauCeti.quadraticNormSubgroup_index_eq_two_of_odd` treats the radicands of odd valuation. This
file treats the radicands of even valuation, which are the units, and it is the last case of the
index theorem away from residue characteristic two. Such a radicand is, up to a square, the
unramified class: the square-class group has four elements away from residue
characteristic two, the two classes of odd valuation are represented by a uniformizer, and the two
classes of even valuation are represented by `1` and by the unramified class. A nonsquare
radicand of even valuation is therefore the unramified class up to a square, and it has the same
norms, namely the elements of even normalized valuation.

Together with the odd valuation case this gives the index theorem in full, and the sign indicator
of an index-two subgroup is a homomorphism, so the local Hilbert symbol is bimultiplicative in
both arguments. Nondegeneracy reads off the same index theorem: a radicand of odd valuation is
separated by the unramified class, and a radicand of even valuation by a uniformizer, because a
unit is a norm of the unramified class.

## Main results

* `TauCeti.quadraticNormSubgroup_index_eq_two_of_even`: the norm index of a radicand of even
  valuation.
* `TauCeti.quadraticNormSubgroup_index_eq_two_of_not_isSquare`: the norm index of every nonsquare
  radicand.
* `TauCeti.hilbertSymbol_mul_right` and `TauCeti.hilbertSymbol_mul_left`: the Hilbert symbol is
  bilinear in both arguments.
* `TauCeti.hilbertSymbol_self`: the diagonal entry, `(π, π)_K = (π, -1)_K`.
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

section NormSubgroup

variable {K : Type*} [Field K]

/-- The quadratic norm subgroup of a radicand and of a square multiple of it coincide: the symbol
depends only on the square class of the radicand. This is the square-class form of
`TauCeti.quadraticNormSubgroup_mul_sq`, read through the description of the subgroup as the set
where the symbol is positive. -/
private theorem quadraticNormSubgroup_eq_of_isSquare_mul {a Δ : Kˣ} (h : IsSquare (a * Δ)) :
    quadraticNormSubgroup (a : K) = quadraticNormSubgroup (Δ : K) := by
  ext b
  calc b ∈ quadraticNormSubgroup (a : K)
      ↔ hilbertSymbol a b = 1 := (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).symm
    _ ↔ hilbertSymbol Δ b = 1 := by rw [hilbertSymbol_congr_sq a Δ b b h ⟨b, rfl⟩]
    _ ↔ b ∈ quadraticNormSubgroup (Δ : K) := hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup Δ b

end NormSubgroup

/-- **The unramified class in the square class of an even-valuation radicand.** Away from residue
characteristic two, if `v_K(a)` is even and `a` is not a square, there is a class `Δ` of valuation
zero, the unramified class, such that `a` and `Δ` differ by a square and the elements of even
normalized valuation are exactly the norms from `K(√Δ)`. -/
private theorem exists_unramifiedClass_mul_sq_of_even_of_not_isSquare (h2 : IsUnit (2 : 𝒪[K]))
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
  obtain ⟨Δ, -, hsq, hΔ⟩ := exists_unramifiedClass_mul_sq_of_even_of_not_isSquare h2 ha ha'
  rw [quadraticNormSubgroup_eq_of_isSquare_mul hsq]
  exact quadraticNormSubgroup_index_eq_two_of_unramified_class hΔ

/-- **The norm index of a nonsquare radicand.** Away from residue characteristic two, the norms
from `K(√a)` form a subgroup of index two in `Kˣ` for every `a` that is not a square. -/
theorem quadraticNormSubgroup_index_eq_two_of_not_isSquare (h2 : IsUnit (2 : 𝒪[K])) {a : Kˣ}
    (ha : ¬IsSquare a) : (quadraticNormSubgroup (a : K)).index = 2 := by
  by_cases hev : Even (normalizedValuation K a).toAdd
  · exact quadraticNormSubgroup_index_eq_two_of_even h2 hev ha
  · exact quadraticNormSubgroup_index_eq_two_of_odd h2 (Int.not_even_iff_odd.mp hev)

/-- **Bimultiplicativity of the local Hilbert symbol in the second argument.** Away from residue
characteristic two, `(a, bc)_K = (a, b)_K (a, c)_K` for every `a`, `b` and `c`. -/
theorem hilbertSymbol_mul_right (h2 : IsUnit (2 : 𝒪[K])) (a b c : Kˣ) :
    hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  by_cases ha : IsSquare a
  · simp [hilbertSymbol_eq_one_of_isSquare_left ha]
  · exact (hilbertSymbol_mul_iff_quadraticNormSubgroup_index_dvd_two a).mpr
      (quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 ha ▸ dvd_rfl) b c

/-- **Bimultiplicativity of the local Hilbert symbol in the first argument.** Away from residue
characteristic two, `(bc, a)_K = (b, a)_K (c, a)_K` for every `a`, `b` and `c`, by symmetry. -/
theorem hilbertSymbol_mul_left (h2 : IsUnit (2 : 𝒪[K])) (a b c : Kˣ) :
    hilbertSymbol (b * c) a = hilbertSymbol b a * hilbertSymbol c a := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  simp only [hilbertSymbol_comm _ a, hilbertSymbol_mul_right h2]

/-- **The diagonal of the local Hilbert symbol.** Away from residue characteristic two,
`(π, π)_K = (π, -1)_K` for every `π`, because `(a, -a)_K = 1` and the symbol is bilinear in the
first argument. The value of `(π, π)_K` is therefore not a separate convention. -/
theorem hilbertSymbol_self (h2 : IsUnit (2 : 𝒪[K])) (π : Kˣ) :
    hilbertSymbol π π = hilbertSymbol π (-1) := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  have hneg : hilbertSymbol (-π) π = 1 := by
    rw [hilbertSymbol_comm, hilbertSymbol_neg_self]
  have hπ : (-π : Kˣ) * (-1) = π := by
    ext
    push_cast
    ring
  calc hilbertSymbol π π = hilbertSymbol ((-π : Kˣ) * (-1)) π := by rw [hπ]
    _ = hilbertSymbol (-π) π * hilbertSymbol (-1) π := hilbertSymbol_mul_left h2 π (-π) (-1)
    _ = hilbertSymbol (-1) π := by rw [hneg, one_mul]
    _ = hilbertSymbol π (-1) := hilbertSymbol_comm _ _

/-- **Nondegeneracy of the local Hilbert symbol.** Away from residue characteristic two, for every
nonsquare `a` there is a unit `b` with `(a, b)_K = -1`. A radicand of odd valuation is separated
by the unramified class, and a radicand of even valuation by a uniformizer. -/
theorem exists_hilbertSymbol_eq_neg_one (h2 : IsUnit (2 : 𝒪[K])) {a : Kˣ} (ha : ¬IsSquare a) :
    ∃ b : Kˣ, hilbertSymbol a b = -1 := by
  by_cases hev : Even (normalizedValuation K a).toAdd
  · obtain ⟨Δ, -, hsq, hΔ⟩ := exists_unramifiedClass_mul_sq_of_even_of_not_isSquare h2 hev ha
    obtain ⟨π, hπ⟩ := exists_isUniformizer K
    refine ⟨π, (hilbertSymbol_congr_sq a Δ π π hsq ⟨π, rfl⟩).trans ?_⟩
    rw [hilbertSymbol_unramified hΔ π, (isUniformizer_def π).mp hπ, toAdd_ofAdd]
    simp only [Int.not_even_one, ↓reduceIte]
  · obtain ⟨b, -, hb⟩ := exists_hilbertSymbol_eq_neg_one_of_odd
      (two_ne_zero_of_isUnit_two h2) (Int.not_even_iff_odd.mp hev)
    exact ⟨b, hb⟩

end TauCeti

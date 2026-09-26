/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.NormalizedValuation

import TauCeti.NumberTheory.LocalField.NatCastValuation
import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass
import TauCeti.NumberTheory.LocalField.SquareClass

/-!
# Quadratic norms for a radicand of odd valuation

Let `K` be a nonarchimedean local field with `2 ≠ 0`, and let `a ∈ Kˣ` have odd normalized
valuation `v_K(a)`, so that `K(√a)/K` is ramified. This file shows that the norm subgroup
`N(K(√a)ˣ) = {x² - a y²} ≤ Kˣ` is proper in every residue characteristic, and that it has index two,
so that the Hilbert symbol `(a, ·)_K` is a character, away from residue characteristic two.

The lower bound holds in every residue characteristic. If `Δ` is the unramified class, whose norms
are exactly the elements of even valuation (`TauCeti.exists_unramified_class`), then
`(Δ, a)_K = (-1)^{v_K(a)} = -1`, and by symmetry `(a, Δ)_K = -1`. So `Δ`, a unit, is not a norm
from `K(√a)`, and the Hilbert symbol with an odd-valuation first argument is nondegenerate.

The upper bound is proved away from residue characteristic two. The norm subgroup contains the
squares and the norm `-a` of `√a`. Since `-a` has odd valuation it is not a square, so the norm
subgroup has index strictly smaller than `#(Kˣ ⧸ (Kˣ)²) = 4`. Together with the lower bound this
forces the index to be `2`, and the sign indicator of an index-two subgroup is multiplicative.

## Main results

* `TauCeti.hilbertSymbol_eq_neg_one_of_unramified_class_of_odd`: `(a, Δ)_K = -1` for the
  unramified class `Δ`.
* `TauCeti.exists_hilbertSymbol_eq_neg_one_of_odd`: there is a unit `b` with `(a, b)_K = -1`.
* `TauCeti.quadraticNormSubgroup_index_eq_two_of_odd`: away from residue characteristic two the
  norms from `K(√a)` form a subgroup of index two.
* `TauCeti.hilbertSymbol_mul_right_of_odd` and `TauCeti.hilbertSymbol_mul_left_of_odd`: away from
  residue characteristic two, the Hilbert symbol is multiplicative in the argument not equal to
  `a`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **An odd-valuation radicand against the unramified class.** If `v_K(a)` is odd and the norms
from `K(√Δ)` are exactly the elements of even valuation, as for the class of
`TauCeti.exists_unramified_class`, then `(a, Δ)_K = -1`. -/
theorem hilbertSymbol_eq_neg_one_of_unramified_class_of_odd (h2 : (2 : K) ≠ 0) {a Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd)
    (ha : Odd (normalizedValuation K a).toAdd) :
    hilbertSymbol a Δ = -1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  rw [hilbertSymbol_comm, hilbertSymbol_unramified hΔ]
  simp only [Int.not_even_iff_odd.mpr ha, ↓reduceIte]

/-- **Nondegeneracy for a radicand of odd valuation.** If `v_K(a)` is odd, there is `b ∈ Kˣ` of
valuation zero with `(a, b)_K = -1`, namely the unramified class. -/
theorem exists_hilbertSymbol_eq_neg_one_of_odd (h2 : (2 : K) ≠ 0) {a : Kˣ}
    (ha : Odd (normalizedValuation K a).toAdd) :
    ∃ b : Kˣ, (normalizedValuation K b).toAdd = 0 ∧ hilbertSymbol a b = -1 := by
  obtain ⟨Δ, -, hΔ0, hΔ⟩ := exists_unramified_class h2
  exact ⟨Δ, hΔ0, hilbertSymbol_eq_neg_one_of_unramified_class_of_odd h2 hΔ ha⟩

/-- **The norm index for a radicand of odd valuation.** Away from residue characteristic two, if
`v_K(a)` is odd then the norms from `K(√a)` form a subgroup of index two in `Kˣ`. -/
theorem quadraticNormSubgroup_index_eq_two_of_odd (h2 : IsUnit (2 : 𝒪[K])) {a : Kˣ}
    (ha : Odd (normalizedValuation K a).toAdd) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  have hsq : (Subgroup.square Kˣ).index = 4 := by
    rw [Subgroup.index_eq_card]
    exact card_squareClass_of_odd h2
  have : (Subgroup.square Kˣ).FiniteIndex := ⟨by omega⟩
  -- `-a` is a norm of odd valuation, hence not a square: the index is below `4`.
  have hneg : ¬IsSquare (-a) := fun h ↦ by
    have := even_toAdd_normalizedValuation_of_isSquare h
    rw [normalizedValuation_neg] at this
    exact Int.not_even_iff_odd.mpr ha this
  have hlt := quadraticNormSubgroup_index_lt_square_index a hneg
  have hdvd := quadraticNormSubgroup_index_dvd_square_index (a : K)
  -- The unramified class is not a norm: the index is not `1`.
  have hne : (quadraticNormSubgroup (a : K)).index ≠ 1 := by
    obtain ⟨b, -, hb⟩ := exists_hilbertSymbol_eq_neg_one_of_odd (two_ne_zero_of_isUnit_two h2) ha
    rw [Ne, Subgroup.index_eq_one, Subgroup.eq_top_iff']
    exact fun h ↦ by
      simpa [hb] using (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mpr (h b)
  rw [hsq] at hlt hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : (quadraticNormSubgroup (a : K)).index <;> simp_all

/-- Away from residue characteristic two, the Hilbert symbol `(a, ·)_K` is multiplicative when
`v_K(a)` is odd. -/
theorem hilbertSymbol_mul_right_of_odd (h2 : IsUnit (2 : 𝒪[K])) {a : Kˣ}
    (ha : Odd (normalizedValuation K a).toAdd) (b c : Kˣ) :
    hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c :=
  (hilbertSymbol_mul_iff_quadraticNormSubgroup_index_dvd_two a).mpr
    (quadraticNormSubgroup_index_eq_two_of_odd h2 ha ▸ dvd_rfl) b c

/-- Away from residue characteristic two, the Hilbert symbol `(·, a)_K` is multiplicative when
`v_K(a)` is odd. -/
theorem hilbertSymbol_mul_left_of_odd (h2 : IsUnit (2 : 𝒪[K])) {a : Kˣ}
    (ha : Odd (normalizedValuation K a).toAdd) (b c : Kˣ) :
    hilbertSymbol (b * c) a = hilbertSymbol b a * hilbertSymbol c a := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  simp only [hilbertSymbol_comm _ a, hilbertSymbol_mul_right_of_odd h2 ha]

end TauCeti

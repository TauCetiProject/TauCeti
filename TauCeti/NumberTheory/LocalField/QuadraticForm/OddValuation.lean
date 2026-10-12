/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.NormalizedValuation

import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass

/-!
# Quadratic norms for a radicand of odd valuation

Let `K` be a nonarchimedean local field with `2 ≠ 0`, and let `a ∈ Kˣ` have odd normalized
valuation `v_K(a)`, so that `K(√a)/K` is ramified. This file exhibits an explicit non-norm from
`K(√a)`, in every residue characteristic. If `Δ` is the unramified class, whose norms are exactly
the elements of even valuation (`TauCeti.exists_unramified_class`), then
`(Δ, a)_K = (-1)^{v_K(a)} = -1`, and by symmetry `(a, Δ)_K = -1`. So `Δ`, a unit, is not a norm
from `K(√a)`. This is the explicit witness for the nondegeneracy of the Hilbert symbol at a radicand
of odd valuation.

## Main results

* `TauCeti.hilbertSymbol_eq_neg_one_of_unramified_class_of_odd`: `(a, Δ)_K = -1` for the
  unramified class `Δ`.
* `TauCeti.exists_hilbertSymbol_eq_neg_one_of_odd`: there is a `b ∈ Kˣ` of valuation zero, the
  unramified class, with `(a, b)_K = -1`.

The index theorem for every nonsquare radicand, and the resulting bimultiplicativity of the Hilbert
symbol, are in `TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity`.

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

end TauCeti

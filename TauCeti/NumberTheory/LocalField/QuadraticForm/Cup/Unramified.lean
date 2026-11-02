/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Cup.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass

/-!
# The Kummer cup of `2` and the unramified class

Let `K` be a nonarchimedean local field in which `2` is invertible, and let `Δ ∈ Kˣ` be the
unramified quadratic class (`TauCeti.exists_unramified_class`). The Hilbert symbol
`(2, Δ)_K = (-1)^{v_K(2)}` (`TauCeti.hilbertSymbol_two_unramified`) determines the Kummer cup
`(2) ∪ (Δ) ∈ H²(G_K, 𝔽₂)`. Over a finite extension of `ℚ₂`, where `v_K(2)` is the absolute
ramification index, this cup is nonzero exactly when that index is odd.

## Main results

* `TauCeti.cup_kummerClass_two_unramified_ne_zero_iff`: over a finite extension of `ℚ₂`,
  `(2) ∪ (Δ) ≠ 0` exactly when the absolute ramification index is odd.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), XIV §2, Proposition 5.
-/

public section

universe u

namespace TauCeti

open _root_.ContinuousCohomology

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- Over a finite extension of `ℚ₂`, the class `(2) ∪ (Δ)` of the unramified class `Δ` is nonzero
exactly when the absolute ramification index is odd. -/
theorem cup_kummerClass_two_unramified_ne_zero_iff [Fact (Nat.Prime 2)]
    [FinitePadicExtension K 2] {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass (unitOfInvertible (2 : K))) (kummerClass Δ) ≠ 0 ↔
      Odd (absoluteRamificationIndex K 2) := by
  rw [Ne, cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one, hilbertSymbol_two_unramified hΔ,
    dyadicLevel_def, ← absoluteRamificationIndex_eq_natCastValuation,
    neg_one_pow_eq_one_iff_even (by decide), Nat.not_even_iff_odd]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Algebra.Category.ModuleCat.Filtration.Complete

/-!
# Check: the `ℓ`-adic filtration of `ℤ_ℓ` is complete

The `ℓ`-adic filtration `adicFiltration (Ideal.span {ℓ}) ℤ_[ℓ]`, with `F^p = ℓ^p ℤ_ℓ` (`p ≥ 0`,
and `ℤ_ℓ` for `p ≤ 0`), of the `ℓ`-adic integers is complete
(`isComplete_adicFiltration_padicInt`): the ideal `(ℓ)` is the maximal ideal of `ℤ_[ℓ]`
(`PadicInt.maximalIdeal_eq_span_p`), for which Mathlib's `ℤ_[ℓ]` is adically complete. The same
filtration `adicFiltration (Ideal.span {ℓ}) ℤ` of `ℤ` is exhaustive and separated but not complete
(`TauCeti.Examples.DecreasingFiltration.not_isComplete_adicFiltration`).
-/

public section

open CategoryTheory

namespace TauCeti.Examples.PadicIntFiltration

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The `ℓ`-adic filtration of `ℤ_ℓ` is complete.** -/
theorem isComplete_adicFiltration_padicInt :
    (FilteredObject.adicFiltration (Ideal.span {(ℓ : ℤ_[ℓ])}) ℤ_[ℓ]).IsComplete := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  exact FilteredObject.isComplete_adicFiltration _ _

end TauCeti.Examples.PadicIntFiltration

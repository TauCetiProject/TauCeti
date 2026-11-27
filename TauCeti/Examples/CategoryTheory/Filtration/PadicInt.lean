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

The `ℓ`-adic filtration `F^p = ℓ^p ℤ_ℓ` (`p ≥ 0`, and `ℤ_ℓ` for `p ≤ 0`) of the `ℓ`-adic
integers is complete (`isComplete_adicFiltration_padicInt`), as Mathlib's `ℤ_[ℓ]` is complete for
its maximal ideal `(ℓ)`. The same filtration of `ℤ` is exhaustive and separated but not complete
(`TauCeti.Examples.DecreasingFiltration.not_isComplete_adicFiltration`).
-/

public section

open CategoryTheory IsLocalRing

namespace TauCeti.Examples.PadicIntFiltration

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The step `F^n = 𝔪^n • ℤ_ℓ` of the adic filtration of `ℤ_ℓ` by its maximal ideal `𝔪` is
`ℓ^n ℤ_ℓ`. -/
theorem maximalIdeal_pow_smul_top (n : ℕ) :
    (maximalIdeal ℤ_[ℓ]) ^ n • (⊤ : Submodule ℤ_[ℓ] ℤ_[ℓ]) = Ideal.span {(ℓ : ℤ_[ℓ]) ^ n} := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]

/-- **The `ℓ`-adic filtration of `ℤ_ℓ` is complete.** -/
theorem isComplete_adicFiltration_padicInt :
    (FilteredObject.adicFiltration (maximalIdeal ℤ_[ℓ]) ℤ_[ℓ]).IsComplete :=
  FilteredObject.isComplete_adicFiltration _ _

end TauCeti.Examples.PadicIntFiltration

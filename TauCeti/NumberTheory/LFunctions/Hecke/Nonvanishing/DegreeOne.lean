/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing.DegreeOne

/-!
# Degree-one boundary nonvanishing for cancellation-continued ray class L-functions

For a ray class character `χ` of any modulus `𝔪` over a number field `K`,
`RayClassCharacter.continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero` already gives
nonvanishing of `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` on `Re s ≥ 1` away from
`χ ^ 2 = 1 ∧ s = 1` when `χ ≠ 1`.

When `Module.finrank ℚ K = 1` at the exceptional point `χ ^ 2 = 1 ∧ s = 1`, Landau's theorem
(`TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one`) closes the
remaining point, yielding
`RayClassCharacter.continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re`.

## Main results

* `RayClassCharacter.continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re`:
  nonvanishing on `Re s ≥ 1` for `continuedLFunctionOfWeight χ.toUnitaryIdealWeight`, requiring
  `χ ≠ 1` on `s.re = 1` and `[K : ℚ] = 1` only when `χ ^ 2 = 1 ∧ s = 1`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section

open NumberField TauCeti TauCeti.LFunctions

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Nonvanishing on `Re s ≥ 1` of the cancellation-continued ray class L-function.**
For any ray class character `χ` of any modulus `𝔪`,
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0` for every `s` with `1 ≤ s.re` provided
`χ ≠ 1` on `Re s = 1`, requiring `[K : ℚ] = 1` only in the exceptional case `χ ^ 2 = 1 ∧ s = 1`
(via Landau's theorem). On `Re s > 1`, nonvanishing holds for every `χ` (including `χ = 1`) via
the Euler product. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re
    {χ : RayClassCharacter 𝔪} {s : ℂ} (hχ : s.re = 1 → χ ≠ 1)
    (hK : χ ^ 2 = 1 → s = 1 → Module.finrank ℚ K = 1) (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re _ hsgt
  · have hχne : χ ≠ 1 := hχ hseq.symm
    by_cases hsq : χ ^ 2 = 1
    · have htriv : (χ.toUnitaryIdealWeight ^ 2).val.IsTrivialOnGood := by
        rw [UnitaryIdealWeight.val_pow, val_toUnitaryIdealWeight]
        exact χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hsq
      exact continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one
        htriv hs (fun hre ↦ hasCancellation_toUnitaryIdealWeight (hχ hre)) (hK hsq)
    · exact continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero hχne hs (.inl hsq)

end TauCeti.GlobalNumberFields.RayClassCharacter

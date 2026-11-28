/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Rat.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic

/-!
# Boundary nonvanishing for presented Hecke L-functions over `ℚ`

Using the identification `TauCeti.LFunctions.heckeLFunctionC_eq_toMeromorphicNFOn_LFunction_rat`
from `TauCeti.NumberTheory.LFunctions.Hecke.Rat.Basic` together with Mathlib's
`DirichletCharacter.LFunction_ne_zero_of_one_le_re`, this file establishes unconditional
nonvanishing and meromorphic order zero on `Re s ≥ 1` for `heckeLFunctionC χ` over `ℚ` whenever
`χ ≠ 1 ∨ s ≠ 1` (excluding the pole of the principal character `χ = 1` at `s = 1`).

## Main results

* `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_rat` and
  `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_rat`: unconditional
  nonvanishing and meromorphic order zero on `Re s ≥ 1` whenever `χ ≠ 1 ∨ s ≠ 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* Nonvanishing on `Re s ≥ 1` comes from `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao).
-/

public section

open Filter NumberField Set
open scoped NumberField Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

/-- **Unconditional nonvanishing on `Re s ≥ 1` over `ℚ`.** For any modulus `𝔪` of `ℚ`, any ray
class character `χ`, and any `s` with `1 ≤ s.re` such that `χ ≠ 1 ∨ s ≠ 1`,
`heckeLFunctionC χ s ≠ 0`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) : heckeLFunctionC χ s ≠ 0 := by
  have hψs : χ.toDirichletCharacter ≠ 1 ∨ s ≠ 1 :=
    h.imp_left RayClassCharacter.toDirichletCharacter_eq_one_iff.not.mpr
  rw [heckeLFunctionC_eq_toMeromorphicNFOn_LFunction_rat χ,
    toMeromorphicNFOn_apply_of_analyticAt χ.toDirichletCharacter.meromorphic_LFunction
      (χ.toDirichletCharacter.analyticAt_LFunction hψs.symm)]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ hψs hs

/-- **Meromorphic order zero on `Re s ≥ 1` over `ℚ`.** For any modulus `𝔪` of `ℚ`, any ray class
character `χ`, and any `s` with `1 ≤ s.re` such that `χ ≠ 1 ∨ s ≠ 1` (excluding the pole of the
principal character `χ = 1` at `s = 1`), `meromorphicOrderAt (heckeLFunctionC χ) s = 0`. -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_rat {𝔪 : Modulus ℚ}
    {χ : RayClassCharacter 𝔪} {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 :=
  ((meromorphicNFOn_heckeLFunctionC χ) (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr
    (heckeLFunctionC_ne_zero_of_one_le_re_rat h hs)

end TauCeti.LFunctions

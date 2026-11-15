/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.FLT.Basic

/-!
# Asymptotic Fermat

**Asymptotic Fermat** is the statement that Fermat's Last Theorem holds for every sufficiently
large exponent: there is an `N` such that `aⁿ + bⁿ = cⁿ` has no solution in positive integers for
any `n ≥ N`. It is the form of Fermat's Last Theorem that conjectural bounds of Szpiro or abc type
yield through the Frey curve, with an `N` that depends on the unknown constant of the conjecture.
It says nothing about any particular exponent.

## Main definitions

* `TauCeti.AsymptoticFermat`: Fermat's Last Theorem holds for every sufficiently large exponent.

## Main results

* `FermatLastTheorem.asymptoticFermat`: Fermat's Last Theorem implies asymptotic Fermat.

## References

* J. Oesterlé, *Nouvelles approches du « théorème » de Fermat*, Séminaire Bourbaki, exposé 694
  (1988), Astérisque 161–162, 165–186.
-/

public section

namespace TauCeti

/-- **Asymptotic Fermat**: Fermat's Last Theorem holds for every sufficiently large exponent, that
is, there is an `N` such that `aⁿ + bⁿ = cⁿ` has no solution in positive integers for any
`n ≥ N`. -/
def AsymptoticFermat : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, FermatLastTheoremFor n

/-- The defining characterization of `TauCeti.AsymptoticFermat`. This is the interface to it
outside its defining module. -/
theorem asymptoticFermat_iff : AsymptoticFermat ↔ ∃ N : ℕ, ∀ n ≥ N, FermatLastTheoremFor n :=
  Iff.rfl

/-- Fermat's Last Theorem implies asymptotic Fermat, with `N = 3`. -/
theorem _root_.FermatLastTheorem.asymptoticFermat (h : FermatLastTheorem) : AsymptoticFermat :=
  ⟨3, h⟩

end TauCeti

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.JacobiTrudi

/-!
# The Schur function `s_{(2, 1)}` under Jacobi--Trudi and `ω`

Checks of `TauCeti.SymmetricFunction.of_stableSchur_singletonSecondRow_eq_hsymm`,
`TauCeti.SymmetricFunction.of_stableSchur_conjugate_singletonSecondRow_eq_esymm`, and
`TauCeti.SymmetricFunction.omega_of_stableSchur` on the self-conjugate partition
`(2, 1) = TauCeti.Nat.Partition.singletonSecondRow 1` over a commutative ring `R`:

* `s_{(2, 1)} = h₂ h₁ - h₃` and `s_{(2, 1)} = e₂ e₁ - e₃` in `Λ_R`;
* `ω(s_{(2, 1)}) = s_{(2, 1)}`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, (3.4), (3.5), and (3.8).
-/

public section

namespace TauCeti.Examples

open DirectSum TauCeti.SymmetricFunction
open TauCeti.Nat.Partition (conjugate_singletonSecondRow_one singletonSecondRow)

variable (R : Type*) [CommRing R]

/-- The Jacobi--Trudi expansion of `s_{(2, 1)}`: `s_{(2, 1)} = h₂ h₁ - h₃` in `Λ_R`. -/
example :
    DirectSum.of _ 3 (stableSchur R (singletonSecondRow 1)) =
      (DirectSum.of _ 2 (stableHsymm R 2) : SymmetricFunction R) *
          DirectSum.of _ 1 (stableHsymm R 1) -
        DirectSum.of _ 3 (stableHsymm R 3) :=
  of_stableSchur_singletonSecondRow_eq_hsymm R 1

/-- The dual Jacobi--Trudi expansion of `s_{(2, 1)}`: `s_{(2, 1)} = e₂ e₁ - e₃` in `Λ_R`. -/
example :
    DirectSum.of _ 3 (stableSchur R (singletonSecondRow 1)) =
      (DirectSum.of _ 2 (stableEsymm R 2) : SymmetricFunction R) *
          DirectSum.of _ 1 (stableEsymm R 1) -
        DirectSum.of _ 3 (stableEsymm R 3) := by
  simpa [conjugate_singletonSecondRow_one] using
    of_stableSchur_conjugate_singletonSecondRow_eq_esymm R 1

/-- Because `(2, 1)` is self-conjugate, the involution `ω` fixes `s_{(2, 1)}`. -/
example :
    omega R (DirectSum.of _ 3 (stableSchur R (singletonSecondRow 1))) =
      DirectSum.of _ 3 (stableSchur R (singletonSecondRow 1)) := by
  rw [omega_of_stableSchur, conjugate_singletonSecondRow_one]

end TauCeti.Examples

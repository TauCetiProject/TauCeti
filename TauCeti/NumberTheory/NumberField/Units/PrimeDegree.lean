/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.FinrankPrime
import TauCeti.NumberTheory.NumberField.Units.Basic

/-!
# Units of a number field of prime degree

In a number field of prime degree, a non-torsion unit lies in no proper subfield, since a unit
with rational value is torsion, and therefore generates `K` over `ℚ`. This is what lets a
statement about integral primitive elements of `K` apply to every non-torsion unit when the
degree is prime.

## Main results

* `TauCeti.NumberField.Units.adjoin_eq_top_of_finrank_prime`: in prime degree, a non-torsion
  unit generates `K` over `ℚ`.
-/

public section

open NumberField NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- **Prime degree makes a competing unit a generator.** In a number field of prime degree, a
non-torsion unit generates `K` over `ℚ`. -/
theorem adjoin_eq_top_of_finrank_prime (hp : Nat.Prime (Module.finrank ℚ K)) {v : (𝓞 K)ˣ}
    (hv : v ∉ torsion K) : Algebra.adjoin ℚ {((v : 𝓞 K) : K)} = ⊤ :=
  TauCeti.Algebra.adjoin_singleton_eq_top_of_finrank_prime hp fun h => hv (mem_torsion_of_mem_bot h)

end TauCeti.NumberField.Units

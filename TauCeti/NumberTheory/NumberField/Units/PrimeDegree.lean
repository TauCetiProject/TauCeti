/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.Basic

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
open scoped IntermediateField
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- **Prime degree makes a competing unit a generator.** In a number field of prime degree, a
non-torsion unit generates `K` over `ℚ`. -/
theorem adjoin_eq_top_of_finrank_prime (hp : Nat.Prime (Module.finrank ℚ K)) {v : (𝓞 K)ˣ}
    (hv : v ∉ torsion K) : Algebra.adjoin ℚ {((v : 𝓞 K) : K)} = ⊤ := by
  -- A field of prime degree has no proper subfield, and a non-torsion unit is not rational.
  have h : IntermediateField.adjoin ℚ {((v : 𝓞 K) : K)} = ⊤ :=
    ((IntermediateField.isSimpleOrder_of_finrank_prime ℚ K hp).eq_bot_or_eq_top _).resolve_left
      fun h => hv (mem_torsion_of_mem_bot (h ▸ IntermediateField.mem_adjoin_simple_self ℚ _))
  exact (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic fun x _ =>
    IsAlgebraic.of_finite ℚ x).mp h

end TauCeti.NumberField.Units

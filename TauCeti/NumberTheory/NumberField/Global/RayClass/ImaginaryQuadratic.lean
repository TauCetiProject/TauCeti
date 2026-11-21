/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.PurelyFinite
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.NumberTheory.NumberField.Quadratic.CongruenceUnits
import TauCeti.NumberTheory.NumberField.Quadratic.Units

/-!
# Congruence unit subgroups for imaginary quadratic fields

For an imaginary quadratic field `K` (`[IsTotallyComplex K]`, `finrank ℚ K = 2`) of discriminant
`D = NumberField.discr K`, this file determines the unit congruence subgroup
`unitsCongruenceSubgroup (Modulus.spanNat K N)` and its index in `(𝓞 K)ˣ`:

* `TauCeti.GlobalNumberFields.unitsCongruenceSubgroup_spanNat`: `⊤` at `N = 1`, `{±1}` at `N = 2`,
  and `⊥` for `3 ≤ N`.
* `TauCeti.GlobalNumberFields.index_unitsCongruenceSubgroup_spanNat_two`: `2` at `D = -4`, `3` at
  `D = -3`, and `1` for `D < -4`.
* `TauCeti.GlobalNumberFields.index_unitsCongruenceSubgroup_spanNat_of_three_le`: `#(𝓞 K)ˣ` (`4` at
  `D = -4`, `6` at `D = -3`, and `2` for `D < -4`) for `3 ≤ N`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open Module NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

/-- **Congruence subgroup of global units modulo `(N)` in an imaginary quadratic field**: `⊤` at
`N = 1`, `Subgroup.zpowers (-1)` at `N = 2`, and `⊥` for `3 ≤ N`. -/
theorem unitsCongruenceSubgroup_spanNat (hK : finrank ℚ K = 2) (N : ℕ) [NeZero N] :
    unitsCongruenceSubgroup (Modulus.spanNat K N) =
      if N = 1 then ⊤ else if N = 2 then Subgroup.zpowers (-1) else ⊥ := by
  rw [unitsCongruenceSubgroup_eq_ker_of_infinitePart_eq_empty (Modulus.spanNat_infinitePart N),
    Modulus.spanNat_finitePart,
    TauCeti.NumberField.ker_unitsMap_ringOfIntegers_quotient_span_natCast hK (NeZero.ne N)]

/-- **Index of `unitsCongruenceSubgroup (Modulus.spanNat K 2)`**: `2` at `D = -4`, `3` at `D = -3`,
and `1` for all `D < -4`. -/
theorem index_unitsCongruenceSubgroup_spanNat_two (hK : finrank ℚ K = 2) :
    (unitsCongruenceSubgroup (Modulus.spanNat K 2)).index =
      if discr K = -4 then 2 else if discr K = -3 then 3 else 1 := by
  rw [unitsCongruenceSubgroup_spanNat hK 2]
  simp only [OfNat.ofNat_ne_one, ↓reduceIte]
  have hmul := (Subgroup.zpowers (-1 : (𝓞 K)ˣ)).card_mul_index
  rw [Nat.card_zpowers, Units.orderOf_neg_one, ringChar.eq_zero,
    TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at hmul
  simp only [OfNat.zero_ne_ofNat, ↓reduceIte] at hmul
  split_ifs at hmul ⊢ <;> omega

/-- **Index of `unitsCongruenceSubgroup (Modulus.spanNat K N)` for `3 ≤ N`**: no unit other than
`1` is congruent to `1` modulo `(N)`, so the index is `#(𝓞 K)ˣ` (`4` at `D = -4`, `6` at `D = -3`,
and `2` for `D < -4`). -/
theorem index_unitsCongruenceSubgroup_spanNat_of_three_le (hK : finrank ℚ K = 2) {N : ℕ}
    [NeZero N] (hN : 3 ≤ N) :
    (unitsCongruenceSubgroup (Modulus.spanNat K N)).index =
      if discr K = -4 then 4 else if discr K = -3 then 6 else 2 := by
  have h1 : N ≠ 1 := by omega
  have h2 : N ≠ 2 := by omega
  rw [unitsCongruenceSubgroup_spanNat hK N]
  simp only [h1, h2, ↓reduceIte]
  have hmul := (⊥ : Subgroup (𝓞 K)ˣ).card_mul_index
  rw [Subgroup.card_bot, one_mul,
    TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at hmul
  exact hmul

end TauCeti.GlobalNumberFields

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.Teichmuller

/-!
# Teichmüller representatives in `ℚ_2` and `ℚ_5`

The Teichmüller section `ω : 𝓀[K]ˣ →* 𝒪[K]ˣ` of a nonarchimedean local field identifies the
units of the residue field with the `(q - 1)`-st roots of unity of `K`. This file computes it in
the two smallest instructive cases.

* Over `ℚ_2` the residue field is `𝔽_2`, whose only unit is `1`, so `ω` is trivial: the only
  Teichmüller representatives are `0` and `1`.
* Over `ℚ_5` the residue field is `𝔽_5`, whose unit group is cyclic of order `4` with generator
  `2`. So `ω(2)` is a primitive fourth root of unity in `ℚ_5`, a square root of `-1` congruent to
  `2` modulo `5`, and the Teichmüller representatives of `0, 1, 2, 3, 4` are
  `0, 1, ω(2), -ω(2), -1`.

## Main results

* `TauCeti.Padic.teichmuller_padic_two`: the Teichmüller section of `ℚ_2` is trivial.
* `TauCeti.Padic.teichmullerLift_padic_two_of_ne_zero`: every nonzero residue class of `ℤ_2`
  has Teichmüller representative `1`.
* `TauCeti.Padic.teichmullerLift_padic_five_four`: in `ℚ_5`, `ω(4) = -1`.
* `TauCeti.Padic.teichmullerLift_padic_five_two_sq`: in `ℚ_5`, `ω(2) ^ 2 = -1`.
* `TauCeti.Padic.teichmullerLift_padic_five_three`: in `ℚ_5`, `ω(3) = -ω(2)`.
* `TauCeti.Padic.isPrimitiveRoot_teichmullerLift_padic_five_two`: `ω(2)` is a primitive fourth
  root of unity in `ℚ_5`.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open IsLocalRing ValuativeRel

namespace TauCeti.Padic

/-- The Teichmüller section of `ℚ_2` is trivial, since `𝔽_2ˣ` is trivial. -/
theorem teichmuller_padic_two : TauCeti.teichmuller 𝒪[ℚ_[2]] = 1 := by
  have h : Nat.card 𝓀[ℚ_[2]]ˣ = 1 := by rw [Nat.card_units, Padic.natCard_residueField]
  have := (Nat.card_eq_one_iff_unique.1 h).1
  ext x
  rw [Subsingleton.elim x 1, map_one, MonoidHom.one_apply]

/-- Every nonzero residue class of `ℤ_2` has Teichmüller representative `1`. -/
theorem teichmullerLift_padic_two_of_ne_zero {a : 𝓀[ℚ_[2]]} (ha : a ≠ 0) :
    teichmullerLift ℚ_[2] a = 1 := by
  rw [← Units.val_mk0 ha, ← coe_teichmuller_apply, teichmuller_padic_two, MonoidHom.one_apply,
    Units.val_one]

/-- The prime `5`, as a `Fact`, so that `ℚ_[5]` can be written. -/
local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- In the residue field `𝔽_5` of `ℚ_5`, `4 = -1`. -/
private theorem four_eq_neg_one : (4 : 𝓀[ℚ_[5]]) = -1 := by
  let _ := Fintype.ofFinite 𝓀[ℚ_[5]]
  have h5 := FiniteField.cast_card_eq_zero 𝓀[ℚ_[5]]
  rw [← Nat.card_eq_fintype_card, Padic.natCard_residueField] at h5
  linear_combination h5

/-- In `ℚ_5`, the Teichmüller representative of `4` is `-1`. -/
theorem teichmullerLift_padic_five_four : teichmullerLift ℚ_[5] 4 = -1 := by
  rw [four_eq_neg_one, teichmullerLift_neg_one]
  rw [Padic.natCard_residueField]
  decide

/-- In `ℚ_5`, the Teichmüller representative of `2` is a square root of `-1`. -/
theorem teichmullerLift_padic_five_two_sq : teichmullerLift ℚ_[5] 2 ^ 2 = -1 := by
  rw [← map_pow, ← teichmullerLift_padic_five_four]
  norm_num

/-- In `ℚ_5`, the Teichmüller representative of `3` is the negative of that of `2`. -/
theorem teichmullerLift_padic_five_three :
    teichmullerLift ℚ_[5] 3 = -teichmullerLift ℚ_[5] 2 := by
  rw [neg_eq_neg_one_mul, ← teichmullerLift_padic_five_four, ← map_mul]
  congr 1
  linear_combination -four_eq_neg_one

/-- The Teichmüller representative of `2` is a primitive fourth root of unity in `ℚ_5`. -/
theorem isPrimitiveRoot_teichmullerLift_padic_five_two :
    IsPrimitiveRoot (teichmullerLift ℚ_[5] 2 : ℚ_[5]) 4 := by
  have h : (teichmullerLift ℚ_[5] 2 : ℚ_[5]) ^ 2 = -1 := by
    rw [← Subring.coe_pow, teichmullerLift_padic_five_two_sq]
    simp
  rw [IsPrimitiveRoot.iff_orderOf, show 4 = 2 ^ (1 + 1) by norm_num]
  refine orderOf_eq_prime_pow (n := 1) ?_ ?_
  · rw [pow_one, h]
    norm_num
  · rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h]
    norm_num

end TauCeti.Padic

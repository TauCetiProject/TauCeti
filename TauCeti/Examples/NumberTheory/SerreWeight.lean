/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.SerreWeight

/-!
# Examples of Serre's weight table

Concrete values of `TauCeti.SerreWeightData.weight` and `TauCeti.SerreWeightData.edixhovenWeight`:

* the `p`-torsion of a supersingular elliptic curve (niveau two, `(0, 1)`) has weight `2`, and
  unramified data have weight `p`, not the value `1` of the tame formula;
* at `p = 5` the niveau-two data `(1, 3)` have weight `9 = 3 + 1 * (5 + 1)`, and three twists by
  `χ` (one twist by `χ⁻¹`) give the data `(0, 2)` of weight `3`;
* the generic wild rows `(1, 3)` and `(3, 1)` at `p = 5` both have weight `9`;
* the peu and très ramifiée extensions of `1` by `χ` have weights `2` and `p + 1` for odd `p`,
  and `2` and `4` for `p = 2`, while their wild exponents agree;
* Edixhoven's weight is `1` on unramified data and `3` on dyadic très ramifiée data;
* at `p = 5`, the three rows `(0, 2)` coming from Fontaine–Laffaille weights `{0, 2}` have weight
  `3`.
-/

public section

namespace TauCeti.SerreWeightData

-- The supersingular niveau-two data `(0, 1)`: tame exponents `(0, 1)`, no wild exponents, weight 2.
example (p : ℕ) (hp : 2 ≤ p) :
    (niveauTwo 0 1 Nat.one_pos (by omega) : SerreWeightData p).tameExponents = some (0, 1) ∧
      (niveauTwo 0 1 Nat.one_pos (by omega) : SerreWeightData p).wildExponents = none ∧
      (niveauTwo 0 1 Nat.one_pos (by omega) : SerreWeightData p).weight = 2 := by
  simp

-- Unramified data: tame exponents `(0, 0)` and weight `p`, not the formula's value `1`.
example (p : ℕ) :
    (unramified p).tameExponents = some (0, 0) ∧ (unramified p).weight = p ∧
      (unramified p).edixhovenWeight = 1 := by
  simp

-- Niveau-one data `(0, 0)` are not wild data with the same integers: `β = 0` is excluded.
example (p : ℕ) (d : SerreWeightData p) (hd : d.wildExponents = some (0, 0)) : False := by
  cases d with
  | niveauOne => simp at hd
  | niveauTwo => simp at hd
  | wild α β hα hβ hβp tres htres =>
    simp only [wildExponents_wild, Option.some.injEq, Prod.mk.injEq] at hd
    omega

-- Niveau two at `p = 5` with `(a, b) = (1, 3)`: weight `9 = 3 + 1 * (5 + 1)`.
example : (niveauTwo 1 3 (by decide) (by decide) : SerreWeightData 5).weight = 9 ∧
    (niveauTwo 0 2 (by decide) (by decide) : SerreWeightData 5).weight = 3 := by
  simp

example : (niveauTwo 1 3 (by decide) (by decide) : SerreWeightData 5).tameExponents =
    some (1, 3) := by
  simp

-- Twisting `(1, 3)` at `p = 5` by `χ⁻¹ = χ ^ 3` renormalises to `(0, 2)`, of weight `3`.
example : twist^[3] (niveauTwo 1 3 (by decide) (by decide) : SerreWeightData 5) =
    niveauTwo 0 2 (by decide) (by decide) := by
  simp [twist_niveauTwo]

-- Twisting by `χ ^ (p - 1) = 1` returns the original data.
example : twist^[4] (niveauTwo 1 3 (by decide) (by decide) : SerreWeightData 5) =
    niveauTwo 1 3 (by decide) (by decide) := by
  simp [twist_niveauTwo]

example : twist^[4] (wild 3 1 (by decide) (by decide) (by decide) false (by simp) :
    SerreWeightData 5) = wild 3 1 (by decide) (by decide) (by decide) false (by simp) := by
  simp [twist_wild]

example : twist^[4] (niveauOne 1 2 (by decide) (by decide) : SerreWeightData 5) =
    niveauOne 1 2 (by decide) (by decide) := by
  simp [twist_niveauOne]

-- The generic wild rows `(1, 3)` and `(3, 1)` at `p = 5` both have weight `9`, and the wild
-- projection keeps the order of the exponents.
example : (wild 1 3 (by decide) (by decide) (by decide) false (by simp) :
      SerreWeightData 5).weight = 9 ∧
    (wild 3 1 (by decide) (by decide) (by decide) false (by simp) :
      SerreWeightData 5).weight = 9 ∧
    (wild 3 1 (by decide) (by decide) (by decide) false (by simp) :
      SerreWeightData 5).wildExponents = some (3, 1) ∧
    (wild 3 1 (by decide) (by decide) (by decide) false (by simp) :
      SerreWeightData 5).tameExponents = none := by
  simp

-- Peu and très ramifiée extensions of `1` by `χ`, for odd `p`: weights `2` and `p + 1`.
example (p : ℕ) (hp : 2 < p) :
    (wild 0 1 (Nat.zero_le _) le_rfl (by omega) false (by simp) : SerreWeightData p).weight = 2 ∧
      (wild 0 1 (Nat.zero_le _) le_rfl (by omega) true (fun _ => rfl) :
        SerreWeightData p).weight = p + 1 := by
  simp [show p ≠ 2 by omega]

-- At `p = 3` the très ramifiée row `(0, 1)` attains the bound `p + 1 = 4`.
example : (wild 0 1 (by decide) le_rfl (by decide) true (fun _ => rfl) :
    SerreWeightData 3).weight = 4 := by
  simp

-- At `p = 2` the peu and très ramifiée rows `(0, 1)` have weights `2` and `4`, both with wild
-- exponents `(0, 1)`, and every cyclotomic twist keeps the très ramifiée weight `4`.
example (n : ℕ) :
    (wild 0 1 le_rfl le_rfl le_rfl false (by simp) : SerreWeightData 2).weight = 2 ∧
      (wild 0 1 le_rfl le_rfl le_rfl true (fun _ => rfl) : SerreWeightData 2).weight = 4 ∧
      (wild 0 1 le_rfl le_rfl le_rfl false (by simp) : SerreWeightData 2).wildExponents =
        some (0, 1) ∧
      (wild 0 1 le_rfl le_rfl le_rfl true (fun _ => rfl) : SerreWeightData 2).wildExponents =
        some (0, 1) ∧
      (twist^[n] (wild 0 1 le_rfl le_rfl le_rfl true (fun _ => rfl) :
        SerreWeightData 2)).weight = 4 := by
  simp [Function.iterate_fixed (twist_eq_self_of_two _)]

-- Edixhoven's weight: `1` against `5` on unramified data at `p = 5`, `3` against `4` on dyadic très
-- ramifiée data, and `2` in both tables on the supersingular and dyadic peu ramifiée rows.
example : (unramified 5).edixhovenWeight = 1 ∧ (unramified 5).weight = 5 := by
  simp

example : (wild 0 1 le_rfl le_rfl le_rfl true (fun _ => rfl) :
      SerreWeightData 2).edixhovenWeight = 3 ∧
    (wild 0 1 le_rfl le_rfl le_rfl false (by simp) : SerreWeightData 2).edixhovenWeight = 2 ∧
    (niveauTwo 0 1 Nat.one_pos le_rfl : SerreWeightData 2).edixhovenWeight = 2 := by
  simp

-- Fontaine–Laffaille weights `{0, 2}` at `p = 5`: the niveau-one, niveau-two and ordered wild
-- rows `(0, 2)` all have weight `3 = r + 1`.
example : (niveauOne 0 2 (by decide) (by decide) : SerreWeightData 5).weight = 3 ∧
    (niveauTwo 0 2 (by decide) (by decide) : SerreWeightData 5).weight = 3 ∧
    (wild 0 2 (by decide) (by decide) (by decide) false (by simp) :
      SerreWeightData 5).weight = 3 := by
  simp

end TauCeti.SerreWeightData

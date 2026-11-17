/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.IntegralDomain

/-!
# Sums of nonsquares in finite fields

In any finite field `F` of odd characteristic (`(2 : F) ≠ 0`), there exist two nonsquare units
`a, b : Fˣ` whose sum in `F` is `1` (`TauCeti.FiniteField.exists_not_isSquare_add_eq_one`).
Equivalently, for any generator `g` of the cyclic unit group `Fˣ`, there exist odd integers `m` and
`n` such that `(g ^ m : F) + (g ^ n : F) = 1`
(`TauCeti.FiniteField.exists_odd_zpow_add_eq_one`).

The proof is a direct pigeonhole count on the subsets `S` of square units and `N` of nonsquare
units: multiplication by a generator `g` (which is itself a nonsquare since `2 ≠ 0`) injects `S`
into `N`, giving `#S ≤ #N`, whereas if `1 - a` were a square for every `a ∈ N` then
`a ↦ 1 - a` would inject `N` into `S \ {1}`, giving `#N ≤ #S - 1`.

## Main results

* `TauCeti.FiniteField.not_isSquare_generator`: a generator of `Fˣ` in odd characteristic is not a
  square.
* `TauCeti.FiniteField.exists_not_isSquare_add_eq_one`: there exist nonsquare units `a, b : Fˣ`
  with `(a : F) + b = 1`.
* `TauCeti.FiniteField.exists_odd_zpow_add_eq_one`: for any generator `g` of `Fˣ`, there exist odd
  integers `m, n` with `((g ^ m : Fˣ) : F) + (g ^ n : Fˣ) = 1`.
-/

public section

namespace TauCeti.FiniteField

variable {F : Type*} [Field F] [Finite F]

/-- In a finite field of odd characteristic, a generator of the unit group `Fˣ` is not a square. -/
theorem not_isSquare_generator (h2 : (2 : F) ≠ 0) {g : Fˣ}
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) : ¬IsSquare g := by
  rintro ⟨u, hu⟩
  have hsurj : Function.Surjective (fun x : Fˣ => x * x) := by
    intro x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    refine ⟨u ^ k, ?_⟩
    dsimp only
    rw [← mul_zpow, ← hu]
  have hinj : Function.Injective (fun x : Fˣ => x * x) :=
    Finite.injective_iff_surjective.mpr hsurj
  have hneg1 : (-1 : Fˣ) = 1 := hinj (by simp)
  have hval : (-1 : F) = 1 := congrArg Units.val hneg1
  have htwo : (2 : F) = 0 := by
    rw [← one_add_one_eq_two]
    calc
      (1 : F) + 1 = (-1 : F) + 1 := congrArg (· + 1) hval.symm
      _ = 0 := neg_add_cancel 1
  exact h2 htwo

/-- In any finite field of odd characteristic, there exist two nonsquare units summing to `1`. -/
theorem exists_not_isSquare_add_eq_one (F : Type*) [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ a b : Fˣ, ¬IsSquare a ∧ ¬IsSquare b ∧ (a : F) + b = 1 := by
  classical
  let _ : Fintype Fˣ := Fintype.ofFinite Fˣ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hg_nsq : ¬IsSquare g := not_isSquare_generator h2 hg
  let S : Finset Fˣ := Finset.univ.filter (fun x : Fˣ => IsSquare x)
  let N : Finset Fˣ := Finset.univ.filter (fun x : Fˣ => ¬IsSquare x)
  have hS_le_N : S.card ≤ N.card := by
    refine Finset.card_le_card_of_injOn (fun x => g * x) (fun x hx => ?_)
      (fun x _ y _ hxy => mul_left_cancel hxy)
    simp only [S, N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨u, rfl⟩ := hx
    rintro ⟨v, hv⟩
    refine hg_nsq ⟨v * u⁻¹, ?_⟩
    have hmul : g * (u * u) = v * v := hv
    calc
      g = g * (u * u) * (u⁻¹ * u⁻¹) := by simp [mul_assoc]
      _ = (v * v) * (u⁻¹ * u⁻¹) := by rw [hmul]
      _ = (v * u⁻¹) * (v * u⁻¹) := by
        simp only [mul_assoc, mul_left_comm]
  by_contra hnone
  push Not at hnone
  let f : Fˣ → Fˣ := fun a =>
    if ha : a = 1 then 1
    else Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr fun h => ha (Units.ext h.symm))
  have hN_le : N.card ≤ (S.erase 1).card := by
    refine Finset.card_le_card_of_injOn f (fun a ha => ?_) (fun a ha b hb hab => ?_)
    · simp only [N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have ha1 : a ≠ 1 := fun h => ha (h ▸ IsSquare.one)
      have hf : f a = Units.mk0 (1 - (a : F))
          (sub_ne_zero.mpr fun h => ha1 (Units.ext h.symm)) := by
        simp only [f, ha1, ↓reduceDIte]
      rw [hf]
      set b : Fˣ := Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr fun h => ha1 (Units.ext h.symm))
      have hb_sum : (a : F) + b = 1 := by simp [b]
      have hb_sq : IsSquare b := by
        by_contra hb_nsq
        exact hnone a b ha hb_nsq hb_sum
      have hb_ne1 : b ≠ 1 := by
        intro h1
        have hv : (1 : F) - (a : F) = 1 := by
          simpa [b] using congrArg Units.val h1
        have ha0 : (a : F) = 0 := sub_eq_self.mp hv
        exact Units.ne_zero a ha0
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨hb_ne1, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hb_sq
    · simp only [N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have ha1 : a ≠ 1 := fun h => ha (h ▸ IsSquare.one)
      have hb1 : b ≠ 1 := fun h => hb (h ▸ IsSquare.one)
      simp only [f, ha1, hb1, ↓reduceDIte] at hab
      have hval : (1 : F) - a = 1 - b := by
        simpa using congrArg Units.val hab
      exact Units.ext (sub_right_inj.mp hval)
  have h1S : (1 : Fˣ) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact IsSquare.one
  have herase : (S.erase 1).card + 1 = S.card := Finset.card_erase_add_one h1S
  omega

/-- In any finite field of odd characteristic, for any generator `g` of `Fˣ`, there exist odd
integers `m, n` such that `((g ^ m : Fˣ) : F) + (g ^ n : Fˣ) = 1`. -/
theorem exists_odd_zpow_add_eq_one (h2 : (2 : F) ≠ 0) {g : Fˣ}
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) :
    ∃ m n : ℤ, Odd m ∧ Odd n ∧ ((g ^ m : Fˣ) : F) + (g ^ n : Fˣ) = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_not_isSquare_add_eq_one F h2
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  have hodd : ∀ k : ℤ, ¬IsSquare (g ^ k) → Odd k := by
    intro k hk
    rw [← Int.not_even_iff_odd]
    rintro ⟨r, rfl⟩
    exact hk ⟨g ^ r, by rw [zpow_add]⟩
  exact ⟨m, n, hodd m ha, hodd n hb, hab⟩

end TauCeti.FiniteField

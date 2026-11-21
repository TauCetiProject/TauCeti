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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralDomain

/-!
# Sums of nonsquares in finite fields

In any finite field `F` of odd characteristic (`(2 : F) ≠ 0`), there exist two nonsquare units
`a, b : Fˣ` whose sum in `F` is `1` (`TauCeti.FiniteField.exists_not_isSquare_add_eq_one`), hence
for any generator `g` of `Fˣ`, two odd powers `g ^ m + g ^ n = 1`
(`TauCeti.FiniteField.exists_odd_zpow_add_eq_one`).

The proof counts squares `S` and nonsquares `N` in `Fˣ`: multiplying by a generator injects `S`
into `N` (`#S ≤ #N`), whereas if `1 - a` were a square for every `a ∈ N` then `a ↦ 1 - a` would
inject `N` into `S.erase 1` (`#N ≤ #S - 1`).
-/

public section

namespace TauCeti.FiniteField

variable {F : Type*} [Field F] [Finite F]

/-- In a finite field of odd characteristic, a generator of the unit group `Fˣ` is not a square. -/
theorem not_isSquare_generator (h2 : (2 : F) ≠ 0) {g : Fˣ}
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) : ¬IsSquare g := by
  rintro ⟨u, hu⟩
  have hchar : ringChar F ≠ 2 :=
    fun h => h2 (by simpa [h] using ringChar.Nat.cast_ringChar (R := F))
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := F) hchar
  have ha0 : a ≠ 0 := by rintro rfl; exact ha IsSquare.zero
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 a ha0))
  refine ha ⟨(u ^ k : Fˣ), ?_⟩
  have hsq : g ^ k = u ^ k * u ^ k := by rw [← mul_zpow, ← hu]
  simpa [Units.ext_iff, hk] using congrArg Units.val hsq

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
    refine Finset.card_le_card_of_injOn (g * ·) (fun x hx => ?_) (fun _ _ _ _ => mul_left_cancel)
    simp only [S, N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨u, rfl⟩ := hx
    rintro ⟨v, hv⟩
    refine hg_nsq ⟨v * u⁻¹, ?_⟩
    rw [mul_mul_mul_comm, ← hv]
    simp [mul_assoc]
  by_contra hnone
  push Not at hnone
  let f : Fˣ → Fˣ := fun a =>
    if ha : a = 1 then 1 else Units.mk0 (1 - a) (sub_ne_zero.mpr fun h => ha (Units.ext h.symm))
  have hne1 : ∀ {a : Fˣ}, a ∈ N → a ≠ 1 := fun ha h =>
    (Finset.mem_filter.mp ha).2 (h ▸ IsSquare.one)
  have hN_le : N.card ≤ (S.erase 1).card := by
    refine Finset.card_le_card_of_injOn f (fun a ha => ?_) (fun a ha b hb hab => ?_)
    · have ha1 : a ≠ 1 := hne1 ha
      set b : Fˣ := Units.mk0 (1 - a) (sub_ne_zero.mpr fun h => ha1 (Units.ext h.symm))
      have hfa : f a = b := by simp only [f, ha1, ↓reduceDIte, b]
      rw [Finset.mem_coe, Finset.mem_erase, hfa]
      refine ⟨fun h1 => Units.ne_zero a (by simpa [b] using congrArg Units.val h1),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          by_contra hb; exact hnone a b (Finset.mem_filter.mp ha).2 hb (by simp [b])⟩⟩
    · simp only [f, hne1 ha, hne1 hb, ↓reduceDIte] at hab
      exact Units.ext (by simpa using congrArg Units.val hab)
  have herase : (S.erase 1).card + 1 = S.card :=
    Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsSquare.one⟩)
  omega

/-- In any finite field of odd characteristic, for any generator `g` of `Fˣ`, there exist odd
integers `m, n` such that `((g ^ m : Fˣ) : F) + (g ^ n : Fˣ) = 1`. -/
theorem exists_odd_zpow_add_eq_one (h2 : (2 : F) ≠ 0) {g : Fˣ}
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) :
    ∃ m n : ℤ, Odd m ∧ Odd n ∧ ((g ^ m : Fˣ) : F) + (g ^ n : Fˣ) = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_not_isSquare_add_eq_one F h2
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  have hodd : ∀ k : ℤ, ¬IsSquare (g ^ k) → Odd k := fun k hk =>
    Int.not_even_iff_odd.mp (fun he => hk (he.isSquare_zpow g))
  exact ⟨m, n, hodd m ha, hodd n hb, hab⟩

end TauCeti.FiniteField

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralDomain
import TauCeti.FieldTheory.Finite.Card
import TauCeti.GroupTheory.SpecificGroups.Cyclic.PowMonoidHom

/-!
# Euler's criterion for `n`-th powers in a finite field

Let `F` be a finite field with `q` elements and `n ∣ q - 1`. A nonzero `a ∈ F` is an `n`-th power
exactly when `a ^ ((q - 1) / n) = 1`. At `n = 2` this is Mathlib's `FiniteField.isSquare_iff`
(in odd characteristic).

## Main results

* `TauCeti.FiniteField.exists_pow_eq_iff_pow_card_sub_one_div_eq_one`: Euler's criterion for
  `n`-th powers in a finite field.
* `TauCeti.FiniteField.pow_card_div_two_eq_neg_one`: a nonsquare `r` satisfies
  `r ^ (#F / 2) = -1`.
* `TauCeti.FiniteField.natCard_isSquare_units_eq_natCard_not_isSquare`: in odd characteristic,
  there are equally many square and nonsquare units.
* `TauCeti.FiniteField.exists_add_eq_one_not_isSquare`: in odd characteristic, two nonsquare
  units sum to `1`.
-/

public section

namespace TauCeti.FiniteField

/-- **Euler's criterion in a finite field.** If `n ∣ #F - 1`, then a nonzero `a ∈ F` is an `n`-th
power exactly when `a ^ ((#F - 1) / n) = 1`. -/
theorem exists_pow_eq_iff_pow_card_sub_one_div_eq_one {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : n ∣ Nat.card F - 1) {a : F} (ha : a ≠ 0) :
    (∃ b, b ^ n = a) ↔ a ^ ((Nat.card F - 1) / n) = 1 := by
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units _
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    have := Nat.eq_zero_of_zero_dvd hn
    omega
  -- Euler's criterion in the cyclic group `Fˣ` of order `#F - 1`.
  have h := IsCyclic.mem_range_powMonoidHom_iff n (Units.mk0 _ ha)
  rw [hcard, Nat.gcd_eq_right hn, ← Units.val_eq_one, Units.val_pow_eq_pow_val, Units.val_mk0] at h
  rw [← h]
  constructor
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact ha (by rw [← hb, zero_pow hn0])
    exact ⟨Units.mk0 b hb0, Units.ext (by simp [hb])⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa using congrArg Units.val hb⟩

/-- **Euler's criterion for a nonsquare.** In a finite field `F`, a nonsquare `r` satisfies
`r ^ (#F / 2) = -1`. -/
theorem pow_card_div_two_eq_neg_one {F : Type*} [Field F] [Finite F] {r : F}
    (hr : ¬IsSquare r) : r ^ (Nat.card F / 2) = -1 := by
  have := Fintype.ofFinite F
  have hF := ringChar_ne_two_of_odd_card (odd_card_of_not_isSquare hr)
  have hr0 : r ≠ 0 := by rintro rfl; exact hr .zero
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.pow_dichotomy hF hr0).resolve_left
    fun h ↦ hr ((FiniteField.isSquare_iff hF hr0).mpr h)

/-- In a finite field of odd characteristic, there are equally many square and nonsquare units. -/
theorem natCard_isSquare_units_eq_natCard_not_isSquare {F : Type*} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) :
    Nat.card {u : Fˣ // IsSquare u} = Nat.card {u : Fˣ // ¬IsSquare u} := by
  have := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare hF
  have hg0 : g ≠ 0 := by rintro rfl; exact hg .zero
  let g₀ : Fˣ := Units.mk0 g hg0
  have hg₀ : ¬IsSquare g₀ := fun h ↦ hg (by simpa [g₀] using h.map (Units.coeHom F))
  -- Multiplication by the nonsquare `g₀` is a bijection between squares and nonsquares in `Fˣ`.
  refine Nat.card_congr
    { toFun := fun u ↦ ⟨g₀ * u.1, fun hgu ↦ hg₀ ?_⟩
      invFun := fun v ↦ ⟨g₀⁻¹ * v.1, (FiniteField.unit_isSquare_iff hF _).mpr ?_⟩
      left_inv := fun u ↦ Subtype.ext (inv_mul_cancel_left g₀ u.1)
      right_inv := fun v ↦ Subtype.ext (mul_inv_cancel_left g₀ v.1) }
  · rcases u.2 with ⟨x, hx⟩
    rcases hgu with ⟨y, hy⟩
    refine ⟨y * x⁻¹, ?_⟩
    have hmul : g₀ = (y * y) * (x * x)⁻¹ := eq_mul_inv_of_mul_eq (by rw [← hx]; exact hy)
    rw [hmul, mul_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]
  · apply Units.ext
    have hv' : ¬IsSquare (v.1 : F) := fun h ↦ v.2 (Units.isSquare_coe_iff.mp h)
    have hv_pow := pow_card_div_two_eq_neg_one hv'
    have hg_pow := pow_card_div_two_eq_neg_one hg
    rw [Nat.card_eq_fintype_card] at hv_pow hg_pow
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one,
      mul_pow, inv_pow, g₀, Units.val_mk0, hg_pow, hv_pow]
    simp

/-- In a finite field of odd characteristic, there exist two nonsquare units summing to `1`. -/
theorem exists_add_eq_one_not_isSquare {F : Type*} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) :
    ∃ a b : Fˣ, (a : F) + b = 1 ∧ ¬IsSquare a ∧ ¬IsSquare b := by
  have := Fintype.ofFinite F
  classical
  let S : Finset Fˣ := Finset.univ.filter fun u : Fˣ ↦ IsSquare u
  let N : Finset Fˣ := Finset.univ.filter fun u : Fˣ ↦ ¬IsSquare u
  have hcard : S.card = N.card := by
    have h := natCard_isSquare_units_eq_natCard_not_isSquare hF
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  -- If `1 - u` were a square for every nonsquare `u`, then `u ↦ 1 - u` would inject `N` into
  -- `S \ {1}`, contradicting `|N| = |S|`.
  by_contra hcontra
  push Not at hcontra
  let f : Fˣ → Fˣ := fun u ↦
    if h : u ≠ 1 then Units.mk0 (1 - (u : F)) (sub_ne_zero.mpr fun h1 ↦ h (Units.ext h1.symm))
    else 1
  have hne1 : ∀ u ∈ N, u ≠ 1 := fun u hu h1 ↦ by
    rw [Finset.mem_filter] at hu
    exact hu.2 (h1 ▸ IsSquare.one)
  have hf_val : ∀ u ∈ N, (f u : F) = 1 - (u : F) := fun u hu ↦ by
    simp [f, hne1 u hu]
  have hmaps : Set.MapsTo f N (S.erase 1) := fun u hu ↦ by
    rw [Finset.mem_coe] at hu ⊢
    have hval := hf_val u hu
    rw [Finset.mem_erase, Finset.mem_filter]
    refine ⟨fun h1 ↦ Units.ne_zero u ?_, Finset.mem_univ _, ?_⟩
    · have h1' : (1 : F) - (u : F) = 1 := by simpa [h1] using hval.symm
      exact sub_eq_self.mp h1'
    · rw [Finset.mem_filter] at hu
      exact hcontra u (f u) (by rw [hval]; ring) hu.2
  have hinj : Set.InjOn f N := fun u₁ hu₁ u₂ hu₂ heq ↦ by
    rw [Finset.mem_coe] at hu₁ hu₂
    apply Units.ext
    have h1 := hf_val u₁ hu₁
    have h2 := hf_val u₂ hu₂
    rw [heq] at h1
    exact sub_right_injective (h1.symm.trans h2)
  have hle : N.card ≤ (S.erase 1).card := Finset.card_le_card_of_injOn f hmaps hinj
  have h1S : (1 : Fˣ) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsSquare.one⟩
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨1, h1S⟩
  rw [Finset.card_erase_of_mem h1S, hcard] at hle
  omega

end TauCeti.FiniteField

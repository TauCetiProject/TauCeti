/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmically weighted harmonic sums in sign classes

Above `1`, a finite set in the residue classes `±1` has at most two terms per
block of length the modulus, when the blocks are indexed by the quotient of `p + 1`.
This bounds the sum of `log p / p` without any prime-counting estimate.
-/

public section

namespace TauCeti

open Finset

-- Compare each term with the harmonic weight of its block and count the two possible residues.
private theorem sum_inv_natCast_le_of_sign_blocks {s : Finset ℕ} {q X : ℕ} (hq : 2 ≤ q)
    (hs : ∀ p ∈ s, 2 ≤ p ∧ p ≤ X ∧ (p + 1) % q ∈ ({0, 2} : Finset ℕ)) :
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ (4 / q) * ∑ j ∈ Icc 1 X, (j : ℝ)⁻¹ := by
  let e (p : ℕ) := ((p + 1) / q, (p + 1) % q)
  have he (p : ℕ) : q * (e p).1 + (e p).2 = p + 1 := Nat.div_add_mod _ _
  have hmem (p : ℕ) (hp : p ∈ s) : e p ∈ Icc 1 X ×ˢ ({0, 2} : Finset ℕ) := by
    obtain ⟨hp₂, hpX, hr⟩ := hs p hp
    have hrem : (e p).2 ≤ 2 := by
      rcases mem_insert.mp hr with h | h
      · simp [e, h]
      · simp [e, mem_singleton.mp h]
    have hj : 1 ≤ (e p).1 := by
      by_contra! hj
      have hj₀ : (e p).1 = 0 := by omega
      have h := he p
      rw [hj₀, mul_zero, zero_add] at h
      omega
    have hqj : 2 * (e p).1 ≤ q * (e p).1 := Nat.mul_le_mul_right _ hq
    have := he p
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hj, by omega⟩, hr⟩
  calc
    _ ≤ ∑ i ∈ Icc 1 X ×ˢ ({0, 2} : Finset ℕ), (2 / q) * (i.1 : ℝ)⁻¹ := by
      refine sum_le_sum_of_injOn e (fun a _ b _ hab ↦ ?_) ?_ (fun p hp ↦ ?_)
        (fun _ _ _ ↦ by positivity)
      · have := congrArg (fun i : ℕ × ℕ ↦ q * i.1 + i.2) hab
        simpa only [he, Nat.add_right_cancel_iff] using this
      · rintro _ hi
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
        exact hmem p hp
      · have hp₂ := (hs p hp).1
        have hj := (mem_Icc.mp (mem_product.mp (hmem p hp)).1).1
        have hqj : q * (e p).1 ≤ 2 * p := by have := he p; omega
        have hqj' : (q : ℝ) * (e p).1 ≤ 2 * p := by exact_mod_cast hqj
        rw [← div_eq_mul_inv, div_div, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        simpa [mul_comm] using hqj'
    _ = _ := by
      simp only [sum_product, sum_const, card_insert_of_notMem (by decide : 0 ∉ {2}),
        card_singleton, Nat.reduceAdd, nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, ← mul_sum]
      congr 1
      ring

/-- A harmonic subsum above `1` in the two sign classes modulo `q` gains a factor `4/q`
compared to the full harmonic sum up to the cutoff. -/
theorem sum_inv_natCast_le_harmonic_of_natCast_eq_one_or_neg_one {s : Finset ℕ} {q X : ℕ}
    (hs : ∀ p ∈ s, 2 ≤ p ∧ p ≤ X ∧ ((p : ZMod q) = 1 ∨ (p : ZMod q) = -1)) :
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ (4 / q) * (harmonic X : ℝ) := by
  have hH : (harmonic X : ℝ) = ∑ j ∈ Icc 1 X, (j : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hH]
  by_cases hq : 2 < q
  · refine sum_inv_natCast_le_of_sign_blocks hq.le fun p hp ↦ ?_
    obtain ⟨hp₂, hpX, hpq⟩ := hs p hp
    refine ⟨hp₂, hpX, ?_⟩
    -- Shifting by one puts the two residues at `0` and `2` within the block.
    rcases hpq with hpq | hpq
    · have hmod := ((ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hpq)).add_right 1
      have hrem : (p + 1) % q = 2 % q := hmod
      simp [hrem, Nat.mod_eq_of_lt hq]
    · have hcast : ((p + 1 : ℕ) : ZMod q) = 0 := by simp [Nat.cast_succ, hpq]
      have hrem := Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp hcast)
      simp [hrem]
  by_cases hq₀ : q = 0
  · subst q
    have : s = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp₂, -, h | h⟩ := hs p hp
      · have := (ZMod.natCast_eq_natCast_iff p 1 0).mp (by simpa using h)
        simp at this
        omega
      · have hd : 0 ∣ p + 1 := (ZMod.natCast_eq_zero_iff (p + 1) 0).mp
          (by simp [Nat.cast_succ, h])
        simp at hd
    simp [this]
  calc
    _ ≤ ∑ j ∈ Icc 1 X, (j : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg (fun j hj ↦ mem_Icc.mpr ⟨one_le_two.trans (hs j hj).1,
        (hs j hj).2.1⟩) (fun _ _ _ ↦ by positivity)
    _ ≤ _ := by
      apply le_mul_of_one_le_left (sum_nonneg fun _ _ ↦ by positivity)
      rw [le_div_iff₀ (by positivity)]
      have hq' : (q : ℝ) ≤ 2 := by exact_mod_cast (by omega : q ≤ 2)
      linarith

/-- The sum of `log p / p` up to `X` in the sign classes modulo `q` is at most
`4 log X (1 + log X) / q`, without any primality assumption. -/
theorem sum_log_div_le_of_natCast_eq_one_or_neg_one {s : Finset ℕ} {q : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hs : ∀ p ∈ s, (p : ℝ) ≤ X ∧ ((p : ZMod q) = 1 ∨ (p : ZMod q) = -1)) :
    ∑ p ∈ s, Real.log p / (p : ℝ) ≤ 4 * Real.log X * (1 + Real.log X) / q := by
  have hlog := Real.log_nonneg hX
  rw [← sum_filter_of_ne (p := fun p ↦ 2 ≤ p)]
  · calc
      _ ≤ ∑ p ∈ s.filter (2 ≤ ·), Real.log X * (p : ℝ)⁻¹ := by
        refine sum_le_sum fun p hp ↦ ?_
        obtain ⟨hp, hp₂⟩ := mem_filter.mp hp
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) (hs p hp).1)
          (by positivity)
      _ ≤ Real.log X * ((4 / q) * (harmonic ⌊X⌋₊ : ℝ)) := by
        rw [← mul_sum]
        refine mul_le_mul_of_nonneg_left (sum_inv_natCast_le_harmonic_of_natCast_eq_one_or_neg_one
          fun p hp ↦ ?_) hlog
        obtain ⟨hp, hp₂⟩ := mem_filter.mp hp
        exact ⟨hp₂, Nat.le_floor (hs p hp).1, (hs p hp).2⟩
      _ ≤ _ := by
        calc
          _ ≤ Real.log X * ((4 / q) * (1 + Real.log X)) := by
            gcongr
            exact harmonic_floor_le_one_add_log X hX
          _ = _ := by ring
  · intro p _ hp
    by_contra! h
    have : p = 0 ∨ p = 1 := by omega
    rcases this with rfl | rfl <;> simp at hp

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.NumberTheory.Harmonic.Basic

/-!
# Harmonic bounds for short shifts of the multiples of a modulus

Weighting the reciprocals in the progression `p + δ ≡ 0 (mod m)` by `m` still costs at
most twice the harmonic sum at the original cutoff when `|δ| ≤ 1`. This is useful when a
loss charged at each prime is amplified by the modulus on just a few residue classes.
-/

public section

open Finset

namespace TauCeti

/-- The sum of `m / p` over a finite subset of `2 ≤ p < B` with `m ∣ p + δ`,
for `-1 ≤ δ ≤ 1`, is at most twice the `B`-th harmonic number. -/
theorem sum_natCast_div_le_two_mul_harmonic_of_dvd_add {S : Finset ℕ} {m B : ℕ} {δ : ℤ}
    (hδ : δ ∈ Set.Icc (-1) 1) (hS : ∀ p ∈ S, 2 ≤ p ∧ p < B ∧ (m : ℤ) ∣ (p : ℤ) + δ) :
    ∑ p ∈ S, (m : ℝ) / p ≤ 2 * (harmonic B : ℝ) := by
  let c (p : ℕ) := ((p : ℤ) + δ).toNat / m
  have hbounds (p : ℕ) (hp : p ∈ S) :
      0 < ((p : ℤ) + δ).toNat ∧ ((p : ℤ) + δ).toNat ≤ B ∧
        ((p : ℤ) + δ).toNat ≤ 2 * p := by
    obtain ⟨hp₂, hpB, _⟩ := hS p hp
    obtain ⟨hlo, hhi⟩ := hδ
    omega
  have hmul (p : ℕ) (hp : p ∈ S) : m * c p = ((p : ℤ) + δ).toNat := by
    have hz : 0 ≤ (p : ℤ) + δ := by have := (hbounds p hp).1; omega
    have hd : m ∣ ((p : ℤ) + δ).toNat := by
      exact_mod_cast (show (m : ℤ) ∣ (↑(((p : ℤ) + δ).toNat) : ℤ) by
        rw [Int.toNat_of_nonneg hz]; exact (hS p hp).2.2)
    exact Nat.mul_div_cancel' hd
  have hcpos (p : ℕ) (hp : p ∈ S) : 0 < c p := by
    apply Nat.pos_of_ne_zero
    intro hc
    exact (hbounds p hp).1.ne' (by simpa [hc] using (hmul p hp).symm)
  rw [cast_harmonic_eq_sum_Ioc, mul_sum]
  refine sum_le_sum_of_injOn c ?_ ?_ ?_ (by intros; positivity)
  · intro p hp q hq heq
    have h := (hmul p hp).symm.trans (congrArg (m * ·) heq) |>.trans (hmul q hq)
    have hp' := (hbounds p hp).1
    omega
  · intro i hi
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
    exact mem_Ioc.mpr ⟨hcpos p hp, (Nat.le_of_dvd (hbounds p hp).1
      ⟨m, by rw [mul_comm, hmul p hp]⟩).trans (hbounds p hp).2.1⟩
  · intro p hp
    have h : m * c p ≤ 2 * p := (hmul p hp).trans_le (hbounds p hp).2.2
    have hp' : 0 < (p : ℝ) := by exact_mod_cast (zero_lt_two.trans_le (hS p hp).1)
    have hc' : 0 < (c p : ℝ) := by exact_mod_cast hcpos p hp
    rw [← div_eq_mul_inv, div_le_div_iff₀ hp' hc']
    exact_mod_cast h

end TauCeti

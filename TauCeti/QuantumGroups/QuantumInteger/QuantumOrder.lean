/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Chebyshev
public import Mathlib.Data.ENat.Lattice

/-!
# Quantum order of a loop parameter

The quantum order of `δ` is the least positive index at which the quantum integer `[n]`
vanishes, or `⊤` if every positive-index quantum integer is nonzero. Using extended natural
numbers keeps the generic case separate from index zero, where `[0]` always vanishes.

`quantumOrder_eq_natCast_iff` characterizes a finite quantum order by vanishing at that index
and nonvanishing below it. `lt_quantumOrder_iff` converts the finite nonvanishing conditions
used in Jones–Wenzl recursions and semisimplicity criteria into an order bound. The definition
works over every commutative ring, including positive characteristic, and is preserved by
injective ring homomorphisms.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The least positive index with vanishing quantum integer, or `⊤` if there is none. -/
noncomputable def quantumOrder (δ : R) : ℕ∞ :=
  ⨅ n : {n : ℕ // 0 < n ∧ qInt R δ n = 0}, (n.val : ℕ∞)

/-- The quantum order is the infimum of the positive vanishing indices. -/
theorem quantumOrder_def (δ : R) :
    quantumOrder δ = ⨅ n : {n : ℕ // 0 < n ∧ qInt R δ n = 0}, (n.val : ℕ∞) := (rfl)

/-- A positive vanishing index bounds the quantum order from above. -/
theorem quantumOrder_le {δ : R} {n : ℕ} (hn : 0 < n) (h : qInt R δ n = 0) :
    quantumOrder δ ≤ n := by
  rw [quantumOrder_def]
  exact iInf_le (fun k : {k : ℕ // 0 < k ∧ qInt R δ k = 0} => (k.val : ℕ∞)) ⟨n, hn, h⟩

/-- The quantum order is infinite exactly when no positive-index quantum integer vanishes. -/
@[simp]
theorem quantumOrder_eq_top_iff (δ : R) :
    quantumOrder δ = ⊤ ↔ ∀ n : ℕ, 0 < n → qInt R δ n ≠ 0 := by
  rw [quantumOrder_def, ENat.iInf_natCast_eq_top]
  simp [isEmpty_subtype]

/-- A finite quantum order is precisely a first positive vanishing index. -/
theorem quantumOrder_eq_natCast_iff (δ : R) (n : ℕ) :
    quantumOrder δ = n ↔
      0 < n ∧ qInt R δ n = 0 ∧ ∀ k : ℕ, 0 < k → k < n → qInt R δ k ≠ 0 := by
  rw [quantumOrder_def, ENat.iInf_eq_natCast_iff]
  simp only [ENat.natCast_inj, Subtype.exists, exists_prop, exists_eq_right, Subtype.forall,
    ENat.natCast_le_natCast]
  constructor
  · rintro ⟨⟨hn, hz⟩, hmin⟩
    exact ⟨hn, hz, fun k hk hkn hz => (not_le_of_gt hkn) (hmin k ⟨hk, hz⟩)⟩
  · rintro ⟨hn, hz, hmin⟩
    exact ⟨⟨hn, hz⟩, fun k ⟨hk, hzero⟩ => le_of_not_gt (fun hkn => hmin k hk hkn hzero)⟩

/-- All positive indices strictly below the quantum order have nonzero quantum integer. -/
theorem qInt_ne_zero_of_lt_quantumOrder {δ : R} {n : ℕ} (hn : 0 < n)
    (h : (n : ℕ∞) < quantumOrder δ) : qInt R δ n ≠ 0 := by
  intro hz
  exact (not_le_of_gt h) (quantumOrder_le hn hz)

/-- A bound below the quantum order is equivalent to nonvanishing through that bound. -/
theorem lt_quantumOrder_iff (δ : R) (n : ℕ) :
    (n : ℕ∞) < quantumOrder δ ↔
      ∀ k : ℕ, 0 < k → k ≤ n → qInt R δ k ≠ 0 := by
  rw [← ENat.natCast_add_one_le_iff, quantumOrder_def, le_iInf_iff]
  simp only [Subtype.forall, ← Nat.cast_add_one, ENat.natCast_le_natCast]
  constructor
  · intro h k hk hkn hz
    exact (by omega : ¬n + 1 ≤ k) (h k ⟨hk, hz⟩)
  · intro h k ⟨hk, hz⟩
    exact Nat.succ_le_of_lt (lt_of_not_ge (fun hkn => h k hk hkn hz))

/-- Every quantum order is positive, including the infinite one. -/
theorem quantumOrder_pos (δ : R) : 0 < quantumOrder δ := by
  rw [← ENat.natCast_zero, lt_quantumOrder_iff]
  intro k hk hk0
  omega

/-- Over a nontrivial ring the first quantum integer is nonzero, so the quantum order exceeds
one. -/
theorem one_lt_quantumOrder [Nontrivial R] (δ : R) : 1 < quantumOrder δ := by
  rw [← ENat.natCast_one, lt_quantumOrder_iff]
  intro k hk hk1
  have : k = 1 := by omega
  simp [this]

/-- The quantum integer at a finite quantum order vanishes. -/
theorem qInt_eq_zero_of_quantumOrder_eq {δ : R} {n : ℕ} (h : quantumOrder δ = n) :
    qInt R δ n = 0 :=
  ((quantumOrder_eq_natCast_iff δ n).mp h).2.1

/-- At loop parameter zero the first vanishing index is two. -/
@[simp]
theorem quantumOrder_zero [Nontrivial R] : quantumOrder (0 : R) = 2 := by
  apply (quantumOrder_eq_natCast_iff (0 : R) 2).mpr
  refine ⟨by omega, by simp, ?_⟩
  intro k hk hk2
  have : k = 1 := by omega
  simp [this]

/-- At loop parameter two no positive-index quantum integer vanishes in characteristic zero. -/
@[simp]
theorem quantumOrder_two [CharZero R] : quantumOrder (2 : R) = ⊤ := by
  rw [quantumOrder_eq_top_iff]
  intro n hn
  simpa using (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn) : (n : R) ≠ 0)

/-- At loop parameter negative two no positive-index quantum integer vanishes in
characteristic zero. -/
@[simp]
theorem quantumOrder_neg_two [CharZero R] : quantumOrder (-2 : R) = ⊤ := by
  rw [quantumOrder_eq_top_iff]
  intro n hn
  simp [qInt_neg_two_left, Nat.ne_of_gt hn]

end TauCeti

namespace RingHom

open TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An injective ring homomorphism preserves the quantum order of each loop parameter. -/
theorem quantumOrder_map (f : R →+* S) (hf : Function.Injective f) (δ : R) :
    quantumOrder (f δ) = quantumOrder δ := by
  apply le_antisymm
  · rw [quantumOrder_def δ]
    apply le_iInf
    intro n
    apply quantumOrder_le n.property.1
    simpa only [← f.map_qInt, map_zero] using congrArg f n.property.2
  · rw [quantumOrder_def (f δ)]
    apply le_iInf
    intro n
    apply quantumOrder_le n.property.1
    apply hf
    simpa only [f.map_qInt, map_zero] using n.property.2

end RingHom

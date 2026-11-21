/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# Big Witt truncation sets

A truncation set is a set of positive naturals closed under divisibility. These sets index big
Witt coordinates. The divisors of an integer give finite truncations, and shifting indices by
a multiplier gives the truncations used for Frobenius and Verschiebung.
See Hesselholt, *The big de Rham–Witt complex*, §1.
-/

public section

namespace TauCeti.BigWitt

/-- A set of positive indices closed under passage to divisors. -/
structure TruncationSet where
  /-- The underlying set of indices. -/
  carrier : Set ℕ
  /-- Every index is positive. -/
  pos' : ∀ {n : ℕ}, n ∈ carrier → 0 < n
  /-- Every divisor of an index is again an index. -/
  mem_of_dvd' : ∀ {n d : ℕ}, n ∈ carrier → d ∣ n → d ∈ carrier

namespace TruncationSet

instance : SetLike TruncationSet ℕ where
  coe := carrier
  coe_injective := by
    intro S T h
    cases S
    cases T
    cases h
    rfl

/-- Truncation sets are determined by their members. -/
@[ext]
theorem ext {S T : TruncationSet} (h : ∀ n : ℕ, n ∈ S ↔ n ∈ T) : S = T :=
  SetLike.ext h

/-- Every member of a truncation set is positive. -/
theorem pos (S : TruncationSet) {n : ℕ} (hn : n ∈ S) : 0 < n :=
  S.pos' hn

/-- Every divisor of an index in a truncation set belongs to the set. -/
theorem mem_of_dvd (S : TruncationSet) {n d : ℕ} (hn : n ∈ S) (hd : d ∣ n) : d ∈ S :=
  S.mem_of_dvd' hn hd

instance : PartialOrder TruncationSet := .ofSetLike _

instance : OrderBot TruncationSet where
  bot := ⟨∅, fun h ↦ h.elim, fun h _ ↦ h.elim⟩
  bot_le := fun _ _ h ↦ False.elim h

/-- The empty truncation set has no indices. -/
@[simp]
theorem notMem_bot (n : ℕ) : n ∉ (⊥ : TruncationSet) :=
  fun h ↦ False.elim h

/-- Zero does not belong to a truncation set. -/
@[simp]
theorem zero_notMem (S : TruncationSet) : 0 ∉ S :=
  fun h ↦ Nat.not_lt_zero _ (S.pos h)

/-- The truncation set of positive divisors of `m`, with `divisors 0 = ⊥`. -/
def divisors (m : ℕ) : TruncationSet where
  carrier := m.divisors
  pos' := Nat.pos_of_mem_divisors
  mem_of_dvd' hn hd := Nat.mem_divisors.mpr <|
    ⟨hd.trans (Nat.dvd_of_mem_divisors hn), Nat.ne_zero_of_mem_divisors hn⟩

/-- Membership in a divisor truncation set is divisibility of a nonzero index. -/
@[simp]
theorem mem_divisors {m d : ℕ} : d ∈ divisors m ↔ d ∣ m ∧ m ≠ 0 :=
  (Nat.mem_divisors)

/-- The divisor truncation at zero is empty. -/
@[simp]
theorem divisors_zero : divisors 0 = ⊥ := by
  ext d
  simp

/-- The truncation set `S/n` of indices whose multiples by `n` lie in `S`. -/
def div (S : TruncationSet) (n : ℕ) : TruncationSet where
  carrier := {d | n * d ∈ S}
  pos' := fun hd ↦ Nat.pos_of_mul_pos_left (S.pos hd)
  mem_of_dvd' hn hd := S.mem_of_dvd hn (Nat.mul_dvd_mul_left n hd)

/-- An index belongs to `S.div n` precisely when its multiple by `n` belongs to `S`. -/
@[simp]
theorem mem_div {S : TruncationSet} {n d : ℕ} : d ∈ S.div n ↔ n * d ∈ S :=
  (Iff.rfl)

/-- Shifting by zero gives the empty truncation set. -/
@[simp]
theorem div_zero (S : TruncationSet) : S.div 0 = ⊥ := by
  ext d
  simp

/-- Shifting by `1` leaves the truncation set unchanged. -/
@[simp]
theorem div_one (S : TruncationSet) : S.div 1 = S := by
  ext d
  simp

/-- Two successive shifts multiply the shifting indices. -/
@[simp]
theorem div_div (S : TruncationSet) (n k : ℕ) : (S.div n).div k = S.div (n * k) := by
  ext d
  simp [Nat.mul_assoc]

end TruncationSet

end TauCeti.BigWitt

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# Truncation sets

A *truncation set* is a set `S` of positive natural numbers that is closed under taking divisors.
Truncation sets index the coordinates of big Witt vectors: the big Witt ring `W_S(R)` has
underlying set `R ^ S`, and its ring structure is the one making the ghost components `w_n`,
`n ∈ S`, ring homomorphisms. The divisors of `p ^ (k - 1)` give the `p`-typical Witt vectors of
length `k`, and the set of all positive integers gives the full big Witt ring.

The empty set is a truncation set; a nonempty truncation set contains `1`.

## Main definitions

* `TauCeti.BigWitt.TruncationSet`: sets of positive integers closed under divisors.
* `TauCeti.BigWitt.TruncationSet.divisors m`: the finite truncation set `Div(m)` of divisors of
  `m`, the smallest truncation set containing `m` when `m ≠ 0`.
* `TauCeti.BigWitt.TruncationSet.FiniteSubtruncation S`: the finite truncation sets contained
  in `S`.
* `S / n`: the truncation set `{e | n * e ∈ S}`, the indexing set for the target of the
  Frobenius `F_n : W_S(R) → W_{S/n}(R)`.
* `⊥` and `⊤`: the empty truncation set and the set of all positive integers.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Acta Math. 214 (2015), §1.
-/

public section

namespace TauCeti.BigWitt

/-- A truncation set is a set of positive natural numbers closed under positive divisors.
The empty truncation set is allowed. -/
structure TruncationSet where
  /-- The underlying set of positive natural numbers. -/
  carrier : Set ℕ
  /-- Every element of a truncation set is positive. -/
  positive : ∀ n ∈ carrier, 0 < n
  /-- A truncation set contains every positive divisor of each of its elements. -/
  divisor_closed : ∀ {n d : ℕ}, n ∈ carrier → 0 < d → d ∣ n → d ∈ carrier

namespace TruncationSet

instance : SetLike TruncationSet ℕ :=
  ⟨carrier, fun S T h ↦ by cases S; cases T; congr⟩

instance : PartialOrder TruncationSet :=
  .ofSetLike TruncationSet

variable {S T : TruncationSet} {n d e k m : ℕ}

@[simp]
theorem mem_carrier : n ∈ S.carrier ↔ n ∈ S :=
  Iff.rfl

@[simp]
theorem coe_mk (s : Set ℕ) (h₁ h₂) : ((⟨s, h₁, h₂⟩ : TruncationSet) : Set ℕ) = s :=
  rfl

@[simp]
theorem mem_mk (s : Set ℕ) (h₁ h₂) : n ∈ (⟨s, h₁, h₂⟩ : TruncationSet) ↔ n ∈ s :=
  Iff.rfl

@[ext]
theorem ext (h : ∀ n, n ∈ S ↔ n ∈ T) : S = T :=
  SetLike.ext h

theorem pos_of_mem (hn : n ∈ S) : 0 < n :=
  S.positive n hn

theorem ne_zero_of_mem (hn : n ∈ S) : n ≠ 0 :=
  (S.pos_of_mem hn).ne'

@[simp]
theorem zero_notMem (S : TruncationSet) : 0 ∉ S :=
  fun h ↦ S.ne_zero_of_mem h rfl

/-- A truncation set contains every divisor of each of its elements. -/
theorem mem_of_dvd (hn : n ∈ S) (hd : d ∣ n) : d ∈ S :=
  S.divisor_closed hn (Nat.pos_of_dvd_of_pos hd (S.pos_of_mem hn)) hd

/-- A nonempty truncation set contains `1`. -/
theorem one_mem_of_mem (hn : n ∈ S) : 1 ∈ S :=
  S.mem_of_dvd hn (one_dvd n)

theorem one_mem_iff_nonempty : 1 ∈ S ↔ (S : Set ℕ).Nonempty :=
  ⟨fun h ↦ ⟨1, h⟩, fun ⟨_, hn⟩ ↦ S.one_mem_of_mem hn⟩

/-! ### The empty truncation set and the truncation set of all positive integers -/

instance : Bot TruncationSet :=
  ⟨⟨∅, fun _ h ↦ h.elim, fun h ↦ h.elim⟩⟩

instance : Top TruncationSet :=
  ⟨⟨{n | 0 < n}, fun _ h ↦ h, fun _ hd _ ↦ hd⟩⟩

@[simp]
theorem notMem_bot : n ∉ (⊥ : TruncationSet) :=
  id

@[simp]
theorem mem_top : n ∈ (⊤ : TruncationSet) ↔ 0 < n :=
  Iff.rfl

@[simp]
theorem coe_bot : ((⊥ : TruncationSet) : Set ℕ) = ∅ :=
  rfl

@[simp]
theorem coe_top : ((⊤ : TruncationSet) : Set ℕ) = {n | 0 < n} :=
  rfl

instance : OrderBot TruncationSet where
  bot_le _ _ h := h.elim

instance : OrderTop TruncationSet where
  le_top S _ hn := S.pos_of_mem hn

theorem eq_bot_iff_one_notMem : S = ⊥ ↔ 1 ∉ S := by
  rw [one_mem_iff_nonempty, Set.not_nonempty_iff_eq_empty, ← coe_bot, SetLike.coe_set_eq]

/-! ### Divisors -/

/-- The finite truncation set `Div(m)` of divisors of `m`. Following `Nat.divisors`, it is empty
for `m = 0`. -/
def divisors (m : ℕ) : TruncationSet where
  carrier := m.divisors
  positive _ h := Nat.pos_of_mem_divisors h
  divisor_closed hn _ hd := Nat.mem_divisors.2
    ⟨hd.trans (Nat.dvd_of_mem_divisors hn), (Nat.mem_divisors.1 hn).2⟩

@[simp]
theorem mem_divisors : d ∈ divisors m ↔ d ∣ m ∧ m ≠ 0 :=
  Nat.mem_divisors

@[simp]
theorem coe_divisors (m : ℕ) : (divisors m : Set ℕ) = m.divisors :=
  Set.ext fun _ ↦ mem_divisors.trans Nat.mem_divisors.symm

theorem mem_divisors_self (hm : m ≠ 0) : m ∈ divisors m :=
  mem_divisors.2 ⟨dvd_rfl, hm⟩

@[simp]
theorem divisors_zero : divisors 0 = ⊥ := by
  ext; simp

/-- For `m ≠ 0`, `Div(m)` is the smallest truncation set containing `m`. -/
theorem divisors_le_iff (hm : m ≠ 0) : divisors m ≤ S ↔ m ∈ S :=
  ⟨fun h ↦ h (mem_divisors_self hm), fun h _ hd ↦ S.mem_of_dvd h (mem_divisors.1 hd).1⟩

theorem divisors_le_divisors_of_dvd (hm : m ≠ 0) (h : k ∣ m) : divisors k ≤ divisors m :=
  fun _ hd ↦ mem_divisors.2 ⟨(mem_divisors.1 hd).1.trans h, hm⟩

/-! ### Finite subtruncations -/

/-- The finite truncation sets contained in `S`. -/
abbrev FiniteSubtruncation (S : TruncationSet) :=
  {T : TruncationSet // T ≤ S ∧ (T : Set ℕ).Finite}

/-- The smallest finite subtruncation of `S` containing the index `n`. -/
abbrev divisorStage (n : S) : FiniteSubtruncation S :=
  ⟨divisors n, (divisors_le_iff (S.ne_zero_of_mem n.property)).2 n.property,
    by simpa only [coe_divisors] using n.val.divisors.finite_toSet⟩

/-- If two coordinate functions agree on every finite subtruncation of `S`,
they agree at each index of `S`. -/
theorem apply_eq_of_finiteSubtruncations {R : Type*} {x y : S → R}
    (h : ∀ (T : FiniteSubtruncation S) (n : T.val),
      x ⟨n, T.property.1 n.property⟩ = y ⟨n, T.property.1 n.property⟩) (n : S) :
    x n = y n :=
  h (divisorStage n) ⟨n, mem_divisors_self (S.ne_zero_of_mem n.property)⟩

/-! ### Quotients `S / n` -/

/-- The truncation set `S / n = {e | n * e ∈ S}`. It indexes the target of the big Witt Frobenius
`F_n : W_S(R) → W_{S/n}(R)` and the source of the Verschiebung `V_n`. For `n = 0` it is empty. -/
instance : HDiv TruncationSet ℕ TruncationSet where
  hDiv S n :=
    { carrier := {e | n * e ∈ S}
      positive _ he := Nat.pos_of_mul_pos_left (S.pos_of_mem he)
      divisor_closed he _ hd := S.mem_of_dvd he (Nat.mul_dvd_mul_left n hd) }

@[simp]
theorem mem_div : e ∈ S / n ↔ n * e ∈ S :=
  Iff.rfl

@[simp]
theorem coe_div (S : TruncationSet) (n : ℕ) : ((S / n : TruncationSet) : Set ℕ) = {e | n * e ∈ S} :=
  rfl

theorem div_div (S : TruncationSet) (n k : ℕ) : S / n / k = S / (n * k) := by
  ext; simp [mul_assoc]

@[simp]
theorem div_one (S : TruncationSet) : S / 1 = S := by
  ext; simp

@[simp]
theorem div_zero (S : TruncationSet) : S / 0 = ⊥ := by
  ext; simp

@[simp]
theorem bot_div (n : ℕ) : (⊥ : TruncationSet) / n = ⊥ := by
  ext; simp

theorem div_le_div (h : S ≤ T) (n : ℕ) : S / n ≤ T / n :=
  fun _ he ↦ h (mem_div.1 he)

/-- `S / n` is nonempty exactly when `n ∈ S`. -/
theorem one_mem_div_iff : 1 ∈ S / n ↔ n ∈ S := by
  simp

theorem divisors_div (h : n ∣ m) : divisors m / n = divisors (m / n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  obtain ⟨c, rfl⟩ := h
  ext e
  simp [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hn), Nat.mul_dvd_mul_iff_left
    (Nat.pos_of_ne_zero hn), hn]

end TruncationSet

end TauCeti.BigWitt

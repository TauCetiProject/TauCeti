/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.CycleData
public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.PermutationTriple.IsoClass
public import TauCeti.Combinatorics.PermutationTriple.Regular

/-!
# Invariants of isomorphism classes of permutation triples

Simultaneous relabeling of the sheets preserves the cycle partitions, cycle counts, Euler
characteristic, combinatorial genus, automorphism-group order, and regularity of a permutation
triple. This file descends each invariant to `TauCeti.PermutationTriple.IsoClass` and restricts
them along `TauCeti.ConnectedIsoClass.forget` to `TauCeti.ConnectedIsoClass`, where `χ ≤ 2`,
`2 - 2 g = χ`, `|Aut| ∣ n`, and regularity is equivalent to `|Aut| = n`.
-/

open Equiv

public section

namespace TauCeti

namespace PermutationTriple.IsoClass

variable {n : ℕ} (c : IsoClass n) (t : PermutationTriple n)

/-- The ordered full cycle partitions `(λ₀, λ₁, λ∞)` of an isomorphism class of triples. -/
def cycleData : IsoClass n → Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  lift PermutationTriple.cycleData fun _ _ => cycleData_eq_of_equivalent

/-- Evaluating `cycleData` on `mk t` recovers `t.cycleData`. -/
@[simp] theorem cycleData_mk : (mk t).cycleData = t.cycleData := lift_mk _ _ t

/-- The unordered multiset of the three full cycle partitions of an isomorphism class. -/
def unorderedCycleData : IsoClass n → Multiset (Multiset ℕ) :=
  lift PermutationTriple.unorderedCycleData fun _ _ => unorderedCycleData_eq_of_equivalent

/-- Evaluating `unorderedCycleData` on `mk t` recovers `t.unorderedCycleData`. -/
@[simp] theorem unorderedCycleData_mk : (mk t).unorderedCycleData = t.unorderedCycleData :=
  lift_mk _ _ t

/-- The unordered cycle data of `c` is the three-element multiset of entries of `c.cycleData`. -/
theorem unorderedCycleData_def :
    c.unorderedCycleData = {c.cycleData.1, c.cycleData.2.1, c.cycleData.2.2} := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simp

/-- The ordered numbers of cycles `(c₀, c₁, c∞)` of an isomorphism class, fixed points included. -/
noncomputable def cycleCounts : IsoClass n → ℕ × ℕ × ℕ :=
  lift PermutationTriple.cycleCounts fun _ _ => cycleCounts_eq_of_equivalent

/-- Evaluating `cycleCounts` on `mk t` recovers `t.cycleCounts`. -/
@[simp] theorem cycleCounts_mk : (mk t).cycleCounts = t.cycleCounts := lift_mk _ _ t

/-- Each entry of `c.cycleCounts` is the cardinality of the corresponding part of `c.cycleData`. -/
theorem cycleCounts_eq_card_cycleData :
    c.cycleCounts = (c.cycleData.1.card, c.cycleData.2.1.card, c.cycleData.2.2.card) := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.cycleCounts_eq_card_cycleData

/-- Each of the three full cycle partitions of `c` sums to the degree `n`. -/
theorem sum_cycleData :
    (c.cycleData.1.sum, c.cycleData.2.1.sum, c.cycleData.2.2.sum) = (n, n, n) := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.sum_cycleData

/-- The combinatorial Euler characteristic `c₀ + c₁ + c∞ - n` of an isomorphism class of triples. -/
noncomputable def eulerChar : IsoClass n → ℤ :=
  lift PermutationTriple.eulerChar fun _ _ => eulerChar_eq_of_equivalent

/-- Evaluating `eulerChar` on `mk t` recovers `t.eulerChar`. -/
@[simp] theorem eulerChar_mk : (mk t).eulerChar = t.eulerChar := lift_mk _ _ t

/-- Expresses `c.eulerChar` in terms of `c.cycleCounts` and the degree `n`. -/
theorem eulerChar_eq_cycleCounts :
    c.eulerChar = (c.cycleCounts.1 : ℤ) + c.cycleCounts.2.1 + c.cycleCounts.2.2 - n := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.eulerChar_eq_cycleCounts

/-- The combinatorial Euler characteristic of any isomorphism class of triples is even. -/
theorem even_eulerChar : Even c.eulerChar := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.even_eulerChar

/-- The combinatorial genus `((2 - χ) / 2).toNat` of an isomorphism class of triples. -/
noncomputable def genus : IsoClass n → ℕ :=
  lift PermutationTriple.genus fun _ _ => genus_eq_of_equivalent

/-- Evaluating `genus` on `mk t` recovers `t.genus`. -/
@[simp] theorem genus_mk : (mk t).genus = t.genus := lift_mk _ _ t

/-- Expresses `c.genus` in terms of `c.eulerChar`. -/
theorem genus_def : c.genus = ((2 - c.eulerChar) / 2).toNat := by
  obtain ⟨t, rfl⟩ := mk_surjective c; rw [genus_mk, eulerChar_mk, PermutationTriple.genus_def]

/-- The cardinality of the automorphism group of any representative of an isomorphism class. -/
noncomputable def natCardAutomorphismGroup : IsoClass n → ℕ :=
  lift (fun t => Nat.card t.automorphismGroup) fun _ _ => natCard_automorphismGroup_eq_of_equivalent

/-- Evaluating `natCardAutomorphismGroup` on `mk t` gives `Nat.card t.automorphismGroup`. -/
@[simp] theorem natCardAutomorphismGroup_mk :
    (mk t).natCardAutomorphismGroup = Nat.card t.automorphismGroup := lift_mk _ _ t

/-- Regularity of an isomorphism class of triples: connected with transitive automorphism group. -/
def IsRegular : IsoClass n → Prop :=
  lift PermutationTriple.IsRegular fun _ _ h => propext (isRegular_iff_of_equivalent h)

/-- Evaluating `IsRegular` on `mk t` recovers `t.IsRegular`. -/
@[simp] theorem isRegular_mk : (mk t).IsRegular ↔ t.IsRegular := of_eq (lift_mk _ _ t)

/-- Every regular isomorphism class of permutation triples is connected. -/
theorem IsRegular.isConnected {c : IsoClass n} (hc : c.IsRegular) : c.IsConnected := by
  obtain ⟨t, rfl⟩ := mk_surjective c; exact (isConnected_mk t).2 ((isRegular_mk t).1 hc).isConnected

end PermutationTriple.IsoClass

namespace ConnectedIsoClass

variable {n : ℕ} (c : ConnectedIsoClass n) (t : ConnectedTriple n)

/-- The ordered full cycle partitions `(λ₀, λ₁, λ∞)` of a connected isomorphism class. -/
def cycleData : Multiset ℕ × Multiset ℕ × Multiset ℕ := c.forget.cycleData

/-- Evaluating `cycleData` on `mk t` recovers `t.val.cycleData`. -/
@[simp] theorem cycleData_mk : (mk t).cycleData = t.val.cycleData := by simp [cycleData]

/-- Forgetting connectedness preserves `cycleData`. -/
@[simp] theorem cycleData_forget : c.forget.cycleData = c.cycleData := (rfl)

/-- The unordered multiset of the three full cycle partitions of a connected isomorphism class. -/
def unorderedCycleData : Multiset (Multiset ℕ) := c.forget.unorderedCycleData

/-- Evaluating `unorderedCycleData` on `mk t` recovers `t.val.unorderedCycleData`. -/
@[simp] theorem unorderedCycleData_mk : (mk t).unorderedCycleData = t.val.unorderedCycleData := by
  simp [unorderedCycleData]

/-- Forgetting connectedness preserves `unorderedCycleData`. -/
@[simp] theorem unorderedCycleData_forget : c.forget.unorderedCycleData = c.unorderedCycleData :=
  (rfl)

/-- The ordered numbers of cycles `(c₀, c₁, c∞)` of a connected class, fixed points included. -/
noncomputable def cycleCounts : ℕ × ℕ × ℕ := c.forget.cycleCounts

/-- Evaluating `cycleCounts` on `mk t` recovers `t.val.cycleCounts`. -/
@[simp] theorem cycleCounts_mk : (mk t).cycleCounts = t.val.cycleCounts := by simp [cycleCounts]

/-- Forgetting connectedness preserves `cycleCounts`. -/
@[simp] theorem cycleCounts_forget : c.forget.cycleCounts = c.cycleCounts := (rfl)

/-- Each entry of `c.cycleCounts` is the cardinality of the corresponding part of `c.cycleData`. -/
theorem cycleCounts_eq_card_cycleData :
    c.cycleCounts = (c.cycleData.1.card, c.cycleData.2.1.card, c.cycleData.2.2.card) :=
  c.forget.cycleCounts_eq_card_cycleData

/-- Each of the three full cycle partitions of a connected isomorphism class sums to `n`. -/
theorem sum_cycleData :
    (c.cycleData.1.sum, c.cycleData.2.1.sum, c.cycleData.2.2.sum) = (n, n, n) :=
  c.forget.sum_cycleData

/-- The combinatorial Euler characteristic `c₀ + c₁ + c∞ - n` of a connected isomorphism class. -/
noncomputable def eulerChar : ℤ := c.forget.eulerChar

/-- Evaluating `eulerChar` on `mk t` recovers `t.val.eulerChar`. -/
@[simp] theorem eulerChar_mk : (mk t).eulerChar = t.val.eulerChar := by simp [eulerChar]

/-- Forgetting connectedness preserves `eulerChar`. -/
@[simp] theorem eulerChar_forget : c.forget.eulerChar = c.eulerChar := (rfl)

/-- Expresses `c.eulerChar` in terms of `c.cycleCounts` and the degree `n`. -/
theorem eulerChar_eq_cycleCounts :
    c.eulerChar = (c.cycleCounts.1 : ℤ) + c.cycleCounts.2.1 + c.cycleCounts.2.2 - n :=
  c.forget.eulerChar_eq_cycleCounts

/-- The Euler characteristic of a connected isomorphism class is even. -/
theorem even_eulerChar : Even c.eulerChar := c.forget.even_eulerChar

/-- Every connected isomorphism class satisfies the Euler bound `χ ≤ 2`. -/
theorem eulerChar_le_two : c.eulerChar ≤ 2 := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.property.eulerChar_le_two

/-- The combinatorial genus `(2 - χ) / 2` of a connected isomorphism class. -/
noncomputable def genus : ℕ := c.forget.genus

/-- Evaluating `genus` on `mk t` recovers `t.val.genus`. -/
@[simp] theorem genus_mk : (mk t).genus = t.val.genus := by simp [genus]

/-- Forgetting connectedness preserves `genus`. -/
@[simp] theorem genus_forget : c.forget.genus = c.genus := (rfl)

/-- Expresses `c.genus` in terms of `c.eulerChar`. -/
theorem genus_def : c.genus = ((2 - c.eulerChar) / 2).toNat := c.forget.genus_def

/-- Coercing the genus of a connected class to `ℤ` recovers the exact quotient `(2 - χ) / 2`. -/
theorem natCast_genus : (c.genus : ℤ) = (2 - c.eulerChar) / 2 := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.property.natCast_genus

/-- The Euler characteristic of a connected isomorphism class is `2 - 2 g`. -/
theorem two_sub_two_mul_genus : 2 - 2 * (c.genus : ℤ) = c.eulerChar := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.property.two_sub_two_mul_genus

/-- The unique connected isomorphism class of degree `1` has genus `0`. -/
@[simp] theorem genus_of_degree_one (c : ConnectedIsoClass 1) : c.genus = 0 := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.val.genus_of_degree_one

/-- The cardinality of the automorphism group of any representative of a connected class. -/
noncomputable def natCardAutomorphismGroup : ℕ := c.forget.natCardAutomorphismGroup

/-- Evaluating `natCardAutomorphismGroup` on `mk t` gives `Nat.card t.val.automorphismGroup`. -/
@[simp] theorem natCardAutomorphismGroup_mk : (mk t).natCardAutomorphismGroup =
    Nat.card t.val.automorphismGroup := by simp [natCardAutomorphismGroup]

/-- Forgetting connectedness preserves `natCardAutomorphismGroup`. -/
@[simp] theorem natCardAutomorphismGroup_forget :
    c.forget.natCardAutomorphismGroup = c.natCardAutomorphismGroup := (rfl)

/-- For a connected isomorphism class, the order of the automorphism group divides the degree. -/
theorem natCardAutomorphismGroup_dvd : c.natCardAutomorphismGroup ∣ n := by
  obtain ⟨t, rfl⟩ := mk_surjective c
  simpa using PermutationTriple.card_automorphismGroup_dvd t.property.isPretransitive

/-- Regularity of a connected isomorphism class: transitive automorphism action on the sheets. -/
def IsRegular : Prop := c.forget.IsRegular

/-- Evaluating `IsRegular` on `mk t` recovers `t.val.IsRegular`. -/
@[simp] theorem isRegular_mk : (mk t).IsRegular ↔ t.val.IsRegular := by simp [IsRegular]

/-- Forgetting connectedness preserves `IsRegular`. -/
@[simp] theorem isRegular_forget : c.forget.IsRegular ↔ c.IsRegular := Iff.rfl

/-- A connected isomorphism class is regular iff its automorphism group has order `n`. -/
theorem isRegular_iff_natCardAutomorphismGroup : c.IsRegular ↔ c.natCardAutomorphismGroup = n := by
  obtain ⟨t, rfl⟩ := mk_surjective c
  simp [PermutationTriple.isRegular_iff_card_automorphismGroup, t.property]

end ConnectedIsoClass

end TauCeti

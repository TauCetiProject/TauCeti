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
`2 - 2 g = χ`, `|Aut| ∣ n`, and regularity is equivalent to `|Aut| = n`. We also record the
degree-`0` `IsEmpty` and degree-`1` `Unique` instances on connected carriers.

## Main definitions and results

* `TauCeti.PermutationTriple.IsoClass.cycleData`, `unorderedCycleData`, `cycleCounts`, `eulerChar`,
  `genus`, `natCardAutomorphismGroup`, `IsRegular` and their restrictions to `ConnectedIsoClass`.
* `TauCeti.ConnectedIsoClass.eulerChar_le_two`, `natCast_genus`, `two_sub_two_mul_genus`,
  `natCardAutomorphismGroup_dvd`, `isRegular_iff_natCardAutomorphismGroup`.
-/

open Equiv

public section

namespace TauCeti

namespace PermutationTriple

variable {n : ℕ}

/-- Relabeling the sheets conjugates the automorphism group, preserving its cardinality. -/
@[simp] theorem natCard_automorphismGroup_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    Nat.card (τ • t).automorphismGroup = Nat.card t.automorphismGroup :=
  (automorphismGroup_smul τ t).symm ▸ Subgroup.card_map_of_injective (MulAut.conj τ).injective

/-- Isomorphic permutation triples have automorphism groups of the same cardinality. -/
theorem natCard_automorphismGroup_eq_of_equivalent {t t' : PermutationTriple n}
    (h : Equivalent t t') : Nat.card t.automorphismGroup = Nat.card t'.automorphismGroup := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h; simp

namespace IsoClass

/-- The ordered full cycle partitions `(λ₀, λ₁, λ∞)` of an isomorphism class of triples. -/
def cycleData : IsoClass n → Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  lift PermutationTriple.cycleData fun _ _ => cycleData_eq_of_equivalent

/-- Evaluating `cycleData` on `mk t` recovers `t.cycleData`. -/
@[simp] theorem cycleData_mk (t : PermutationTriple n) : (mk t).cycleData = t.cycleData :=
  lift_mk _ _ t

/-- The unordered multiset of the three full cycle partitions of an isomorphism class. -/
def unorderedCycleData : IsoClass n → Multiset (Multiset ℕ) :=
  lift PermutationTriple.unorderedCycleData fun _ _ => unorderedCycleData_eq_of_equivalent

/-- Evaluating `unorderedCycleData` on `mk t` recovers `t.unorderedCycleData`. -/
@[simp] theorem unorderedCycleData_mk (t : PermutationTriple n) :
    (mk t).unorderedCycleData = t.unorderedCycleData := lift_mk _ _ t

/-- The unordered cycle data of `c` is the three-element multiset of entries of `c.cycleData`. -/
theorem unorderedCycleData_def (c : IsoClass n) :
    c.unorderedCycleData = {c.cycleData.1, c.cycleData.2.1, c.cycleData.2.2} := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simp

/-- The ordered numbers of cycles `(c₀, c₁, c∞)` of an isomorphism class, fixed points included. -/
noncomputable def cycleCounts : IsoClass n → ℕ × ℕ × ℕ :=
  lift PermutationTriple.cycleCounts fun _ _ => cycleCounts_eq_of_equivalent

/-- Evaluating `cycleCounts` on `mk t` recovers `t.cycleCounts`. -/
@[simp] theorem cycleCounts_mk (t : PermutationTriple n) : (mk t).cycleCounts = t.cycleCounts :=
  lift_mk _ _ t

/-- Each entry of `c.cycleCounts` is the cardinality of the corresponding part of `c.cycleData`. -/
theorem cycleCounts_eq_card_cycleData (c : IsoClass n) :
    c.cycleCounts = (c.cycleData.1.card, c.cycleData.2.1.card, c.cycleData.2.2.card) := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.cycleCounts_eq_card_cycleData

/-- Each of the three full cycle partitions of `c` sums to the degree `n`. -/
theorem sum_cycleData (c : IsoClass n) :
    (c.cycleData.1.sum, c.cycleData.2.1.sum, c.cycleData.2.2.sum) = (n, n, n) := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.sum_cycleData

/-- The combinatorial Euler characteristic `c₀ + c₁ + c∞ - n` of an isomorphism class of triples. -/
noncomputable def eulerChar : IsoClass n → ℤ :=
  lift PermutationTriple.eulerChar fun _ _ => eulerChar_eq_of_equivalent

/-- Evaluating `eulerChar` on `mk t` recovers `t.eulerChar`. -/
@[simp] theorem eulerChar_mk (t : PermutationTriple n) : (mk t).eulerChar = t.eulerChar :=
  lift_mk _ _ t

/-- Expresses `c.eulerChar` in terms of `c.cycleCounts` and the degree `n`. -/
theorem eulerChar_eq_cycleCounts (c : IsoClass n) :
    c.eulerChar = (c.cycleCounts.1 : ℤ) + c.cycleCounts.2.1 + c.cycleCounts.2.2 - n := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.eulerChar_eq_cycleCounts

/-- The combinatorial Euler characteristic of any isomorphism class of triples is even. -/
theorem even_eulerChar (c : IsoClass n) : Even c.eulerChar := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.even_eulerChar

/-- The combinatorial genus `((2 - χ) / 2).toNat` of an isomorphism class of triples. -/
noncomputable def genus : IsoClass n → ℕ :=
  lift PermutationTriple.genus fun _ _ => genus_eq_of_equivalent

/-- Evaluating `genus` on `mk t` recovers `t.genus`. -/
@[simp] theorem genus_mk (t : PermutationTriple n) : (mk t).genus = t.genus := lift_mk _ _ t

/-- Expresses `c.genus` in terms of `c.eulerChar`. -/
theorem genus_def (c : IsoClass n) : c.genus = ((2 - c.eulerChar) / 2).toNat := by
  obtain ⟨t, rfl⟩ := mk_surjective c; rw [genus_mk, eulerChar_mk, PermutationTriple.genus_def]

/-- The cardinality of the automorphism group of any representative of an isomorphism class. -/
noncomputable def natCardAutomorphismGroup : IsoClass n → ℕ :=
  lift (fun t => Nat.card t.automorphismGroup) fun _ _ => natCard_automorphismGroup_eq_of_equivalent

/-- Evaluating `natCardAutomorphismGroup` on `mk t` gives `Nat.card t.automorphismGroup`. -/
@[simp] theorem natCardAutomorphismGroup_mk (t : PermutationTriple n) :
    (mk t).natCardAutomorphismGroup = Nat.card t.automorphismGroup := lift_mk _ _ t

/-- Regularity of an isomorphism class of triples: connected with transitive automorphism group. -/
def IsRegular : IsoClass n → Prop :=
  lift PermutationTriple.IsRegular fun _ _ h => propext (isRegular_iff_of_equivalent h)

/-- Evaluating `IsRegular` on `mk t` recovers `t.IsRegular`. -/
@[simp] theorem isRegular_mk (t : PermutationTriple n) : (mk t).IsRegular ↔ t.IsRegular :=
  of_eq (lift_mk _ _ t)

/-- Every regular isomorphism class of permutation triples is connected. -/
theorem IsRegular.isConnected {c : IsoClass n} (hc : c.IsRegular) : c.IsConnected := by
  obtain ⟨t, rfl⟩ := mk_surjective c; exact (isConnected_mk t).2 ((isRegular_mk t).1 hc).isConnected

end IsoClass

end PermutationTriple

/-! ### Degree zero and degree one for connected triples -/

/-- No connected permutation triple has degree zero. -/
instance : IsEmpty (ConnectedTriple 0) := ⟨fun t => t.2.ne_zero rfl⟩

/-- There are no connected isomorphism classes of permutation triples in degree zero. -/
instance : IsEmpty (ConnectedIsoClass 0) := ⟨Quotient.ind isEmptyElim⟩

/-- There is a unique connected permutation triple of degree one. -/
instance : Unique (ConnectedTriple 1) where
  default := ⟨1, PermutationTriple.isConnected_iff.2 ⟨one_ne_zero, inferInstance⟩⟩
  uniq t := Subtype.ext (Subsingleton.elim t.1 1)

/-- Up to simultaneous relabeling there is a unique connected permutation triple of degree one. -/
instance : Unique (ConnectedIsoClass 1) where
  default := ConnectedIsoClass.mk default
  uniq := Quotient.ind fun t => congrArg ConnectedIsoClass.mk (Subsingleton.elim t default)

namespace ConnectedIsoClass

variable {n : ℕ}

/-- Every degree admitting a connected isomorphism class is nonzero. -/
theorem ne_zero (c : ConnectedIsoClass n) : n ≠ 0 :=
  Quotient.ind (motive := fun _ => n ≠ 0) (fun t => t.2.ne_zero) c

/-- The ordered full cycle partitions `(λ₀, λ₁, λ∞)` of a connected isomorphism class. -/
def cycleData (c : ConnectedIsoClass n) : Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  c.forget.cycleData

/-- Evaluating `cycleData` on `mk t` recovers `t.1.cycleData`. -/
@[simp] theorem cycleData_mk (t : ConnectedTriple n) : (mk t).cycleData = t.1.cycleData := by
  simp [cycleData]

/-- Forgetting connectedness preserves `cycleData`. -/
@[simp] theorem cycleData_forget (c : ConnectedIsoClass n) : c.forget.cycleData = c.cycleData :=
  (rfl)

/-- The unordered multiset of the three full cycle partitions of a connected isomorphism class. -/
def unorderedCycleData (c : ConnectedIsoClass n) : Multiset (Multiset ℕ) :=
  c.forget.unorderedCycleData

/-- Evaluating `unorderedCycleData` on `mk t` recovers `t.1.unorderedCycleData`. -/
@[simp] theorem unorderedCycleData_mk (t : ConnectedTriple n) :
    (mk t).unorderedCycleData = t.1.unorderedCycleData := by simp [unorderedCycleData]

/-- Forgetting connectedness preserves `unorderedCycleData`. -/
@[simp] theorem unorderedCycleData_forget (c : ConnectedIsoClass n) :
    c.forget.unorderedCycleData = c.unorderedCycleData := (rfl)

/-- The ordered numbers of cycles `(c₀, c₁, c∞)` of a connected class, fixed points included. -/
noncomputable def cycleCounts (c : ConnectedIsoClass n) : ℕ × ℕ × ℕ := c.forget.cycleCounts

/-- Evaluating `cycleCounts` on `mk t` recovers `t.1.cycleCounts`. -/
@[simp] theorem cycleCounts_mk (t : ConnectedTriple n) : (mk t).cycleCounts = t.1.cycleCounts := by
  simp [cycleCounts]

/-- Forgetting connectedness preserves `cycleCounts`. -/
@[simp] theorem cycleCounts_forget (c : ConnectedIsoClass n) :
    c.forget.cycleCounts = c.cycleCounts := (rfl)

/-- Each entry of `c.cycleCounts` is the cardinality of the corresponding part of `c.cycleData`. -/
theorem cycleCounts_eq_card_cycleData (c : ConnectedIsoClass n) :
    c.cycleCounts = (c.cycleData.1.card, c.cycleData.2.1.card, c.cycleData.2.2.card) :=
  c.forget.cycleCounts_eq_card_cycleData

/-- Each of the three full cycle partitions of a connected isomorphism class sums to `n`. -/
theorem sum_cycleData (c : ConnectedIsoClass n) :
    (c.cycleData.1.sum, c.cycleData.2.1.sum, c.cycleData.2.2.sum) = (n, n, n) :=
  c.forget.sum_cycleData

/-- The combinatorial Euler characteristic `c₀ + c₁ + c∞ - n` of a connected isomorphism class. -/
noncomputable def eulerChar (c : ConnectedIsoClass n) : ℤ := c.forget.eulerChar

/-- Evaluating `eulerChar` on `mk t` recovers `t.1.eulerChar`. -/
@[simp] theorem eulerChar_mk (t : ConnectedTriple n) : (mk t).eulerChar = t.1.eulerChar := by
  simp [eulerChar]

/-- Forgetting connectedness preserves `eulerChar`. -/
@[simp] theorem eulerChar_forget (c : ConnectedIsoClass n) : c.forget.eulerChar = c.eulerChar :=
  (rfl)

/-- Expresses `c.eulerChar` in terms of `c.cycleCounts` and the degree `n`. -/
theorem eulerChar_eq_cycleCounts (c : ConnectedIsoClass n) :
    c.eulerChar = (c.cycleCounts.1 : ℤ) + c.cycleCounts.2.1 + c.cycleCounts.2.2 - n :=
  c.forget.eulerChar_eq_cycleCounts

/-- The Euler characteristic of a connected isomorphism class is even. -/
theorem even_eulerChar (c : ConnectedIsoClass n) : Even c.eulerChar := c.forget.even_eulerChar

/-- Every connected isomorphism class satisfies the Euler bound `χ ≤ 2`. -/
theorem eulerChar_le_two (c : ConnectedIsoClass n) : c.eulerChar ≤ 2 := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.2.eulerChar_le_two

/-- The combinatorial genus `(2 - χ) / 2` of a connected isomorphism class. -/
noncomputable def genus (c : ConnectedIsoClass n) : ℕ := c.forget.genus

/-- Evaluating `genus` on `mk t` recovers `t.1.genus`. -/
@[simp] theorem genus_mk (t : ConnectedTriple n) : (mk t).genus = t.1.genus := by simp [genus]

/-- Forgetting connectedness preserves `genus`. -/
@[simp] theorem genus_forget (c : ConnectedIsoClass n) : c.forget.genus = c.genus := (rfl)

/-- Expresses `c.genus` in terms of `c.eulerChar`. -/
theorem genus_def (c : ConnectedIsoClass n) : c.genus = ((2 - c.eulerChar) / 2).toNat :=
  c.forget.genus_def

/-- Coercing the genus of a connected class to `ℤ` recovers the exact quotient `(2 - χ) / 2`. -/
theorem natCast_genus (c : ConnectedIsoClass n) : (c.genus : ℤ) = (2 - c.eulerChar) / 2 := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.2.natCast_genus

/-- The Euler characteristic of a connected isomorphism class is `2 - 2 g`. -/
theorem two_sub_two_mul_genus (c : ConnectedIsoClass n) : 2 - 2 * (c.genus : ℤ) = c.eulerChar := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.2.two_sub_two_mul_genus

/-- The unique connected isomorphism class of degree `1` has genus `0`. -/
@[simp] theorem genus_of_degree_one (c : ConnectedIsoClass 1) : c.genus = 0 := by
  obtain ⟨t, rfl⟩ := mk_surjective c; simpa using t.1.genus_of_degree_one

/-- The cardinality of the automorphism group of any representative of a connected class. -/
noncomputable def natCardAutomorphismGroup (c : ConnectedIsoClass n) : ℕ :=
  c.forget.natCardAutomorphismGroup

/-- Evaluating `natCardAutomorphismGroup` on `mk t` gives `Nat.card t.1.automorphismGroup`. -/
@[simp] theorem natCardAutomorphismGroup_mk (t : ConnectedTriple n) :
    (mk t).natCardAutomorphismGroup = Nat.card t.1.automorphismGroup := by
  simp [natCardAutomorphismGroup]

/-- Forgetting connectedness preserves `natCardAutomorphismGroup`. -/
@[simp] theorem natCardAutomorphismGroup_forget (c : ConnectedIsoClass n) :
    c.forget.natCardAutomorphismGroup = c.natCardAutomorphismGroup := (rfl)

/-- For a connected isomorphism class, the order of the automorphism group divides the degree. -/
theorem natCardAutomorphismGroup_dvd (c : ConnectedIsoClass n) :
    c.natCardAutomorphismGroup ∣ n := by
  obtain ⟨t, rfl⟩ := mk_surjective c
  simpa using PermutationTriple.card_automorphismGroup_dvd t.2.isPretransitive

/-- Regularity of a connected isomorphism class: transitive automorphism action on the sheets. -/
def IsRegular (c : ConnectedIsoClass n) : Prop := c.forget.IsRegular

/-- Evaluating `IsRegular` on `mk t` recovers `t.1.IsRegular`. -/
@[simp] theorem isRegular_mk (t : ConnectedTriple n) : (mk t).IsRegular ↔ t.1.IsRegular := by
  simp [IsRegular]

/-- Forgetting connectedness preserves `IsRegular`. -/
@[simp] theorem isRegular_forget (c : ConnectedIsoClass n) : c.forget.IsRegular ↔ c.IsRegular :=
  Iff.rfl

/-- A connected isomorphism class is regular iff its automorphism group has order `n`. -/
theorem isRegular_iff_natCardAutomorphismGroup (c : ConnectedIsoClass n) :
    c.IsRegular ↔ c.natCardAutomorphismGroup = n := by
  obtain ⟨t, rfl⟩ := mk_surjective c
  simp [PermutationTriple.isRegular_iff_card_automorphismGroup, t.2]

end ConnectedIsoClass

end TauCeti

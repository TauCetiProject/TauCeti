/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Pi

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Order
import Mathlib.Tactic.Abel
import TauCeti.Algebra.Order.Group.Lattice

/-!
# Dimension groups, Riesz interpolation, and unperforation

A partially ordered abelian group `G` is a **dimension group** if it is directed, unperforated,
and satisfies the Riesz interpolation property. Dimension groups arise in operator algebra
classification as the ordered `K₀`-groups of approximately finite-dimensional (AF) C*-algebras,
and in ordered algebra as sequential positive inductive limits of simplicial groups `ℤʳ`.

This file defines `HasRieszInterpolation`, `HasRieszDecomposition`, `IsUnperforated`, and
`IsDimensionGroup`, establishes the equivalence between Riesz interpolation and Riesz
decomposition together with finite Riesz decomposition, Riesz refinement, and finite
interpolation, derives unique divisibility and torsion-freeness from unperforation, and shows
that lattice-ordered abelian groups and arbitrary products of dimension groups are dimension
groups.

## Main definitions

* `TauCeti.HasRieszInterpolation G` : Whenever `a₁, a₂ ≤ b₁, b₂` in `G`, some `c : G` satisfies
  `a₁, a₂ ≤ c ≤ b₁, b₂`.
* `TauCeti.HasRieszDecomposition G` : Whenever `0 ≤ g, a, b` and `g ≤ a + b` in `G`, `g` splits
  as `g₁ + g₂` with `0 ≤ g₁ ≤ a` and `0 ≤ g₂ ≤ b`.
* `TauCeti.IsUnperforated G` : Whenever `0 < n` and `0 ≤ n • g`, one has `0 ≤ g`.
* `TauCeti.IsDimensionGroup G` : `G` is directed, unperforated, and has Riesz interpolation.

## Main results

* `TauCeti.hasRieszInterpolation_iff_hasRieszDecomposition` : Riesz interpolation and Riesz
  decomposition are equivalent in every partially ordered abelian group.
* `TauCeti.HasRieszInterpolation.exists_finset_sum_eq_of_le_sum` : Finite Riesz decomposition for
  `0 ≤ g ≤ ∑ i ∈ s, b i`.
* `TauCeti.HasRieszInterpolation.exists_matrix_of_sum_eq_sum` : Riesz refinement for two positive
  finite decompositions with equal sum.
* `TauCeti.HasRieszInterpolation.exists_between_finsets` and
  `TauCeti.IsDimensionGroup.exists_between_finsets` : Interpolation between finite sets.
* `TauCeti.IsUnperforated.hasUniqueDiv` and `TauCeti.IsUnperforated.isAddTorsionFree` :
  Unperforated partially ordered abelian groups are torsion-free with unique divisibility.
* `TauCeti.IsDimensionGroup.of_lattice` and `TauCeti.IsDimensionGroup.pi` : Every lattice-ordered
  abelian group and every product of dimension groups is a dimension group.

## References

* E. G. Effros, D. E. Handelman, C.-L. Shen, *Dimension groups and their affine representations*,
  Amer. J. Math. **102** (1980), 385–407.
* K. R. Goodearl, F. Wehrung, *Representations of distributive semilattices in ideal lattices of
  various algebraic structures*, Algebra Universalis **45** (2001), 71–102 (arXiv:math/0011083),
  §3.
* M. Rørdam, *Classification of Nuclear C*-Algebras*, Encyclopaedia Math. Sci. **126**,
  Springer, 2002, §1.4.
* L. Fuchs, *Partially Ordered Algebraic Systems*, Pergamon Press, 1963, Chapter V.
-/

public section

namespace TauCeti

section Definitions

/-- Riesz interpolation in a preordered type: whenever `aᵢ ≤ bⱼ` for `i, j ∈ {1, 2}`, there is
`c` with `aᵢ ≤ c ≤ bⱼ` for all `i, j`. This is weaker than a join- or meet-semilattice order. -/
def HasRieszInterpolation (G : Type*) [Preorder G] : Prop :=
  ∀ a₁ a₂ b₁ b₂ : G,
    a₁ ≤ b₁ → a₁ ≤ b₂ → a₂ ≤ b₁ → a₂ ≤ b₂ →
    ∃ c : G, a₁ ≤ c ∧ a₂ ≤ c ∧ c ≤ b₁ ∧ c ≤ b₂

/-- Riesz decomposition in a preordered additive commutative monoid: whenever `0 ≤ g ≤ a + b`
with `0 ≤ a` and `0 ≤ b`, there exist `g₁, g₂` with `0 ≤ g₁ ≤ a`, `0 ≤ g₂ ≤ b`, and
`g = g₁ + g₂`. -/
def HasRieszDecomposition (G : Type*) [AddCommMonoid G] [Preorder G] : Prop :=
  ∀ ⦃g a b : G⦄, 0 ≤ g → 0 ≤ a → 0 ≤ b → g ≤ a + b →
    ∃ g₁ g₂ : G, 0 ≤ g₁ ∧ g₁ ≤ a ∧ 0 ≤ g₂ ∧ g₂ ≤ b ∧ g = g₁ + g₂

/-- Unperforation of a preordered additive commutative monoid: `0 ≤ n • g` with `0 < n` forces
`0 ≤ g`. -/
def IsUnperforated (G : Type*) [AddCommMonoid G] [Preorder G] : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ g : G, 0 ≤ n • g → 0 ≤ g

/-- A dimension group: a directed, unperforated partially ordered abelian group satisfying Riesz
interpolation. Countability and a scale are separate data. -/
structure IsDimensionGroup (G : Type*) [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] : Prop where
  /-- A dimension group is upward-directed. -/
  isDirected : IsDirected G (· ≤ ·)
  /-- A dimension group is unperforated. -/
  isUnperforated : IsUnperforated G
  /-- A dimension group has the Riesz interpolation property. -/
  hasRieszInterpolation : HasRieszInterpolation G

end Definitions

section RieszOrder

variable {G : Type*} [Preorder G]

/-- Unfolding characterization of `HasRieszInterpolation`. -/
theorem hasRieszInterpolation_def :
    HasRieszInterpolation G ↔
      ∀ a₁ a₂ b₁ b₂ : G, a₁ ≤ b₁ → a₁ ≤ b₂ → a₂ ≤ b₁ → a₂ ≤ b₂ →
        ∃ c : G, a₁ ≤ c ∧ a₂ ≤ c ∧ c ≤ b₁ ∧ c ≤ b₂ :=
  (Iff.rfl)

namespace HasRieszInterpolation

/-- Interpolate an element between two lower bounds and two upper bounds. -/
theorem exists_between (hr : HasRieszInterpolation G) {a₁ a₂ b₁ b₂ : G}
    (h₁₁ : a₁ ≤ b₁) (h₁₂ : a₁ ≤ b₂) (h₂₁ : a₂ ≤ b₁) (h₂₂ : a₂ ≤ b₂) :
    ∃ c : G, a₁ ≤ c ∧ a₂ ≤ c ∧ c ≤ b₁ ∧ c ≤ b₂ :=
  hr a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂

private theorem exists_between_finsets_two (hr : HasRieszInterpolation G)
    {A : Finset G} (hA : A.Nonempty) {b₁ b₂ : G}
    (hle : ∀ a ∈ A, a ≤ b₁ ∧ a ≤ b₂) :
    ∃ c : G, (∀ a ∈ A, a ≤ c) ∧ c ≤ b₁ ∧ c ≤ b₂ := by
  induction hA using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact ⟨a, by simp, (hle a (Finset.mem_singleton_self a)).1,
      (hle a (Finset.mem_singleton_self a)).2⟩
  | cons a A ha _ ih =>
    obtain ⟨c', hc', hc'₁, hc'₂⟩ := ih fun x hx => hle x (Finset.mem_cons_of_mem hx)
    have ha' := hle a (Finset.mem_cons_self a A)
    obtain ⟨c, hac, hc'c, hcb₁, hcb₂⟩ := hr a c' b₁ b₂ ha'.1 ha'.2 hc'₁ hc'₂
    refine ⟨c, fun x hx => ?_, hcb₁, hcb₂⟩
    rcases Finset.mem_cons.mp hx with rfl | hx'
    · exact hac
    · exact (hc' x hx').trans hc'c

/-- Finite Riesz interpolation: if `A` and `B` are nonempty finite subsets of `G` with `a ≤ b`
for all `a ∈ A` and `b ∈ B`, some `c : G` satisfies `a ≤ c ≤ b` for all `a ∈ A` and `b ∈ B`. -/
theorem exists_between_finsets (hr : HasRieszInterpolation G)
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hle : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    ∃ c : G, (∀ a ∈ A, a ≤ c) ∧ (∀ b ∈ B, c ≤ b) := by
  induction hB using Finset.Nonempty.cons_induction with
  | singleton b =>
    obtain ⟨c, hcA, hcb, _⟩ :=
      hr.exists_between_finsets_two hA (b₁ := b) (b₂ := b) fun a ha =>
        ⟨hle a ha b (Finset.mem_singleton_self b), hle a ha b (Finset.mem_singleton_self b)⟩
    exact ⟨c, hcA, by simpa using hcb⟩
  | cons b B hb _ ih =>
    obtain ⟨c', hc'A, hc'B⟩ := ih fun a ha x hx => hle a ha x (Finset.mem_cons_of_mem hx)
    obtain ⟨c, hcA, hcb, hcc'⟩ :=
      hr.exists_between_finsets_two hA (b₁ := b) (b₂ := c') fun a ha =>
        ⟨hle a ha b (Finset.mem_cons_self b B), hc'A a ha⟩
    refine ⟨c, hcA, fun x hx => ?_⟩
    rcases Finset.mem_cons.mp hx with rfl | hx'
    · exact hcb
    · exact hcc'.trans (hc'B x hx')

end HasRieszInterpolation

end RieszOrder

section RieszMonoid

section PreorderMonoid

variable {G : Type*} [AddCommMonoid G] [Preorder G]

/-- Unfolding characterization of `HasRieszDecomposition`. -/
theorem hasRieszDecomposition_def :
    HasRieszDecomposition G ↔
      ∀ ⦃g a b : G⦄, 0 ≤ g → 0 ≤ a → 0 ≤ b → g ≤ a + b →
        ∃ g₁ g₂ : G, 0 ≤ g₁ ∧ g₁ ≤ a ∧ 0 ≤ g₂ ∧ g₂ ≤ b ∧ g = g₁ + g₂ :=
  (Iff.rfl)

/-- Split a nonnegative element bounded by `a + b` into nonnegative summands bounded by `a` and
`b`. -/
theorem HasRieszDecomposition.exists_add_eq (hd : HasRieszDecomposition G) {g a b : G}
    (hg : 0 ≤ g) (ha : 0 ≤ a) (hb : 0 ≤ b) (hle : g ≤ a + b) :
    ∃ g₁ g₂ : G, 0 ≤ g₁ ∧ g₁ ≤ a ∧ 0 ≤ g₂ ∧ g₂ ≤ b ∧ g = g₁ + g₂ :=
  hd hg ha hb hle

end PreorderMonoid

/-- Finite Riesz decomposition in a partially ordered additive commutative monoid: if
`0 ≤ g ≤ ∑ i ∈ s, b i` with `0 ≤ b i` on `s`, then `g` decomposes as `∑ i ∈ s, d i` with
`0 ≤ d i ≤ b i` on `s`. -/
theorem HasRieszDecomposition.exists_finset_sum_eq_of_le_sum
    {G : Type*} [AddCommMonoid G] [PartialOrder G] [IsOrderedAddMonoid G] {ι : Type*}
    (hd : HasRieszDecomposition G) {s : Finset ι} {b : ι → G} (hb : ∀ i ∈ s, 0 ≤ b i)
    {g : G} (hg : 0 ≤ g) (hle : g ≤ ∑ i ∈ s, b i) :
    ∃ d : ι → G, (∀ i ∈ s, 0 ≤ d i ∧ d i ≤ b i) ∧ ∑ i ∈ s, d i = g := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty =>
    rw [Finset.sum_empty] at hle
    obtain rfl := le_antisymm hle hg
    exact ⟨0, by simp, Finset.sum_empty⟩
  | @insert i₀ s hi₀ ih =>
    rw [Finset.sum_insert hi₀] at hle
    have hb₀ : 0 ≤ b i₀ := hb i₀ (Finset.mem_insert_self i₀ s)
    have hbs : ∀ i ∈ s, 0 ≤ b i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    obtain ⟨g₁, g₂, hg₁₀, hg₁b, hg₂₀, hg₂s, rfl⟩ :=
      hd hg hb₀ (Finset.sum_nonneg hbs) hle
    obtain ⟨d, hds, hdsum⟩ := ih hbs hg₂₀ hg₂s
    refine ⟨Function.update d i₀ g₁, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · simpa using ⟨hg₁₀, hg₁b⟩
      · simpa [ne_of_mem_of_not_mem hi' hi₀] using hds i hi'
    · rw [Finset.sum_insert hi₀, Function.update_self,
        Finset.sum_congr rfl fun i hi => Function.update_of_ne (ne_of_mem_of_not_mem hi hi₀) g₁ d,
        hdsum]

end RieszMonoid

section RieszGroup

section PreorderGroup

variable {G : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]

/-- Riesz interpolation implies Riesz decomposition. -/
theorem HasRieszInterpolation.hasRieszDecomposition (hr : HasRieszInterpolation G) :
    HasRieszDecomposition G := by
  intro g a b hg ha hb hle
  obtain ⟨g₁, hg₁₀, hgb, hg₁a, hg₁g⟩ :=
    hr 0 (g - b) a g ha hg (sub_le_iff_le_add.mpr hle) (sub_le_self g hb)
  exact ⟨g₁, g - g₁, hg₁₀, hg₁a, sub_nonneg.mpr hg₁g, sub_le_comm.mp hgb,
    (add_sub_cancel g₁ g).symm⟩

/-- Riesz decomposition implies Riesz interpolation. -/
theorem HasRieszDecomposition.hasRieszInterpolation (hd : HasRieszDecomposition G) :
    HasRieszInterpolation G := by
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  have hbound : b₁ - a₁ ≤ (b₁ - a₂) + (b₂ - a₁) := by
    have h := add_le_add_left (sub_nonneg.mpr h₂₂) (b₁ - a₁)
    have hRearr : b₂ - a₂ + (b₁ - a₁) = (b₁ - a₂) + (b₂ - a₁) := by abel
    rwa [zero_add, hRearr] at h
  obtain ⟨g₁, g₂, hg₁₀, hg₁, hg₂₀, hg₂, hsum⟩ :=
    hd (sub_nonneg.mpr h₁₁) (sub_nonneg.mpr h₂₁) (sub_nonneg.mpr h₁₂) hbound
  have hc : a₁ + g₂ = b₁ - g₁ := by
    apply eq_sub_of_add_eq
    calc
      a₁ + g₂ + g₁ = a₁ + (g₁ + g₂) := by abel
      _ = a₁ + (b₁ - a₁) := by rw [← hsum]
      _ = b₁ := add_sub_cancel a₁ b₁
  refine ⟨a₁ + g₂, le_add_of_nonneg_right hg₂₀, ?_, ?_, le_sub_iff_add_le'.mp hg₂⟩
  · rw [hc]
    exact le_sub_comm.mp hg₁
  · rw [hc]
    exact sub_le_self b₁ hg₁₀

/-- Riesz interpolation and Riesz decomposition are equivalent in every preordered abelian
group. -/
theorem hasRieszInterpolation_iff_hasRieszDecomposition :
    HasRieszInterpolation G ↔ HasRieszDecomposition G :=
  ⟨HasRieszInterpolation.hasRieszDecomposition, HasRieszDecomposition.hasRieszInterpolation⟩

end PreorderGroup

namespace HasRieszInterpolation

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Finite Riesz decomposition: if `0 ≤ g ≤ ∑ i ∈ s, b i` with `0 ≤ b i` for each `i ∈ s`, then
`g` decomposes as `∑ i ∈ s, d i` with `0 ≤ d i ≤ b i` on `s`. -/
theorem exists_finset_sum_eq_of_le_sum {ι : Type*} (hr : HasRieszInterpolation G)
    {s : Finset ι} {b : ι → G} (hb : ∀ i ∈ s, 0 ≤ b i) {g : G} (hg : 0 ≤ g)
    (hle : g ≤ ∑ i ∈ s, b i) :
    ∃ d : ι → G, (∀ i ∈ s, 0 ≤ d i ∧ d i ≤ b i) ∧ ∑ i ∈ s, d i = g :=
  hr.hasRieszDecomposition.exists_finset_sum_eq_of_le_sum hb hg hle

/-- Riesz refinement: if two nonnegative finite families have the same sum, there is a nonnegative
matrix refining both. -/
theorem exists_matrix_of_sum_eq_sum {ι κ : Type*} (hr : HasRieszInterpolation G)
    {s : Finset ι} {t : Finset κ} {a : ι → G} {b : κ → G}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ t, 0 ≤ b j)
    (hsum : ∑ i ∈ s, a i = ∑ j ∈ t, b j) :
    ∃ c : ι → κ → G,
      (∀ i ∈ s, ∀ j ∈ t, 0 ≤ c i j) ∧
      (∀ i ∈ s, ∑ j ∈ t, c i j = a i) ∧
      (∀ j ∈ t, ∑ i ∈ s, c i j = b j) := by
  classical
  induction s using Finset.induction_on generalizing b with
  | empty =>
    rw [Finset.sum_empty] at hsum
    have hb0 : ∀ j ∈ t, b j = 0 := (Finset.sum_eq_zero_iff_of_nonneg hb).mp hsum.symm
    exact ⟨fun _ _ => 0, by simp, by simp, fun j hj => by simp [hb0 j hj]⟩
  | @insert i₀ s hi₀ ih =>
    rw [Finset.sum_insert hi₀] at hsum
    have hai₀ : 0 ≤ a i₀ := ha i₀ (Finset.mem_insert_self i₀ s)
    have has : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hai₀_le : a i₀ ≤ ∑ j ∈ t, b j := by
      rw [← hsum]
      exact le_add_of_nonneg_right (Finset.sum_nonneg has)
    obtain ⟨d, hd, hdt⟩ := hr.exists_finset_sum_eq_of_le_sum hb hai₀ hai₀_le
    have hb' : ∀ j ∈ t, 0 ≤ b j - d j := fun j hj => sub_nonneg.mpr (hd j hj).2
    have hsum' : ∑ i ∈ s, a i = ∑ j ∈ t, (b j - d j) := by
      rw [Finset.sum_sub_distrib, ← hsum, hdt, add_sub_cancel_left]
    obtain ⟨c, hc₀, hca, hcb⟩ := ih has hb' hsum'
    refine ⟨Function.update c i₀ d, ?_, ?_, ?_⟩
    · intro i hi j hj
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · simpa using (hd j hj).1
      · simpa [ne_of_mem_of_not_mem hi' hi₀] using hc₀ i hi' j hj
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · simpa using hdt
      · simpa [ne_of_mem_of_not_mem hi' hi₀] using hca i hi'
    · intro j hj
      rw [Finset.sum_insert hi₀, Function.update_self,
        Finset.sum_congr rfl fun i hi =>
          congrFun (Function.update_of_ne (ne_of_mem_of_not_mem hi hi₀) d c) j,
        hcb j hj, add_sub_cancel]

end HasRieszInterpolation

end RieszGroup

section Unperforated

section Monoid

variable {G : Type*} [AddCommMonoid G] [Preorder G]

/-- Unfolding characterization of `IsUnperforated`. -/
theorem isUnperforated_def :
    IsUnperforated G ↔ ∀ (n : ℕ), 0 < n → ∀ g : G, 0 ≤ n • g → 0 ≤ g :=
  (Iff.rfl)

/-- In an unperforated additive commutative monoid, `0 ≤ n • g` with `n ≠ 0` implies `0 ≤ g`. -/
theorem IsUnperforated.nonneg_of_nsmul_nonneg (hu : IsUnperforated G) {n : ℕ} (hn : n ≠ 0) {g : G}
    (hg : 0 ≤ n • g) : 0 ≤ g :=
  hu n (Nat.pos_of_ne_zero hn) g hg

/-- In an unperforated ordered additive commutative monoid, `0 ≤ n • g ↔ 0 ≤ g` for every
`n : ℕ` with `n ≠ 0`. -/
theorem IsUnperforated.nsmul_nonneg_iff [IsOrderedAddMonoid G] (hu : IsUnperforated G) {n : ℕ}
    (hn : n ≠ 0) {g : G} :
    0 ≤ n • g ↔ 0 ≤ g :=
  ⟨hu.nonneg_of_nsmul_nonneg hn, fun hg => nsmul_nonneg hg n⟩

end Monoid

namespace IsUnperforated

section PreorderGroup

variable {G : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]

/-- In an unperforated preordered abelian group, `n • a ≤ n • b ↔ a ≤ b` for every `n : ℕ` with
`n ≠ 0`. -/
theorem nsmul_le_nsmul_iff_right (hu : IsUnperforated G) {n : ℕ} (hn : n ≠ 0) {a b : G} :
    n • a ≤ n • b ↔ a ≤ b := by
  rw [← sub_nonneg, ← nsmul_sub, hu.nsmul_nonneg_iff hn, sub_nonneg]

/-- In an unperforated preordered abelian group, `0 ≤ n • g ↔ 0 ≤ g` for every positive integer
`n : ℤ`. -/
theorem zsmul_nonneg_iff (hu : IsUnperforated G) {n : ℤ} (hn : 0 < n) {g : G} :
    0 ≤ n • g ↔ 0 ≤ g := by
  lift n to ℕ using hn.le
  rw [natCast_zsmul]
  exact hu.nsmul_nonneg_iff (Int.natCast_pos.mp hn).ne'

/-- In an unperforated preordered abelian group, `n • a ≤ n • b ↔ a ≤ b` for every positive
integer `n : ℤ`. -/
theorem zsmul_le_zsmul_iff_right (hu : IsUnperforated G) {n : ℤ} (hn : 0 < n) {a b : G} :
    n • a ≤ n • b ↔ a ≤ b := by
  rw [← sub_nonneg, ← zsmul_sub, hu.zsmul_nonneg_iff hn, sub_nonneg]

end PreorderGroup

section PartialOrderGroup

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Every unperforated partially ordered abelian group has unique divisibility. -/
theorem hasUniqueDiv (hu : IsUnperforated G) : HasUniqueDiv G where
  nsmul_right_injective _ hn _ _ hab :=
    le_antisymm
      ((hu.nsmul_le_nsmul_iff_right hn).mp hab.le)
      ((hu.nsmul_le_nsmul_iff_right hn).mp hab.ge)

/-- Every unperforated partially ordered abelian group is torsion-free. -/
theorem isAddTorsionFree (hu : IsUnperforated G) : IsAddTorsionFree G := by
  have := hu.hasUniqueDiv
  infer_instance

end PartialOrderGroup

end IsUnperforated

end Unperforated

section DimensionGroup

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Unfolding characterization of `IsDimensionGroup`. -/
theorem isDimensionGroup_def :
    IsDimensionGroup G ↔
      IsDirected G (· ≤ ·) ∧ IsUnperforated G ∧ HasRieszInterpolation G :=
  ⟨fun h => ⟨h.isDirected, h.isUnperforated, h.hasRieszInterpolation⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

namespace IsDimensionGroup

/-- A dimension group is downward-directed. -/
theorem isCodirectedOrder (hd : IsDimensionGroup G) : IsCodirectedOrder G :=
  ⟨fun a b =>
    let ⟨c, ha, hb⟩ := hd.isDirected.directed (-a) (-b)
    ⟨-c, neg_le.mp ha, neg_le.mp hb⟩⟩

/-- A dimension group has the Riesz decomposition property. -/
theorem hasRieszDecomposition (hd : IsDimensionGroup G) : HasRieszDecomposition G :=
  hd.hasRieszInterpolation.hasRieszDecomposition

/-- A dimension group has unique divisibility. -/
theorem hasUniqueDiv (hd : IsDimensionGroup G) : HasUniqueDiv G :=
  hd.isUnperforated.hasUniqueDiv

/-- A dimension group is torsion-free. -/
theorem isAddTorsionFree (hd : IsDimensionGroup G) : IsAddTorsionFree G :=
  hd.isUnperforated.isAddTorsionFree

/-- Finite interpolation in a dimension group: for arbitrary finite subsets `A` and `B` of `G`
with `a ≤ b` for all `a ∈ A` and `b ∈ B`, there exists `c : G` with `a ≤ c ≤ b` for all `a ∈ A`
and `b ∈ B`. Unlike `HasRieszInterpolation.exists_between_finsets`, `A` and `B` may be empty. -/
theorem exists_between_finsets (hd : IsDimensionGroup G) (A B : Finset G)
    (hle : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    ∃ c : G, (∀ a ∈ A, a ≤ c) ∧ (∀ b ∈ B, c ≤ b) := by
  have : IsDirectedOrder G := hd.isDirected
  have : IsCodirectedOrder G := hd.isCodirectedOrder
  rcases A.eq_empty_or_nonempty with rfl | hA
  · obtain ⟨c, hcB⟩ := Finset.exists_ge B
    exact ⟨c, by simp, hcB⟩
  · rcases B.eq_empty_or_nonempty with rfl | hB
    · obtain ⟨c, hcA⟩ := Finset.exists_le A
      exact ⟨c, hcA, by simp⟩
    · exact hd.hasRieszInterpolation.exists_between_finsets hA hB hle

end IsDimensionGroup

end DimensionGroup

section Isomorphism

/-- Riesz interpolation transfers across any order isomorphism between preorders. -/
theorem HasRieszInterpolation.of_orderIso {F G H : Type*} [Preorder G] [Preorder H]
    (hr : HasRieszInterpolation G) [EquivLike F G H] [OrderIsoClass F G H] (e : F) :
    HasRieszInterpolation H := by
  let e' : G ≃o H := OrderIso.ofClass e
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  obtain ⟨c, hc₁, hc₂, hc₃, hc₄⟩ :=
    hr (e'.symm a₁) (e'.symm a₂) (e'.symm b₁) (e'.symm b₂)
      (e'.symm.monotone h₁₁) (e'.symm.monotone h₁₂)
      (e'.symm.monotone h₂₁) (e'.symm.monotone h₂₂)
  refine ⟨e' c, ?_, ?_, ?_, ?_⟩
  · simpa using e'.monotone hc₁
  · simpa using e'.monotone hc₂
  · simpa using e'.monotone hc₃
  · simpa using e'.monotone hc₄

/-- Order-isomorphic preorders simultaneously satisfy or fail Riesz interpolation. -/
theorem hasRieszInterpolation_iff_of_orderIso {F G H : Type*} [Preorder G] [Preorder H]
    [EquivLike F G H] [OrderIsoClass F G H] (e : F) :
    HasRieszInterpolation G ↔ HasRieszInterpolation H :=
  ⟨fun h => h.of_orderIso e, fun h => h.of_orderIso (OrderIso.ofClass e).symm⟩

/-- Unperforation transfers across any ordered additive monoid isomorphism. -/
theorem IsUnperforated.of_orderAddMonoidIso {F G H : Type*}
    [AddCommMonoid G] [Preorder G] [AddCommMonoid H] [Preorder H]
    (hu : IsUnperforated G)
    [EquivLike F G H] [AddEquivClass F G H] [OrderIsoClass F G H] (e : F) :
    IsUnperforated H := by
  let e' : G ≃+o H := e
  intro n hn g hg
  have hg' : 0 ≤ n • e'.symm g := by
    rw [← map_nsmul e'.symm, ← map_zero e'.symm]
    exact (map_le_map_iff e'.symm).mpr hg
  simpa [map_zero] using (map_le_map_iff e').mpr (hu n hn (e'.symm g) hg')

/-- Ordered-monoid-isomorphic preordered additive commutative monoids simultaneously satisfy or
fail unperforation. -/
theorem isUnperforated_iff_of_orderAddMonoidIso {F G H : Type*}
    [AddCommMonoid G] [Preorder G] [AddCommMonoid H] [Preorder H]
    [EquivLike F G H] [AddEquivClass F G H] [OrderIsoClass F G H] (e : F) :
    IsUnperforated G ↔ IsUnperforated H :=
  ⟨fun h => h.of_orderAddMonoidIso e, fun h => h.of_orderAddMonoidIso (e : G ≃+o H).symm⟩

/-- Being a dimension group transfers across any ordered additive group isomorphism. -/
theorem IsDimensionGroup.of_orderAddMonoidIso {F G H : Type*}
    [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    (hd : IsDimensionGroup G)
    [EquivLike F G H] [AddEquivClass F G H] [OrderIsoClass F G H] (e : F) :
    IsDimensionGroup H := by
  let e' : G ≃+o H := e
  refine ⟨⟨fun a b => ?_⟩, hd.isUnperforated.of_orderAddMonoidIso e,
    hd.hasRieszInterpolation.of_orderIso e⟩
  obtain ⟨c, ha, hb⟩ := hd.isDirected.directed (e'.symm a) (e'.symm b)
  exact ⟨e' c, by simpa using (map_le_map_iff e').mpr ha,
    by simpa using (map_le_map_iff e').mpr hb⟩

/-- Ordered-group-isomorphic partially ordered abelian groups are simultaneously dimension
groups. -/
theorem isDimensionGroup_iff_of_orderAddMonoidIso {F G H : Type*}
    [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [EquivLike F G H] [AddEquivClass F G H] [OrderIsoClass F G H] (e : F) :
    IsDimensionGroup G ↔ IsDimensionGroup H :=
  ⟨fun h => h.of_orderAddMonoidIso e, fun h => h.of_orderAddMonoidIso (e : G ≃+o H).symm⟩

end Isomorphism

section Examples

/-- Every join-semilattice satisfies Riesz interpolation via binary suprema. -/
theorem HasRieszInterpolation.of_semilatticeSup (G : Type*) [SemilatticeSup G] :
    HasRieszInterpolation G :=
  fun a₁ a₂ _ _ h₁₁ h₁₂ h₂₁ h₂₂ =>
    ⟨a₁ ⊔ a₂, le_sup_left, le_sup_right, sup_le h₁₁ h₂₁, sup_le h₁₂ h₂₂⟩

/-- Every lattice-ordered abelian group is unperforated (Fuchs, *Partially Ordered Algebraic
Systems*, Chapter V, §1.E). -/
theorem IsUnperforated.of_lattice (G : Type*) [AddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] : IsUnperforated G :=
  fun _ hn _ hg => (nsmul_nonneg_iff_of_lattice hn.ne').mp hg

/-- Every lattice-ordered abelian group is a dimension group. -/
theorem IsDimensionGroup.of_lattice (G : Type*) [AddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] : IsDimensionGroup G :=
  ⟨inferInstance, IsUnperforated.of_lattice G, HasRieszInterpolation.of_semilatticeSup G⟩

/-- Any subsingleton partially ordered abelian group is a dimension group. -/
theorem IsDimensionGroup.of_subsingleton (G : Type*) [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] [Subsingleton G] : IsDimensionGroup G :=
  ⟨⟨fun a _ => ⟨a, (Subsingleton.elim _ _).le, (Subsingleton.elim _ _).le⟩⟩,
    fun _ _ _ _ => (Subsingleton.elim _ _).le,
    fun a _ _ _ _ _ _ _ =>
      ⟨a, le_rfl, (Subsingleton.elim _ _).le, (Subsingleton.elim _ _).le,
        (Subsingleton.elim _ _).le⟩⟩

/-- Riesz interpolation passes to arbitrary products of preorders. -/
theorem HasRieszInterpolation.pi {ι : Type*} {G : ι → Type*} [∀ i, Preorder (G i)]
    (hr : ∀ i, HasRieszInterpolation (G i)) : HasRieszInterpolation (∀ i, G i) := by
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  choose c hc₁ hc₂ hc₃ hc₄ using fun i => hr i (a₁ i) (a₂ i) (b₁ i) (b₂ i)
    (h₁₁ i) (h₁₂ i) (h₂₁ i) (h₂₂ i)
  exact ⟨c, hc₁, hc₂, hc₃, hc₄⟩

/-- Unperforation passes to arbitrary products of preordered additive commutative monoids. -/
theorem IsUnperforated.pi {ι : Type*} {G : ι → Type*}
    [∀ i, AddCommMonoid (G i)] [∀ i, Preorder (G i)]
    (hu : ∀ i, IsUnperforated (G i)) : IsUnperforated (∀ i, G i) :=
  fun n hn g hg i => hu i n hn (g i) (hg i)

/-- Every product of dimension groups is a dimension group. -/
theorem IsDimensionGroup.pi {ι : Type*} {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, PartialOrder (G i)] [∀ i, IsOrderedAddMonoid (G i)]
    (hd : ∀ i, IsDimensionGroup (G i)) : IsDimensionGroup (∀ i, G i) := by
  refine ⟨⟨fun a b => ?_⟩,
    IsUnperforated.pi fun i => (hd i).isUnperforated,
    HasRieszInterpolation.pi fun i => (hd i).hasRieszInterpolation⟩
  choose c ha hb using fun i => (hd i).isDirected.directed (a i) (b i)
  exact ⟨c, ha, hb⟩

/-- Every simplicial group `ι → ℤ` with the pointwise order is a dimension group. -/
theorem isDimensionGroup_pi_int (ι : Type*) : IsDimensionGroup (ι → ℤ) :=
  IsDimensionGroup.pi fun _ => IsDimensionGroup.of_lattice ℤ

end Examples

end TauCeti

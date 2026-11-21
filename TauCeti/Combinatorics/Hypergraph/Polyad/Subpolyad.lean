/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic
import Mathlib.Tactic.FinCases

/-!
# Subpolyads of a triadic polyad

A `Subpolyad3 P` selects arbitrary subgraphs of the three pair supports of `P`. Its triple
support is computed by requiring all three coordinate pairs to be selected. These are the
subtriad tests used in hypergraph regularity; restricting the three vertex cells is only a
special case, supplied by `Subpolyad3.ofSubcells`.

Subpolyads are extensional in their three selected pair graphs and form a finite type, even
without a finite pair palette, of exact cardinality
`2 ^ (#pairSupport₀₁ + #pairSupport₀₂ + #pairSupport₁₂)` (`TauCeti.card_subpolyad3_eq`), bounded
in terms of cell sizes by `TauCeti.card_subpolyad3_le_mul_card` and in terms of `|V|` by
`TauCeti.card_subpolyad3_le`. Their supports lie in the parent support. Nonempty finite
intersections are formed coordinatewise and their supports are the intersections of the supports.
The subcell constructor accepts arbitrary vertex sets and intersects with the parent pair supports,
so no containment hypotheses are needed. `Subpolyad3.unionSupport` collects the supports
of a finite family. A family of at most `r` members has the same union as one indexed by `Fin r`.
When the pair graphs of a polyad `P'`, possibly over another skeleton, lie in those of `P`,
`Subpolyad3.inclusion` regards each subpolyad of `P'` as a subpolyad of `P` with the same
support. For arbitrary polyads `P` and `P'`, `Subpolyad3.restrict` intersects the selected pair
graphs with those of `P`; the resulting support is the part of the original one lying in `P`.
The role-indexed pair graph `Subpolyad3.pairGraph` accesses all directed role pairs uniformly, and
`Subpolyad3.cast_pairGraph`, `Subpolyad3.cast_support`, and `Subpolyad3.unionSupport_cast`
transport subpolyad data along equalities of parent polyads.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*.
* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*.
* C. Terry, *Growth of regular partitions 4: strong regularity and the pairs partition*,
  arXiv:2404.02030.
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V}

/-- A subpolyad selects arbitrary subgraphs of the three canonically oriented pair graphs of
its parent. Its triple support is derived, not independently chosen. -/
structure Subpolyad3 (P : Polyad3 S) where
  /-- The selected pairs on roles zero and one. -/
  pair₀₁ : Finset {p : V × V // p.1 ≠ p.2}
  /-- The selected pairs on roles zero and two. -/
  pair₀₂ : Finset {p : V × V // p.1 ≠ p.2}
  /-- The selected pairs on roles one and two. -/
  pair₁₂ : Finset {p : V × V // p.1 ≠ p.2}
  /-- The selected zero-one pairs belong to the parent pair graph. -/
  pair₀₁_sub : pair₀₁ ⊆ P.pairSupport₀₁
  /-- The selected zero-two pairs belong to the parent pair graph. -/
  pair₀₂_sub : pair₀₂ ⊆ P.pairSupport₀₂
  /-- The selected one-two pairs belong to the parent pair graph. -/
  pair₁₂_sub : pair₁₂ ⊆ P.pairSupport₁₂

/-- The parent triples whose three coordinate pairs lie in three prescribed pair sets. -/
noncomputable def subpolyadSupport (P : Polyad3 S)
    (q₀₁ q₀₂ q₁₂ : Finset {p : V × V // p.1 ≠ p.2}) :
    Finset {x : Fin 3 → V // Function.Injective x} :=
  P.support.filter fun x ↦
    coordPair x 0 1 (by decide) ∈ q₀₁ ∧ coordPair x 0 2 (by decide) ∈ q₀₂ ∧
      coordPair x 1 2 (by decide) ∈ q₁₂

/-- Membership in a computed subpolyad support. -/
@[simp]
theorem mem_subpolyadSupport {P : Polyad3 S}
    {q₀₁ q₀₂ q₁₂ : Finset {p : V × V // p.1 ≠ p.2}}
    {x : {x : Fin 3 → V // Function.Injective x}} :
    x ∈ subpolyadSupport P q₀₁ q₀₂ q₁₂ ↔ x ∈ P.support ∧
      coordPair x 0 1 (by decide) ∈ q₀₁ ∧ coordPair x 0 2 (by decide) ∈ q₀₂ ∧
        coordPair x 1 2 (by decide) ∈ q₁₂ := by
  simp [subpolyadSupport]

namespace Subpolyad3

variable {P : Polyad3 S}

/-- Two subpolyads agree precisely when their three selected pair graphs agree. -/
@[ext]
theorem ext_data {Q R : Subpolyad3 P} (h₀₁ : Q.pair₀₁ = R.pair₀₁)
    (h₀₂ : Q.pair₀₂ = R.pair₀₂) (h₁₂ : Q.pair₁₂ = R.pair₁₂) : Q = R := by
  cases Q
  cases R
  simp only at h₀₁ h₀₂ h₁₂
  subst h₀₁
  subst h₀₂
  subst h₁₂
  rfl

private theorem pairData_injective : Function.Injective
    (fun Q : Subpolyad3 P ↦ (Q.pair₀₁, Q.pair₀₂, Q.pair₁₂)) := by
  intro Q R h
  simp only [Prod.mk.injEq] at h
  exact ext_data h.1 h.2.1 h.2.2

/-- Equality of subpolyads is decidable without a decidable pair palette. -/
@[no_expose] instance : DecidableEq (Subpolyad3 P) :=
  pairData_injective.decidableEq

/-- A finite host admits only finitely many subpolyads of any fixed polyad. -/
@[no_expose] noncomputable instance : Fintype (Subpolyad3 P) :=
  Fintype.ofInjective _ pairData_injective

end Subpolyad3

/-- The exact number of subpolyads of a polyad `P` is
`2 ^ (#pairSupport₀₁ + #pairSupport₀₂ + #pairSupport₁₂)`. -/
theorem card_subpolyad3_eq (P : Polyad3 S) :
    Fintype.card (Subpolyad3 P) =
      2 ^ (#P.pairSupport₀₁ + #P.pairSupport₀₂ + #P.pairSupport₁₂) := by
  let e : Subpolyad3 P ≃
      P.pairSupport₀₁.powerset × P.pairSupport₀₂.powerset × P.pairSupport₁₂.powerset :=
    { toFun := fun Q ↦
        (⟨Q.pair₀₁, mem_powerset.2 Q.pair₀₁_sub⟩,
          ⟨Q.pair₀₂, mem_powerset.2 Q.pair₀₂_sub⟩,
          ⟨Q.pair₁₂, mem_powerset.2 Q.pair₁₂_sub⟩)
      invFun := fun ⟨q₀₁, q₀₂, q₁₂⟩ ↦
        ⟨q₀₁.val, q₀₂.val, q₁₂.val, mem_powerset.1 q₀₁.property, mem_powerset.1 q₀₂.property,
          mem_powerset.1 q₁₂.property⟩
      left_inv := fun _ ↦ Subpolyad3.ext_data rfl rfl rfl
      right_inv := fun ⟨_, _, _⟩ ↦ rfl }
  rw [Fintype.card_congr e]
  simp [pow_add, mul_assoc, -mem_powerset]

/-- The number of subpolyads of a polyad `P` is at most
`2 ^ (#P.c₀ * #P.c₁ + #P.c₀ * #P.c₂ + #P.c₁ * #P.c₂)`. -/
theorem card_subpolyad3_le_mul_card (P : Polyad3 S) :
    Fintype.card (Subpolyad3 P) ≤ 2 ^ (#P.c₀ * #P.c₁ + #P.c₀ * #P.c₂ + #P.c₁ * #P.c₂) := by
  have hle {A B : Finset V} {E : Finset {p : V × V // p.1 ≠ p.2}}
      (hE : ∀ p ∈ E, p.val.1 ∈ A ∧ p.val.2 ∈ B) : #E ≤ #A * #B := by
    rw [← card_product]
    exact card_le_card_of_injOn (fun p ↦ p.val) (fun p hp ↦ mem_product.2 (hE p hp))
      Subtype.val_injective.injOn
  rw [card_subpolyad3_eq]
  refine Nat.pow_le_pow_right two_pos (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_)
  · exact hle fun p hp ↦ ⟨((P.mem_pairSupport₀₁ p).1 hp).1, ((P.mem_pairSupport₀₁ p).1 hp).2.1⟩
  · exact hle fun p hp ↦ ⟨((P.mem_pairSupport₀₂ p).1 hp).1, ((P.mem_pairSupport₀₂ p).1 hp).2.1⟩
  · exact hle fun p hp ↦ ⟨((P.mem_pairSupport₁₂ p).1 hp).1, ((P.mem_pairSupport₁₂ p).1 hp).2.1⟩

/-- The number of subpolyads of a polyad on a host `V` is at most `2 ^ (3 * |V|²)`. -/
theorem card_subpolyad3_le (P : Polyad3 S) :
    Fintype.card (Subpolyad3 P) ≤ 2 ^ (3 * Fintype.card V ^ 2) := by
  refine (card_subpolyad3_le_mul_card P).trans (Nat.pow_le_pow_right two_pos ?_)
  have h0 : #P.c₀ ≤ Fintype.card V := P.c₀.card_le_univ
  have h1 : #P.c₁ ≤ Fintype.card V := P.c₁.card_le_univ
  have h2 : #P.c₂ ≤ Fintype.card V := P.c₂.card_le_univ
  calc #P.c₀ * #P.c₁ + #P.c₀ * #P.c₂ + #P.c₁ * #P.c₂
      ≤ Fintype.card V * Fintype.card V + Fintype.card V * Fintype.card V +
          Fintype.card V * Fintype.card V := by gcongr
    _ = 3 * Fintype.card V ^ 2 := by ring

namespace Subpolyad3

variable {P : Polyad3 S}

/-- The injective triples whose three coordinate pairs belong to the selected pair graphs. -/
noncomputable def support (Q : Subpolyad3 P) :
    Finset {x : Fin 3 → V // Function.Injective x} :=
  subpolyadSupport P Q.pair₀₁ Q.pair₀₂ Q.pair₁₂

/-- Membership in the support of a subpolyad. -/
theorem mem_support (Q : Subpolyad3 P) (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ Q.support ↔ x ∈ P.support ∧
      coordPair x 0 1 (by decide) ∈ Q.pair₀₁ ∧
      coordPair x 0 2 (by decide) ∈ Q.pair₀₂ ∧
      coordPair x 1 2 (by decide) ∈ Q.pair₁₂ :=
  mem_subpolyadSupport

/-- A subpolyad's support lies in the parent support. -/
theorem support_subset (Q : Subpolyad3 P) : Q.support ⊆ P.support :=
  fun x hx ↦ ((Q.mem_support x).1 hx).1

/-- For a bundled subpolyad, membership in the three selected pair graphs already implies
membership in the parent support. -/
@[simp]
theorem mem_support_iff_coordPair_mem (Q : Subpolyad3 P)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ Q.support ↔ coordPair x 0 1 (by decide) ∈ Q.pair₀₁ ∧
      coordPair x 0 2 (by decide) ∈ Q.pair₀₂ ∧
      coordPair x 1 2 (by decide) ∈ Q.pair₁₂ := by
  rw [mem_support]
  refine ⟨And.right, fun hx ↦ ⟨?_, hx⟩⟩
  exact Polyad3.mem_support_iff_coordPair_mem.2
    ⟨Q.pair₀₁_sub hx.1, Q.pair₀₂_sub hx.2.1, Q.pair₁₂_sub hx.2.2⟩

/-- Enlarging each selected pair graph can only enlarge the supported triples. -/
theorem support_mono {Q R : Subpolyad3 P} (h₀₁ : Q.pair₀₁ ⊆ R.pair₀₁)
    (h₀₂ : Q.pair₀₂ ⊆ R.pair₀₂) (h₁₂ : Q.pair₁₂ ⊆ R.pair₁₂) :
    Q.support ⊆ R.support := by
  intro x hx
  rw [mem_support_iff_coordPair_mem] at hx ⊢
  exact ⟨h₀₁ hx.1, h₀₂ hx.2.1, h₁₂ hx.2.2⟩

/-- The intersection of a nonempty finite family of subpolyads, formed by intersecting each
of their three selected pair graphs. -/
noncomputable def finsetInter {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → Subpolyad3 P) : Subpolyad3 P where
  pair₀₁ := s.inf' hs fun i ↦ (Q i).pair₀₁
  pair₀₂ := s.inf' hs fun i ↦ (Q i).pair₀₂
  pair₁₂ := s.inf' hs fun i ↦ (Q i).pair₁₂
  pair₀₁_sub := by
    have ⟨i, hi⟩ := hs
    exact fun _ hx ↦ (Q i).pair₀₁_sub ((mem_inf' hs).1 hx i hi)
  pair₀₂_sub := by
    have ⟨i, hi⟩ := hs
    exact fun _ hx ↦ (Q i).pair₀₂_sub ((mem_inf' hs).1 hx i hi)
  pair₁₂_sub := by
    have ⟨i, hi⟩ := hs
    exact fun _ hx ↦ (Q i).pair₁₂_sub ((mem_inf' hs).1 hx i hi)

/-- The zero-one pair graph of a finite intersection. -/
@[simp]
theorem finsetInter_pair₀₁ {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → Subpolyad3 P) :
    (finsetInter s hs Q).pair₀₁ = s.inf' hs fun i ↦ (Q i).pair₀₁ :=
  (rfl)

/-- The zero-two pair graph of a finite intersection. -/
@[simp]
theorem finsetInter_pair₀₂ {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → Subpolyad3 P) :
    (finsetInter s hs Q).pair₀₂ = s.inf' hs fun i ↦ (Q i).pair₀₂ :=
  (rfl)

/-- The one-two pair graph of a finite intersection. -/
@[simp]
theorem finsetInter_pair₁₂ {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → Subpolyad3 P) :
    (finsetInter s hs Q).pair₁₂ = s.inf' hs fun i ↦ (Q i).pair₁₂ :=
  (rfl)

/-- A finite intersection of subpolyads supports exactly the intersection of their supports. -/
@[simp]
theorem support_finsetInter {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → Subpolyad3 P) :
    (finsetInter s hs Q).support = s.inf' hs fun i ↦ (Q i).support := by
  ext x
  simp only [mem_support_iff_coordPair_mem, finsetInter_pair₀₁, finsetInter_pair₀₂,
    finsetInter_pair₁₂, mem_inf']
  aesop

/-- Restrict a polyad to three vertex sets, intersecting each parent pair graph with the
corresponding vertex rectangle. The sets need not be contained in the parent cells. -/
noncomputable def ofSubcells (P : Polyad3 S) (a₀ a₁ a₂ : Finset V) : Subpolyad3 P where
  pair₀₁ := P.pairSupport₀₁.filter fun p ↦ p.val.1 ∈ a₀ ∧ p.val.2 ∈ a₁
  pair₀₂ := P.pairSupport₀₂.filter fun p ↦ p.val.1 ∈ a₀ ∧ p.val.2 ∈ a₂
  pair₁₂ := P.pairSupport₁₂.filter fun p ↦ p.val.1 ∈ a₁ ∧ p.val.2 ∈ a₂
  pair₀₁_sub := filter_subset _ _
  pair₀₂_sub := filter_subset _ _
  pair₁₂_sub := filter_subset _ _

/-- The selected zero-one pairs of a vertex restriction. -/
@[simp]
theorem mem_ofSubcells_pair₀₁ (P : Polyad3 S) (a₀ a₁ a₂ : Finset V)
    (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ (ofSubcells P a₀ a₁ a₂).pair₀₁ ↔
      p ∈ P.pairSupport₀₁ ∧ p.val.1 ∈ a₀ ∧ p.val.2 ∈ a₁ := by
  simp [ofSubcells]

/-- The selected zero-two pairs of a vertex restriction. -/
@[simp]
theorem mem_ofSubcells_pair₀₂ (P : Polyad3 S) (a₀ a₁ a₂ : Finset V)
    (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ (ofSubcells P a₀ a₁ a₂).pair₀₂ ↔
      p ∈ P.pairSupport₀₂ ∧ p.val.1 ∈ a₀ ∧ p.val.2 ∈ a₂ := by
  simp [ofSubcells]

/-- The selected one-two pairs of a vertex restriction. -/
@[simp]
theorem mem_ofSubcells_pair₁₂ (P : Polyad3 S) (a₀ a₁ a₂ : Finset V)
    (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ (ofSubcells P a₀ a₁ a₂).pair₁₂ ↔
      p ∈ P.pairSupport₁₂ ∧ p.val.1 ∈ a₁ ∧ p.val.2 ∈ a₂ := by
  simp [ofSubcells]

/-- A vertex restriction keeps exactly the parent triples landing in the three given sets. -/
-- Simplify vertex restrictions before general support membership expands all three pair graphs.
@[simp high]
theorem mem_ofSubcells_support (P : Polyad3 S) (a₀ a₁ a₂ : Finset V)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ (ofSubcells P a₀ a₁ a₂).support ↔
      x ∈ P.support ∧ x.val 0 ∈ a₀ ∧ x.val 1 ∈ a₁ ∧ x.val 2 ∈ a₂ := by
  rw [mem_support]
  simp only [mem_ofSubcells_pair₀₁, mem_ofSubcells_pair₀₂, mem_ofSubcells_pair₁₂,
    coe_coordPair]
  constructor
  · tauto
  · rintro ⟨hx, h₀, h₁, h₂⟩
    exact ⟨hx, ⟨coordPair_mem_pairSupport₀₁ hx, h₀, h₁⟩,
      ⟨coordPair_mem_pairSupport₀₂ hx, h₀, h₂⟩,
      ⟨coordPair_mem_pairSupport₁₂ hx, h₁, h₂⟩⟩

/-- The support of a vertex restriction, as a filter of the parent support. -/
theorem support_ofSubcells (P : Polyad3 S) (a₀ a₁ a₂ : Finset V) :
    (ofSubcells P a₀ a₁ a₂).support =
      {x ∈ P.support | x.val 0 ∈ a₀ ∧ x.val 1 ∈ a₁ ∧ x.val 2 ∈ a₂} := by
  ext x
  rw [mem_ofSubcells_support, mem_filter]

/-- Restricting to the whole parent cells preserves the support, including repeated cells. -/
@[simp]
theorem support_ofSubcells_cells (P : Polyad3 S) :
    (ofSubcells P P.c₀ P.c₁ P.c₂).support = P.support := by
  ext x
  rw [mem_ofSubcells_support]
  exact ⟨And.left, fun hx ↦ ⟨hx, ((P.mem_support x).1 hx).1,
    ((P.mem_support x).1 hx).2.1, ((P.mem_support x).1 hx).2.2.1⟩⟩

section inclusion

variable {κ' : Type*} {S' : PairSkeleton3 κ' V} {P' : Polyad3 S'}
  (h₀₁ : P'.pairSupport₀₁ ⊆ P.pairSupport₀₁) (h₀₂ : P'.pairSupport₀₂ ⊆ P.pairSupport₀₂)
  (h₁₂ : P'.pairSupport₁₂ ⊆ P.pairSupport₁₂)

/-- A subpolyad of `P'` regarded as a subpolyad of `P`, when each pair graph of `P'` lies in the
corresponding pair graph of `P`. The polyad `P'` may live over a different skeleton, for instance
one refining the skeleton of `P`. The selected pairs are unchanged. -/
def inclusion (Q : Subpolyad3 P') : Subpolyad3 P where
  pair₀₁ := Q.pair₀₁
  pair₀₂ := Q.pair₀₂
  pair₁₂ := Q.pair₁₂
  pair₀₁_sub := Q.pair₀₁_sub.trans h₀₁
  pair₀₂_sub := Q.pair₀₂_sub.trans h₀₂
  pair₁₂_sub := Q.pair₁₂_sub.trans h₁₂

/-- A subpolyad and its inclusion select the same pairs on roles zero and one. -/
@[simp]
theorem inclusion_pair₀₁ (Q : Subpolyad3 P') :
    (Q.inclusion h₀₁ h₀₂ h₁₂).pair₀₁ = Q.pair₀₁ :=
  (rfl)

/-- A subpolyad and its inclusion select the same pairs on roles zero and two. -/
@[simp]
theorem inclusion_pair₀₂ (Q : Subpolyad3 P') :
    (Q.inclusion h₀₁ h₀₂ h₁₂).pair₀₂ = Q.pair₀₂ :=
  (rfl)

/-- A subpolyad and its inclusion select the same pairs on roles one and two. -/
@[simp]
theorem inclusion_pair₁₂ (Q : Subpolyad3 P') :
    (Q.inclusion h₀₁ h₀₂ h₁₂).pair₁₂ = Q.pair₁₂ :=
  (rfl)

/-- Including a subpolyad does not change its support. -/
@[simp]
theorem support_inclusion (Q : Subpolyad3 P') :
    (Q.inclusion h₀₁ h₀₂ h₁₂).support = Q.support := by
  ext x
  simp

end inclusion

section restrict

variable {κ' : Type*} {S' : PairSkeleton3 κ' V} {P' : Polyad3 S'}

/-- The restriction of a subpolyad of `P'` to a polyad `P`, possibly over another skeleton: each
selected pair graph is intersected with the corresponding pair graph of `P`. Its support
consists of the triples supported by both the subpolyad and `P`. -/
noncomputable def restrict (Q : Subpolyad3 P') (P : Polyad3 S) : Subpolyad3 P where
  pair₀₁ := Q.pair₀₁ ∩ P.pairSupport₀₁
  pair₀₂ := Q.pair₀₂ ∩ P.pairSupport₀₂
  pair₁₂ := Q.pair₁₂ ∩ P.pairSupport₁₂
  pair₀₁_sub := inter_subset_right
  pair₀₂_sub := inter_subset_right
  pair₁₂_sub := inter_subset_right

/-- The restriction keeps the selected zero-one pairs lying in the pair graph of `P`. -/
@[simp]
theorem restrict_pair₀₁ (Q : Subpolyad3 P') (P : Polyad3 S) :
    (Q.restrict P).pair₀₁ = Q.pair₀₁ ∩ P.pairSupport₀₁ :=
  (rfl)

/-- The restriction keeps the selected zero-two pairs lying in the pair graph of `P`. -/
@[simp]
theorem restrict_pair₀₂ (Q : Subpolyad3 P') (P : Polyad3 S) :
    (Q.restrict P).pair₀₂ = Q.pair₀₂ ∩ P.pairSupport₀₂ :=
  (rfl)

/-- The restriction keeps the selected one-two pairs lying in the pair graph of `P`. -/
@[simp]
theorem restrict_pair₁₂ (Q : Subpolyad3 P') (P : Polyad3 S) :
    (Q.restrict P).pair₁₂ = Q.pair₁₂ ∩ P.pairSupport₁₂ :=
  (rfl)

/-- The support of a restriction is the part of the original support lying in `P`. -/
@[simp]
theorem support_restrict (Q : Subpolyad3 P') (P : Polyad3 S) :
    (Q.restrict P).support = Q.support ∩ P.support := by
  ext x
  simp only [mem_support_iff_coordPair_mem, restrict_pair₀₁, restrict_pair₀₂, restrict_pair₁₂,
    mem_inter, Polyad3.mem_support_iff_coordPair_mem]
  tauto

end restrict

/-- The union of the supports of a finite family of subpolyads of `P`. -/
noncomputable def unionSupport {ι : Type*} [Fintype ι] (Q : ι → Subpolyad3 P) :
    Finset {x : Fin 3 → V // Function.Injective x} :=
  univ.biUnion fun i ↦ (Q i).support

/-- The union support is the finite union of the members' supports. -/
theorem unionSupport_def {ι : Type*} [Fintype ι] (Q : ι → Subpolyad3 P) :
    unionSupport Q = univ.biUnion fun i ↦ (Q i).support :=
  (rfl)

variable {ι : Type*} [Fintype ι]

/-- A triple lies in the union support when it lies in the support of some member. -/
@[simp]
theorem mem_unionSupport {Q : ι → Subpolyad3 P} {x : {x : Fin 3 → V // Function.Injective x}} :
    x ∈ unionSupport Q ↔ ∃ i, x ∈ (Q i).support := by
  simp [unionSupport]

/-- Each member's support lies in the union support. -/
theorem support_subset_unionSupport (Q : ι → Subpolyad3 P) (i : ι) :
    (Q i).support ⊆ unionSupport Q :=
  fun _ hx ↦ mem_unionSupport.2 ⟨i, hx⟩

/-- The union support lies in the support of the parent polyad. -/
theorem unionSupport_subset (Q : ι → Subpolyad3 P) : unionSupport Q ⊆ P.support := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_unionSupport.1 hx
  exact (Q i).support_subset hi

/-- The empty family has empty union support. -/
@[simp]
theorem unionSupport_of_isEmpty [IsEmpty ι] (Q : ι → Subpolyad3 P) : unionSupport Q = ∅ := by
  ext x
  simp

/-- A family with a single member has that member's support as union support. -/
@[simp]
theorem unionSupport_unique [Unique ι] (Q : ι → Subpolyad3 P) :
    unionSupport Q = (Q default).support := by
  ext x
  simp [Unique.exists_iff]

/-- A family of at most `r` subpolyads has the same union support as a family indexed by
`Fin r`, padded by the restriction to empty vertex sets. -/
theorem exists_unionSupport_eq_of_card_le {r : ℕ} (Q : ι → Subpolyad3 P)
    (hr : Fintype.card ι ≤ r) : ∃ Q' : Fin r → Subpolyad3 P, unionSupport Q' = unionSupport Q := by
  let e := Fintype.equivFin ι
  refine ⟨fun j ↦ if h : (j : ℕ) < Fintype.card ι then Q (e.symm ⟨j, h⟩) else
    ofSubcells P ∅ ∅ ∅, ?_⟩
  ext x
  simp only [mem_unionSupport]
  constructor
  · rintro ⟨j, hj⟩
    split_ifs at hj with h
    · exact ⟨_, hj⟩
    · simp at hj
  · rintro ⟨i, hi⟩
    refine ⟨⟨e i, (e i).isLt.trans_le hr⟩, ?_⟩
    simpa [(e i).isLt] using hi

/-- Including every member of a family of subpolyads does not change its union support. -/
@[simp]
theorem unionSupport_inclusion {κ' : Type*} {S' : PairSkeleton3 κ' V} {P' : Polyad3 S'}
    (h₀₁ : P'.pairSupport₀₁ ⊆ P.pairSupport₀₁) (h₀₂ : P'.pairSupport₀₂ ⊆ P.pairSupport₀₂)
    (h₁₂ : P'.pairSupport₁₂ ⊆ P.pairSupport₁₂) (Q : ι → Subpolyad3 P') :
    unionSupport (fun i ↦ (Q i).inclusion h₀₁ h₀₂ h₁₂) = unionSupport Q := by
  ext x
  simp

/-- Restricting every member of a family to `P` restricts its union support to `P`. -/
@[simp]
theorem unionSupport_restrict {κ' : Type*} {S' : PairSkeleton3 κ' V} {P' : Polyad3 S'}
    (Q : ι → Subpolyad3 P') (P : Polyad3 S) :
    unionSupport (fun i ↦ (Q i).restrict P) = unionSupport Q ∩ P.support := by
  ext x
  simp only [mem_unionSupport, support_restrict, mem_inter, exists_and_right]

/-! ### Oriented pair graphs and parent-equality transport -/

/-- The selected pair graph of a subpolyad from role `i` to role `j`, swapping pairs when
`i > j`. -/
noncomputable def pairGraph (Q : Subpolyad3 P) :
    Fin 3 → Fin 3 → Finset {p : V × V // p.1 ≠ p.2}
  | 0, 1 => Q.pair₀₁
  | 0, 2 => Q.pair₀₂
  | 1, 2 => Q.pair₁₂
  | 1, 0 => Q.pair₀₁.image swapDistinctPair
  | 2, 0 => Q.pair₀₂.image swapDistinctPair
  | 2, 1 => Q.pair₁₂.image swapDistinctPair
  | _, _ => ∅

/-- On diagonal roles, `pairGraph` is empty. -/
@[simp]
theorem pairGraph_self (Q : Subpolyad3 P) (i : Fin 3) : Q.pairGraph i i = ∅ := by
  fin_cases i <;> rfl

/-- On roles `(0, 1)`, `pairGraph` is `pair₀₁`. -/
@[simp]
theorem pairGraph_zero_one (Q : Subpolyad3 P) : Q.pairGraph 0 1 = Q.pair₀₁ := (rfl)

/-- On roles `(0, 2)`, `pairGraph` is `pair₀₂`. -/
@[simp]
theorem pairGraph_zero_two (Q : Subpolyad3 P) : Q.pairGraph 0 2 = Q.pair₀₂ := (rfl)

/-- On roles `(1, 2)`, `pairGraph` is `pair₁₂`. -/
@[simp]
theorem pairGraph_one_two (Q : Subpolyad3 P) : Q.pairGraph 1 2 = Q.pair₁₂ := (rfl)

/-- On roles `(1, 0)`, `pairGraph` is `pair₀₁` mapped by `swapDistinctPair`. -/
@[simp]
theorem pairGraph_one_zero (Q : Subpolyad3 P) :
    Q.pairGraph 1 0 = Q.pair₀₁.image swapDistinctPair := (rfl)

/-- On roles `(2, 0)`, `pairGraph` is `pair₀₂` mapped by `swapDistinctPair`. -/
@[simp]
theorem pairGraph_two_zero (Q : Subpolyad3 P) :
    Q.pairGraph 2 0 = Q.pair₀₂.image swapDistinctPair := (rfl)

/-- On roles `(2, 1)`, `pairGraph` is `pair₁₂` mapped by `swapDistinctPair`. -/
@[simp]
theorem pairGraph_two_one (Q : Subpolyad3 P) :
    Q.pairGraph 2 1 = Q.pair₁₂.image swapDistinctPair := (rfl)

/-- Every role-indexed pair graph of a finite intersection of subpolyads is the intersection of
their corresponding pair graphs. -/
@[simp]
theorem finsetInter_pairGraph {ι' : Type*} (s : Finset ι') (hs : s.Nonempty)
    (Q : ι' → Subpolyad3 P) (i j : Fin 3) :
    (finsetInter s hs Q).pairGraph i j = s.inf' hs fun k ↦ (Q k).pairGraph i j := by
  have himg (f : ι' → Finset {p : V × V // p.1 ≠ p.2}) :
      (s.inf' hs f).image swapDistinctPair = s.inf' hs fun k ↦ (f k).image swapDistinctPair := by
    ext p
    simp only [mem_image, mem_inf']
    constructor
    · rintro ⟨q, hq, rfl⟩ k hk
      exact ⟨q, hq k hk, rfl⟩
    · intro hp
      obtain ⟨k₀, hk₀⟩ := hs
      obtain ⟨q, -, rfl⟩ := hp k₀ hk₀
      exact ⟨q, fun k hk ↦ by
        obtain ⟨r, hr, hrq⟩ := hp k hk
        exact swapDistinctPair_injective hrq ▸ hr, rfl⟩
  fin_cases i <;> fin_cases j <;>
    first
    | exact (inf'_const (s := s) hs (∅ : Finset _)).symm
    | rfl
    | exact himg _

/-- Including a subpolyad preserves every role-indexed pair graph. -/
@[simp]
theorem inclusion_pairGraph {κ' : Type*} {S' : PairSkeleton3 κ' V} {P' : Polyad3 S'}
    (h₀₁ : P'.pairSupport₀₁ ⊆ P.pairSupport₀₁) (h₀₂ : P'.pairSupport₀₂ ⊆ P.pairSupport₀₂)
    (h₁₂ : P'.pairSupport₁₂ ⊆ P.pairSupport₁₂) (Q : Subpolyad3 P') (i j : Fin 3) :
    (Q.inclusion h₀₁ h₀₂ h₁₂).pairGraph i j = Q.pairGraph i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Restricting a subpolyad to `P` intersects every role-indexed pair graph with the corresponding
pair graph of `P`. -/
@[simp]
theorem restrict_pairGraph {κ' : Type*} {S' : PairSkeleton3 κ' V} {P' : Polyad3 S'}
    (Q : Subpolyad3 P') (P : Polyad3 S) (i j : Fin 3) :
    (Q.restrict P).pairGraph i j = Q.pairGraph i j ∩ P.pairSupportAt i j := by
  fin_cases i <;> fin_cases j <;>
    simp [Finset.image_inter _ _ swapDistinctPair_injective]

/-- Two subpolyads agree precisely when all their oriented pair graphs agree. -/
theorem ext_pairGraph {Q R : Subpolyad3 P}
    (h : ∀ i j : Fin 3, i ≠ j → Q.pairGraph i j = R.pairGraph i j) : Q = R :=
  ext_data
    (by simpa only [pairGraph_zero_one] using h 0 1 (by decide))
    (by simpa only [pairGraph_zero_two] using h 0 2 (by decide))
    (by simpa only [pairGraph_one_two] using h 1 2 (by decide))

/-- Swapping a pair corresponds to exchanging the roles of `pairGraph`. -/
theorem swapDistinctPair_mem_pairGraph (Q : Subpolyad3 P) {i j : Fin 3} (hij : i ≠ j)
    (p : {p : V × V // p.1 ≠ p.2}) :
    swapDistinctPair p ∈ Q.pairGraph j i ↔ p ∈ Q.pairGraph i j := by
  have himg (E : Finset {p : V × V // p.1 ≠ p.2}) (q) :
      swapDistinctPair q ∈ E.image swapDistinctPair ↔ q ∈ E :=
    ⟨fun h ↦ let ⟨_, hr, hrq⟩ := mem_image.1 h; swapDistinctPair_injective hrq ▸ hr,
      fun h ↦ mem_image.2 ⟨q, h, rfl⟩⟩
  have himg' (E : Finset {p : V × V // p.1 ≠ p.2}) :
      swapDistinctPair p ∈ E ↔ p ∈ E.image swapDistinctPair := by
    simpa [swapDistinctPair_swap] using (himg E (swapDistinctPair p)).symm
  match i, j with
  | 0, 1 | 0, 2 | 1, 2 => exact himg _ p
  | 1, 0 | 2, 0 | 2, 1 => exact himg' _
  | 0, 0 | 1, 1 | 2, 2 => exact (hij rfl).elim

/-- Membership in the role-indexed pair graphs of a vertex restriction `ofSubcells`. -/
@[simp]
theorem mem_ofSubcells_pairGraph (P : Polyad3 S) (a₀ a₁ a₂ : Finset V) (i j : Fin 3)
    (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ (ofSubcells P a₀ a₁ a₂).pairGraph i j ↔
      p ∈ P.pairSupportAt i j ∧ p.val.1 ∈ ![a₀, a₁, a₂] i ∧ p.val.2 ∈ ![a₀, a₁, a₂] j := by
  have hrev (a b : Fin 3) (hab : a ≠ b)
      (h : swapDistinctPair p ∈ (ofSubcells P a₀ a₁ a₂).pairGraph b a ↔
        swapDistinctPair p ∈ P.pairSupportAt b a ∧
          (swapDistinctPair p).val.1 ∈ ![a₀, a₁, a₂] b ∧
          (swapDistinctPair p).val.2 ∈ ![a₀, a₁, a₂] a) :
      p ∈ (ofSubcells P a₀ a₁ a₂).pairGraph a b ↔
        p ∈ P.pairSupportAt a b ∧ p.val.1 ∈ ![a₀, a₁, a₂] a ∧ p.val.2 ∈ ![a₀, a₁, a₂] b := by
    rw [← (ofSubcells P a₀ a₁ a₂).swapDistinctPair_mem_pairGraph hab,
      ← P.swapDistinctPair_mem_pairSupportAt hab, h]
    simp only [swapDistinctPair_val, Prod.fst_swap, Prod.snd_swap]
    tauto
  match i, j with
  | 0, 1 => simp [mem_ofSubcells_pair₀₁]
  | 0, 2 => simp [mem_ofSubcells_pair₀₂]
  | 1, 2 => simp [mem_ofSubcells_pair₁₂]
  | 1, 0 =>
    exact hrev 1 0 (by decide) (by simp [mem_ofSubcells_pair₀₁])
  | 2, 0 =>
    exact hrev 2 0 (by decide) (by simp [mem_ofSubcells_pair₀₂])
  | 2, 1 =>
    exact hrev 2 1 (by decide) (by simp [mem_ofSubcells_pair₁₂])
  | 0, 0 | 1, 1 | 2, 2 => simp

/-- Each oriented pair graph of a subpolyad lies in the corresponding pair graph of its parent. -/
theorem pairGraph_subset_pairSupportAt (Q : Subpolyad3 P) (i j : Fin 3) :
    Q.pairGraph i j ⊆ P.pairSupportAt i j := by
  intro p hp
  match i, j with
  | 0, 1 => simpa using Q.pair₀₁_sub hp
  | 0, 2 => simpa using Q.pair₀₂_sub hp
  | 1, 2 => simpa using Q.pair₁₂_sub hp
  | 1, 0 =>
    rw [← Q.swapDistinctPair_mem_pairGraph (by decide : (1 : Fin 3) ≠ 0)] at hp
    exact (P.swapDistinctPair_mem_pairSupportAt (by decide : (1 : Fin 3) ≠ 0) p).1
      (by simpa using Q.pair₀₁_sub hp)
  | 2, 0 =>
    rw [← Q.swapDistinctPair_mem_pairGraph (by decide : (2 : Fin 3) ≠ 0)] at hp
    exact (P.swapDistinctPair_mem_pairSupportAt (by decide : (2 : Fin 3) ≠ 0) p).1
      (by simpa using Q.pair₀₂_sub hp)
  | 2, 1 =>
    rw [← Q.swapDistinctPair_mem_pairGraph (by decide : (2 : Fin 3) ≠ 1)] at hp
    exact (P.swapDistinctPair_mem_pairSupportAt (by decide : (2 : Fin 3) ≠ 1) p).1
      (by simpa using Q.pair₁₂_sub hp)
  | 0, 0 | 1, 1 | 2, 2 => simp at hp

/-- Membership in a subpolyad's support characterized uniformly across all distinct role pairs. -/
theorem mem_support_iff_pairGraph (Q : Subpolyad3 P)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ Q.support ↔
      ∀ i j : Fin 3, (hij : i ≠ j) → coordPair x i j hij ∈ Q.pairGraph i j := by
  rw [mem_support_iff_coordPair_mem]
  refine ⟨fun ⟨h₀₁, h₀₂, h₁₂⟩ i j hij ↦ ?_,
    fun h ↦ ⟨h 0 1 (by decide), h 0 2 (by decide), h 1 2 (by decide)⟩⟩
  have hsw (a b : Fin 3) (hab : a ≠ b) :
      swapDistinctPair (coordPair x a b hab) = coordPair x b a hab.symm :=
    Subtype.ext (by simp [swapDistinctPair_val, coe_coordPair])
  match i, j with
  | 0, 1 => exact h₀₁
  | 0, 2 => exact h₀₂
  | 1, 2 => exact h₁₂
  | 1, 0 => rw [← hsw 0 1 (by decide), Q.swapDistinctPair_mem_pairGraph (by decide)]; exact h₀₁
  | 2, 0 => rw [← hsw 0 2 (by decide), Q.swapDistinctPair_mem_pairGraph (by decide)]; exact h₀₂
  | 2, 1 => rw [← hsw 1 2 (by decide), Q.swapDistinctPair_mem_pairGraph (by decide)]; exact h₁₂
  | 0, 0 | 1, 1 | 2, 2 => exact (hij rfl).elim

/-- Transporting a subpolyad along an equality of parent polyads preserves `pairGraph`. -/
@[simp]
theorem cast_pairGraph {P₁ P₂ : Polyad3 S} (hP : P₁ = P₂) (Q : Subpolyad3 P₁) (i j : Fin 3) :
    (hP ▸ Q).pairGraph i j = Q.pairGraph i j := by
  subst hP; rfl

/-- Transporting a subpolyad along an equality of parent polyads preserves its support. -/
@[simp]
theorem cast_support {P₁ P₂ : Polyad3 S} (hP : P₁ = P₂) (Q : Subpolyad3 P₁) :
    (hP ▸ Q).support = Q.support := by
  subst hP; rfl

/-- Transporting a family of subpolyads along an equality of parent polyads preserves its union
support. -/
@[simp]
theorem unionSupport_cast {ι' : Type*} [Fintype ι'] {P₁ P₂ : Polyad3 S} (hP : P₁ = P₂)
    (Q : ι' → Subpolyad3 P₁) :
    unionSupport (fun i ↦ hP ▸ Q i) = unionSupport Q := by
  subst hP; rfl

end Subpolyad3

end TauCeti

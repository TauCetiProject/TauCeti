/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Basic

/-!
# Subpolyads of a triadic polyad

A `Subpolyad3 P` selects arbitrary subgraphs of the three pair supports of `P`. Its triple
support is computed by requiring all three coordinate pairs to be selected. These are the
subtriad tests used in hypergraph regularity; restricting the three vertex cells is only a
special case, supplied by `Subpolyad3.ofSubcells`.

Subpolyads are extensional in their three selected pair graphs and form a finite type, even
without a finite pair palette. Their supports lie in the parent support. The subcell constructor
accepts arbitrary vertex sets and intersects with the parent pair supports, so no containment
hypotheses are needed. `Subpolyad3.unionSupport` collects the supports of a finite family of
subpolyads, and a family of at most `r` members has the same union as one indexed by `Fin r`.
When the pair graphs of a polyad `P'`, possibly over another skeleton, lie in those of `P`,
`Subpolyad3.inclusion` regards each subpolyad of `P'` as a subpolyad of `P` with the same
support.

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

/-- Restrict a polyad to three vertex sets, intersecting each parent pair graph with the
corresponding vertex rectangle. The sets need not be contained in the parent cells. -/
noncomputable def ofSubcells (P : Polyad3 S) (a₀ a₁ a₂ : Finset V) : Subpolyad3 P where
  pair₀₁ := P.pairSupport₀₁.filter fun p ↦ p.1.1 ∈ a₀ ∧ p.1.2 ∈ a₁
  pair₀₂ := P.pairSupport₀₂.filter fun p ↦ p.1.1 ∈ a₀ ∧ p.1.2 ∈ a₂
  pair₁₂ := P.pairSupport₁₂.filter fun p ↦ p.1.1 ∈ a₁ ∧ p.1.2 ∈ a₂
  pair₀₁_sub := filter_subset _ _
  pair₀₂_sub := filter_subset _ _
  pair₁₂_sub := filter_subset _ _

/-- The selected zero-one pairs of a vertex restriction. -/
@[simp]
theorem mem_ofSubcells_pair₀₁ (P : Polyad3 S) (a₀ a₁ a₂ : Finset V)
    (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ (ofSubcells P a₀ a₁ a₂).pair₀₁ ↔
      p ∈ P.pairSupport₀₁ ∧ p.1.1 ∈ a₀ ∧ p.1.2 ∈ a₁ := by
  simp [ofSubcells]

/-- The selected zero-two pairs of a vertex restriction. -/
@[simp]
theorem mem_ofSubcells_pair₀₂ (P : Polyad3 S) (a₀ a₁ a₂ : Finset V)
    (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ (ofSubcells P a₀ a₁ a₂).pair₀₂ ↔
      p ∈ P.pairSupport₀₂ ∧ p.1.1 ∈ a₀ ∧ p.1.2 ∈ a₂ := by
  simp [ofSubcells]

/-- The selected one-two pairs of a vertex restriction. -/
@[simp]
theorem mem_ofSubcells_pair₁₂ (P : Polyad3 S) (a₀ a₁ a₂ : Finset V)
    (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ (ofSubcells P a₀ a₁ a₂).pair₁₂ ↔
      p ∈ P.pairSupport₁₂ ∧ p.1.1 ∈ a₁ ∧ p.1.2 ∈ a₂ := by
  simp [ofSubcells]

/-- A vertex restriction keeps exactly the parent triples landing in the three given sets. -/
-- Simplify vertex restrictions before general support membership expands all three pair graphs.
@[simp high]
theorem mem_ofSubcells_support (P : Polyad3 S) (a₀ a₁ a₂ : Finset V)
    (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ (ofSubcells P a₀ a₁ a₂).support ↔
      x ∈ P.support ∧ x.1 0 ∈ a₀ ∧ x.1 1 ∈ a₁ ∧ x.1 2 ∈ a₂ := by
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
      {x ∈ P.support | x.1 0 ∈ a₀ ∧ x.1 1 ∈ a₁ ∧ x.1 2 ∈ a₂} := by
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

/-- The union of the supports of a finite family of subpolyads of `P`. -/
noncomputable def unionSupport {ι : Type*} [Fintype ι] (Q : ι → Subpolyad3 P) :
    Finset {x : Fin 3 → V // Function.Injective x} :=
  univ.biUnion fun i ↦ (Q i).support

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
    refine ⟨⟨e i, (e i).2.trans_le hr⟩, ?_⟩
    simpa [(e i).2] using hi

/-- Including every member of a family of subpolyads does not change its union support. -/
@[simp]
theorem unionSupport_inclusion {κ' : Type*} {S' : PairSkeleton3 κ' V} {P' : Polyad3 S'}
    (h₀₁ : P'.pairSupport₀₁ ⊆ P.pairSupport₀₁) (h₀₂ : P'.pairSupport₀₂ ⊆ P.pairSupport₀₂)
    (h₁₂ : P'.pairSupport₁₂ ⊆ P.pairSupport₁₂) (Q : ι → Subpolyad3 P') :
    unionSupport (fun i ↦ (Q i).inclusion h₀₁ h₀₂ h₁₂) = unionSupport Q := by
  ext x
  simp

end Subpolyad3

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Prod
public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic

/-!
# Sections of a generalised equation

This file sets up the combinatorics of items, bases and boundaries of a generalised equation `Ω`
(Kharlampovich–Myasnikov, §4.3). The source numbers the boundaries `1, …, ρ + 1` and the items
`h₁, …, h_ρ`; as in `TauCeti.GenEq`, every index here is shifted down by one, so that the
boundaries are `0, …, ρ` and item `hₖ` lies between the boundaries `k` and `k + 1`.

* The *section* `[i, j]` is the set of items `hᵢ, …, h_{j-1}`. The section `σ(μ)` of a variable
  base `μ` is `[α(μ), β(μ)]`; an item *belongs to* `μ` when it lies in `σ(μ)`, and `μ` is
  *contained* in a base `ν` when `σ(μ) ⊆ σ(ν)`, that is `α(ν) ≤ α(μ) < β(μ) ≤ β(ν)`.
* An item is *constant* when it belongs to a constant base and *free* when it belongs to no base
  at all. Its *degree* `γ(hₖ)` is the number of bases containing it.
* A boundary `i` *crosses* `μ` when `α(μ) < i < β(μ)` and *touches* `μ` when it is an end-point of
  `μ`. It is *open* when it crosses some base and *closed* otherwise; the boundaries `0` and `ρ`
  are closed.
* A nonempty section `[i, j]` is *closed* when the boundaries `i` and `j` are closed and every
  boundary strictly between them is open.

The source also writes `[i, j]` for the `j` items starting at `hᵢ`; we use throughout the
end-point convention of `σ(μ) = [α(μ), β(μ)]` and of the standard form (Definition 12).

The closed sections partition the items: every item `hₖ` lies in exactly one closed section,
which runs from the last closed boundary at or before `k` to the first closed boundary after `k`,
and two items lie in the same closed section exactly when every boundary between them is open.
Since the boundaries crossing a base are open, every base lies in exactly one closed section.
Closed sections are the units that the derived transformations of Makanin's process close and
transport, and the closed sections of a parametric generalised equation are partitioned into
active, non-active, parametric and constant sections.

## Main definitions

* `TauCeti.GenEq.sectionItems`, `TauCeti.GenEq.baseItems`: the section `[i, j]` and the section
  `σ(μ)` of a variable base, as sets of items.
* `TauCeti.GenEq.IsConstantItem`, `TauCeti.GenEq.IsFreeItem`, `TauCeti.GenEq.degree`: constant and
  free items, and the degree of an item.
* `TauCeti.GenEq.Crosses`, `TauCeti.GenEq.Touches`: a boundary crossing or touching a base.
* `TauCeti.GenEq.IsOpenBoundary`, `TauCeti.GenEq.IsClosedBoundary`: open and closed boundaries.
* `TauCeti.GenEq.IsClosedSection`, `TauCeti.GenEq.closedSections`: closed sections and the set
  `Σ_Ω` of all closed sections.
* `TauCeti.GenEq.closedSectionOfItem`, `TauCeti.GenEq.closedSectionOfBase`: the closed section
  containing an item or a variable base.

## Main results

* `TauCeti.GenEq.closedSectionOfItem_eq_iff`: the closed section of `hₖ` is the unique closed
  section containing `hₖ`, so the closed sections partition the items.
* `TauCeti.GenEq.closedSectionOfItem_eq_closedSectionOfItem_iff`: two items lie in the same
  closed section exactly when every boundary between them is open.
* `TauCeti.GenEq.closedSectionOfBase_eq_iff`: every variable base lies in exactly one closed
  section.
* `TauCeti.GenEq.degree_eq_zero_iff`: an item is free exactly when its degree is zero.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.3.
-/

public section

namespace TauCeti

namespace GenEq

open Finset

variable {A : Type*} (Ω : GenEq A)

/-! ### Sections and the items of a base -/

/-- The section `[i, j]` of `Ω`: the set of items `hᵢ, …, h_{j-1}` lying between the boundaries
`i` and `j`. -/
def sectionItems (i j : ℕ) : Finset (Fin Ω.numItems) :=
  {k | i ≤ k ∧ (k : ℕ) < j}

@[simp, grind =]
theorem mem_sectionItems {i j : ℕ} {k : Fin Ω.numItems} :
    k ∈ Ω.sectionItems i j ↔ i ≤ k ∧ (k : ℕ) < j := by
  simp [sectionItems]

/-- A nonempty section `[i, j]` lies in a section `[i', j']` exactly when `i' ≤ i` and
`j ≤ j'`. -/
theorem sectionItems_subset_sectionItems_iff {i j i' j' : ℕ} (hij : i < j) (hj : j ≤ Ω.numItems) :
    Ω.sectionItems i j ⊆ Ω.sectionItems i' j' ↔ i' ≤ i ∧ j ≤ j' := by
  refine ⟨fun h ↦ ?_, fun h k hk ↦ ?_⟩
  · -- Test the inclusion on the first and the last item of `[i, j]`.
    have h₁ := h ((Ω.mem_sectionItems (k := ⟨i, by omega⟩)).2 ⟨le_rfl, hij⟩)
    have h₂ := h ((Ω.mem_sectionItems (k := ⟨j - 1, by omega⟩)).2 ⟨by grind, by grind⟩)
    simp only [mem_sectionItems] at h₁ h₂
    omega
  · rw [mem_sectionItems] at hk ⊢
    omega

/-- The initial boundary `α(μ)` of a variable base is the left end-point of an item. -/
theorem left_lt_numItems (μ : Fin Ω.numBases) : (Ω.left μ : ℕ) < Ω.numItems :=
  lt_of_lt_of_le (Ω.left_lt_right μ) (Ω.right μ).is_le

/-- The items of a variable base `μ`: the section `σ(μ) = [α(μ), β(μ)]`. An item `hₖ` belongs to
`μ` (and `μ` contains `hₖ`) when `α(μ) ≤ k < β(μ)`. -/
def baseItems (μ : Fin Ω.numBases) : Finset (Fin Ω.numItems) :=
  Ω.sectionItems (Ω.left μ) (Ω.right μ)

theorem baseItems_def (μ : Fin Ω.numBases) :
    Ω.baseItems μ = Ω.sectionItems (Ω.left μ) (Ω.right μ) :=
  (rfl)

@[simp, grind =]
theorem mem_baseItems {μ : Fin Ω.numBases} {k : Fin Ω.numItems} :
    k ∈ Ω.baseItems μ ↔ (Ω.left μ : ℕ) ≤ k ∧ (k : ℕ) < Ω.right μ :=
  Ω.mem_sectionItems

/-- The first item `h_{α(μ)}` of a variable base belongs to it. -/
theorem left_mem_baseItems (μ : Fin Ω.numBases) :
    ⟨Ω.left μ, Ω.left_lt_numItems μ⟩ ∈ Ω.baseItems μ :=
  Ω.mem_baseItems.2 ⟨le_rfl, Ω.left_lt_right μ⟩

/-- A base `μ` is contained in a base `ν`, that is `σ(μ) ⊆ σ(ν)`, exactly when
`α(ν) ≤ α(μ) < β(μ) ≤ β(ν)`. -/
theorem baseItems_subset_baseItems_iff {μ ν : Fin Ω.numBases} :
    Ω.baseItems μ ⊆ Ω.baseItems ν ↔ Ω.left ν ≤ Ω.left μ ∧ Ω.right μ ≤ Ω.right ν := by
  rw [baseItems_def, baseItems_def,
    Ω.sectionItems_subset_sectionItems_iff (Ω.left_lt_right μ) (Ω.right μ).is_le, Fin.le_def,
    Fin.le_def]

/-! ### Constant items, free items and the degree -/

/-- An item is constant when it belongs to a constant base. -/
def IsConstantItem (k : Fin Ω.numItems) : Prop :=
  ∃ b ∈ Ω.constBases, b.1 = k

theorem isConstantItem_iff {k : Fin Ω.numItems} :
    Ω.IsConstantItem k ↔ ∃ b ∈ Ω.constBases, b.1 = k :=
  Iff.rfl

instance (k : Fin Ω.numItems) : Decidable (Ω.IsConstantItem k) :=
  decidable_of_iff _ Ω.isConstantItem_iff.symm

/-- An item is free when it belongs to no base, variable or constant. -/
def IsFreeItem (k : Fin Ω.numItems) : Prop :=
  (∀ μ, k ∉ Ω.baseItems μ) ∧ ¬ Ω.IsConstantItem k

theorem isFreeItem_iff {k : Fin Ω.numItems} :
    Ω.IsFreeItem k ↔ (∀ μ, k ∉ Ω.baseItems μ) ∧ ¬ Ω.IsConstantItem k :=
  Iff.rfl

instance (k : Fin Ω.numItems) : Decidable (Ω.IsFreeItem k) :=
  decidable_of_iff ((∀ μ, ¬ ((Ω.left μ : ℕ) ≤ k ∧ (k : ℕ) < Ω.right μ)) ∧ ¬ Ω.IsConstantItem k)
    (by simp only [isFreeItem_iff, mem_baseItems])

/-- The degree `γ(hₖ)` of an item: the number of bases containing it, that is the variable bases
`μ` with `hₖ ∈ σ(μ)` together with the constant bases on `hₖ`. -/
def degree (k : Fin Ω.numItems) : ℕ :=
  #{μ | k ∈ Ω.baseItems μ} + #{b ∈ Ω.constBases | b.1 = k}

theorem degree_def (k : Fin Ω.numItems) :
    Ω.degree k = #{μ | k ∈ Ω.baseItems μ} + #{b ∈ Ω.constBases | b.1 = k} :=
  (rfl)

/-- An item is free exactly when its degree is zero. -/
@[simp]
theorem degree_eq_zero_iff {k : Fin Ω.numItems} : Ω.degree k = 0 ↔ Ω.IsFreeItem k := by
  simp only [degree, Nat.add_eq_zero_iff, card_eq_zero, filter_eq_empty_iff, mem_univ,
    true_implies, isFreeItem_iff, isConstantItem_iff, not_exists, not_and]

/-! ### Open and closed boundaries -/

/-- A boundary `i` crosses (or intersects) the variable base `μ` when `α(μ) < i < β(μ)`. A constant
base spans a single item, so no boundary crosses it. -/
def Crosses (i : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) : Prop :=
  Ω.left μ < i ∧ i < Ω.right μ

@[grind =]
theorem crosses_iff {i : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} :
    Ω.Crosses i μ ↔ Ω.left μ < i ∧ i < Ω.right μ :=
  Iff.rfl

instance (i : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) : Decidable (Ω.Crosses i μ) :=
  decidable_of_iff _ Ω.crosses_iff.symm

/-- The first boundary `p` of a boundary connection `(p, μ, q)` crosses `μ`. -/
theorem crosses_fst_of_mem_connections
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections) :
    Ω.Crosses c.1 c.2.1 :=
  ⟨(Ω.bounds_of_mem_connections c hc).1, (Ω.bounds_of_mem_connections c hc).2.1⟩

/-- The last boundary `q` of a boundary connection `(p, μ, q)` crosses the dual base `Δ(μ)`. -/
theorem crosses_snd_snd_of_mem_connections
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections) :
    Ω.Crosses c.2.2 (Ω.dual c.2.1) :=
  ⟨(Ω.bounds_of_mem_connections c hc).2.2.1, (Ω.bounds_of_mem_connections c hc).2.2.2⟩

/-- A boundary `i` touches the variable base `μ`, or is an end-point of `μ`, when `i = α(μ)` or
`i = β(μ)`. The end-points of a constant base on the item `hₖ` are the boundaries `k` and
`k + 1`. -/
def Touches (i : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) : Prop :=
  i = Ω.left μ ∨ i = Ω.right μ

@[grind =]
theorem touches_iff {i : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} :
    Ω.Touches i μ ↔ i = Ω.left μ ∨ i = Ω.right μ :=
  Iff.rfl

instance (i : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) : Decidable (Ω.Touches i μ) :=
  decidable_of_iff _ Ω.touches_iff.symm

variable {Ω} in
/-- A boundary crossing a base is not one of its end-points. -/
theorem Crosses.not_touches {i : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} (h : Ω.Crosses i μ) :
    ¬ Ω.Touches i μ := by
  rintro (rfl | rfl)
  exacts [lt_irrefl _ h.1, lt_irrefl _ h.2]

/-- The boundaries crossing or touching a base `μ` are those from `α(μ)` to `β(μ)`. -/
theorem crosses_or_touches_iff {i : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} :
    Ω.Crosses i μ ∨ Ω.Touches i μ ↔ Ω.left μ ≤ i ∧ i ≤ Ω.right μ := by
  grind [Ω.left_lt_right μ]

/-- A boundary is open when it crosses at least one base. -/
def IsOpenBoundary (i : Fin (Ω.numItems + 1)) : Prop :=
  ∃ μ, Ω.Crosses i μ

/-- A boundary is closed when it is not open, that is when it crosses no base. -/
def IsClosedBoundary (i : Fin (Ω.numItems + 1)) : Prop :=
  ¬ Ω.IsOpenBoundary i

theorem isOpenBoundary_iff {i : Fin (Ω.numItems + 1)} : Ω.IsOpenBoundary i ↔ ∃ μ, Ω.Crosses i μ :=
  Iff.rfl

theorem isClosedBoundary_iff {i : Fin (Ω.numItems + 1)} :
    Ω.IsClosedBoundary i ↔ ∀ μ, ¬ Ω.Crosses i μ :=
  not_exists

@[simp, grind =]
theorem not_isOpenBoundary {i : Fin (Ω.numItems + 1)} :
    ¬ Ω.IsOpenBoundary i ↔ Ω.IsClosedBoundary i :=
  Iff.rfl

@[simp, grind =]
theorem not_isClosedBoundary {i : Fin (Ω.numItems + 1)} :
    ¬ Ω.IsClosedBoundary i ↔ Ω.IsOpenBoundary i :=
  not_not

instance (i : Fin (Ω.numItems + 1)) : Decidable (Ω.IsOpenBoundary i) :=
  decidable_of_iff _ Ω.isOpenBoundary_iff.symm

instance (i : Fin (Ω.numItems + 1)) : Decidable (Ω.IsClosedBoundary i) :=
  decidable_of_iff _ Ω.isClosedBoundary_iff.symm

variable {Ω} in
/-- A boundary crossing a base is open. -/
theorem Crosses.isOpenBoundary {i : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} (h : Ω.Crosses i μ) :
    Ω.IsOpenBoundary i :=
  ⟨μ, h⟩

variable {Ω} in
/-- A closed boundary `i` lies before or after every base `μ`: `i ≤ α(μ)` or `β(μ) ≤ i`. -/
theorem IsClosedBoundary.le_left_or_right_le {i : Fin (Ω.numItems + 1)}
    (hi : Ω.IsClosedBoundary i) (μ : Fin Ω.numBases) : i ≤ Ω.left μ ∨ Ω.right μ ≤ i := by
  simpa only [crosses_iff, not_and_or, not_lt] using Ω.isClosedBoundary_iff.1 hi μ

/-- The first boundary is closed. -/
@[simp]
theorem isClosedBoundary_zero : Ω.IsClosedBoundary 0 :=
  Ω.isClosedBoundary_iff.2 fun _ h ↦ Fin.not_lt_zero _ h.1

/-- The last boundary is closed. -/
@[simp]
theorem isClosedBoundary_last : Ω.IsClosedBoundary (Fin.last Ω.numItems) :=
  Ω.isClosedBoundary_iff.2 fun _ h ↦ absurd h.2 (not_lt.2 (Fin.le_last _))

/-- The first boundary is not open. -/
@[simp]
theorem not_isOpenBoundary_zero : ¬ Ω.IsOpenBoundary 0 :=
  Ω.isClosedBoundary_zero

/-- The last boundary is not open. -/
@[simp]
theorem not_isOpenBoundary_last : ¬ Ω.IsOpenBoundary (Fin.last Ω.numItems) :=
  Ω.isClosedBoundary_last

/-! ### Closed sections -/

/-- A section `[i, j]` with `i < j` is closed when the boundaries `i` and `j` are closed and every
boundary strictly between them is open. -/
structure IsClosedSection (i j : Fin (Ω.numItems + 1)) : Prop where
  /-- A closed section is nonempty. -/
  lt : i < j
  /-- The left end-point of a closed section is a closed boundary. -/
  isClosedBoundary_left : Ω.IsClosedBoundary i
  /-- The right end-point of a closed section is a closed boundary. -/
  isClosedBoundary_right : Ω.IsClosedBoundary j
  /-- The boundaries strictly inside a closed section are open. -/
  isOpenBoundary : ∀ l, i < l → l < j → Ω.IsOpenBoundary l

theorem isClosedSection_iff {i j : Fin (Ω.numItems + 1)} :
    Ω.IsClosedSection i j ↔ i < j ∧ Ω.IsClosedBoundary i ∧ Ω.IsClosedBoundary j ∧
      ∀ l, i < l → l < j → Ω.IsOpenBoundary l :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩⟩

instance (i j : Fin (Ω.numItems + 1)) : Decidable (Ω.IsClosedSection i j) :=
  decidable_of_iff _ Ω.isClosedSection_iff.symm

variable {Ω} in
/-- The left end-point of a closed section is the left end-point of an item. -/
theorem IsClosedSection.left_lt_numItems {i j : Fin (Ω.numItems + 1)} (h : Ω.IsClosedSection i j) :
    (i : ℕ) < Ω.numItems :=
  lt_of_lt_of_le h.lt j.is_le

/-- The set `Σ_Ω` of all closed sections of `Ω`, each recorded by the pair of its end-points. -/
def closedSections : Finset (Fin (Ω.numItems + 1) × Fin (Ω.numItems + 1)) :=
  {s | Ω.IsClosedSection s.1 s.2}

@[simp, grind =]
theorem mem_closedSections {s : Fin (Ω.numItems + 1) × Fin (Ω.numItems + 1)} :
    s ∈ Ω.closedSections ↔ Ω.IsClosedSection s.1 s.2 := by
  simp [closedSections]

/-- The closed section containing the item `hₖ`: from the last closed boundary at or before `k` to
the first closed boundary at or after `k + 1`. -/
def closedSectionOfItem (k : Fin Ω.numItems) : Fin (Ω.numItems + 1) × Fin (Ω.numItems + 1) :=
  (({i | Ω.IsClosedBoundary i ∧ i ≤ k.castSucc} : Finset (Fin (Ω.numItems + 1))).max'
      ⟨0, by simp [Ω.isClosedBoundary_zero]⟩,
    ({j | Ω.IsClosedBoundary j ∧ k.succ ≤ j} : Finset (Fin (Ω.numItems + 1))).min'
      ⟨Fin.last _, by simp [Ω.isClosedBoundary_last, Fin.le_last]⟩)

private theorem closedSectionOfItem_fst_mem (k : Fin Ω.numItems) :
    Ω.IsClosedBoundary (Ω.closedSectionOfItem k).1 ∧ (Ω.closedSectionOfItem k).1 ≤ k.castSucc :=
  (mem_filter.1 (max'_mem ({i | Ω.IsClosedBoundary i ∧ i ≤ k.castSucc} : Finset _)
    ⟨0, by simp⟩)).2

private theorem closedSectionOfItem_snd_mem (k : Fin Ω.numItems) :
    Ω.IsClosedBoundary (Ω.closedSectionOfItem k).2 ∧ k.succ ≤ (Ω.closedSectionOfItem k).2 :=
  (mem_filter.1 (min'_mem ({j | Ω.IsClosedBoundary j ∧ k.succ ≤ j} : Finset _)
    ⟨Fin.last _, by simp [Fin.le_last]⟩)).2

/-- The closed section of `hₖ` starts at a closed boundary. -/
@[simp]
theorem isClosedBoundary_closedSectionOfItem_fst (k : Fin Ω.numItems) :
    Ω.IsClosedBoundary (Ω.closedSectionOfItem k).1 :=
  (Ω.closedSectionOfItem_fst_mem k).1

/-- The closed section of `hₖ` starts at or before the boundary `k`. -/
theorem closedSectionOfItem_fst_le (k : Fin Ω.numItems) :
    (Ω.closedSectionOfItem k).1 ≤ k.castSucc :=
  (Ω.closedSectionOfItem_fst_mem k).2

/-- The closed section of `hₖ` starts at the last closed boundary at or before `k`. -/
theorem le_closedSectionOfItem_fst {k : Fin Ω.numItems} {i : Fin (Ω.numItems + 1)}
    (hi : Ω.IsClosedBoundary i) (hik : i ≤ k.castSucc) : i ≤ (Ω.closedSectionOfItem k).1 :=
  le_max' _ _ (by simp [hi, hik])

/-- The closed section of `hₖ` ends at a closed boundary. -/
@[simp]
theorem isClosedBoundary_closedSectionOfItem_snd (k : Fin Ω.numItems) :
    Ω.IsClosedBoundary (Ω.closedSectionOfItem k).2 :=
  (Ω.closedSectionOfItem_snd_mem k).1

/-- The closed section of `hₖ` ends at or after the boundary `k + 1`. -/
theorem succ_le_closedSectionOfItem_snd (k : Fin Ω.numItems) :
    k.succ ≤ (Ω.closedSectionOfItem k).2 :=
  (Ω.closedSectionOfItem_snd_mem k).2

/-- The closed section of `hₖ` ends at the first closed boundary at or after `k + 1`. -/
theorem closedSectionOfItem_snd_le {k : Fin Ω.numItems} {j : Fin (Ω.numItems + 1)}
    (hj : Ω.IsClosedBoundary j) (hkj : k.succ ≤ j) : (Ω.closedSectionOfItem k).2 ≤ j :=
  min'_le _ _ (by simp [hj, hkj])

/-- The closed section of an item is a closed section. -/
@[simp]
theorem isClosedSection_closedSectionOfItem (k : Fin Ω.numItems) :
    Ω.IsClosedSection (Ω.closedSectionOfItem k).1 (Ω.closedSectionOfItem k).2 := by
  have h₂ := Ω.closedSectionOfItem_fst_le k
  have h₄ := Ω.succ_le_closedSectionOfItem_snd k
  refine ⟨by grind, Ω.isClosedBoundary_closedSectionOfItem_fst k,
    Ω.isClosedBoundary_closedSectionOfItem_snd k, fun l hl₁ hl₂ ↦ ?_⟩
  -- A closed boundary strictly inside would be a nearer closed boundary on one side of `hₖ`.
  by_contra hl
  rw [not_isOpenBoundary] at hl
  rcases le_or_gt l k.castSucc with h | h
  · exact absurd (Ω.le_closedSectionOfItem_fst hl h) (not_le.2 hl₁)
  · exact absurd (Ω.closedSectionOfItem_snd_le hl (Fin.castSucc_lt_iff_succ_le.1 h))
      (not_le.2 hl₂)

/-- The closed section of an item belongs to `Σ_Ω`. -/
theorem closedSectionOfItem_mem_closedSections (k : Fin Ω.numItems) :
    Ω.closedSectionOfItem k ∈ Ω.closedSections :=
  Ω.mem_closedSections.2 (Ω.isClosedSection_closedSectionOfItem k)

/-- An item lies in its closed section. -/
theorem mem_sectionItems_closedSectionOfItem (k : Fin Ω.numItems) :
    k ∈ Ω.sectionItems (Ω.closedSectionOfItem k).1 (Ω.closedSectionOfItem k).2 := by
  have h₂ := Ω.closedSectionOfItem_fst_le k
  have h₄ := Ω.succ_le_closedSectionOfItem_snd k
  rw [mem_sectionItems]
  grind

/-- A closed section containing an item is the closed section of that item. -/
theorem closedSectionOfItem_eq_of_mem {k : Fin Ω.numItems}
    {s : Fin (Ω.numItems + 1) × Fin (Ω.numItems + 1)} (hs : s ∈ Ω.closedSections)
    (hk : k ∈ Ω.sectionItems s.1 s.2) : Ω.closedSectionOfItem k = s := by
  rw [mem_closedSections] at hs
  rw [mem_sectionItems] at hk
  obtain ⟨h₁, h₂⟩ := Ω.closedSectionOfItem_fst_mem k
  obtain ⟨h₃, h₄⟩ := Ω.closedSectionOfItem_snd_mem k
  refine Prod.ext (le_antisymm ?_ (Ω.le_closedSectionOfItem_fst hs.isClosedBoundary_left ?_))
    (le_antisymm (Ω.closedSectionOfItem_snd_le hs.isClosedBoundary_right ?_) ?_)
  · -- A closed boundary between the left end-point of `s` and `hₖ` would lie inside `s`.
    exact not_lt.1 fun h ↦ h₁ (hs.isOpenBoundary _ h (by grind))
  · grind
  · grind
  · -- A closed boundary between `hₖ` and the right end-point of `s` would lie inside `s`.
    exact not_lt.1 fun h ↦ h₃ (hs.isOpenBoundary _ (by grind) h)

/-- The closed section of `hₖ` is the unique closed section containing `hₖ`: the closed sections
partition the items. -/
theorem closedSectionOfItem_eq_iff {k : Fin Ω.numItems}
    {s : Fin (Ω.numItems + 1) × Fin (Ω.numItems + 1)} :
    Ω.closedSectionOfItem k = s ↔ s ∈ Ω.closedSections ∧ k ∈ Ω.sectionItems s.1 s.2 :=
  ⟨by rintro rfl; exact ⟨Ω.closedSectionOfItem_mem_closedSections k,
    Ω.mem_sectionItems_closedSectionOfItem k⟩, fun h ↦ Ω.closedSectionOfItem_eq_of_mem h.1 h.2⟩

/-- Every item lies in exactly one closed section. -/
theorem existsUnique_mem_closedSections_and_mem_sectionItems (k : Fin Ω.numItems) :
    ∃! s, s ∈ Ω.closedSections ∧ k ∈ Ω.sectionItems s.1 s.2 :=
  ⟨_, Ω.closedSectionOfItem_eq_iff.1 rfl, fun _ h ↦ (Ω.closedSectionOfItem_eq_iff.2 h).symm⟩

/-- Two items `hₖ` and `h_{k'}` with `k ≤ k'` lie in the same closed section exactly when every
boundary between them is open. -/
theorem closedSectionOfItem_eq_closedSectionOfItem_iff {k k' : Fin Ω.numItems} (hkk' : k ≤ k') :
    Ω.closedSectionOfItem k = Ω.closedSectionOfItem k' ↔
      ∀ l, k.castSucc < l → l ≤ k'.castSucc → Ω.IsOpenBoundary l := by
  obtain ⟨hs, hk⟩ := Ω.closedSectionOfItem_eq_iff.1 (rfl : Ω.closedSectionOfItem k = _)
  have hs' := Ω.mem_closedSections.1 hs
  rw [mem_sectionItems] at hk
  rw [Fin.le_def] at hkk'
  refine ⟨fun h l hl₁ hl₂ ↦ hs'.isOpenBoundary l (by grind) ?_, fun h ↦ ?_⟩
  · have hk' := (Ω.mem_sectionItems.1 (h ▸ Ω.mem_sectionItems_closedSectionOfItem k')).2
    grind
  · -- The right end-point of the closed section of `hₖ` is closed, so it lies beyond `k'`.
    refine (Ω.closedSectionOfItem_eq_of_mem hs ((Ω.mem_sectionItems).2 ⟨by omega, ?_⟩)).symm
    by_contra hlt
    exact hs'.isClosedBoundary_right (h _ (by grind) (by grind))

/-! ### The closed section of a base -/

/-- The closed section containing the variable base `μ`: the closed section of its first item
`h_{α(μ)}`. -/
def closedSectionOfBase (μ : Fin Ω.numBases) : Fin (Ω.numItems + 1) × Fin (Ω.numItems + 1) :=
  Ω.closedSectionOfItem ⟨Ω.left μ, Ω.left_lt_numItems μ⟩

/-- The items of a base lie in its closed section: the boundaries crossing a base are open. -/
theorem closedSectionOfItem_eq_closedSectionOfBase {μ : Fin Ω.numBases} {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) : Ω.closedSectionOfItem k = Ω.closedSectionOfBase μ := by
  rw [mem_baseItems] at hk
  exact ((Ω.closedSectionOfItem_eq_closedSectionOfItem_iff (Fin.le_def.2 hk.1)).2
    fun l hl₁ hl₂ ↦ Crosses.isOpenBoundary (μ := μ) ⟨by grind, by grind⟩).symm

/-- The closed section of a base is a closed section. -/
@[simp]
theorem isClosedSection_closedSectionOfBase (μ : Fin Ω.numBases) :
    Ω.IsClosedSection (Ω.closedSectionOfBase μ).1 (Ω.closedSectionOfBase μ).2 :=
  Ω.isClosedSection_closedSectionOfItem _

/-- The closed section of a variable base belongs to `Σ_Ω`. -/
theorem closedSectionOfBase_mem_closedSections (μ : Fin Ω.numBases) :
    Ω.closedSectionOfBase μ ∈ Ω.closedSections :=
  Ω.closedSectionOfItem_mem_closedSections _

/-- A variable base lies in its closed section. -/
theorem baseItems_subset_sectionItems_closedSectionOfBase (μ : Fin Ω.numBases) :
    Ω.baseItems μ ⊆ Ω.sectionItems (Ω.closedSectionOfBase μ).1 (Ω.closedSectionOfBase μ).2 :=
  fun k hk ↦ Ω.closedSectionOfItem_eq_closedSectionOfBase hk ▸
    Ω.mem_sectionItems_closedSectionOfItem k

/-- The closed section of a variable base `μ` starts at or before `α(μ)`. -/
theorem closedSectionOfBase_fst_le (μ : Fin Ω.numBases) :
    (Ω.closedSectionOfBase μ).1 ≤ Ω.left μ := by
  have := Ω.baseItems_subset_sectionItems_closedSectionOfBase μ
  grind [baseItems_def, sectionItems_subset_sectionItems_iff, left_lt_right]

/-- The closed section of a variable base `μ` ends at or after `β(μ)`. -/
theorem right_le_closedSectionOfBase_snd (μ : Fin Ω.numBases) :
    Ω.right μ ≤ (Ω.closedSectionOfBase μ).2 := by
  have := Ω.baseItems_subset_sectionItems_closedSectionOfBase μ
  grind [baseItems_def, sectionItems_subset_sectionItems_iff, left_lt_right]

/-- The closed section of a variable base starts at a closed boundary. -/
@[simp]
theorem isClosedBoundary_closedSectionOfBase_fst (μ : Fin Ω.numBases) :
    Ω.IsClosedBoundary (Ω.closedSectionOfBase μ).1 :=
  Ω.isClosedBoundary_closedSectionOfItem_fst _

/-- The closed section of a variable base ends at a closed boundary. -/
@[simp]
theorem isClosedBoundary_closedSectionOfBase_snd (μ : Fin Ω.numBases) :
    Ω.IsClosedBoundary (Ω.closedSectionOfBase μ).2 :=
  Ω.isClosedBoundary_closedSectionOfItem_snd _

/-- The closed section of a variable base `μ` starts at the last closed boundary at or before
`α(μ)`. -/
theorem le_closedSectionOfBase_fst {μ : Fin Ω.numBases} {i : Fin (Ω.numItems + 1)}
    (hi : Ω.IsClosedBoundary i) (hiμ : i ≤ Ω.left μ) : i ≤ (Ω.closedSectionOfBase μ).1 :=
  Ω.le_closedSectionOfItem_fst hi hiμ

/-- The closed section of a variable base `μ` ends at the first closed boundary at or after
`β(μ)`. -/
theorem closedSectionOfBase_snd_le {μ : Fin Ω.numBases} {j : Fin (Ω.numItems + 1)}
    (hj : Ω.IsClosedBoundary j) (hμj : Ω.right μ ≤ j) : (Ω.closedSectionOfBase μ).2 ≤ j :=
  Ω.closedSectionOfItem_snd_le hj ((Fin.castSucc_lt_iff_succ_le.1 (Ω.left_lt_right μ)).trans hμj)

/-- The closed section of a variable base is the unique closed section containing it. -/
theorem closedSectionOfBase_eq_iff {μ : Fin Ω.numBases}
    {s : Fin (Ω.numItems + 1) × Fin (Ω.numItems + 1)} :
    Ω.closedSectionOfBase μ = s ↔ s ∈ Ω.closedSections ∧ Ω.baseItems μ ⊆ Ω.sectionItems s.1 s.2 :=
  ⟨by rintro rfl; exact ⟨Ω.closedSectionOfBase_mem_closedSections μ,
    Ω.baseItems_subset_sectionItems_closedSectionOfBase μ⟩,
    fun h ↦ Ω.closedSectionOfItem_eq_of_mem h.1 (h.2 (Ω.left_mem_baseItems μ))⟩

/-- Every variable base lies in exactly one closed section. -/
theorem existsUnique_mem_closedSections_and_baseItems_subset (μ : Fin Ω.numBases) :
    ∃! s, s ∈ Ω.closedSections ∧ Ω.baseItems μ ⊆ Ω.sectionItems s.1 s.2 :=
  ⟨_, Ω.closedSectionOfBase_eq_iff.1 rfl, fun _ h ↦ (Ω.closedSectionOfBase_eq_iff.2 h).symm⟩

end GenEq

end TauCeti

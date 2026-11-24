/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Order
import TauCeti.Algebra.Order.BigOperators.Group.Finset

/-!
# Elimination of free heights over finite support rows

A separable constraint `∑ j, f j x ≤ b` is often approximated by giving each component `j` a
finite family of rows `row j i`, indexed by `i ∈ H j` (for instance tangent lines of a convex
`f j` at finitely many anchors), and imposing one free height `y j` above the rows of component `j`
together with the budget `∑ j, y j ≤ b`. This file computes the projection of such a system onto
the original variables.

For a domain `D`, `sharedRows D row H b` is the set of pairs `(x, y)` with `x ∈ D`,
`row j i x ≤ y j` for every `j` and `i ∈ H j`, and `∑ j, y j ≤ b`. When every support `H j` is
nonempty, `x` admits such heights exactly when `x ∈ D` and the row maxima satisfy
`∑ j, (H j).sup' _ (row j · x) ≤ b`, equivalently when `∑ j, row j (c j) x ≤ b` for every choice
`c` of one row per component. The first form is the exact projection of the lift
`TauCeti.ConvexLifting.liftedSet` whose inner map is the vector of row maxima and whose outer map
is the sum; the second follows from it by `Finset.sum_univ_sup'`.
For heights in a directed additive group such as `ℝ`, a component with empty support leaves its
height unconstrained from below, and then the projection is all of `D`.

Giving each anchor `a` its own vector of heights instead, `independentRows D row b` imposes
`row a j x ≤ y a j` and `∑ j, y a j ≤ b a` for every anchor `a`. Its projection keeps only the
same-anchor sums `∑ j, row a j x ≤ b a`. Shared heights over all anchors are therefore at least as
tight as independent heights: they enforce every mixed choice of anchors across components, while
independent heights enforce only the diagonal choices.

## Main declarations

* `TauCeti.ConvexLifting.sharedRows`, `TauCeti.ConvexLifting.independentRows`: the two height
  systems.
* `TauCeti.ConvexLifting.exists_mem_sharedRows_iff_sum_sup'_le` and
  `TauCeti.ConvexLifting.exists_mem_sharedRows_iff_forall_sum_le`: the projection of
  `sharedRows`, through row maxima and through mixed choices.
* `TauCeti.ConvexLifting.exists_mem_sharedRows_iff_of_eq_empty`: an empty support makes the
  projection the whole domain.
* `TauCeti.ConvexLifting.exists_mem_independentRows_iff`: the projection of `independentRows`.
* `TauCeti.ConvexLifting.fst_image_sharedRows_subset_fst_image_independentRows`: shared heights
  over all anchors project into independent heights with the same budget.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Mathematical Programming 103 (2005), 225–249, §2, Proposition 5 and its proof,
  p. 231.
* J. Kronqvist, A. Lundell and T. Westerlund, *Reformulations for utilizing separability when
  solving convex MINLP problems*, Journal of Global Optimization 71 (2018), 571–592, §3,
  Eqs. (4)–(7) and Proposition 1, p. 574.
-/

public section

open Set Finset

namespace TauCeti.ConvexLifting

variable {X ι κ α β : Type*}

section Defs

variable [Fintype κ] [AddCommMonoid β] [LE β]

/-- Pairs `(x, y)` with `x ∈ D`, one height `y j` per component `j` lying above every support row
`row j i x` with `i ∈ H j`, and heights summing to at most the budget `b`. -/
def sharedRows (D : Set X) (row : κ → ι → X → β) (H : κ → Finset ι) (b : β) :
    Set (X × (κ → β)) :=
  {z | z.1 ∈ D ∧ (∀ j, ∀ i ∈ H j, row j i z.1 ≤ z.2 j) ∧ ∑ j, z.2 j ≤ b}

/-- Membership in `sharedRows`. -/
@[simp]
theorem mem_sharedRows_iff {D : Set X} {row : κ → ι → X → β} {H : κ → Finset ι} {b : β}
    {z : X × (κ → β)} :
    z ∈ sharedRows D row H b ↔
      z.1 ∈ D ∧ (∀ j, ∀ i ∈ H j, row j i z.1 ≤ z.2 j) ∧ ∑ j, z.2 j ≤ b :=
  (Iff.rfl)

/-- Pairs `(x, y)` with `x ∈ D` and, for every anchor `a`, a separate height vector `y a` lying
above the rows `row a j x` of that anchor and summing to at most the anchor's budget `b a`. -/
def independentRows (D : Set X) (row : α → κ → X → β) (b : α → β) :
    Set (X × (α → κ → β)) :=
  {z | z.1 ∈ D ∧ ∀ a, (∀ j, row a j z.1 ≤ z.2 a j) ∧ ∑ j, z.2 a j ≤ b a}

/-- Membership in `independentRows`. -/
@[simp]
theorem mem_independentRows_iff {D : Set X} {row : α → κ → X → β} {b : α → β}
    {z : X × (α → κ → β)} :
    z ∈ independentRows D row b ↔
      z.1 ∈ D ∧ ∀ a, (∀ j, row a j z.1 ≤ z.2 a j) ∧ ∑ j, z.2 a j ≤ b a :=
  (Iff.rfl)

end Defs

section Shared

variable [Fintype κ] [AddCommMonoid β]
variable {D : Set X} {row : κ → ι → X → β} {H : κ → Finset ι} {b : β}

section SemilatticeSup

variable [SemilatticeSup β]

/-- The height of each component in `sharedRows` lies above the maximum of its support rows. -/
theorem sup'_le_of_mem_sharedRows {z : X × (κ → β)} (hz : z ∈ sharedRows D row H b) (j : κ)
    (hne : (H j).Nonempty) : (H j).sup' hne (fun i => row j i z.1) ≤ z.2 j :=
  sup'_le _ _ (hz.2.1 j)

/-- With nonempty supports, `sharedRows` is the lifted set whose inner map is the vector of row
maxima and whose outer map is the sum of the heights, with unrestricted heights. -/
theorem sharedRows_eq_liftedSet (hne : ∀ j, (H j).Nonempty) :
    sharedRows D row H b =
      liftedSet D univ (fun x j => (H j).sup' (hne j) fun i => row j i x)
        (fun y => ∑ j, y j) b := by
  ext z
  simp [Pi.le_def]

/-- Taking each height equal to the maximum of its component's rows gives a point of
`sharedRows`, as soon as these maxima satisfy the budget. -/
theorem mk_sup'_mem_sharedRows (hne : ∀ j, (H j).Nonempty) {x : X} (hx : x ∈ D)
    (hb : ∑ j, (H j).sup' (hne j) (fun i => row j i x) ≤ b) :
    (x, fun j => (H j).sup' (hne j) fun i => row j i x) ∈ sharedRows D row H b := by
  rw [sharedRows_eq_liftedSet hne]
  exact graph_mem_liftedSet (mapsTo_univ _ _) (mem_originalSet_iff.2 ⟨hx, hb⟩)

variable [IsOrderedAddMonoid β]

/-- **Elimination of shared heights through row maxima.** With nonempty supports, `x` admits
heights in `sharedRows` if and only if `x ∈ D` and the row maxima sum to at most `b`. -/
theorem exists_mem_sharedRows_iff_sum_sup'_le (hne : ∀ j, (H j).Nonempty) (x : X) :
    (∃ y, (x, y) ∈ sharedRows D row H b) ↔
      x ∈ D ∧ ∑ j, (H j).sup' (hne j) (fun i => row j i x) ≤ b := by
  rw [sharedRows_eq_liftedSet hne]
  exact (mem_originalSet_iff_exists_mem_liftedSet (mapsTo_univ _ _)
    (fun (y : κ → β) _ (y' : κ → β) _ (hy : y ≤ y') => sum_le_sum fun j _ => hy j) x).symm.trans
    mem_originalSet_iff

/-- Set form of `exists_mem_sharedRows_iff_sum_sup'_le`. -/
theorem fst_image_sharedRows (hne : ∀ j, (H j).Nonempty) :
    Prod.fst '' sharedRows D row H b =
      {x | x ∈ D ∧ ∑ j, (H j).sup' (hne j) (fun i => row j i x) ≤ b} := by
  ext x
  simpa only [mem_image, Prod.exists, exists_and_right, exists_eq_right, mem_ofPred_eq] using
    exists_mem_sharedRows_iff_sum_sup'_le hne x

end SemilatticeSup

variable [LinearOrder β] [IsOrderedAddMonoid β]

/-- **Elimination of shared heights through mixed choices.** With nonempty supports, `x` admits
heights in `sharedRows` if and only if `x ∈ D` and every choice of one support row per component
has sum at most `b`. -/
theorem exists_mem_sharedRows_iff_forall_sum_le (hne : ∀ j, (H j).Nonempty) (x : X) :
    (∃ y, (x, y) ∈ sharedRows D row H b) ↔
      x ∈ D ∧ ∀ c : κ → ι, (∀ j, c j ∈ H j) → ∑ j, row j (c j) x ≤ b := by
  classical
  rw [exists_mem_sharedRows_iff_sum_sup'_le hne, sum_univ_sup' H hne fun j i => row j i x,
    sup'_le_iff]
  simp only [Fintype.mem_piFinset]

end Shared

/-- **Empty support.** For heights in a directed additive group, if some component has no support
rows, then its height is unconstrained from below, so every point of `D` admits heights in
`sharedRows`. -/
theorem exists_mem_sharedRows_iff_of_eq_empty [Fintype κ] [AddCommGroup β] [Preorder β]
    [IsDirectedOrder β] {D : Set X} {row : κ → ι → X → β} {H : κ → Finset ι} {b : β}
    {j₀ : κ} (h₀ : H j₀ = ∅) (x : X) :
    (∃ y, (x, y) ∈ sharedRows D row H b) ↔ x ∈ D := by
  classical
  refine ⟨fun ⟨_, hy⟩ => hy.1, fun hx => ?_⟩
  choose M hM using fun j => ((H j).image fun i => row j i x).exists_le
  refine ⟨Function.update M j₀ (b - ∑ j ∈ univ \ {j₀}, M j), hx, fun j i hi => ?_, ?_⟩
  · have hj : j ≠ j₀ := by rintro rfl; simp [h₀] at hi
    simpa only [Function.update_of_ne hj] using hM j _ (mem_image_of_mem _ hi)
  · rw [sum_update_of_mem (mem_univ j₀), sub_add_cancel]

section Independent

variable [Fintype κ] [AddCommMonoid β] [Preorder β]
variable {D : Set X} {row : α → κ → X → β} {b : α → β}

/-- Every anchor's rows at a point of `independentRows` satisfy that anchor's budget. -/
theorem sum_le_of_mem_independentRows [IsOrderedAddMonoid β] {z : X × (α → κ → β)}
    (hz : z ∈ independentRows D row b) (a : α) : ∑ j, row a j z.1 ≤ b a :=
  (sum_le_sum fun j _ => (hz.2 a).1 j).trans (hz.2 a).2

/-- Own-row witness: taking each anchor's heights equal to its own row values gives a point of
`independentRows`, as soon as every same-anchor sum satisfies its budget. -/
theorem mk_mem_independentRows {x : X} (hx : x ∈ D) (hb : ∀ a, ∑ j, row a j x ≤ b a) :
    (x, fun a j => row a j x) ∈ independentRows D row b :=
  ⟨hx, fun a => ⟨fun _ => le_rfl, hb a⟩⟩

/-- **Elimination of independent heights.** A point `x` admits heights in `independentRows` if and
only if `x ∈ D` and, for every anchor, the sum of that anchor's rows satisfies its budget. -/
theorem exists_mem_independentRows_iff [IsOrderedAddMonoid β] (x : X) :
    (∃ y, (x, y) ∈ independentRows D row b) ↔ x ∈ D ∧ ∀ a, ∑ j, row a j x ≤ b a :=
  ⟨fun ⟨_, hy⟩ => ⟨hy.1, sum_le_of_mem_independentRows hy⟩,
    fun ⟨hx, hb⟩ => ⟨_, mk_mem_independentRows hx hb⟩⟩

/-- Set form of `exists_mem_independentRows_iff`. -/
theorem fst_image_independentRows [IsOrderedAddMonoid β] :
    Prod.fst '' independentRows D row b = {x | x ∈ D ∧ ∀ a, ∑ j, row a j x ≤ b a} := by
  ext x
  simpa only [mem_image, Prod.exists, exists_and_right, exists_eq_right, mem_ofPred_eq] using
    exists_mem_independentRows_iff x

/-- Shared heights over all anchors give independent heights: repeating a shared height vector
for every anchor satisfies each anchor's rows and the common budget. -/
theorem mk_const_mem_independentRows_of_mem_sharedRows [Fintype α] {b : β}
    {z : X × (κ → β)} (hz : z ∈ sharedRows D (fun j a => row a j) (fun _ => univ) b) :
    (z.1, fun _ => z.2) ∈ independentRows D row fun _ => b :=
  ⟨hz.1, fun a => ⟨fun j => hz.2.1 j a (mem_univ a), hz.2.2⟩⟩

/-- **Shared heights are tighter than independent heights.** With every anchor in the support of
every component, the projection of `sharedRows` is contained in that of `independentRows` with the
same budget at each anchor. -/
theorem fst_image_sharedRows_subset_fst_image_independentRows [Fintype α] {b : β} :
    Prod.fst '' sharedRows D (fun j a => row a j) (fun _ => univ) b ⊆
      Prod.fst '' independentRows D row fun _ => b := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨_, mk_const_mem_independentRows_of_mem_sharedRows hz, rfl⟩

end Independent

end TauCeti.ConvexLifting

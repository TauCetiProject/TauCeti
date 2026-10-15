/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Diagram.Components

/-!
# One blocked marking per link component

A component blocking is a finite set of columns containing exactly one column from each
component cycle. It records the `O`-markings whose variables are set to zero in the simply
blocked link complex. Such selections exist even for the empty grid, and their cardinality
is the number of link components. On a knot grid every singleton is a selection.

The convention follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Definition 8.2.7.
-/

public section

namespace TauCeti
namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- Exactly one of the selected columns lies on each link component. -/
def IsComponentBlocking (B : Finset (Fin n)) : Prop :=
  ∀ σ ∈ G.componentCycles, (B ∩ σ.support).card = 1

/-- A selection of one `O`-marking column on every link component. The finite set is the
only data; its component blocking property is a proof. -/
abbrev ComponentBlocking := {B : Finset (Fin n) // G.IsComponentBlocking B}

/-- The cardinality criterion defining a component blocking. -/
theorem isComponentBlocking_iff (B : Finset (Fin n)) :
    G.IsComponentBlocking B ↔ ∀ σ ∈ G.componentCycles, (B ∩ σ.support).card = 1 :=
  Iff.rfl

/-- A component blocking selects a unique column on each component. -/
theorem isComponentBlocking_iff_existsUnique (B : Finset (Fin n)) :
    G.IsComponentBlocking B ↔
      ∀ σ ∈ G.componentCycles, ∃! c : Fin n, c ∈ B ∧ c ∈ σ.support := by
  simp only [isComponentBlocking_iff, Finset.card_eq_one_iff_existsUnique, Finset.mem_inter]

private theorem component_support_disjoint {σ τ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ G.componentCycles) (hτ : τ ∈ G.componentCycles) (hne : σ ≠ τ) :
    Disjoint σ.support τ.support :=
  (G.componentPerm.cycleFactorsFinset_pairwise_disjoint
    (by simpa only [G.componentCycles_def, Finset.mem_coe] using hσ)
    (by simpa only [G.componentCycles_def, Finset.mem_coe] using hτ) hne).disjoint_support

/-- Every grid admits a selection of one `O`-marking on each component. -/
theorem exists_isComponentBlocking : ∃ B, G.IsComponentBlocking B := by
  classical
  let pick (σ : G.componentCycles) : Fin n :=
    ((G.mem_componentCycles_iff σ).mp σ.property).1.nonempty_support.choose
  have hpick (σ : G.componentCycles) : pick σ ∈ (σ : Equiv.Perm (Fin n)).support :=
    ((G.mem_componentCycles_iff σ).mp σ.property).1.nonempty_support.choose_spec
  refine ⟨Finset.univ.image pick, (G.isComponentBlocking_iff_existsUnique _).mpr ?_⟩
  intro σ hσ
  refine ⟨pick ⟨σ, hσ⟩, ⟨Finset.mem_image.mpr ⟨⟨σ, hσ⟩, Finset.mem_univ _, rfl⟩,
    hpick ⟨σ, hσ⟩⟩, ?_⟩
  rintro c ⟨hc, hcs⟩
  obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hc
  have heq : (τ : Equiv.Perm (Fin n)) = σ := by
    by_contra hne
    exact Finset.disjoint_left.mp (G.component_support_disjoint τ.property hσ hne)
      (hpick τ) hcs
  exact congrArg pick (Subtype.ext heq)

/-- The type of component blockings is inhabited for every grid, including the empty grid. -/
instance : Nonempty G.ComponentBlocking := by
  obtain ⟨B, hB⟩ := G.exists_isComponentBlocking
  exact ⟨⟨B, hB⟩⟩

/-- A component blocking contains as many columns as there are link components. -/
theorem IsComponentBlocking.card {B : Finset (Fin n)} (hB : G.IsComponentBlocking B) :
    B.card = G.componentCount := by
  classical
  have hcover : G.componentCycles.biUnion (fun σ => B ∩ σ.support) = B := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨σ, _, hc, _⟩
      exact hc
    · intro hc
      have hs : c ∈ G.componentPerm.support := by simp
      obtain ⟨σ, hσ, hcs⟩ :=
        Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hs
      exact ⟨σ, by simpa only [G.componentCycles_def, Finset.mem_coe] using hσ, hc, hcs⟩
  rw [← hcover, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun σ hσ => hB σ hσ]
    simp
  · intro σ hσ τ hτ hne
    exact (G.component_support_disjoint hσ hτ hne).mono
      Finset.inter_subset_right Finset.inter_subset_right

/-- On a knot grid, blocking any single `O`-marking blocks exactly one on every component. -/
theorem IsKnot.isComponentBlocking_singleton (hG : G.IsKnot) (i : Fin n) :
    G.IsComponentBlocking {i} := by
  intro σ hσ
  have hcycles : G.componentCycles = {G.componentPerm} :=
    by simpa only [G.componentCycles_def] using
      (G.isKnot_iff_componentPerm_isCycle.mp hG).cycleFactorsFinset_eq_singleton
  rw [hcycles, Finset.mem_singleton] at hσ
  subst σ
  simp

-- Two disjoint transpositions give two components; one selected column comes from each.
example :
    let G : GridDiagram 4 :=
      ⟨⟨1⟩, ⟨Equiv.swap 0 1 * Equiv.swap 2 3⟩, by decide⟩
    G.IsComponentBlocking {0, 2} := by
  dsimp only
  rw [isComponentBlocking_iff, componentCycles_def, componentPerm_def]
  simp only [mul_inv_rev, Equiv.swap_inv, mul_one]
  have hd : Equiv.Perm.Disjoint (Equiv.swap (2 : Fin 4) 3) (Equiv.swap 0 1) := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    decide
  rw [hd.cycleFactorsFinset_mul_eq_union,
    (Equiv.Perm.isCycle_swap (by decide : (2 : Fin 4) ≠ 3)).cycleFactorsFinset_eq_singleton,
    (Equiv.Perm.isCycle_swap (by decide : (0 : Fin 4) ≠ 1)).cycleFactorsFinset_eq_singleton]
  intro σ hσ
  simp only [Finset.mem_union, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl <;> decide

end GridDiagram
end TauCeti

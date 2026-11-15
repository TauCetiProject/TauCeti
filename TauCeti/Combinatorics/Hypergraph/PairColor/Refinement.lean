/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular

/-!
# Refining coherent pair colors by Boolean tests

`PairColorSystem.refine` retains an existing pair color and records a family of Boolean tests
in both orientations. Recording the reversed tests as well preserves palette reversal even
when the tests are directed. Equal refined colors therefore imply equal original colors and
agreement on every test. For finitely many tests, the palette grows by a factor of four per test.

This construction lets a lower skeleton distinguish selected pair subgraphs without changing
its vertex cells, as needed when refining along subpolyad irregularity witnesses.
-/

public section

namespace TauCeti.PairColorSystem

variable {κ V ι : Type*}

/-- Refine a coherent pair coloring by Boolean tests, retaining the original color and the test
values in both orientations. Reversal reverses the original color and exchanges the two test
vectors. -/
def refine (S : PairColorSystem κ V)
    (test : ι → {p : V × V // p.1 ≠ p.2} → Bool) :
    PairColorSystem (κ × (ι → Bool) × (ι → Bool)) V where
  color p := (S.color p, (fun i ↦ test i p), fun i ↦ test i ⟨p.val.swap, p.property.symm⟩)
  rev c := (S.rev c.1, c.2.2, c.2.1)
  rev_involutive c := by simp [S.rev_rev]
  color_rev p := by simp [S.color_rev]

/-- A refined color records the original color and both orientations of the tests. -/
@[simp]
theorem refine_color (S : PairColorSystem κ V)
    (test : ι → {p : V × V // p.1 ≠ p.2} → Bool)
    (p : {p : V × V // p.1 ≠ p.2}) :
    (S.refine test).color p =
      (S.color p, (fun i ↦ test i p), fun i ↦ test i ⟨p.val.swap, p.property.symm⟩) := (rfl)

/-- Reversal exchanges the test vectors and reverses the original color. -/
@[simp]
theorem refine_rev (S : PairColorSystem κ V)
    (test : ι → {p : V × V // p.1 ≠ p.2} → Bool)
    (c : κ × (ι → Bool) × (ι → Bool)) :
    (S.refine test).rev c = (S.rev c.1, c.2.2, c.2.1) := (rfl)

/-- Two refined colors agree exactly when the original colors and all tests in both
orientations agree. -/
theorem refine_color_eq_iff (S : PairColorSystem κ V)
    (test : ι → {p : V × V // p.1 ≠ p.2} → Bool)
    (p q : {p : V × V // p.1 ≠ p.2}) :
    (S.refine test).color p = (S.refine test).color q ↔
      S.color p = S.color q ∧ (∀ i, test i p = test i q) ∧
        ∀ i, test i ⟨p.val.swap, p.property.symm⟩ =
          test i ⟨q.val.swap, q.property.symm⟩ := by
  simp only [refine_color, Prod.mk.injEq, funext_iff]

end TauCeti.PairColorSystem

namespace TauCeti.PairSkeleton3

variable {κ V ι : Type*} [Fintype V] [DecidableEq V]

/-- Refine the pair palette to distinguish a family of directed pair sets. Both orientations
are recorded; the vertex partition is preserved exactly. -/
noncomputable def refinePairSets (S : PairSkeleton3 κ V)
    (test : ι → Finset {p : V × V // p.1 ≠ p.2}) :
    PairSkeleton3 (κ × (ι → Bool) × (ι → Bool)) V where
  vertexPart := S.vertexPart
  pairColors := S.pairColors.refine fun i p ↦ decide (p ∈ test i)

/-- Refining pair sets preserves the vertex partition. -/
@[simp]
theorem refinePairSets_vertexPart (S : PairSkeleton3 κ V)
    (test : ι → Finset {p : V × V // p.1 ≠ p.2}) :
    (S.refinePairSets test).vertexPart = S.vertexPart := (rfl)

/-- The pair coloring records membership in each test in both orientations. -/
theorem refinePairSets_pairColors (S : PairSkeleton3 κ V)
    (test : ι → Finset {p : V × V // p.1 ≠ p.2}) :
    (S.refinePairSets test).pairColors =
      S.pairColors.refine (fun i p ↦ decide (p ∈ test i)) := (rfl)

/-- Projecting a refined color recovers the original pair color. -/
@[simp]
theorem refinePairSets_color_fst (S : PairSkeleton3 κ V)
    (test : ι → Finset {p : V × V // p.1 ≠ p.2})
    (p : {p : V × V // p.1 ≠ p.2}) :
    ((S.refinePairSets test).pairColors.color p).1 = S.pairColors.color p := (rfl)

/-- Equal refined pair colors force agreement on membership in every selected pair set. -/
theorem mem_test_iff_of_refinePairSets_color_eq (S : PairSkeleton3 κ V)
    (test : ι → Finset {p : V × V // p.1 ≠ p.2})
    {p q : {p : V × V // p.1 ≠ p.2}}
    (h : (S.refinePairSets test).pairColors.color p =
      (S.refinePairSets test).pairColors.color q) (i : ι) :
    p ∈ test i ↔ q ∈ test i := by
  rw [refinePairSets_pairColors, PairColorSystem.refine_color_eq_iff] at h
  simpa only [decide_eq_decide] using h.2.1 i

end TauCeti.PairSkeleton3

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Lattice

/-!
# Uniform repeated representatives for finite colourings

Given two finite-valued colourings `A` and `B` of the natural numbers, every sufficiently
late `B`-colour has two distinct, uniformly bounded representatives that agree under `A`.
The bound is independent of the queried natural number. It does not say that occurrences
of a colour have bounded gaps.

This selection is useful when `A` and `B` encode automaton states: the two representatives
then give equal-state comparisons in one automaton and share the queried state in the other.
Finite `B`-fibres must first be excluded from the tail; infinite pigeonhole supplies a pair
in each remaining fibre.

## References

* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018), §3, p. 2:
  the choices of the infinite state fibres, their two representatives, and the common bound.
-/

public section

namespace TauCeti

/-- For two finite-valued colourings, every sufficiently late `B`-colour has two distinct
representatives below a common positive bound that agree under `A`.

The representatives need not be close to the queried `x`. -/
theorem exists_uniform_repeated_representatives {α β : Type*} [Finite α] [Finite β]
    (A : ℕ → α) (B : ℕ → β) :
    ∃ N ξ : ℕ, 1 ≤ ξ ∧ ∀ x ≥ N, ∃ u < ξ, ∃ v < ξ,
      u ≠ v ∧ B u = B x ∧ B v = B x ∧ A u = A v := by
  classical
  -- All finite fibres lie before one cutoff.
  let bad := {b : β // {n : ℕ | B n = b}.Finite}
  have hbad : (⋃ b : bad, {n : ℕ | B n = b.1}).Finite :=
    Set.finite_iUnion fun b ↦ b.2
  obtain ⟨M, hM⟩ := hbad.bddAbove
  have hinfinite (x : ℕ) (hx : M + 1 ≤ x) : {n : ℕ | B n = B x}.Infinite := by
    intro hfinite
    have hmem : x ∈ ⋃ b : bad, {n : ℕ | B n = b.1} :=
      Set.mem_iUnion.mpr ⟨⟨B x, hfinite⟩, rfl⟩
    have := hM hmem
    omega
  -- Select a collision in each infinite fibre and bound all the selected points at once.
  let good := {b : β // {n : ℕ | B n = b}.Infinite}
  have hpairs (b : good) : ∃ u, B u = b.1 ∧ ∃ v, B v = b.1 ∧ u ≠ v ∧ A u = A v :=
    b.2.exists_ne_map_eq_of_mapsTo (fun _ _ ↦ Set.mem_univ _) (Set.finite_univ :
      (Set.univ : Set α).Finite)
  choose u hu v hv hne hA using hpairs
  obtain ⟨K, hK⟩ := ((Set.finite_range u).union (Set.finite_range v)).bddAbove
  refine ⟨M + 1, K + 1, by omega, ?_⟩
  intro x hx
  let b : good := ⟨B x, hinfinite x hx⟩
  have huK := hK (Set.mem_union_left _ (Set.mem_range_self b))
  have hvK := hK (Set.mem_union_right _ (Set.mem_range_self b))
  exact ⟨u b, by omega, v b, by omega, hne b, hu b, hv b, hA b⟩

-- Constant colourings admit representatives 0 and 1, with no exceptional prefix.
example {α β : Type*} (a : α) (b : β) :
    ∀ x ≥ 0, ∃ u < 2, ∃ v < 2,
      u ≠ v ∧ (fun _ : ℕ ↦ b) u = b ∧ (fun _ : ℕ ↦ b) v = b ∧
        (fun _ : ℕ ↦ a) u = (fun _ ↦ a) v := by
  intro _ _
  exact ⟨0, by decide, 1, by decide, by decide, rfl, rfl, rfl⟩

-- A colour occurring only at zero is excluded by the cutoff; the tail uses 1 and 3.
example : ∀ x ≥ 1, ∃ u < 4, ∃ v < 4,
    u ≠ v ∧ (u == 0) = (x == 0) ∧ (v == 0) = (x == 0) ∧ u % 2 = v % 2 := by
  intro x hx
  have hx0 : x ≠ 0 := by omega
  exact ⟨1, by decide, 3, by decide, by decide, by simp [hx0], by simp [hx0], by decide⟩

-- With that exceptional colour, a zero cutoff is impossible, regardless of the bound.
example : ¬ ∃ ξ : ℕ, ∀ x ≥ 0, ∃ u < ξ, ∃ v < ξ,
    u ≠ v ∧ (u == 0) = (x == 0) ∧ (v == 0) = (x == 0) := by
  rintro ⟨ξ, h⟩
  obtain ⟨u, _, v, _, hne, hu, hv⟩ := h 0 (by omega)
  simp only [beq_self_eq_true, beq_iff_eq] at hu hv
  exact hne (hu.trans hv.symm)

end TauCeti

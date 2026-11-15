/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Basic

/-!
# Finite and infinite fibers of stack cells

A section has a finite fiber over every ambient base point. A sector of a pointwise strictly
ordered stack in a dense linear order without endpoints has an infinite fiber exactly over its
base. This requires no continuity of the section functions: a fiber fixes their base argument,
leaving an open interval.
These statements distinguish sections from sectors in dimension computations.
-/

public section

open Function Set Topology

namespace TauCeti

variable {n k : ℕ}

-- Simplify fiber predicates before simp expands membership in the image.

/-- The fiber of a section over any ambient base point is finite, even outside the base. -/
@[simp↓] theorem finite_setOf_cons_mem_image_cylinder_sectionSet {α : Type*} {C : Set (Fin n → α)}
    (θ : Fin k → C → α) (i : Fin k) (x : Fin n → α) :
    {t : α | Fin.cons t x ∈ cylinder C '' sectionSet θ i}.Finite := by
  by_cases hx : x ∈ C
  · apply (finite_singleton (θ i ⟨x, hx⟩)).subset
    intro t ht
    obtain ⟨hx', ht'⟩ := (mem_image_cylinder (y := Fin.cons t x)).mp ht
    have ht'' := mem_sectionSet.mp ht'
    simpa only [Fin.tail_cons, Fin.cons_zero, mem_singleton_iff] using ht''.symm
  · have he : {t : α | Fin.cons t x ∈ cylinder C '' sectionSet θ i} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_image_cylinder, Fin.tail_cons, Fin.cons_zero, notMem_empty,
        iff_false, not_exists]
      exact fun h ↦ (hx h).elim
    rw [he]
    exact finite_empty

/-- A sector has an infinite fiber exactly over its base. This includes unbounded sectors. -/
@[simp↓] theorem infinite_setOf_cons_mem_image_cylinder_sectorSet_iff {α : Type*} [LinearOrder α]
    [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α]
    {C : Set (Fin n → α)} {θ : Fin k → C → α}
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) (x : Fin n → α) :
    {t : α | Fin.cons t x ∈ cylinder C '' sectorSet θ j}.Infinite ↔ x ∈ C := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h.nonempty
    obtain ⟨hx, _⟩ := (mem_image_cylinder (y := Fin.cons t x)).mp ht
    simpa only [Fin.tail_cons] using hx
  · intro hx
    have he : {t : α | Fin.cons t x ∈ cylinder C '' sectorSet θ j} =
        (fun t ↦ (⟨x, hx⟩, t)) ⁻¹' sectorSet θ j := by
      ext t
      simp only [mem_ofPred_eq, mem_image_cylinder, Fin.tail_cons, Fin.cons_zero, mem_preimage]
      exact ⟨fun ⟨_, ht⟩ ↦ ht, fun ht ↦ ⟨hx, ht⟩⟩
    rw [he]
    cases k with
    | zero =>
      simpa only [sectorSet_fin_zero, preimage_univ] using (infinite_univ : (univ : Set α).Infinite)
    | succ k =>
      have hm : ∀ x, Monotone fun i ↦ θ i x := fun x ↦ (hθ x).monotone
      cases j using Fin.cases with
      | zero =>
        simpa only [sectorSet_zero hm, preimage_ofPred_eq, Iio_def] using Iio_infinite (θ 0 ⟨x, hx⟩)
      | succ j =>
        cases j using Fin.lastCases with
        | last =>
          simpa only [Fin.succ_last, sectorSet_last hm, preimage_ofPred_eq, Ioi_def] using
            Ioi_infinite (θ (Fin.last k) ⟨x, hx⟩)
        | cast i =>
          simpa only [sectorSet_castSucc_succ hm, preimage_ofPred_eq, Ioo_def] using
            Ioo_infinite (hθ ⟨x, hx⟩ i.castSucc_lt_succ)

end TauCeti

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
ordered real stack has an infinite fiber exactly over its base. This requires no continuity
of the section functions: a fiber fixes their base argument, leaving an open real interval.
These statements distinguish sections from sectors in dimension computations.
-/

public section

open Function Set Topology

namespace TauCeti

variable {n k : ℕ} {C : Set (Fin n → ℝ)} {θ : Fin k → C → ℝ}

/-- The fiber of a section over any ambient base point is finite, even outside the base. -/
theorem finite_fiber_image_cylinder_sectionSet {α : Type*} {C : Set (Fin n → α)}
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
theorem infinite_fiber_image_cylinder_sectorSet_iff
    (hθ : ∀ x, StrictMono fun i ↦ θ i x) (j : Fin (k + 1)) (x : Fin n → ℝ) :
    {t : ℝ | Fin.cons t x ∈ cylinder C '' sectorSet θ j}.Infinite ↔ x ∈ C := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h.nonempty
    obtain ⟨hx, _⟩ := (mem_image_cylinder (y := Fin.cons t x)).mp ht
    simpa only [Fin.tail_cons] using hx
  · intro hx
    have he : {t : ℝ | Fin.cons t x ∈ cylinder C '' sectorSet θ j} =
        (fun t ↦ (⟨x, hx⟩, t)) ⁻¹' sectorSet θ j := by
      ext t
      simp only [mem_ofPred_eq, mem_image_cylinder, Fin.tail_cons, Fin.cons_zero, mem_preimage]
      exact ⟨fun ⟨_, ht⟩ ↦ ht, fun ht ↦ ⟨hx, ht⟩⟩
    rw [he]
    have ho : IsOpen ((fun t : ℝ ↦ (⟨x, hx⟩, t)) ⁻¹' sectorSet θ j) := by
      convert! (isOpen_sectorSet (θ := fun i (_ : Unit) ↦ θ i ⟨x, hx⟩)
        (fun _ ↦ continuous_const) j).preimage
        (continuous_const.prodMk continuous_id : Continuous fun t : ℝ ↦ ((), t)) using 1
      ext t
      simp only [mem_preimage, mem_sectorSet]
    have hn : ((fun t : ℝ ↦ (⟨x, hx⟩, t)) ⁻¹' sectorSet θ j).Nonempty := by
      obtain ⟨z, hz, he⟩ := (fst_image_sectorSet hθ j).superset (mem_univ (⟨x, hx⟩ : C))
      exact ⟨z.2, by simpa only [mem_preimage, ← he, Prod.mk.eta] using hz⟩
    obtain ⟨t, ht⟩ := hn
    exact infinite_of_mem_nhds t (ho.mem_nhds ht)

end TauCeti

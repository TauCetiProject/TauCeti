/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset

/-!
# Infinite-set pigeonhole principles

Given a family of sets `E : ι → Set α` and a finite test set `B : Set α`, restricting each `E j`
to `B` takes values in the finite powerset `Set B`. By `Finite.exists_infinite_fiber`, any infinite
index set `S : Set ι` admits an infinite subset `S' ⊆ S` on which `x ∈ E j` is independent of
`j ∈ S'` for every `x ∈ B` (`Set.Infinite.exists_infinite_subset_mem_iff`).
-/

public section

namespace Set.Infinite

/-- **Finite-restriction pigeonhole principle**: for any family of sets `E : ι → Set α`, an
infinite index set `S` contains an infinite subset `S'` on which membership in `E j` is constant
on a finite set `B`, agreeing with membership in some subset `A ⊆ B`. -/
theorem exists_infinite_subset_mem_iff {ι α : Type*} {S : Set ι} (hS : S.Infinite)
    (E : ι → Set α) {B : Set α} (hB : B.Finite) :
    ∃ S' ⊆ S, S'.Infinite ∧ ∃ A ⊆ B, ∀ j ∈ S', ∀ x ∈ B, (x ∈ E j ↔ x ∈ A) := by
  classical
  have : Infinite S := Set.infinite_coe_iff.mpr hS
  have : Finite B := hB.to_subtype
  let g : S → Set B := fun j ↦ {x : B | x.val ∈ E j.val}
  obtain ⟨A₀, hfib⟩ := Finite.exists_infinite_fiber g
  refine ⟨Subtype.val '' (g ⁻¹' {A₀}), Subtype.coe_image_subset S _,
    (Set.infinite_coe_iff.mp hfib).image Subtype.val_injective.injOn,
    Subtype.val '' A₀, Subtype.coe_image_subset B A₀, ?_⟩
  rintro _ ⟨⟨j, hjS⟩, hjg, rfl⟩ x hxB
  have hval : ∀ z : B, z.val ∈ E j ↔ z ∈ A₀ := Set.ext_iff.mp (Set.mem_singleton_iff.mp hjg)
  constructor
  · intro hxE
    exact ⟨⟨x, hxB⟩, (hval ⟨x, hxB⟩).mp hxE, rfl⟩
  · rintro ⟨⟨y, hyB⟩, hyA, rfl⟩
    exact (hval ⟨y, hyB⟩).mpr hyA

end Set.Infinite

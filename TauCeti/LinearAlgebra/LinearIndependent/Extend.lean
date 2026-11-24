/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Extending a linearly independent family by members of a spanning family

Over a division ring, a linearly independent family `f` can be completed to a linearly independent
spanning family by adding members of any spanning family `e`, keeping track of which members were
added: `LinearIndependent.exists_linearIndependent_sumElim` gives a set `u` of indices of `e` such
that `Sum.elim f (e ∘ (↑) : u → V)` is linearly independent and spans. This is the indexed form of
Mathlib's `Basis.extendLe`, which works with sets of vectors and so cannot tell a member of `f`
from an equal member of `e`. It is Mathlib's `exists_linearIndepOn_extension` applied to the family
`Sum.elim f e`.

The typical use completes a linearly independent family of linear forms on `ι → K` by coordinate
forms, whose values at a point are bounded by its coordinates.
-/

public section

open Set Submodule

namespace LinearIndependent

variable {K V τ ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A linearly independent family `f` extends, by members of a spanning family `e`, to a linearly
independent spanning family `Sum.elim f (e ∘ (↑) : u → V)`. -/
theorem exists_linearIndependent_sumElim {f : τ → V} (hf : LinearIndependent K f) {e : ι → V}
    (he : span K (range e) = ⊤) :
    ∃ u : Set ι, LinearIndependent K (Sum.elim f fun j : u ↦ e j) ∧
      span K (range (Sum.elim f fun j : u ↦ e j)) = ⊤ := by
  set g : τ ⊕ ι → V := Sum.elim f e
  have hs : LinearIndepOn K g (range Sum.inl) := by
    rw [← image_univ]
    exact LinearIndepOn.image_of_comp Sum.inl g hf.linearIndepOn_univ
  obtain ⟨b, -, hsb, hspan, hb⟩ := exists_linearIndepOn_extension hs (subset_univ _)
  refine ⟨Sum.inr ⁻¹' b, ?_, ?_⟩
  · -- The family is `g` on `b`, reindexed by an injection of `τ ⊕ (Sum.inr ⁻¹' b)` into `b`.
    let φ : τ ⊕ (Sum.inr ⁻¹' b : Set ι) → b :=
      Sum.elim (fun k ↦ ⟨Sum.inl k, hsb (mem_range_self k)⟩) fun j ↦ ⟨Sum.inr j, j.property⟩
    have hφ : Function.Injective φ := by
      rintro (k | j) (k' | j') h <;> simp_all [φ, Subtype.ext_iff]
    convert hb.comp φ hφ using 1
    ext (k | j) <;> rfl
  · have hsub : g '' b ⊆ range (Sum.elim f fun j : (Sum.inr ⁻¹' b : Set ι) ↦ e j) := by
      rintro _ ⟨k | j, hb, rfl⟩
      · exact ⟨Sum.inl k, rfl⟩
      · exact ⟨Sum.inr ⟨j, hb⟩, rfl⟩
    refine eq_top_iff.mpr (he ▸ span_le.mpr ?_)
    rintro _ ⟨j, rfl⟩
    exact span_mono hsub (hspan ⟨Sum.inr j, trivial, rfl⟩)

end LinearIndependent

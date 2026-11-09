/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Adjoin.Basic

/-!
# Right multiplication stability of left ideals from generators

Let `J : ι → Submodule A A` be a family of left ideals of a ring `A` that is directed downwards.
The family is stable under right multiplication by `b : A` if for each `i` some `J j` satisfies
`J j * b ⊆ J i`. For an `R`-algebra `A`, the elements `b` with this property form a subalgebra, so
stability under right multiplication by a generating set implies stability under right
multiplication by every element (`TauCeti.exists_forall_mul_mem_of_adjoin_eq_top`).

This is the condition under which the smooth vectors of a module for `J` are exactly those killed
by some `J i` (`TauCeti.mem_smoothPart_iff_of_mul_mem`), and it is checked on generators for the
left ideals of enveloping algebras of current algebras.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A] {ι : Type*} {J : ι → Submodule A A}

/-- If the directed family `J` of left ideals of an `R`-algebra `A` is stable under right
multiplication by every element of a generating set `s` (for each `x ∈ s` and `i` some `J j`
satisfies `J j * x ⊆ J i`), then it is stable under right multiplication by every element of `A`. -/
theorem exists_forall_mul_mem_of_adjoin_eq_top {R : Type*} [CommSemiring R] [Algebra R A]
    (hJ : Directed (· ≥ ·) J) {s : Set A} (hs : Algebra.adjoin R s = ⊤)
    (h : ∀ x ∈ s, ∀ i, ∃ j, ∀ a ∈ J j, a * x ∈ J i) (b : A) (i : ι) :
    ∃ j, ∀ a ∈ J j, a * b ∈ J i := by
  have hb : b ∈ Algebra.adjoin R s := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction generalizing i with
  | mem x hx => exact h x hx i
  | algebraMap r =>
    refine ⟨i, fun a ha ↦ ?_⟩
    rw [← Algebra.commutes, ← Algebra.smul_def]
    exact (J i).smul_of_tower_mem r ha
  | add x y _ _ hx hy =>
    obtain ⟨j₁, h₁⟩ := hx i
    obtain ⟨j₂, h₂⟩ := hy i
    obtain ⟨j, hj₁, hj₂⟩ := hJ j₁ j₂
    exact ⟨j, fun a ha ↦ mul_add a x y ▸ add_mem (h₁ a (hj₁ ha)) (h₂ a (hj₂ ha))⟩
  | mul x y _ _ hx hy =>
    obtain ⟨j₁, h₁⟩ := hy i
    obtain ⟨j, hj⟩ := hx j₁
    exact ⟨j, fun a ha ↦ mul_assoc a x y ▸ h₁ _ (hj a ha)⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite covers of generated subgroups

A family of left cosets covers a generated subgroup if it contains the identity and is
preserved by multiplication by every generator and its inverse. The preservation conditions
are expressed as membership of the Schreier residues in the subgroup of the cosets.
They give a normal form, hence a cardinal bound when the family and subgroup are finite.

Iterating `Subgroup.natCard_closure_le_mul` gives upper bounds from stabilizer chains.
Unlike the full Schreier generation theorem, this bound does not require that the
representatives form a transversal or that they belong to the generated subgroup.
-/

public section

namespace Subgroup

variable {G α β : Type*} [Group G]

/-- Schreier residues in `H` give a left-coset normal form for the generated subgroup. -/
theorem exists_eq_mul_of_mem_closure (s : α → G) (t : β → G) (H : Subgroup G)
    (hone : ∃ i, t i = 1)
    (hstep : ∀ a i, ∃ j, (t j)⁻¹ * s a * t i ∈ H)
    (hinv : ∀ a i, ∃ j, (t j)⁻¹ * (s a)⁻¹ * t i ∈ H)
    {g : G} (hg : g ∈ closure (Set.range s)) :
    ∃ i, ∃ h : H, g = t i * h := by
  induction hg using closure_induction_left with
  | one =>
    obtain ⟨i, hi⟩ := hone
    exact ⟨i, 1, by simp only [hi, OneMemClass.coe_one, mul_one]⟩
  | mul_left x hx y _ ih =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨i, h, rfl⟩ := ih
    obtain ⟨j, hj⟩ := hstep a i
    refine ⟨j, ⟨_, H.mul_mem hj h.property⟩, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left]
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨i, h, rfl⟩ := ih
    obtain ⟨j, hj⟩ := hinv a i
    refine ⟨j, ⟨_, H.mul_mem hj h.property⟩, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left]

/-- A finite Schreier cover bounds the number of elements of a generated subgroup. -/
theorem natCard_closure_le_mul (s : α → G) (t : β → G) (H : Subgroup G)
    [Finite β] [Finite H] (hone : ∃ i, t i = 1)
    (hstep : ∀ a i, ∃ j, (t j)⁻¹ * s a * t i ∈ H)
    (hinv : ∀ a i, ∃ j, (t j)⁻¹ * (s a)⁻¹ * t i ∈ H) :
    Nat.card (closure (Set.range s)) ≤ Nat.card β * Nat.card H := by
  classical
  have hnormal (g : closure (Set.range s)) :
      ∃ p : β × H, (g : G) = t p.1 * p.2 := by
    obtain ⟨i, h, hh⟩ :=
      exists_eq_mul_of_mem_closure s t H hone hstep hinv g.property
    exact ⟨(i, h), hh⟩
  choose f hf using hnormal
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rw [hf x, hf y, hxy]
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hinj

end Subgroup

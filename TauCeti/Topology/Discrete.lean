/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Order

/-!
# Continuous inverse evaluation on discrete spaces

Pointwise continuous families of equivalences have continuous inverse evaluation when the
target space is discrete.

This supplies continuity of inverse permutation evaluation in
`TauCeti.WreathProduct.continuous_right_inv` and inverse coset translation in
`Subgroup.continuous_inv_smul_const`, over a discrete index or coset quotient.
-/

public section

namespace TauCeti

/-- Inverse evaluation of a family of equivalences on a discrete space is continuous if every
forward evaluation is continuous. -/
theorem continuous_equiv_symm_apply {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [DiscreteTopology β] {f : α → β ≃ β}
    (hf : ∀ b, Continuous fun a => f a b) (b : β) :
    Continuous fun a => (f a).symm b := by
  rw [continuous_discrete_rng]
  intro c
  have h : (fun a : α => (f a).symm b) ⁻¹' {c} =
      (fun a : α => f a c) ⁻¹' {b} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (Equiv.symm_apply_eq (e := f a) (x := b) (y := c)).trans eq_comm
  rw [h]
  exact (isOpen_discrete _).preimage (hf c)

end TauCeti

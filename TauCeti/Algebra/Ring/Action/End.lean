/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Ring.Action.End

/-!
# The kernel of the automorphism representation of a group acting on a ring

A group `G` acting on a semiring `S` by ring automorphisms is represented by
`MulSemiringAction.toRingAut G S`. This file reads off the kernel of that representation: an
element lies in it exactly when it fixes every element of `S`, so the kernel is trivial precisely
because the action is faithful.

## Main results

* `TauCeti.MulSemiringAction.mem_ker_toRingAut_iff`: membership in the kernel is acting trivially
  on every element.
* `TauCeti.MulSemiringAction.ker_toRingAut_eq_bot`: a faithful action is a faithful
  representation.
-/

public section

namespace TauCeti.MulSemiringAction

variable {G : Type*} [Group G] {S : Type*} [Semiring S] [MulSemiringAction G S]

/-- Membership in the kernel of the automorphism representation means acting trivially on every
element. -/
theorem mem_ker_toRingAut_iff {σ : G} :
    σ ∈ MonoidHom.ker (_root_.MulSemiringAction.toRingAut G S) ↔ ∀ x : S, σ • x = x := by
  simp [MonoidHom.mem_ker, RingEquiv.ext_iff]

/-- A faithful action by ring automorphisms has trivial kernel. -/
theorem ker_toRingAut_eq_bot [FaithfulSMul G S] :
    MonoidHom.ker (_root_.MulSemiringAction.toRingAut G S) = ⊥ := by
  ext σ
  rw [mem_ker_toRingAut_iff, Subgroup.mem_bot]
  exact ⟨fun h ↦ eq_of_smul_eq_smul fun x : S ↦ by rw [h x, one_smul],
    fun h x ↦ by rw [h, one_smul]⟩

end TauCeti.MulSemiringAction

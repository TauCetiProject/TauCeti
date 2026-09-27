/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Ring.Action.End

/-!
# The kernel of the automorphism representation of a group acting on a ring

A group `G` acting on a semiring `S` by ring automorphisms is represented by
`MulSemiringAction.toRingAut G S`. This file reads off the kernel of that representation: an
element lies in it exactly when it fixes every element of `S`, so the kernel is trivial precisely
because the action is faithful. When `S` is moreover generated over a base ring `R` by a single
element `ξ` and the action is by `R`-algebra maps, faithfulness can be tested at `ξ` alone.

## Main results

* `TauCeti.MulSemiringAction.mem_ker_toRingAut_iff`: membership in the kernel is acting trivially
  on every element.
* `TauCeti.MulSemiringAction.ker_toRingAut_eq_bot`: a faithful action is a faithful
  representation.
* `TauCeti.eq_one_of_smul_eq_of_adjoin_singleton_eq_top`: for a faithful action by `R`-algebra
  maps, only the identity fixes a single generator of `S` over `R`.
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

namespace TauCeti

variable {G : Type*} [Monoid G] {S : Type*} [Semiring S] [MulSemiringAction G S]
variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/-- For a faithful action by `R`-algebra maps on `S = R[ξ]`, an element fixing the generator `ξ`
is the identity. -/
theorem eq_one_of_smul_eq_of_adjoin_singleton_eq_top [FaithfulSMul G S] {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) {σ : G} (h : σ • ξ = ξ) : σ = 1 := by
  refine eq_of_smul_eq_smul fun x : S ↦ ?_
  have hx : x ∈ Algebra.adjoin R {ξ} := hξ ▸ Algebra.mem_top
  rw [one_smul]
  exact (Algebra.forall_mem_adjoin_smul_eq_self_iff {ξ} σ).2 (Set.forall_mem_singleton.2 h) x hx

end TauCeti

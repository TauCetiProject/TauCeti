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
element lies in it exactly when it fixes every element of `S`, so a faithful action has trivial
kernel. When `S` is moreover generated over a base ring `R` by a single element `ξ` and a monoid
acts faithfully by `R`-algebra maps, the action is already determined by where it sends `ξ`.
The file also records the product-displacement identity for a ring action.

## Main results

* `TauCeti.MulSemiringAction.mem_ker_toRingAut_iff`: membership in the kernel is acting trivially
  on every element.
* `TauCeti.MulSemiringAction.ker_toRingAut_eq_bot`: a faithful action is a faithful
  representation.
* `TauCeti.smul_mul_sub_mul`: product-displacement identity for a ring action.
* `TauCeti.smul_left_injective_of_adjoin_singleton_eq_top`: for a faithful action of a monoid by
  `R`-algebra maps, distinct elements move a single generator of `S` over `R` to distinct elements.
* `TauCeti.eq_one_of_smul_eq_of_adjoin_singleton_eq_top`: under the same hypotheses, only the
  identity fixes the generator.
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
    MonoidHom.ker (_root_.MulSemiringAction.toRingAut G S) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun σ hσ ↦ eq_of_smul_eq_smul fun x : S ↦ by
    rw [mem_ker_toRingAut_iff.1 hσ x, one_smul]

end TauCeti.MulSemiringAction

namespace TauCeti

/-- Product-displacement identity for a ring action: `σ • (a * b) - a * b` splits into a left
displacement `(σ • a - a) * (σ • b)` and a right displacement `a * (σ • b - b)`. -/
theorem smul_mul_sub_mul {G : Type*} [Monoid G] {S : Type*} [Ring S] [MulSemiringAction G S]
    (σ : G) (a b : S) :
    σ • (a * b) - a * b = (σ • a - a) * (σ • b) + a * (σ • b - b) := by
  rw [smul_mul', sub_mul, mul_sub, sub_add_sub_cancel]

variable {G : Type*} [Monoid G] {S : Type*} [Semiring S] [MulSemiringAction G S]
variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/-- For a faithful action by `R`-algebra maps on `S = R[ξ]`, the orbit map at `ξ` is injective. -/
theorem smul_left_injective_of_adjoin_singleton_eq_top [FaithfulSMul G S] {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) : Function.Injective fun σ : G ↦ σ • ξ :=
  fun _ _ h ↦ MulSemiringAction.toAlgHom_injective R S <|
    AlgHom.ext_of_adjoin_eq_top hξ <| Set.eqOn_singleton.2 h

/-- For a faithful action by `R`-algebra maps on `S = R[ξ]`, an element fixing the generator `ξ`
is the identity. -/
theorem eq_one_of_smul_eq_of_adjoin_singleton_eq_top [FaithfulSMul G S] {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) {σ : G} (h : σ • ξ = ξ) : σ = 1 :=
  smul_left_injective_of_adjoin_singleton_eq_top hξ <| h.trans (one_smul G ξ).symm

end TauCeti

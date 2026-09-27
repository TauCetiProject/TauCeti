/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Conjugation by an element of a normal subgroup, seen through a commutative target

A normal subgroup `N` of `G` carries the conjugation action `MulAut.conjNormal` of the whole of
`G`. Conjugation by an element of `N` itself is inner, so a homomorphism `ψ : N →* M` to a
*commutative* monoid cannot see it: conjugate elements of `N` have the same image in `M`.

Dually, conjugation cannot move a *central* element: a subgroup containing one has every
conjugate containing it too.

## Main statements

* `MonoidHom.map_conjNormal_val`: a homomorphism from a normal subgroup to a commutative monoid is
  unchanged by conjugation by an element of that subgroup.
* `Subgroup.mem_conjAct_smul_of_mem_center`: a central element of a subgroup lies in each of its
  conjugates.
* `Subgroup.inclusion_conj_smul`: the inclusion of a normal subgroup into a larger normal
  subgroup commutes with conjugation.
-/

public section

namespace MonoidHom

variable {G M : Type*} [Group G] [CommMonoid M] {N : Subgroup G} [N.Normal]

/-- **Conjugation by an element of a normal subgroup does not move a homomorphism from that
subgroup to a commutative monoid**: conjugate elements have the same image in a commutative
target. -/
@[simp]
theorem map_conjNormal_val (ψ : N →* M) (a x : N) : ψ (MulAut.conjNormal (a : G) x) = ψ x := by
  have h : IsConj x (MulAut.conjNormal (a : G) x) :=
    isConj_iff.mpr ⟨a, by rw [MulAut.conjNormal_val, MulAut.conj_apply]⟩
  exact (isConj_iff_eq.mp (ψ.map_isConj h)).symm

end MonoidHom

namespace Subgroup

open scoped Pointwise

/-- **A central element of a subgroup lies in each of its conjugates**, since conjugation fixes
it. -/
theorem mem_conjAct_smul_of_mem_center {G : Type*} [Group G] {H : Subgroup G} {z : G}
    (hz : z ∈ center G) (c : G) (h : z ∈ H) : z ∈ ConjAct.toConjAct c • H := by
  rw [mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct,
    inv_inv, mem_center_iff.mp hz c⁻¹, inv_mul_cancel_right]
  exact h

/-- The inclusion of a normal subgroup `H` into a larger normal subgroup `K` commutes with the
conjugation actions of `ConjAct G` on `H` and on `K`. -/
theorem inclusion_conj_smul {G : Type*} [Group G] {H K : Subgroup G} [H.Normal] [K.Normal]
    (h : H ≤ K) (g : ConjAct G) (x : H) : inclusion h (g • x) = g • inclusion h x :=
  Subtype.ext <| by
    rw [coe_inclusion, ConjAct.Subgroup.val_conj_smul, ConjAct.Subgroup.val_conj_smul,
      coe_inclusion]

end Subgroup

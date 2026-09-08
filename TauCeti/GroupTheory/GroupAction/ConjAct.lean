/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation by an element of a normal subgroup, seen through a commutative target

A normal subgroup `N` of `G` carries the conjugation action `MulAut.conjNormal` of the whole of
`G`. Conjugation by an element of `N` itself is inner, so a homomorphism `ψ : N →* M` to a
*commutative* monoid cannot see it: conjugate elements of `N` have the same image in `M`.

## Main statements

* `MonoidHom.map_conjNormal_val`: a homomorphism from a normal subgroup to a commutative monoid is
  unchanged by conjugation by an element of that subgroup.
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

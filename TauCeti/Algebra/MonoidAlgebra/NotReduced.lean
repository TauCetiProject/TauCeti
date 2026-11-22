/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# A monoid algebra is non-reduced in the presence of `p`-torsion

This file records the failure of the monoid algebra `R[G]` of a monoid `G` to be
reduced whenever `R` has prime characteristic `p` and `G` has a nontrivial element killed by `p`.

The mechanism is the freshman's dream: if `g ≠ 1` with `g ^ p = 1`, then in characteristic `p`
the group-like element `single g 1` and the identity `1 = single 1 1` satisfy
`(single g 1 - 1) ^ p = single (g ^ p) 1 - 1 = single 1 1 - 1 = 0`, while `single g 1 - 1 ≠ 0`
by `TauCeti.single_sub_one_ne_zero_iff`. So `single g 1 - 1` is a nonzero nilpotent and `R[G]`
is not reduced. The coefficient ring need not be commutative.

## Main declarations

* `TauCeti.single_sub_one_pow_eq_zero`: `(single g 1 - 1) ^ p = 0` when `g ^ p = 1`, in
  characteristic `p`.
* `TauCeti.isNilpotent_single_sub_one`: the element `single g 1 - 1` is nilpotent.
* `TauCeti.not_isReduced_monoidAlgebra`: `R[G]` is not reduced when `G` has nontrivial
  `p`-torsion and `R` has characteristic `p`.
* `TauCeti.not_isReduced_monoidAlgebra_of_not_isUnit_card`: over a field, noninvertibility
  of the order of a finite group forces its group algebra to be non-reduced.

## References

The freshman's-dream identity `(x - y) ^ p = x ^ p - y ^ p` in characteristic `p`, for commuting
`x` and `y`, is Mathlib's `sub_pow_char_of_commute`; it applies because `single g 1` commutes
with `1`. The monomial power law `single m r ^ n = single (m ^ n) (r ^ n)` is Mathlib's
`MonoidAlgebra.single_pow`.
The characteristic of the monoid algebra is transported from that of `R` along the injective
ring homomorphism `MonoidAlgebra.singleOneRingHom` (`charP_of_injective_ringHom`).
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] {G : Type*} [Monoid G]
variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- In characteristic `p`, the `p`-th power of `single g 1 - 1` vanishes when `g ^ p = 1`. -/
theorem single_sub_one_pow_eq_zero {g : G} (hgp : g ^ p = 1) :
    (MonoidAlgebra.single g (1 : R) - 1) ^ p = 0 := by
  have : CharP (MonoidAlgebra R G) p :=
    charP_of_injective_ringHom (f := MonoidAlgebra.singleOneRingHom)
      MonoidAlgebra.single_right_injective p
  rw [sub_pow_char_of_commute p (Commute.one_right _), MonoidAlgebra.single_pow,
    one_pow, hgp, one_pow,
    ← MonoidAlgebra.one_def, sub_self]

/-- The group-like difference `single g 1 - 1` is nilpotent when `g ^ p = 1` in characteristic
`p`. -/
theorem isNilpotent_single_sub_one {g : G} (hgp : g ^ p = 1) :
    IsNilpotent (MonoidAlgebra.single g (1 : R) - 1) :=
  ⟨p, single_sub_one_pow_eq_zero p hgp⟩

/-- **A monoid algebra with `p`-torsion is non-reduced in characteristic `p`.** If `R` has
characteristic `p` and `G` has a nontrivial element `g` with `g ^ p = 1`, then `R[G]` is not
reduced. -/
theorem not_isReduced_monoidAlgebra {g : G} (hg : g ≠ 1) (hgp : g ^ p = 1) :
    ¬ IsReduced (MonoidAlgebra R G) := by
  intro h
  have := h
  have : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.out.ne_one
  exact single_sub_one_ne_zero_iff.mpr hg
    (isNilpotent_iff_eq_zero.mp (isNilpotent_single_sub_one (R := R) p hgp))

/-- If the order of a finite group vanishes in a field, its group algebra is
non-reduced. Cauchy's theorem supplies a nontrivial element of order the characteristic. -/
theorem not_isReduced_monoidAlgebra_of_not_isUnit_card
    (k G : Type*) [Field k] [Group G] [Finite G]
    (h : ¬ IsUnit (Nat.card G : k)) : ¬ IsReduced (MonoidAlgebra k G) := by
  rw [isUnit_iff_ne_zero] at h
  have hdiv : ringChar k ∣ Nat.card G :=
    (CharP.cast_eq_zero_iff k (ringChar k) _).mp (not_ne_iff.mp h)
  have hp : (ringChar k).Prime :=
    (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right
      (fun hzero => Nat.card_pos.ne' (zero_dvd_iff.mp (hzero ▸ hdiv)))
  let : Fact (ringChar k).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) (ringChar k) hdiv
  have hgne : g ≠ 1 := by
    intro hgone
    simp only [hgone, orderOf_one] at hg
    exact hp.ne_one hg.symm
  exact not_isReduced_monoidAlgebra (R := k) (ringChar k) hgne
    (hg ▸ pow_orderOf_eq_one g)

end TauCeti

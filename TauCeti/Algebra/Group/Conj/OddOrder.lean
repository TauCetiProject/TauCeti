/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj
public import TauCeti.Algebra.Group.SquareRoot

/-!
# Real elements of a group of odd order

An element `g` of a group is *real* when it is conjugate to its inverse, and a conjugacy class is
real (`TauCeti.IsRealClass`) when its members are. In a group of odd order the identity is the only
real element. If `h g h⁻¹ = g⁻¹`, then `h²` commutes with `g`; the order of `h` is odd, so `h` is a
power of `h²` and commutes with `g` as well, whence `g = g⁻¹`. Finally, squaring is a bijection of a
group of odd order, so `g * g = 1` forces `g = 1` (`TauCeti.mul_self_eq_one_iff_of_odd_card`).

Consequently a group of odd order has exactly one real conjugacy class. Over the complex numbers,
the number of real classes is the number of real-valued irreducible characters, so this count says
that the trivial character is the only real-valued irreducible character of a group of odd order;
this is a theorem of Burnside.

## Main statements

* `TauCeti.isConj_inv_iff_of_odd_card`: in a group of odd order, `g` is conjugate to `g⁻¹` only for
  `g = 1`.
* `TauCeti.isRealClass_iff_of_odd_card` and `TauCeti.card_realClasses_of_odd_card`: the identity
  class is the only real class.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Problem 3.16.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), Exercise 13.9.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **In a group of odd order the identity is the only element conjugate to its inverse.**

If `h g h⁻¹ = g⁻¹`, then `h²` commutes with `g`; the order of `h` divides the order of the group,
so it is odd and `h` is a power of `h²`. Hence `h` commutes with `g`, so `g = g⁻¹`. -/
theorem isConj_inv_iff_of_odd_card (hG : Odd (Nat.card G)) {g : G} :
    IsConj g g⁻¹ ↔ g = 1 := by
  refine ⟨fun hg => ?_, fun h => by simp [h]⟩
  obtain ⟨u, hu⟩ := hg
  -- `u` inverts `g`, so `u²` commutes with `g`.
  have hsq : Commute ((u : G) ^ 2) g := by
    rw [pow_two]
    exact (inv_inv g ▸ hu.inv_right).mul_left hu
  -- The order of `u` is odd, so `u` is a power of `u²`.
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (Nat.coprime_two_left.mpr (hG.of_dvd_nat (orderOf_dvd_natCard (u : G))))
  have hcomm : Commute (u : G) g := hm ▸ hsq.pow_left m
  rw [← mul_self_eq_one_iff_of_odd_card hG]
  exact mul_eq_one_iff_eq_inv.mpr (mul_right_cancel (hcomm.eq.symm.trans hu.eq))

/-- **In a group of odd order the identity class is the only real conjugacy class.** -/
theorem isRealClass_iff_of_odd_card (hG : Odd (Nat.card G)) {C : ConjClasses G} :
    IsRealClass C ↔ C = 1 := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [isRealClass_mk_iff, isConj_inv_iff_of_odd_card hG, ConjClasses.one_eq_mk_one,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]

/-- **A group of odd order has exactly one real conjugacy class.** -/
theorem card_realClasses_of_odd_card (hG : Odd (Nat.card G)) :
    Nat.card {C : ConjClasses G // IsRealClass C} = 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun _ => isRealClass_iff_of_odd_card hG),
    Nat.card_unique]

end TauCeti

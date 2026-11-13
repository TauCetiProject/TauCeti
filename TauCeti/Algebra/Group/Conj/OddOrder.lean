/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj

/-!
# Real elements of a group of odd order

An element `g` of a group is *real* when it is conjugate to its inverse, and a conjugacy class is
real (`TauCeti.IsRealClass`) when its members are. In a group of odd order the identity is the only
real element. If `h g h⁻¹ = g⁻¹`, then `h²` commutes with `g`; the order of `h` is odd, so `h` is a
power of `h²` and commutes with `g` as well, whence `g = g⁻¹`. Finally, squaring is a bijection of a
group of odd order (`Nat.Coprime.pow_left_bijective`), so `g * g = 1` forces `g = 1`.

Consequently a group of odd order has exactly one real conjugacy class and exactly one solution of
`g * g = 1`. Over the complex numbers, the number of real classes is the number of real-valued
irreducible characters, so these counts say that the trivial character is the only real-valued
irreducible character of a group of odd order; this is a theorem of Burnside.

## Main statements

* `TauCeti.mul_self_eq_one_iff_of_odd_card` and `TauCeti.card_squareRoot_one_of_odd_card`: in a
  group of odd order, `g * g = 1` only for `g = 1`.
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

/-- In a group of odd order, `g * g = 1` only for `g = 1`: squaring is a bijection, since `2` is
coprime to the order. -/
theorem mul_self_eq_one_iff_of_odd_card (hG : Odd (Nat.card G)) {g : G} :
    g * g = 1 ↔ g = 1 := by
  refine ⟨fun h => (Nat.coprime_two_right.mpr hG).pow_left_bijective.1 ?_, fun h => by simp [h]⟩
  simp only [pow_two, h, mul_one]

/-- **A group of odd order has exactly one solution of `g * g = 1`**, the identity. -/
theorem card_squareRoot_one_of_odd_card (hG : Odd (Nat.card G)) :
    Nat.card {g : G // g * g = 1} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext <| by
    rw [(mul_self_eq_one_iff_of_odd_card hG).mp a.2, (mul_self_eq_one_iff_of_odd_card hG).mp b.2]⟩,
    ⟨⟨1, mul_one 1⟩⟩⟩

/-- **In a group of odd order the identity is the only element conjugate to its inverse.**

If `h g h⁻¹ = g⁻¹`, then `h²` commutes with `g`; the order of `h` divides the order of the group,
so it is odd and `h` is a power of `h²`. Hence `h` commutes with `g`, so `g = g⁻¹`. -/
theorem isConj_inv_iff_of_odd_card (hG : Odd (Nat.card G)) {g : G} :
    IsConj g g⁻¹ ↔ g = 1 := by
  refine ⟨fun hg => ?_, fun h => by simp [h]⟩
  obtain ⟨h, hh⟩ := isConj_iff.mp hg
  -- `h` inverts `g`, so `h²` commutes with `g`.
  have hsemi : h * g = g⁻¹ * h := by rw [← hh, inv_mul_cancel_right]
  have hsq : Commute (h ^ 2) g := by
    have hsemi' : h * g⁻¹ = g * h := by
      have hinv : (h * g * h⁻¹)⁻¹ = g := by rw [hh, inv_inv]
      rwa [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_eq_iff_eq_mul] at hinv
    rw [Commute, SemiconjBy, pow_two, mul_assoc, hsemi, ← mul_assoc, hsemi', mul_assoc]
  -- The order of `h` is odd, so `h = (h²) ^ (m + 1)` where `orderOf h = 2 * m + 1`.
  obtain ⟨m, hm⟩ := hG.of_dvd_nat (orderOf_dvd_natCard h)
  have hpow : (h ^ 2) ^ (m + 1) = h := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf h + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hcomm : Commute h g := hpow ▸ hsq.pow_left (m + 1)
  rw [← mul_self_eq_one_iff_of_odd_card hG]
  rw [hcomm.eq, mul_left_inj] at hsemi
  rw [← mul_inv_cancel g, ← hsemi]

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

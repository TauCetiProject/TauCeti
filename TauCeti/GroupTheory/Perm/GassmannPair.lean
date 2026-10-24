/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.AlmostConjugate
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.GroupTheory.Perm.Regular

/-!
# A Gassmann pair in the symmetric group on sixteen points

The groups `C₄ × C₄` and `Q₈ × C₂` both have order `16`, and both have one element of order `1`,
three of order `2` and twelve of order `4`. By
`Equiv.almostConjugate_permutationRepresentation_range_iff` their left-regular actions, numbered
by `Fin 16`, are almost-conjugate subgroups of
`Equiv.Perm (Fin 16)`. The left-regular images contain one permutation of full cycle type
`1 ^ 16` (the identity, whose raw `Equiv.Perm.cycleType` is empty), three of cycle type `2 ^ 8`
and twelve of cycle type `4 ^ 4`. By
`Equiv.exists_map_conj_permutationRepresentation_range_eq_iff` the two images are not conjugate,
because `C₄ × C₄` is abelian and `Q₈ × C₂` is not.

This is a Gassmann pair: almost-conjugate but non-conjugate subgroups. For a Galois extension of
number fields with group `S₁₆`, the fixed fields of such a pair are non-isomorphic but have the
same Dedekind zeta function (Perlis).

## Main results

* `TauCeti.exists_S16_gassmann_pair`: there are almost-conjugate subgroups of order `16` of
  `Equiv.Perm (Fin 16)` which are not conjugate.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open MulAction

namespace TauCeti

/-- The cyclic-group product `C₄ × C₄`. -/
private abbrev C4C4 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

/-- The product `Q₈ × C₂` of the quaternion group of order eight with a group of order two. -/
private abbrev Q8C2 : Type := QuaternionGroup 2 × Multiplicative (ZMod 2)

/-- Which of the powers `x ^ 0, x ^ 1, x ^ 2, x ^ 3` are trivial. -/
private def trivialPowers {M : Type*} [Monoid M] [DecidableEq M] (x : M) : Fin 4 → Bool :=
  fun k ↦ decide (x ^ (k : ℕ) = 1)

/-- An order-preserving bijection `C₄ × C₄ ≃ Q₈ × C₂`. Both groups have exponent four, and they
have equally many elements with each pattern of trivial powers. -/
private theorem exists_equiv_orderOf_eq :
    ∃ f : C4C4 ≃ Q8C2, ∀ g, orderOf (f g) = orderOf g := by
  have hcard : ∀ c : Fin 4 → Bool, Fintype.card {a : C4C4 // trivialPowers a = c} =
      Fintype.card {b : Q8C2 // trivialPowers b = c} := by decide
  have hA : ∀ a : C4C4, a ^ 4 = 1 := by decide
  have hB : ∀ b : Q8C2, b ^ 4 = 1 := by decide
  let e : ∀ c, {a // trivialPowers a = c} ≃ {b // trivialPowers b = c} := fun c ↦
    Fintype.equivOfCardEq (hcard c)
  exact ⟨Equiv.ofFiberEquiv e, fun g ↦
    orderOf_eq_orderOf_of_forall_lt_pow_eq_one_iff (by norm_num) (hB _) (hA g) fun k hk ↦ by
      simpa [trivialPowers] using congrFun (Equiv.ofFiberEquiv_map e g) ⟨k, hk⟩⟩

/-- **A Gassmann pair in `S₁₆`.** There are subgroups `H` and `K` of order `16` of the symmetric
group on sixteen points which are almost conjugate, that is, meet every conjugacy class in the
same number of elements, but are not conjugate. They are the left-regular images of `C₄ × C₄` and
`Q₈ × C₂`. -/
theorem exists_S16_gassmann_pair :
    ∃ H K : Subgroup (Equiv.Perm (Fin 16)),
      Nat.card H = 16 ∧ Nat.card K = 16 ∧ H.AlmostConjugate K ∧
        ¬ ∃ σ : Equiv.Perm (Fin 16),
          H.map (MulAut.conj σ : Equiv.Perm (Fin 16) →* Equiv.Perm (Fin 16)) = K := by
  let eA : C4C4 ≃ Fin 16 := Fintype.equivFinOfCardEq (by decide)
  let eB : Q8C2 ≃ Fin 16 := Fintype.equivFinOfCardEq (by decide)
  refine ⟨_, _, ?_, ?_, (Equiv.almostConjugate_permutationRepresentation_range_iff eA eB).2
    exists_equiv_orderOf_eq, ?_⟩
  · have hcard : Nat.card C4C4 = 16 := by
      rw [Nat.card_eq_fintype_card]
      decide
    simpa only [MonoidHom.mem_range] using
      (Equiv.natCard_permutationRepresentation_range eA).trans hcard
  · have hcard : Nat.card Q8C2 = 16 := by
      rw [Nat.card_eq_fintype_card]
      decide
    simpa only [MonoidHom.mem_range] using
      (Equiv.natCard_permutationRepresentation_range eB).trans hcard
  · rw [Equiv.exists_map_conj_permutationRepresentation_range_eq_iff]
    rintro ⟨i⟩
    have hB : ¬ ∀ x y : Q8C2, x * y = y * x := by decide
    exact hB fun x y ↦ i.symm.injective (by rw [map_mul, map_mul, mul_comm])

end TauCeti

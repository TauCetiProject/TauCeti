/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import TauCeti.GroupTheory.AlmostConjugate.Regular

/-!
# A Gassmann pair in `S₁₆`

The groups `C₄ × C₄ = Multiplicative (ZMod 4) × Multiplicative (ZMod 4)` and
`Q₈ × C₂ = QuaternionGroup 2 × Multiplicative (ZMod 2)` both have one element of order `1`, three
of order `2` and twelve of order `4`. Their regular actions have the full cycle types `1^16`,
`2^8` and `4^4`, with multiplicities `1`, `3` and `12`. (Mathlib's `Equiv.Perm.cycleType` omits
the fixed points, so it records these as the empty multiset, `2^8` and `4^4`.) The first group is
commutative and the second is not, so by
`Equiv.almostConjugate_range_permutationRepresentation` and
`Equiv.not_exists_map_conj_range_permutationRepresentation_eq` their regular images are two
non-conjugate almost-conjugate subgroups of `Equiv.Perm (Fin 16)`.

## Main statements

* `TauCeti.natCard_orderOf_zmod_four_prod_eq_quaternionGroup_prod`: `C₄ × C₄` and `Q₈ × C₂` have
  the same number of elements of each order.
* `TauCeti.exists_S16_gassmann_pair`: `Equiv.Perm (Fin 16)` has two almost-conjugate subgroups of
  order `16` that are not conjugate.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

namespace TauCeti

/-- **`C₄ × C₄` and `Q₈ × C₂` have the same order statistics**: for every `n`, they have equally
many elements of order `n`. Both have one element of order `1`, three of order `2` and twelve of
order `4`. -/
theorem natCard_orderOf_zmod_four_prod_eq_quaternionGroup_prod (n : ℕ) :
    Nat.card {a : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // orderOf a = n} =
      Nat.card {b : QuaternionGroup 2 × Multiplicative (ZMod 2) // orderOf b = n} := by
  -- In a group of exponent dividing four the order of an element is read off from whether it and
  -- its square are trivial, so the two order counts become a finite computation.
  have key (M : Type) [Group M] [Fintype M] [DecidableEq M] (h : ∀ a : M, a ^ 4 = 1) :
      Nat.card {a : M // orderOf a = n} = Multiset.count n ((Finset.univ : Finset M).val.map
        fun a ↦ if a = 1 then 1 else if a ^ 2 = 1 then 2 else 4) := by
    have hord (a : M) : orderOf a = if a = 1 then 1 else if a ^ 2 = 1 then 2 else 4 := by
      split_ifs with h1 h2
      · rw [h1, orderOf_one]
      · exact orderOf_eq_prime h2 h1
      · simpa using orderOf_eq_prime_pow (p := 2) (n := 1) h2 (h a)
    rw [Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hord, eq_comm (a := n), ← Finset.filter_val, Finset.card_val]
  rw [key _ (by decide), key _ (by decide)]
  congr 1
  decide

/-- **A Gassmann pair in `S₁₆`.** The symmetric group on sixteen letters has two subgroups of order
`16` that are almost conjugate but not conjugate: the regular representations of `C₄ × C₄` and of
`Q₈ × C₂`. -/
theorem exists_S16_gassmann_pair :
    ∃ H K : Subgroup (Equiv.Perm (Fin 16)), Nat.card H = 16 ∧ Nat.card K = 16 ∧
      H.AlmostConjugate K ∧ ¬ ∃ σ : Equiv.Perm (Fin 16), H.map (MulAut.conj σ) = K := by
  let e : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃ Fin 16 :=
    Fintype.equivFinOfCardEq (by decide)
  let f : QuaternionGroup 2 × Multiplicative (ZMod 2) ≃ Fin 16 :=
    Fintype.equivFinOfCardEq (by decide)
  refine ⟨_, _, ?_, ?_, e.almostConjugate_range_permutationRepresentation f
      natCard_orderOf_zmod_four_prod_eq_quaternionGroup_prod,
    e.not_exists_map_conj_range_permutationRepresentation_eq f ?_⟩
  · rw [e.natCard_range_permutationRepresentation, Nat.card_eq_fintype_card]
    decide
  · rw [f.natCard_range_permutationRepresentation, Nat.card_eq_fintype_card]
    decide
  · rw [isMulCommutative_iff]
    decide

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ProductOne
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Product-one counts in the symmetric group on three letters

In `S₃` the three-cycles form a conjugacy class of size `2` and the transpositions one of size `3`.
The two counts below are decided by kernel computation and factor as
`TauCeti.card_productOneTriples` predicts: `6 = 3 · 2` at a three-cycle and two transpositions, and
`0 = 3 · 0` at three transpositions, the second factor being the structure constant. On the
character side the class sizes contribute `2 · 3 · 3 / 6 = 3` and `3 · 3 · 3 / 6`, so the character
sums are `2` and `0`.

## Main results

* `TauCeti.card_productOneTriples_threeCycle_transposition` and
  `TauCeti.card_productOneTriples_transposition`: the product-one counts.
* `TauCeti.sum_characterTable_threeCycle_transposition` and
  `TauCeti.sum_characterTable_transposition`: the corresponding character sums.
-/

public section

namespace TauCeti

universe u

/-- **A transposition of `Fin 3` factors as a transposition times a three-cycle in two ways.** -/
theorem structureConstant_transposition_threeCycle :
    structureConstant (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)) (ConjClasses.mk (finRotate 3))
      (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))⁻¹ = 2 := by
  rw [ConjClasses.inv_mk, Equiv.swap_inv, structureConstant_mk_eq_card_filter]
  decide

/-- **Six product-one triples in `S₃` at a three-cycle and two transpositions.** A triple
`(x, y, z)` with `x` a three-cycle and `y`, `z` transpositions satisfies `z * y * x = 1` exactly
when `x = y * z`, which is a three-cycle precisely when `y ≠ z`; there are six such ordered
pairs. -/
theorem card_productOneTriples_threeCycle_transposition :
    (productOneTriples (ConjClasses.mk (finRotate 3)) (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))
      (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))).card = 6 := by
  rw [card_productOneTriples, structureConstant_transposition_threeCycle,
    ConjClasses.card_carrier_mk_eq_card_filter]
  decide

/-- **No product-one triple in `S₃` has all three entries transpositions.** A product of two
transpositions of `Fin 3` is the identity or a three-cycle, never a transposition. -/
theorem card_productOneTriples_transposition :
    (productOneTriples (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))
      (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))
      (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))).card = 0 := by
  rw [card_productOneTriples, ConjClasses.inv_mk, Equiv.swap_inv,
    structureConstant_mk_eq_card_filter]
  decide

/-- **The character side of the Frobenius formula in `S₃`**, at a three-cycle and two
transpositions: the sum over the irreducible characters is `2`, the count of six product-one
triples divided by the class-size factor `2 · 3 · 3 / 6 = 3`. -/
theorem sum_characterTable_threeCycle_transposition (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] [Invertible (Nat.card (Equiv.Perm (Fin 3)) : k)] :
    ∑ l, characterTable k (Equiv.Perm (Fin 3)) l (ConjClasses.mk (finRotate 3)) *
        characterTable k (Equiv.Perm (Fin 3)) l (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)) *
        characterTable k (Equiv.Perm (Fin 3)) l (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)) /
      (characterDegree k l : k) = 2 := by
  have hthree : Nat.card (ConjClasses.mk (finRotate 3)).carrier = 2 := by
    rw [ConjClasses.card_carrier_mk_eq_card_filter]
    decide
  have htrans : Nat.card (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)).carrier = 3 := by
    rw [ConjClasses.card_carrier_mk_eq_card_filter]
    decide
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h := card_productOneTriples_eq_sum_characterTable (k := k) (ConjClasses.mk (finRotate 3))
    (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)) (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))
  rw [card_productOneTriples_threeCycle_transposition, hthree, htrans, hcard] at h
  -- Normalizing evaluates the class-size factor `2 * 3 * 3 / 6` to `3` in `h`, and rewrites both
  -- character sums to `TauCeti.characterTable_apply` normal form so that they match.
  norm_num at h ⊢
  refine mul_left_cancel₀ (three_ne_zero : (3 : k) ≠ 0) ?_
  rw [← h]
  norm_num

/-- **The character side of the Frobenius formula in `S₃`**, at three transpositions: the sum over
the irreducible characters is `0`, since there is no product-one triple of transpositions and the
class-size factor `3 · 3 · 3 / 6` is nonzero. -/
theorem sum_characterTable_transposition (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Invertible (Nat.card (Equiv.Perm (Fin 3)) : k)] :
    ∑ l, characterTable k (Equiv.Perm (Fin 3)) l (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)) *
        characterTable k (Equiv.Perm (Fin 3)) l (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)) *
        characterTable k (Equiv.Perm (Fin 3)) l (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)) /
      (characterDegree k l : k) = 0 := by
  have htrans : Nat.card (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)).carrier = 3 := by
    rw [ConjClasses.card_carrier_mk_eq_card_filter]
    decide
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h := card_productOneTriples_eq_sum_characterTable (k := k)
    (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)) (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))
    (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))
  rw [card_productOneTriples_transposition, htrans, hcard] at h
  push_cast at h
  exact (mul_eq_zero.1 h.symm).resolve_left (by norm_num)

end TauCeti

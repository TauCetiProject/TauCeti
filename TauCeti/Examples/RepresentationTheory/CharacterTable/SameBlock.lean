/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import TauCeti.RepresentationTheory.CharacterTable.SameBlock

/-!
# Regression examples: the block congruence of complex characters

These examples compute `TauCeti.SameBlock` on the characters of `C₃` and `S₃`:

* on `C₃`, modulo a proper ideal containing `2`, a faithful linear character is not congruent to
  the trivial one: their difference `ζ₃ − 1` at a generator has norm `3`;
* on `C₃`, modulo a prime ideal containing `3`, every linear character is congruent to the trivial
  one, since `(1 − ζ₃)² = −3ζ₃`;
* on `S₃`, modulo an ideal containing `2`, the sign character is congruent to the trivial one,
  whereas modulo a proper ideal containing `2` the standard character is not: on the class of the
  three transpositions the difference is `3 (0 − 1) = −3`; modulo an ideal containing `3` it is,
  the difference on the two `3`-cycles being `2 (−1/2 − 1) = −3`.
-/

open TauCeti

variable (M : Ideal (integralClosure ℤ ℂ))

section C3

variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3)

include hζ in
-- Modulo a proper ideal containing `2`, the linear character `r ↦ ζ` of `C₃` is not congruent to
-- the trivial character: `ζ - 1` would lie in the ideal, and `(ζ - 1)(ζ² - 1) = 3`.
example (h2 : (2 : integralClosure ℤ ℂ) ∈ M) (hM : M ≠ ⊤) :
    ¬ SameBlock M (fun g : Multiplicative (ZMod 3) => ζ ^ (Multiplicative.toAdd g).val) 1 := by
  -- Conjugacy classes of the commutative group `C₃` are single points.
  have hC (g : Multiplicative (ZMod 3)) : Nat.card (ConjClasses.mk g).carrier = 1 := by
    have : (ConjClasses.mk g).carrier = {g} := Set.ext fun h => by
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq,
        Set.mem_singleton_iff, eq_comm]
    rw [this, Nat.card_unique]
  intro h
  obtain ⟨x, hx, hxg⟩ := sameBlock_iff.1 h (Multiplicative.ofAdd 1)
  set z : integralClosure ℤ ℂ := ⟨ζ, hζ.isIntegral (by norm_num)⟩
  have hx' : x = z - 1 := Subtype.ext <| by
    rw [hxg, hC]
    simp [z, ZMod.val_one]
  have h3 : (3 : integralClosure ℤ ℂ) = x * (z ^ 2 - 1) := Subtype.ext <| by
    have hsum := hζ.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
    have c3 : ((3 : integralClosure ℤ ℂ) : ℂ) = 3 := rfl
    rw [hx']
    push_cast [c3]
    linear_combination -(1 : ℂ) * hζ.pow_eq_one + hsum
  have h1 : (1 : integralClosure ℤ ℂ) ∈ M := by
    have := M.sub_mem (h3 ▸ M.mul_mem_right (z ^ 2 - 1) hx) h2
    norm_num at this
    exact this
  exact hM ((Ideal.eq_top_iff_one M).2 h1)

include hζ in
-- Modulo a prime ideal containing `3`, every linear character `r ↦ ζ ^ j` of `C₃` is congruent to
-- the trivial character: `(ζ - 1)² = -3ζ` puts `ζ - 1` in the ideal.
example [M.IsPrime] (h3 : (3 : integralClosure ℤ ℂ) ∈ M) (j : ℕ) :
    SameBlock M (fun g : Multiplicative (ZMod 3) => ζ ^ (j * (Multiplicative.toAdd g).val)) 1 := by
  -- Conjugacy classes of the commutative group `C₃` are single points.
  have hC (g : Multiplicative (ZMod 3)) : Nat.card (ConjClasses.mk g).carrier = 1 := by
    have : (ConjClasses.mk g).carrier = {g} := Set.ext fun h => by
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq,
        Set.mem_singleton_iff, eq_comm]
    rw [this, Nat.card_unique]
  set z : integralClosure ℤ ℂ := ⟨ζ, hζ.isIntegral (by norm_num)⟩
  have hz : z - 1 ∈ M := by
    have hsq : (z - 1) ^ 2 = -(3 * z) := Subtype.ext <| by
      have hsum := hζ.geom_sum_eq_zero (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
      have c3 : ((3 : integralClosure ℤ ℂ) : ℂ) = 3 := rfl
      push_cast [c3]
      linear_combination hsum
    exact Ideal.IsPrime.mem_of_pow_mem ‹_› 2 (hsq ▸ M.neg_mem_iff.2 (M.mul_mem_right z h3))
  refine sameBlock_iff.2 fun g => ⟨z ^ (j * (Multiplicative.toAdd g).val) - 1, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_pow, Ideal.Quotient.eq.2 hz, map_one, one_pow]
  · rw [hC]
    simp [z]

end C3

section S3

-- Modulo an ideal containing `2`, the sign character of `S₃` is congruent to the trivial one: the
-- difference is `0` on even permutations and `|C| (-1 - 1) = -2|C|` on odd ones.
example (h2 : (2 : integralClosure ℤ ℂ) ∈ M) :
    SameBlock M (fun σ : Equiv.Perm (Fin 3) => ((Equiv.Perm.sign σ : ℤ) : ℂ)) 1 := by
  refine sameBlock_iff.2 fun g => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg
  · exact ⟨0, M.zero_mem, by simp [hg]⟩
  · refine ⟨-(Nat.card (ConjClasses.mk g).carrier * 2), M.neg_mem_iff.2 (M.mul_mem_left _ h2), ?_⟩
    have c2 : ((2 : integralClosure ℤ ℂ) : ℂ) = 2 := rfl
    simp only [hg, map_one, Pi.one_apply]
    push_cast [c2]
    ring

-- Modulo a proper ideal containing `2`, the standard character `σ ↦ #fix(σ) - 1` of `S₃` is not
-- congruent to the trivial one: on the class of the three transpositions the difference is
-- `3 (0/2 - 1) = -3`, and `1 = 3 - 2`.
example (h2 : (2 : integralClosure ℤ ℂ) ∈ M) (hM : M ≠ ⊤) :
    ¬ SameBlock M (fun σ : Equiv.Perm (Fin 3) =>
      ((Finset.univ.filter fun i => σ i = i).card : ℂ) - 1) 1 := by
  intro h
  obtain ⟨x, hx, hxg⟩ := sameBlock_iff.1 h (Equiv.swap 0 1)
  have hcard : Nat.card (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1)).carrier = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hfix : (Finset.univ.filter fun i : Fin 3 => Equiv.swap 0 1 i = i).card = 1 := by decide
  have hfix1 : (Finset.univ.filter fun i : Fin 3 => (1 : Equiv.Perm (Fin 3)) i = i).card = 3 := by
    decide
  have hx' : x = -3 := Subtype.ext <| by
    rw [hxg, hcard, hfix, hfix1, Pi.one_apply, Pi.one_apply,
      show ((-3 : integralClosure ℤ ℂ) : ℂ) = -3 from rfl]
    norm_num
  have h1 : (1 : integralClosure ℤ ℂ) ∈ M := by
    have := M.sub_mem (M.neg_mem_iff.1 (hx' ▸ hx : (-3 : integralClosure ℤ ℂ) ∈ M)) h2
    norm_num at this
    exact this
  exact hM ((Ideal.eq_top_iff_one M).2 h1)

-- Modulo an ideal containing `3`, the standard character of `S₃` is congruent to the trivial one:
-- the difference is `0` at the identity, `3 (0/2 - 1) = -3` on the three transpositions and
-- `2 (-1/2 - 1) = -3` on the two `3`-cycles. Without the class size the last value would be
-- `-3/2`, which is not an algebraic integer.
example (h3 : (3 : integralClosure ℤ ℂ) ∈ M) :
    SameBlock M (fun σ : Equiv.Perm (Fin 3) =>
      ((Finset.univ.filter fun i => σ i = i).card : ℂ) - 1) 1 := by
  have hfix1 : (Finset.univ.filter fun i : Fin 3 => (1 : Equiv.Perm (Fin 3)) i = i).card = 3 := by
    decide
  have hcases : ∀ g : Equiv.Perm (Fin 3),
      (Fintype.card (ConjClasses.mk g).carrier = 1 ∧
        (Finset.univ.filter fun i => g i = i).card = 3) ∨
      (Fintype.card (ConjClasses.mk g).carrier = 3 ∧
        (Finset.univ.filter fun i => g i = i).card = 1) ∨
      (Fintype.card (ConjClasses.mk g).carrier = 2 ∧
        (Finset.univ.filter fun i => g i = i).card = 0) := by
    decide
  have hm3 : (-3 : integralClosure ℤ ℂ) ∈ M := M.neg_mem_iff.2 h3
  have c3 : ((-3 : integralClosure ℤ ℂ) : ℂ) = -3 := rfl
  refine sameBlock_iff.2 fun g => ?_
  simp only [Pi.one_apply, hfix1, Nat.card_eq_fintype_card]
  rcases hcases g with ⟨hc, hf⟩ | ⟨hc, hf⟩ | ⟨hc, hf⟩ <;> rw [hc, hf]
  · exact ⟨0, M.zero_mem, by norm_num⟩
  · exact ⟨-3, hm3, by rw [c3]; norm_num⟩
  · exact ⟨-3, hm3, by rw [c3]; norm_num⟩

end S3

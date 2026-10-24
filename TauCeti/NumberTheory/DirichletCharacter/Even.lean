/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Even and odd Dirichlet characters

A Dirichlet character `χ` of level `n` is even when `χ (-1) = 1` (`DirichletCharacter.Even`).
The even characters form a subgroup of the group of Dirichlet characters of level `n`: the
characters trivial on the subgroup `{±1}` of `(ℤ/nℤ)ˣ`. Under the character correspondence for
the `n`-th cyclotomic field it is the subgroup attached to the maximal real subfield.

## Main definitions

* `TauCeti.DirichletCharacter.evenSubgroup`: the subgroup of even Dirichlet characters of level `n`.

## Main statements

* `DirichletCharacter.mem_evenSubgroup_iff`: membership in `evenSubgroup` is evenness.
* `DirichletCharacter.exists_odd`: above level two there is an odd character, when the values
  have enough roots of unity.
* `DirichletCharacter.even_of_le_two`: at the levels `1` and `2` every character is even.
* `DirichletCharacter.two_mul_card_apply_neg_one_mul_apply_neg_one_eq`: if one of two levels
  exceeds two, exactly half of the pairs of characters at these levels have a given product
  parity.
* `DirichletCharacter.card_apply_neg_one_mul_apply_neg_one_eq_of_le_two`: if neither level
  exceeds two, the only pair of characters has product parity `1`.
-/

public section

namespace TauCeti.DirichletCharacter

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The subgroup of even Dirichlet characters of level `n`, those with `χ (-1) = 1`. -/
def evenSubgroup : Subgroup (DirichletCharacter R n) where
  carrier := {χ | χ.Even}
  mul_mem' {χ ψ} (hχ : χ.Even) (hψ : ψ.Even) := by
    rw [Set.mem_ofPred_eq, DirichletCharacter.Even, MulChar.mul_apply, hχ, hψ, mul_one]
  one_mem' := MulChar.one_apply isUnit_one.neg
  inv_mem' {χ} (hχ : χ.Even) := by
    rw [Set.mem_ofPred_eq, DirichletCharacter.Even, MulChar.inv_apply_eq_inv, hχ,
      Ring.inverse_one]

end TauCeti.DirichletCharacter

namespace DirichletCharacter

variable {R : Type*} [CommRing R] {n : ℕ}

@[simp]
theorem mem_evenSubgroup_iff (χ : DirichletCharacter R n) :
    χ ∈ TauCeti.DirichletCharacter.evenSubgroup R n ↔ χ.Even :=
  Iff.rfl

/-- Above level two there is an odd Dirichlet character: since `-1 ≠ 1` modulo `n`, some
character separates them, and its value at `-1` is then `-1`. -/
theorem exists_odd [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    (hn : 2 < n) : ∃ χ : DirichletCharacter R n, χ.Odd := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (2 < n) := ⟨hn⟩
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity R (ZMod.neg_one_ne_one (n := n))
  exact ⟨χ, χ.even_or_odd.resolve_left hχ⟩

/-- At the levels `1` and `2` every Dirichlet character is even, since `-1 = 1` there. -/
theorem even_of_le_two [NeZero n] (hn : n ≤ 2) (χ : DirichletCharacter R n) : χ.Even := by
  have h : (-1 : ZMod n) = 1 := by
    obtain rfl | rfl : n = 1 ∨ n = 2 := by have := NeZero.ne n; omega
    all_goals decide
  rw [DirichletCharacter.Even, h, map_one]

/-- If one of two levels exceeds `2`, exactly half of the pairs of Dirichlet characters at these
levels have a prescribed product parity `ε = ±1`: multiplying by a pair of parity `-1` exchanges
the two parities. -/
theorem two_mul_card_apply_neg_one_mul_apply_neg_one_eq {a b : ℕ} [NeZero a] [NeZero b]
    [IsDomain R] [NeZero (2 : R)] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod a)ˣ)]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod b)ˣ)] (hab : 2 < a ∨ 2 < b) {ε : R}
    (hε : ε = 1 ∨ ε = -1) :
    2 * Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = ε} = a.totient * b.totient := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : DirichletCharacter R a × DirichletCharacter R b,
      x.1 (-1) * x.2 (-1) = -1 := by
    rcases hab with h | h
    · obtain ⟨χ, hχ⟩ := exists_odd (R := R) h
      exact ⟨(χ, 1), by rw [hχ, MulChar.one_apply isUnit_one.neg, mul_one]⟩
    · obtain ⟨χ, hχ⟩ := exists_odd (R := R) h
      exact ⟨(1, χ), by rw [hχ, MulChar.one_apply isUnit_one.neg, one_mul]⟩
  have hne : (1 : R) ≠ -1 := fun h ↦ (two_ne_zero : (2 : R) ≠ 0) (by linear_combination h)
  have hpar (q : DirichletCharacter R a × DirichletCharacter R b) :
      ¬q.1 (-1) * q.2 (-1) = 1 ↔ q.1 (-1) * q.2 (-1) = -1 := by
    rcases q.1.even_or_odd with h₁ | h₁ <;> rcases q.2.even_or_odd with h₂ | h₂ <;>
      rw [h₁, h₂] <;> simp [hne, hne.symm]
  -- Multiplication by `x` exchanges the two parities.
  have hswap : Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = 1} = Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = -1} := by
    refine Nat.card_congr ((Equiv.mulLeft x).subtypeEquiv fun q ↦ ?_)
    simp only [Equiv.coe_mulLeft, Prod.fst_mul, Prod.snd_mul, MulChar.mul_apply]
    grind
  -- Every pair has parity `1` or `-1`.
  have htot : Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = 1} + Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = -1} = a.totient * b.totient := by
    rw [← card_eq_totient_of_hasEnoughRootsOfUnity R a,
      ← card_eq_totient_of_hasEnoughRootsOfUnity R b, ← Nat.card_prod, ← Nat.card_sum]
    exact Nat.card_congr (((Equiv.refl _).sumCongr (Equiv.subtypeEquivRight hpar).symm).trans
      (Equiv.sumCompl _))
  rcases hε with rfl | rfl <;> omega

/-- If neither of two levels exceeds `2`, there is a single pair of Dirichlet characters at these
levels, and it is even: the pairs of product parity `ε` number one when `ε = 1` and none
otherwise. -/
theorem card_apply_neg_one_mul_apply_neg_one_eq_of_le_two {a b : ℕ} [NeZero a] [NeZero b]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod a)ˣ)]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod b)ˣ)] [DecidableEq R] (ha : a ≤ 2)
    (hb : b ≤ 2) (ε : R) :
    Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = ε} = if ε = 1 then 1 else 0 := by
  have ha' : ∀ χ : DirichletCharacter R a, χ (-1) = 1 := even_of_le_two ha
  have hb' : ∀ χ : DirichletCharacter R b, χ (-1) = 1 := even_of_le_two hb
  have htot {n : ℕ} [NeZero n] (hn : n ≤ 2) : n.totient = 1 := by
    obtain rfl | rfl : n = 1 ∨ n = 2 := by have := NeZero.ne n; omega
    all_goals rfl
  simp only [ha', hb', one_mul]
  split_ifs with hε
  · subst hε
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ rfl), Nat.card_prod,
      card_eq_totient_of_hasEnoughRootsOfUnity R a, card_eq_totient_of_hasEnoughRootsOfUnity R b,
      htot ha, htot hb]
  · have : IsEmpty {q : DirichletCharacter R a × DirichletCharacter R b // (1 : R) = ε} :=
      ⟨fun ⟨_, h⟩ ↦ hε h.symm⟩
    exact Nat.card_of_isEmpty

end DirichletCharacter

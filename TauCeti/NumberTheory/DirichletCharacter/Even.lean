/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import TauCeti.NumberTheory.DirichletCharacter.Basic

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

/-- The parity of an inverse character is unchanged. -/
@[simp]
theorem even_inv_iff (χ : DirichletCharacter R n) : χ⁻¹.Even ↔ χ.Even :=
  (TauCeti.DirichletCharacter.evenSubgroup R n).inv_mem_iff

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
  have h : (-1 : ZMod n) = 1 := ZMod.neg_one_eq_one_iff.mpr (by have := NeZero.ne n; omega)
  rw [DirichletCharacter.Even, h, map_one]

/-- Above level two, `R` has exactly two square roots of unity, and some Dirichlet character is
odd: its value at `-1` differs from `1`. -/
private lemma natCard_rootsOfUnity_two_and_exists_apply_neg_one_ne_one [NeZero n]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)] (hn : 2 < n) :
    Nat.card (rootsOfUnity 2 R) = 2 ∧ ∃ χ : DirichletCharacter R n, χ (-1) ≠ 1 := by
  have : Fact (2 < n) := ⟨hn⟩
  have hu : (-1 : (ZMod n)ˣ) ≠ 1 := fun h ↦ ZMod.neg_one_ne_one (n := n) (congrArg Units.val h)
  have h2 : 2 ∣ Monoid.exponent (ZMod n)ˣ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Monoid.order_dvd_exponent (-1 : (ZMod n)ˣ)
    rwa [orderOf_eq_prime (p := 2) (neg_one_sq : (-1 : (ZMod n)ˣ) ^ 2 = 1) hu] at this
  have := HasEnoughRootsOfUnity.of_dvd R h2
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot R 2
  have : Nontrivial R := ⟨ζ, 1, hζ.ne_one one_lt_two⟩
  exact ⟨HasEnoughRootsOfUnity.natCard_rootsOfUnity R 2,
    exists_apply_ne_one_of_hasEnoughRootsOfUnity R (ZMod.neg_one_ne_one (n := n))⟩

/-- If `R` has exactly two square roots of unity, any two elements other than `1` that square
to `1` are equal. -/
private lemma eq_of_mul_self_eq_one (hcard : Nat.card (rootsOfUnity 2 R) = 2) (r s : R)
    (hr : r * r = 1) (hs : s * s = 1) (hr1 : r ≠ 1) (hs1 : s ≠ 1) : r = s := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : rootsOfUnity 2 R)).1 hcard
  have hmk (t : R) (ht : t * t = 1) (ht1 : t ≠ 1) :
      ∃ z : rootsOfUnity 2 R, z ≠ 1 ∧ (z : Rˣ) = ⟨t, t, ht, ht⟩ := by
    refine ⟨⟨⟨t, t, ht, ht⟩, ?_⟩, fun h ↦ ht1 ?_, rfl⟩
    · rw [mem_rootsOfUnity]
      ext
      simp [pow_two, ht]
    · simpa using congrArg (fun z : rootsOfUnity 2 R ↦ ((z : Rˣ) : R)) h
  obtain ⟨z, hz, hzr⟩ := hmk r hr hr1
  obtain ⟨w, hw, hws⟩ := hmk s hs hs1
  have := (hy z hz).trans (hy w hw).symm
  simpa [hzr, hws] using congrArg (fun z : rootsOfUnity 2 R ↦ ((z : Rˣ) : R)) this

/-- A Dirichlet character takes a square root of unity as its value at `-1`. -/
private lemma apply_neg_one_mul_self (χ : DirichletCharacter R n) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

/-- With enough roots of unity there are finitely many Dirichlet characters, even when `R` is not
a domain. -/
private lemma finite_of_hasEnoughRootsOfUnity [NeZero n]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)] : Finite (DirichletCharacter R n) :=
  Nat.finite_of_card_ne_zero <| by
    rw [card_eq_totient_of_hasEnoughRootsOfUnity R n]
    exact (Nat.totient_pos.2 (NeZero.pos n)).ne'

/-- If one of two levels exceeds `2`, exactly half of the pairs of Dirichlet characters at these
levels have a prescribed product parity `ε = ±1`: multiplying by a pair of parity `-1` exchanges
the two parities. -/
theorem two_mul_card_apply_neg_one_mul_apply_neg_one_eq {a b : ℕ} [NeZero a] [NeZero b]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod a)ˣ)]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod b)ˣ)] (hab : 2 < a ∨ 2 < b) {ε : R}
    (hε : ε = 1 ∨ ε = -1) :
    2 * Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = ε} = a.totient * b.totient := by
  classical
  obtain ⟨hcard, x, hx⟩ : Nat.card (rootsOfUnity 2 R) = 2 ∧
      ∃ x : DirichletCharacter R a × DirichletCharacter R b, x.1 (-1) * x.2 (-1) ≠ 1 := by
    rcases hab with h | h
    · obtain ⟨hc, χ, hχ⟩ := natCard_rootsOfUnity_two_and_exists_apply_neg_one_ne_one (R := R) h
      exact ⟨hc, (χ, 1), by
        change χ (-1) * (1 : DirichletCharacter R b) (-1) ≠ 1
        rwa [MulChar.one_apply isUnit_one.neg, mul_one]⟩
    · obtain ⟨hc, χ, hχ⟩ := natCard_rootsOfUnity_two_and_exists_apply_neg_one_ne_one (R := R) h
      exact ⟨hc, (1, χ), by
        change (1 : DirichletCharacter R a) (-1) * χ (-1) ≠ 1
        rwa [MulChar.one_apply isUnit_one.neg, one_mul]⟩
  obtain ⟨f, hf⟩ : ∃ f : DirichletCharacter R a × DirichletCharacter R b → R,
      ∀ q, f q = q.1 (-1) * q.2 (-1) := ⟨_, fun _ ↦ rfl⟩
  simp only [← hf]
  have hmul (q q' : DirichletCharacter R a × DirichletCharacter R b) :
      f (q * q') = f q * f q' := by
    simp only [hf, Prod.fst_mul, Prod.snd_mul, MulChar.mul_apply]
    ring
  have hsq (q : DirichletCharacter R a × DirichletCharacter R b) : f q * f q = 1 := by
    calc f q * f q = (q.1 (-1) * q.1 (-1)) * (q.2 (-1) * q.2 (-1)) := by rw [hf]; ring
      _ = 1 := by rw [apply_neg_one_mul_self, apply_neg_one_mul_self, mul_one]
  have hg : f x ≠ 1 := by rwa [hf]
  have := finite_of_hasEnoughRootsOfUnity (R := R) (n := a)
  have := finite_of_hasEnoughRootsOfUnity (R := R) (n := b)
  have hpar (q : DirichletCharacter R a × DirichletCharacter R b) : ¬f q = 1 ↔ f q = f x :=
    ⟨fun h ↦ eq_of_mul_self_eq_one hcard _ _ (hsq q) (hsq x) h hg, fun h h1 ↦ hg (h.symm.trans h1)⟩
  -- Multiplication by `x` exchanges the two parities.
  have hswap : Nat.card {q : DirichletCharacter R a × DirichletCharacter R b // f q = 1} =
      Nat.card {q : DirichletCharacter R a × DirichletCharacter R b // f q = f x} := by
    refine Nat.card_congr ((Equiv.mulLeft x).subtypeEquiv fun q ↦ ?_)
    simp only [Equiv.coe_mulLeft, hmul]
    exact ⟨fun h ↦ by rw [h, mul_one], fun h ↦ by
      rw [← one_mul (f q), ← hsq x, mul_assoc, h, hsq]⟩
  -- Every pair has parity `1` or `f x`.
  have htot : Nat.card {q : DirichletCharacter R a × DirichletCharacter R b // f q = 1} +
      Nat.card {q : DirichletCharacter R a × DirichletCharacter R b // f q = f x} =
      a.totient * b.totient := by
    rw [← card_eq_totient_of_hasEnoughRootsOfUnity R a,
      ← card_eq_totient_of_hasEnoughRootsOfUnity R b, ← Nat.card_prod, ← Nat.card_sum]
    exact Nat.card_congr (((Equiv.refl _).sumCongr (Equiv.subtypeEquivRight hpar).symm).trans
      (Equiv.sumCompl _))
  have hε' : ε = 1 ∨ ε = f x := by
    rcases hε with rfl | rfl
    · exact Or.inl rfl
    · by_cases h : (-1 : R) = 1
      · exact Or.inl h
      · exact Or.inr (eq_of_mul_self_eq_one hcard _ _ (by simp) (hsq x) h hg)
  rcases hε' with rfl | rfl <;> omega

/-- If neither of two levels exceeds `2`, there is a single pair of Dirichlet characters at these
levels, and it is even: the pairs of product parity `ε` number one when `ε = 1` and none
otherwise. -/
theorem card_apply_neg_one_mul_apply_neg_one_eq_of_le_two {R : Type*} [CommMonoidWithZero R]
    {a b : ℕ} [NeZero a] [NeZero b] [DecidableEq R] (ha : a ≤ 2) (hb : b ≤ 2) (ε : R) :
    Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = ε} = if ε = 1 then 1 else 0 := by
  have hneg {n : ℕ} [NeZero n] (hn : n ≤ 2) (χ : DirichletCharacter R n) : χ (-1) = 1 := by
    rw [ZMod.neg_one_eq_one_iff.mpr (by have := NeZero.ne n; omega), map_one]
  have := subsingleton_of_le_two (R := R) ha
  have := subsingleton_of_le_two (R := R) hb
  simp only [hneg ha, hneg hb, one_mul]
  split_ifs with hε
  · subst hε
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ rfl), Nat.card_prod,
      Nat.card_unique, Nat.card_unique]
  · have : IsEmpty {_q : DirichletCharacter R a × DirichletCharacter R b // (1 : R) = ε} :=
      ⟨fun ⟨_, h⟩ ↦ hε h.symm⟩
    exact Nat.card_of_isEmpty

end DirichletCharacter

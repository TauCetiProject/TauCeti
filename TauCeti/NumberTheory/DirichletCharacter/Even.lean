/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Algebra.Field.ZMod
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.RingTheory.RootsOfUnity.ZMod

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
* `DirichletCharacter.two_mul_card_apply_neg_one_eq`: above level two, exactly half of the
  characters have a given parity.
* `DirichletCharacter.card_apply_neg_one_mul_apply_neg_one_eq_of_le_two`: if neither level
  exceeds two, the only pair of characters has product parity `1`.
* `DirichletCharacter.two_mul_sum_even`: twice a sum over the even characters is the sum of
  `(1 + χ (-1)) f χ` over all characters.
* `DirichletCharacter.sum_even_ne_one`: removing the trivial character from a sum over the even
  characters.
* `DirichletCharacter.sum_even_eq_totient_div_two_mul`: above level two, halving an identity for
  twice a sum over the even characters.
* `DirichletCharacter.two_mul_sum_even_apply`, `DirichletCharacter.sum_even_apply`: orthogonality
  for the even characters, which detect `a = ±1` rather than `a = 1`.
* `DirichletCharacter.sum_even_ne_one_apply`: at an odd prime level `q`, the sum of `χ a` over
  the even nontrivial characters is `0` at `a = 0`, `(q - 1) / 2 - 1` at `a = ±1` and `-1`
  otherwise.
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

/-- If one of two levels exceeds `2`, exactly half of the pairs of Dirichlet characters at these
levels have a prescribed product parity `ε = ±1`. -/
theorem two_mul_card_apply_neg_one_mul_apply_neg_one_eq {a b : ℕ} [NeZero a] [NeZero b]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod a)ˣ)]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod b)ˣ)] (hab : 2 < a ∨ 2 < b) {ε : R}
    (hε : ε = 1 ∨ ε = -1) :
    2 * Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = ε} = a.totient * b.totient := by
  -- The product parity, as a homomorphism to the square roots of unity of `R`.
  let φ : DirichletCharacter R a × DirichletCharacter R b →* rootsOfUnity 2 R :=
    .mk' (fun q ↦ ⟨q.1.toUnitHom (-1) * q.2.toUnitHom (-1), by
      rw [mem_rootsOfUnity, mul_pow, ← map_pow, ← map_pow, neg_one_sq, neg_one_sq, map_one,
        map_one, one_mul]⟩) fun q q' ↦ by
      ext
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul,
        MulChar.coe_toUnitHom, MulChar.mul_apply]
      ring
  have hφ (q) (y : rootsOfUnity 2 R) : φ q = y ↔ q.1 (-1) * q.2 (-1) = ((y : Rˣ) : R) := by
    simp [φ, Subtype.ext_iff, Units.ext_iff]
  -- Above level two, `2` divides the exponent of `(ℤ/nℤ)ˣ`, so `R` has the square roots of unity.
  have : HasEnoughRootsOfUnity R 2 :=
    hab.elim (HasEnoughRootsOfUnity.two_of_two_lt R) (HasEnoughRootsOfUnity.two_of_two_lt R)
  have hcard := HasEnoughRootsOfUnity.natCard_rootsOfUnity R 2
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot R 2
  have : Nontrivial R := ⟨ζ, 1, hζ.ne_one one_lt_two⟩
  -- Some pair has product parity other than `1`.
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 1 := by
    rcases hab with h | h
    · have : Fact (2 < a) := ⟨h⟩
      obtain ⟨χ, hχ⟩ :=
        exists_apply_ne_one_of_hasEnoughRootsOfUnity R (ZMod.neg_one_ne_one (n := a))
      exact ⟨(χ, 1), by simpa [hφ, MulChar.one_apply isUnit_one.neg] using hχ⟩
    · have : Fact (2 < b) := ⟨h⟩
      obtain ⟨χ, hχ⟩ :=
        exists_apply_ne_one_of_hasEnoughRootsOfUnity R (ZMod.neg_one_ne_one (n := b))
      exact ⟨(1, χ), by simpa [hφ, MulChar.one_apply isUnit_one.neg] using hχ⟩
  -- Hence `φ` is onto, since `1` and `φ x` are the only square roots of unity.
  have hsurj : Function.Surjective φ := fun y ↦ by
    obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : rootsOfUnity 2 R)).1 hcard
    by_cases hy : y = 1
    · exact ⟨1, by rw [map_one, hy]⟩
    · exact ⟨x, (hz _ hx).trans (hz _ hy).symm⟩
  -- Each fibre of `φ` is a coset of its kernel.
  have hfib (q₀ : DirichletCharacter R a × DirichletCharacter R b) :
      Nat.card {q // φ q = φ q₀} = Nat.card φ.ker :=
    (Nat.card_congr ((Equiv.mulLeft q₀).subtypeEquiv fun q ↦ by
      simp [MonoidHom.mem_ker] : φ.ker ≃ {q // φ q = φ q₀})).symm
  obtain ⟨q₀, hq₀⟩ := hsurj (rootsOfUnity.mkOfPowEq ε (by rcases hε with rfl | rfl <;> simp))
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun q ↦
      (by rw [hq₀, hφ, rootsOfUnity.val_mkOfPowEq_coe] : φ q = φ q₀ ↔ _).symm), hfib,
    ← card_eq_totient_of_hasEnoughRootsOfUnity R a, ← card_eq_totient_of_hasEnoughRootsOfUnity R b,
    ← Nat.card_prod, ← Subgroup.card_ker_mul_card_of_surjective hsurj, hcard, mul_comm]

/-- Above level two, exactly half of the Dirichlet characters have a prescribed parity
`ε = ±1`. -/
theorem two_mul_card_apply_neg_one_eq [NeZero n]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)] (hn : 2 < n) {ε : R}
    (hε : ε = 1 ∨ ε = -1) :
    2 * Nat.card {χ : DirichletCharacter R n // χ (-1) = ε} = n.totient := by
  have : HasEnoughRootsOfUnity R (Monoid.exponent (ZMod 1)ˣ) := by
    rw [Monoid.exp_eq_one_iff.2 inferInstance]
    infer_instance
  have h := two_mul_card_apply_neg_one_mul_apply_neg_one_eq (R := R) (b := 1) (Or.inl hn) hε
  rw [Nat.totient_one, mul_one] at h
  rw [← h, Nat.card_congr ((Equiv.prodUnique _ (DirichletCharacter R 1)).symm.subtypeEquiv
    fun χ ↦ ?_)]
  simp [Subsingleton.elim (-1 : ZMod 1) 1]

/-- If neither of two levels exceeds `2`, there is a single pair of Dirichlet characters at these
levels, and it is even: the pairs of product parity `ε` number one when `ε = 1` and none
otherwise. -/
theorem card_apply_neg_one_mul_apply_neg_one_eq_of_le_two {R : Type*} [CommMonoidWithZero R]
    {a b : ℕ} [NeZero a] [NeZero b] [DecidableEq R] (ha : a ≤ 2) (hb : b ≤ 2) (ε : R) :
    Nat.card {q : DirichletCharacter R a × DirichletCharacter R b //
      q.1 (-1) * q.2 (-1) = ε} = if ε = 1 then 1 else 0 := by
  have := subsingleton_of_le_two (R := R) ha
  have := subsingleton_of_le_two (R := R) hb
  -- The only pair is the trivial one, and its product parity is `1`.
  have h1 (q : DirichletCharacter R a × DirichletCharacter R b) : q.1 (-1) * q.2 (-1) = 1 := by
    rw [Subsingleton.elim q 1]
    simp [MulChar.one_apply isUnit_one.neg]
  simp only [h1]
  split_ifs with hε
  · subst hε
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ rfl), Nat.card_unique]
  · have : IsEmpty {_q : DirichletCharacter R a × DirichletCharacter R b // (1 : R) = ε} :=
      ⟨fun ⟨_, h⟩ ↦ hε h.symm⟩
    exact Nat.card_of_isEmpty

/-! ### Orthogonality for even characters -/

open Finset

open scoped Classical in
/-- **Projection onto the even characters.** Twice the sum of `f χ` over the even characters
is the sum of `(1 + χ (-1)) f χ` over all characters, since `χ (-1)` is `1` for an even and
`-1` for an odd character. -/
theorem two_mul_sum_even [IsDomain R] (f : DirichletCharacter R n → R) :
    2 * ∑ χ : DirichletCharacter R n with χ.Even, f χ = ∑ χ, f χ + ∑ χ, χ (-1) * f χ := by
  rw [mul_sum, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun χ _ ↦ ?_
  split_ifs with h
  · rw [h]
    ring
  · rw [χ.even_or_odd.resolve_left h]
    ring

open scoped Classical in
/-- Removing the trivial character from a sum over the even characters. -/
theorem sum_even_ne_one [IsDomain R] {M : Type*} [AddCommGroup M]
    (f : DirichletCharacter R n → M) :
    ∑ χ : DirichletCharacter R n with χ.Even ∧ χ ≠ 1, f χ =
      ∑ χ : DirichletCharacter R n with χ.Even, f χ - f 1 := by
  rw [← filter_filter, filter_ne', sum_erase_eq_sub (by simp)]

variable [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

open scoped Classical in
/-- **Halving a sum over the even characters.** Above level two `φ(n)` is even, so an identity
`2 * ∑_{χ even} f χ = φ(n) * c` gives `∑_{χ even} f χ = φ(n) / 2 * c`. -/
theorem sum_even_eq_totient_div_two_mul (hn : 2 < n) {f : DirichletCharacter R n → R} {c : R}
    (h : 2 * ∑ χ : DirichletCharacter R n with χ.Even, f χ = n.totient * c) :
    ∑ χ : DirichletCharacter R n with χ.Even, f χ = ((n.totient / 2 : ℕ) : R) * c := by
  have := HasEnoughRootsOfUnity.neZero_two_of_two_lt R hn
  refine mul_left_cancel₀ (two_ne_zero (α := R)) ?_
  have h2 : (2 : R) * ((n.totient / 2 : ℕ) : R) = n.totient := by
    rw [← Nat.cast_two, ← Nat.cast_mul, Nat.two_mul_div_two_of_even (Nat.totient_even hn)]
  rw [h, ← mul_assoc, h2]

variable [NeZero n]

open scoped Classical in
/-- **Orthogonality for even characters.** Twice the sum of `χ a` over the even characters
of level `n` is `φ(n) [a = 1] + φ(n) [a = -1]`: it is `φ(n)` at `a = ±1` when `1 ≠ -1`, it is
`2 φ(n)` at `a = 1` when `1 = -1` (levels one and two), and it vanishes when `a ≠ ±1`. -/
theorem two_mul_sum_even_apply (a : ZMod n) :
    2 * ∑ χ : DirichletCharacter R n with χ.Even, χ a =
      (if a = 1 then (n.totient : R) else 0) + if a = -1 then (n.totient : R) else 0 := by
  simp_rw [two_mul_sum_even, ← map_mul, neg_one_mul, sum_characters_eq, neg_eq_iff_eq_neg]

open scoped Classical in
/-- **Orthogonality for even characters**, above level two: the sum of `χ a` over the even
characters of level `n` is `φ(n) / 2` for each of `a = 1` and `a = -1`, and vanishes when
`a ≠ ±1`. -/
theorem sum_even_apply (hn : 2 < n) (a : ZMod n) :
    ∑ χ : DirichletCharacter R n with χ.Even, χ a =
      ((n.totient / 2 : ℕ) : R) * ((if a = 1 then 1 else 0) + if a = -1 then 1 else 0) := by
  refine sum_even_eq_totient_div_two_mul hn ?_
  rw [two_mul_sum_even_apply]
  split_ifs <;> ring

open scoped Classical in
/-- **Orthogonality for even nontrivial characters** at an odd prime level `q`: the sum of
`χ a` over the even characters other than the trivial one is `0` at `a = 0`,
`(q - 1) / 2 - 1` at `a = ±1`, and `-1` at every other residue. -/
theorem sum_even_ne_one_apply {q : ℕ} [Fact q.Prime]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod q)ˣ)] (hq : 2 < q) (a : ZMod q) :
    ∑ χ : DirichletCharacter R q with χ.Even ∧ χ ≠ 1, χ a =
      if a = 0 then 0 else if a = 1 ∨ a = -1 then (((q - 1) / 2 : ℕ) : R) - 1 else -1 := by
  have : Fact (2 < q) := ⟨hq⟩
  rw [sum_even_ne_one, sum_even_apply hq, Nat.totient_prime Fact.out]
  have hne : (1 : ZMod q) ≠ -1 := (ZMod.neg_one_ne_one).symm
  by_cases ha : a = 0
  · subst ha
    simp [zero_ne_one, (neg_ne_zero.mpr one_ne_zero).symm, MulChar.map_zero]
  · have hu : IsUnit a := Ne.isUnit ha
    rw [MulChar.one_apply hu]
    by_cases h1 : a = 1
    · subst h1
      simp [hne]
    · by_cases h2 : a = -1
      · subst h2
        simp [hne.symm]
      · simp [ha, h1, h2]

end DirichletCharacter

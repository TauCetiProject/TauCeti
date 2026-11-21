/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import TauCeti.Data.ZMod.OrderOf
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
  have : HasEnoughRootsOfUnity R 2 := hab.elim
    (fun h ↦ .of_dvd R (ZMod.two_dvd_exponent_units (n := a) (by omega) (by omega)))
    (fun h ↦ .of_dvd R (ZMod.two_dvd_exponent_units (n := b) (by omega) (by omega)))
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

end DirichletCharacter

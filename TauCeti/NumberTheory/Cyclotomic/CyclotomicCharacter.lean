/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Naturality of the cyclotomic character

Mathlib's `cyclotomicCharacter L p : (L ≃+* L) →* ℤ_[p]ˣ` records the action of a ring
automorphism of a domain `L` on the roots of unity of `p`-power order in `L`, and is the trivial
character when `L` does not contain a primitive `pⁱ`-th root of unity for every `i`. This file
proves that the character only depends on that action on roots of unity, so that it is natural
along injective ring homomorphisms.

Concretely, let `f : A →+* B` be an injective homomorphism of domains intertwining automorphisms
`g` of `A` and `h` of `B`, that is `h (f x) = f (g x)`. If every primitive `pⁱ`-th root of unity
needed by `B` already exists in `A`, then `h` and `g` have the same cyclotomic character. This is
how the cyclotomic character of an absolute Galois group is compared across different models of
the separable or algebraic closure, and across finite extensions of the ground field.

When `L` has all of these roots of unity, the character is characterized by that action: an
automorphism raising every root of unity of `p`-power order to the `c`-th power has cyclotomic
character `c`. This is how the character of an automorphism with a known action on roots of unity,
such as a Frobenius lift or an element of inertia, is computed.

## Main results

* `TauCeti.cyclotomicCharacter_eq_one_of_not_forall_isPrimitiveRoot`: the cyclotomic character of
  a domain lacking a primitive `pⁱ`-th root of unity for some `i` is trivial.
* `TauCeti.cyclotomicCharacter_eq_of_forall_pow_eq_one`: two automorphisms that agree on the roots
  of unity of `p`-power order have the same cyclotomic character.
* `TauCeti.cyclotomicCharacter_eq_of_injective`: the cyclotomic character is natural along an
  injective ring homomorphism intertwining two automorphisms.
* `TauCeti.coe_cyclotomicCharacter_eq_natCast`: an automorphism raising every root of unity of
  `p`-power order to the `c`-th power has cyclotomic character `c`.
-/

public section

namespace TauCeti

open Function

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  (p : ℕ) [Fact p.Prime]

/-- **The cyclotomic character is trivial without enough roots of unity**: if a domain `A` lacks a
primitive `pⁱ`-th root of unity for some `i`, its cyclotomic character is the trivial
character. -/
@[simp]
theorem cyclotomicCharacter_eq_one_of_not_forall_isPrimitiveRoot
    (H : ¬ ∀ i : ℕ, ∃ ζ : A, IsPrimitiveRoot ζ (p ^ i)) (g : A ≃+* A) :
    cyclotomicCharacter A p g = 1 := by
  -- `cyclotomicCharacter` is `MonoidHom.toHomUnits` of `cyclotomicCharacter.toFun`, a `dite` on
  -- the existence of the roots of unity; Mathlib states no lemma for its negative branch.
  ext1
  simp only [cyclotomicCharacter, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk,
    cyclotomicCharacter.toFun, dite_eq_right H, Units.val_one]

/-- **The cyclotomic character only depends on the action on roots of unity**: two automorphisms
of a domain `A` that agree on every root of unity of `p`-power order have the same cyclotomic
character. In particular an automorphism fixing all these roots of unity has trivial character. -/
theorem cyclotomicCharacter_eq_of_forall_pow_eq_one {g h : A ≃+* A}
    (hgh : ∀ (n : ℕ) (t : A), t ^ p ^ n = 1 → g t = h t) :
    cyclotomicCharacter A p g = cyclotomicCharacter A p h := by
  by_cases hA : ∀ i : ℕ, ∃ ζ : A, IsPrimitiveRoot ζ (p ^ i)
  · have _ (i : ℕ) : HasEnoughRootsOfUnity A (p ^ i) := ⟨hA i, rootsOfUnity.isCyclic _ _⟩
    refine Units.ext <| PadicInt.ext_of_toZModPow.1 fun n ↦ ?_
    -- Both characters are read off from the action on one primitive `pⁿ`-th root of unity.
    obtain ⟨ζ, hζ⟩ := hA n
    have hpow := hgh n ζ hζ.pow_eq_one
    rw [cyclotomicCharacter.spec p g ζ hζ.pow_eq_one,
      cyclotomicCharacter.spec p h ζ hζ.pow_eq_one] at hpow
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow)
  · simp [hA]

/-- **Naturality of the cyclotomic character.** Let `f : A →+* B` be an injective homomorphism of
domains with `h ∘ f = f ∘ g` for automorphisms `g` of `A` and `h` of `B`. If `A` has primitive
`pⁱ`-th roots of unity for all `i` as soon as `B` does, then `g` and `h` have the same
cyclotomic character. -/
theorem cyclotomicCharacter_eq_of_injective {f : A →+* B} (hf : Injective f) {g : A ≃+* A}
    {h : B ≃+* B} (hfg : ∀ x, h (f x) = f (g x))
    (hroots : (∀ i : ℕ, ∃ ζ : B, IsPrimitiveRoot ζ (p ^ i)) →
      ∀ i : ℕ, ∃ ζ : A, IsPrimitiveRoot ζ (p ^ i)) :
    cyclotomicCharacter B p h = cyclotomicCharacter A p g := by
  by_cases hB : ∀ i : ℕ, ∃ ζ : B, IsPrimitiveRoot ζ (p ^ i)
  · have hA := hroots hB
    have _ (i : ℕ) : HasEnoughRootsOfUnity A (p ^ i) := ⟨hA i, rootsOfUnity.isCyclic _ _⟩
    have _ (i : ℕ) : HasEnoughRootsOfUnity B (p ^ i) := ⟨hB i, rootsOfUnity.isCyclic _ _⟩
    refine Units.ext <| PadicInt.ext_of_toZModPow.1 fun n ↦ ?_
    -- Both characters are read off from the action on the image of one primitive root.
    obtain ⟨ζ, hζ⟩ := hA n
    have hfζ : IsPrimitiveRoot (f ζ) (p ^ n) := hζ.map_of_injective hf
    have hpow := cyclotomicCharacter.spec p h (f ζ) hfζ.pow_eq_one
    rw [hfg, cyclotomicCharacter.spec p g ζ hζ.pow_eq_one, map_pow] at hpow
    exact ZMod.val_injective _ (hfζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow).symm
  · rw [cyclotomicCharacter_eq_one_of_not_forall_isPrimitiveRoot p hB,
      cyclotomicCharacter_eq_one_of_not_forall_isPrimitiveRoot (A := A) p fun hA ↦
        hB fun i ↦ let ⟨ζ, hζ⟩ := hA i; ⟨f ζ, hζ.map_of_injective hf⟩]

/-- **The cyclotomic character of an automorphism acting by a fixed power.** If a domain `A`
contains all roots of unity of `p`-power order and `g` raises each of them to the `c`-th power,
then the cyclotomic character of `g` is `c`. -/
theorem coe_cyclotomicCharacter_eq_natCast [∀ i, HasEnoughRootsOfUnity A (p ^ i)]
    {g : A ≃+* A} {c : ℕ} (hc : ∀ (n : ℕ) (t : A), t ^ p ^ n = 1 → g t = t ^ c) :
    (cyclotomicCharacter A p g : ℤ_[p]) = c := by
  refine PadicInt.ext_of_toZModPow.1 fun n ↦ ?_
  -- Both sides are read off from the action on one primitive `pⁿ`-th root of unity.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot A (p ^ n)
  have h := (cyclotomicCharacter.spec p g ζ hζ.pow_eq_one).symm.trans (hc n ζ hζ.pow_eq_one)
  rw [← pow_mod_orderOf ζ c, ← hζ.eq_orderOf] at h
  have hp : (p ^ n : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rw [map_natCast, ← ZMod.natCast_zmod_val (PadicInt.toZModPow n _),
    hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (Nat.pos_of_ne_zero hp)) h, ZMod.natCast_mod]

end TauCeti

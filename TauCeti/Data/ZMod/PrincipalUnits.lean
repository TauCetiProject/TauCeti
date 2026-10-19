/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

/-!
# Units congruent to one modulo a prime

For a prime `p`, the units of `ZMod (p ^ (k + 1))` that reduce to `1` in `ZMod p` form the kernel
of the reduction `ZMod.unitsMap`. That kernel has `p ^ k` elements, so raising to a power `n`
coprime to `p` permutes it. In particular, for an odd prime `p` every unit congruent to one
modulo `p` is a square modulo every power of `p`. This is the finite-level, group-order form of
the Hensel argument for principal units.

## Main results

* `ZMod.card_ker_unitsMap_mul_totient`: for `n ∣ m` with `m ≠ 0`, the kernel of
  `(ZMod m)ˣ → (ZMod n)ˣ` has `φ m / φ n` elements.
* `ZMod.card_ker_unitsMap_prime_pow`: the kernel of `(ZMod (p ^ (k + 1)))ˣ → (ZMod p)ˣ` has
  `p ^ k` elements.
* `ZMod.existsUnique_pow_eq_of_unitsMap_eq_one`: for `n` coprime to `p`, a unit congruent to one
  modulo `p` has a unique `n`-th root among the units congruent to one modulo `p`.
* `ZMod.isSquare_of_unitsMap_eq_one`: for an odd prime `p`, a unit of `ZMod (p ^ (k + 1))`
  congruent to one modulo `p` is a square.

## References

* Keith Conrad, *Hensel's lemma*, Example 2.8.
-/

public section

namespace ZMod

/-- The kernel of the reduction `(ZMod m)ˣ → (ZMod n)ˣ` along `n ∣ m` has `φ m / φ n` elements,
stated without division. -/
theorem card_ker_unitsMap_mul_totient {m n : ℕ} [NeZero m] (h : n ∣ m) :
    Nat.card (unitsMap h).ker * n.totient = m.totient := by
  have : NeZero n := ⟨fun hn ↦ NeZero.ne m (eq_zero_of_zero_dvd (hn ▸ h))⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective (unitsMap_surjective h)
  rwa [Nat.card_eq_fintype_card (α := (ZMod n)ˣ), Nat.card_eq_fintype_card (α := (ZMod m)ˣ),
    card_units_eq_totient, card_units_eq_totient] at hcard

/-- The units of `ZMod (p ^ (k + 1))` congruent to one modulo the prime `p` form a subgroup
with `p ^ k` elements. -/
theorem card_ker_unitsMap_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (h : p ∣ p ^ (k + 1)) :
    Nat.card (unitsMap h).ker = p ^ k := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcard := card_ker_unitsMap_mul_totient h
  rw [Nat.totient_prime hp, Nat.totient_prime_pow_succ hp] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.one_lt) hcard

/-- **`n`-th roots of units congruent to one modulo a prime.** If `n` is coprime to the prime
`p`, every unit of `ZMod (p ^ (k + 1))` congruent to one modulo `p` has exactly one `n`-th root
among the units congruent to one modulo `p`. -/
theorem existsUnique_pow_eq_of_unitsMap_eq_one {p k n : ℕ} (hp : p.Prime) (hn : n.Coprime p)
    {h : p ∣ p ^ (k + 1)} {u : (ZMod (p ^ (k + 1)))ˣ} (hu : unitsMap h u = 1) :
    ∃! v : (ZMod (p ^ (k + 1)))ˣ, unitsMap h v = 1 ∧ v ^ n = u := by
  have hcop : (Nat.card (unitsMap h).ker).Coprime n := by
    rw [card_ker_unitsMap_prime_pow hp k h]
    exact (hn.pow_right k).symm
  -- The `n`-th power map is a bijection of the kernel, whose order `p ^ k` is prime to `n`.
  obtain ⟨⟨v, hv⟩, hvu, huniq⟩ := (Nat.Coprime.pow_left_bijective hcop).existsUnique ⟨u, hu⟩
  refine ⟨v, ⟨hv, by simpa using congrArg Subtype.val hvu⟩, fun w ⟨hw, hwu⟩ ↦ ?_⟩
  simpa using congrArg Subtype.val (huniq ⟨w, hw⟩ (Subtype.ext (by simpa using hwu)))

/-- **Units congruent to one modulo an odd prime are squares.** For an odd prime `p`, every unit
of `ZMod (p ^ (k + 1))` whose reduction to `ZMod p` is `1` is a square of a unit. -/
theorem isSquare_of_unitsMap_eq_one {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {h : p ∣ p ^ (k + 1)} {u : (ZMod (p ^ (k + 1)))ˣ} (hu : unitsMap h u = 1) : IsSquare u := by
  have hn : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 hp2.symm
  obtain ⟨v, ⟨-, hv⟩, -⟩ := existsUnique_pow_eq_of_unitsMap_eq_one hp hn hu
  exact ⟨v, by rw [← hv, sq]⟩

/-! Modulo `9`, the units `4` and `7` are `2 ^ 2` and `4 ^ 2`. The hypothesis that `p` is odd is
needed: `5` is congruent to one modulo `2` but is not a square modulo `8`. -/

example : (2 : ZMod 9) ^ 2 = 4 ∧ (4 : ZMod 9) ^ 2 = 7 := by decide

example : ¬ ∃ x : ZMod 8, x ^ 2 = 5 := by decide

end ZMod

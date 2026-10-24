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
import Mathlib.RingTheory.Artinian.Module
-- Supplies completeness of Artinian local rings, needed by the Henselian instance.
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.ZMod.LocalRing
import TauCeti.Data.ZMod.LocalRing
import TauCeti.RingTheory.Henselian.Basic

/-!
# Units congruent to one modulo a prime

For a prime `p`, the units of `ZMod (p ^ (k + 1))` that reduce to `1` in `ZMod p` form the kernel
of the reduction `ZMod.unitsMap`. That kernel has `p ^ k` elements, so raising to a power `n`
coprime to `p` permutes it. In particular, for an odd prime `p` every unit congruent to one
modulo `p` is a square modulo every power of `p`. This is the finite-level, group-order form of
the Hensel argument for principal units.

Consequently, for `n` coprime to `p` and an integer `a` prime to `p`, reduction modulo `p` is a
bijection from the `n`-th roots of `a` modulo `p ^ k` (`k ≠ 0`) to those modulo `p`. Surjectivity
is Hensel's lemma `TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq` in the Henselian
local ring `ZMod (p ^ k)`, and injectivity holds because two `n`-th roots of `a` with the same
reduction differ by a principal unit whose `n`-th power is `1`.

## Main results

* `ZMod.card_ker_unitsMap_mul_totient`: for `n ∣ m` with `m ≠ 0`, the kernel of
  `(ZMod m)ˣ → (ZMod n)ˣ` has `φ m / φ n` elements.
* `ZMod.card_ker_unitsMap_prime_pow`: the kernel of `(ZMod (p ^ (k + 1)))ˣ → (ZMod p)ˣ` has
  `p ^ k` elements.
* `ZMod.existsUnique_pow_eq_of_unitsMap_eq_one`: for `n` coprime to `p`, a unit congruent to one
  modulo `p` has a unique `n`-th root among the units congruent to one modulo `p`.
* `ZMod.isSquare_of_unitsMap_eq_one`: for an odd prime `p`, a unit of `ZMod (p ^ (k + 1))`
  congruent to one modulo `p` is a square.
* `ZMod.natCard_nthRoots_prime_pow_eq_natCard_nthRoots`: for `n` coprime to `p`, a unit `a` has
  as many `n`-th roots modulo `p ^ k` as modulo `p`.

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

/-- **Hensel's lemma for `n`-th roots, as a count.** For `n` coprime to the prime `p`, an integer
`a` prime to `p` and `k ≠ 0`, reduction modulo `p` is a bijection from the `n`-th roots of `a`
modulo `p ^ k` to those modulo `p`; so there are equally many. -/
theorem natCard_nthRoots_prime_pow_eq_natCard_nthRoots {p n k : ℕ} [Fact p.Prime]
    (hn : n.Coprime p) (hk : k ≠ 0) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    Nat.card {x : ZMod (p ^ k) // x ^ n = a} = Nat.card {x : ZMod p // x ^ n = a} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hdvd : p ∣ p ^ (k + 1) := dvd_pow_self p hk
  set π := castHom hdvd (ZMod p)
  have hunit (x : ZMod (p ^ (k + 1))) (hx : π x ^ n = a) : IsUnit x := by
    refine (isUnit_prime_pow_iff_castHom_ne_zero p (k + 1) k.succ_pos x).mpr fun h0 ↦ ha ?_
    rw [← hx, h0, zero_pow]
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.mp hn)
  have hπ (x : ZMod (p ^ (k + 1))) (hx : x ^ n = a) : π x ^ n = a := by
    rw [← map_pow, hx, map_intCast]
  refine Finset.card_bij (fun x _ ↦ π x) (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_) (fun z hz ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hπ x hx
  · -- Two `n`-th roots of `a` with the same reduction differ by a principal unit `w` with
    -- `w ^ n = 1`, which is `1` by uniqueness of principal `n`-th roots.
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have huniq := existsUnique_pow_eq_of_unitsMap_eq_one (Fact.out : p.Prime) hn (map_one _)
      (h := hdvd)
    have hw : (hunit y (hπ y hy)).unit * (hunit x (hπ x hx)).unit⁻¹ = 1 := by
      refine huniq.unique ⟨?_, ?_⟩ ⟨map_one _, one_pow n⟩
      · rw [map_mul, map_inv, mul_inv_eq_one]
        ext
        simpa [unitsMap_val, π] using hxy.symm
      · rw [mul_pow, inv_pow, mul_inv_eq_one]
        ext
        simp [hx, hy]
    simpa using congrArg Units.val (mul_inv_eq_one.mp hw).symm
  · -- `ZMod (p ^ (k + 1))` is a Henselian local ring whose residue map is the reduction `π`, so a
    -- lift of the simple root `z` of `X ^ n - a` modulo `p` lifts to a root.
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    let : IsArtinianRing (ZMod (p ^ (k + 1))) := isArtinian_of_finite
    set x₀ : ZMod (p ^ (k + 1)) := (z.val : ZMod (p ^ (k + 1)))
    have hπx₀ : π x₀ ^ n = a := by rw [map_natCast, natCast_zmod_val, hz]
    obtain ⟨x, hx, hxx₀⟩ := TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq
      (u := (a : ZMod (p ^ (k + 1)))) ((isUnit_iff_coprime n _).mpr (hn.pow_right _))
      (hunit x₀ hπx₀)
      (by rw [← map_pow, residue_eq_residue_iff_castHom_eq p (k + 1) k.succ_pos,
        map_pow, hπx₀, map_intCast])
    exact ⟨x, by simpa using hx, by
      rw [(residue_eq_residue_iff_castHom_eq p (k + 1) k.succ_pos x x₀).mp hxx₀,
        map_natCast, natCast_zmod_val]⟩

/-! Modulo `9`, the units `4` and `7` are `2 ^ 2` and `4 ^ 2`. The hypothesis that `p` is odd is
needed: `5` is congruent to one modulo `2` but is not a square modulo `8`. -/

example : (2 : ZMod 9) ^ 2 = 4 ∧ (4 : ZMod 9) ^ 2 = 7 := by decide

example : ¬ ∃ x : ZMod 8, x ^ 2 = 5 := by decide

end ZMod

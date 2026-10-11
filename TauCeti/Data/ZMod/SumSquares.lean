/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Data.ZMod.Units

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NthRewrite

/-!
# Sums of two squares modulo odd prime powers

Every unit modulo a power of an odd prime is a sum of two squares. Mathlib's
finite-field sum-of-squares theorem supplies a residue solution with a nonzero
coordinate. Hensel lifting in the finite local ring lifts that coordinate.
The exponent-zero case is the trivial ring.

## Main declarations

* `ZMod.exists_sq_add_sq_eq_of_isUnit_prime_pow`: the unit sum-of-squares representation.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(a), for the doubled odd cyclic relation that this arithmetic supplies.
-/

public section

open Polynomial

namespace ZMod

private theorem unit_iff_cast_ne_zero (p k : ℕ) [Fact p.Prime] (hk : 0 < k)
    (x : ZMod (p ^ k)) :
    IsUnit x ↔ ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x ≠ 0 := by
  have h := ZMod.isUnit_natCast_iff_not_dvd_pow (a := x.val) (Fact.out : p.Prime) hk
  rw [ZMod.natCast_zmod_val] at h
  rw [h]
  have hx : ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x =
      (x.val : ZMod p) := by
    nth_rw 1 [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  rw [hx, Ne, ZMod.natCast_eq_zero_iff]

private theorem local_ring_prime_power (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    IsLocalRing (ZMod (p ^ k)) := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow hk.ne' (Fact.out : p.Prime).one_lt⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  rw [unit_iff_cast_ne_zero p k hk, unit_iff_cast_ne_zero p k hk, map_sub, map_one]
  by_cases h : ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x = 0
  · right
    simp [h]
  · exact Or.inl h

private theorem lift_norm (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 0 < k)
    (r : ZMod (p ^ k)) (a b : ZMod p) (ha : a ≠ 0)
    (hab : a ^ 2 + b ^ 2 = ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) r) :
    ∃ x y : ZMod (p ^ k), x ^ 2 + y ^ 2 = r := by
  let := local_ring_prime_power p k hk
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let : IsArtinianRing (ZMod (p ^ k)) := isArtinian_of_finite
  let φ := ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p)
  let a₀ : ZMod (p ^ k) := a.val
  let b₀ : ZMod (p ^ k) := b.val
  let f : (ZMod (p ^ k))[X] := X ^ 2 + C (b₀ ^ 2 - r)
  have ha₀ : φ a₀ = a := by simp only [φ, a₀, map_natCast, ZMod.natCast_zmod_val]
  have hb₀ : φ b₀ = b := by simp only [φ, b₀, map_natCast, ZMod.natCast_zmod_val]
  have hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal (ZMod (p ^ k)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, unit_iff_cast_ne_zero p k hk]
    simp only [not_not]
    change φ (f.eval a₀) = 0
    simp only [f, eval_add, eval_pow, eval_X, eval_C, eval_sub, map_add, map_pow, map_sub, ha₀, hb₀]
    linear_combination hab
  have hd : IsUnit (f.derivative.eval a₀) := by
    rw [unit_iff_cast_ne_zero p k hk]
    have htwo : (2 : ZMod p) ≠ 0 := by
      rw [← Nat.cast_ofNat, Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) h
      obtain ⟨s, hs⟩ := hp
      have := (Fact.out : p.Prime).two_le
      omega
    have hdval : f.derivative.eval a₀ = 2 * a₀ := by
      simp [f, derivative_pow]
    change φ (f.derivative.eval a₀) ≠ 0
    rw [hdval, map_mul, map_ofNat, ha₀]
    exact mul_ne_zero htwo ha
  obtain ⟨x, hx, _⟩ := HenselianRing.is_henselian f (monic_X_pow_add_C _ (by decide)) a₀
    hfa (hd.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ZMod (p ^ k)))))
  refine ⟨x, b₀, ?_⟩
  have hx' : x ^ 2 + (b₀ ^ 2 - r) = 0 := by
    simpa only [f, Polynomial.IsRoot, eval_add, eval_pow, eval_X, eval_C] using hx
  linear_combination hx'

/-- Every unit modulo a power of an odd prime is a sum of two squares. -/
theorem exists_sq_add_sq_eq_of_isUnit_prime_pow (p k : ℕ) [Fact p.Prime]
    (hp : Odd p) {r : ZMod (p ^ k)} (hr : IsUnit r) :
    ∃ a b : ZMod (p ^ k), a ^ 2 + b ^ 2 = r := by
  by_cases hk : k = 0
  · subst k
    have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  · have hkpos := Nat.pos_of_ne_zero hk
    let φ := ZMod.castHom (dvd_pow_self p hk) (ZMod p)
    have hr0 : φ r ≠ 0 := (hr.map φ).ne_zero
    obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (φ r)
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb ↦ hr0 (by simpa [ha, hb] using hab.symm)
      exact lift_norm p k hp hkpos r b a hb (by rw [add_comm]; exact hab)
    · exact lift_norm p k hp hkpos r a b ha hab

end ZMod

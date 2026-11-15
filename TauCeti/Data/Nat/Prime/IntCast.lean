/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Int.Basic

/-!
# Divisibility of integers by powers of a prime, read in a commutative ring

Let `p` be a prime number and `R` a commutative ring in which the image of `p` is not a unit. Then
the cast `ℤ → R` reflects divisibility by `p`: `(p : R) ∣ (x : R)` exactly when `p ∣ x` in `ℤ`,
since otherwise `p` and `x` are coprime in `ℤ` and `(p : R)` would divide `1`. If moreover the
image of `p` is not a zero divisor, for instance when `R` is a discrete valuation ring with
uniformiser `p` such as `ℤ_[p]` or the localisation of `ℤ` at `p`, the cast reflects divisibility
by powers of `p`: `(p : R) ^ n ∣ (x : R)` exactly when `p ^ n ∣ x` in `ℤ`. Divisibility conditions
on integral Weierstrass coefficients can therefore be checked over `ℤ`, by computation, and read
over `R`.

If every element of `R` is congruent to an integer modulo `p`, as when `R` has residue field
`𝔽_p`, then roots modulo `p` in `R` of an integer polynomial are read in `ZMod p`, where they can
be found by a finite search.

## Main results

* `Nat.Prime.dvd_intCast_iff`: `(p : R) ∣ (x : R) ↔ (p : ℤ) ∣ x`.
* `Nat.Prime.pow_dvd_intCast_iff`: `(p : R) ^ n ∣ (x : R) ↔ (p : ℤ) ^ n ∣ x`.
* `Nat.Prime.exists_dvd_eval_map_iff`: an integer polynomial has a root modulo `p` in `R` exactly
  when it has a root in `ZMod p`.
* `Nat.Prime.not_dvd_eval_map_of_forall_ne_zero`: an integer polynomial with no root in `ZMod p`
  has no root modulo `p` in `R`.
-/

public section

namespace Nat.Prime

/-- **Over a commutative ring in which a prime `p` is not a unit, divisibility of integers by `p`
can be read in `ℤ`.** -/
theorem dvd_intCast_iff {p : ℕ} (hp : p.Prime) {R : Type*} [CommRing R]
    (hu : ¬ IsUnit (p : R)) (x : ℤ) : (p : R) ∣ (x : R) ↔ (p : ℤ) ∣ x := by
  refine ⟨fun h ↦ not_not.1 fun hpx ↦ hu ?_, fun h ↦ by simpa using map_dvd (Int.castRingHom R) h⟩
  have hcop : IsCoprime ((p : ℤ) : R) (x : R) :=
    ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd.2 hpx).intCast
  exact hcop.isUnit_of_dvd' (by simp) h

/-- **Over a commutative ring in which a prime `p` is a nonunit and not a zero divisor,
divisibility of integers by powers of `p` can be read in `ℤ`.** This is the general form of
`PadicInt.pow_p_dvd_int_iff`. -/
theorem pow_dvd_intCast_iff {p : ℕ} (hp : p.Prime) {R : Type*} [CommRing R]
    (h₀ : IsRegular (p : R)) (hu : ¬ IsUnit (p : R)) (n : ℕ) (x : ℤ) :
    (p : R) ^ n ∣ (x : R) ↔ (p : ℤ) ^ n ∣ x := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using map_dvd (Int.castRingHom R) h⟩
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, rfl⟩ := ih x ((pow_dvd_pow _ n.le_succ).trans h)
    rw [pow_succ, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      (h₀.left.pow n).dvd_cancel_left, hp.dvd_intCast_iff hu] at h
    exact pow_succ (p : ℤ) n ▸ mul_dvd_mul_left _ h

open Polynomial in
/-- **Roots modulo `p` of an integer polynomial are read in `ZMod p`** over a commutative ring `R`
in which the prime `p` is not a unit and every element is congruent to an integer modulo `p`, for
instance a discrete valuation ring with uniformiser `p` and residue field `𝔽_p`. -/
theorem exists_dvd_eval_map_iff {p : ℕ} (hp : p.Prime) {R : Type*} [CommRing R]
    (hu : ¬ IsUnit (p : R)) (hR : ∀ x : R, ∃ n : ℤ, (p : R) ∣ x - n) (f : ℤ[X]) :
    (∃ s : R, (p : R) ∣ (f.map (Int.castRingHom R)).eval s) ↔
      ∃ x : ZMod p, (f.map (Int.castRingHom (ZMod p))).eval x = 0 := by
  have heval (n : ℤ) : (p : R) ∣ (f.map (Int.castRingHom R)).eval (n : R) ↔
      (f.map (Int.castRingHom (ZMod p))).eval (n : ZMod p) = 0 := by
    rw [eval_intCast_map, eval_intCast_map, eq_intCast, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd, hp.dvd_intCast_iff hu]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨n, hn⟩ := hR s
    exact ⟨n, (heval n).1 <|
      (dvd_iff_dvd_of_dvd_sub (hn.trans (sub_dvd_eval_sub s (n : R) _))).1 hs⟩
  · rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨n, (heval n).2 hx⟩

open Polynomial in
/-- **An integer polynomial with no root in `ZMod p` has no root modulo `p`** over a commutative
ring `R` as in `Nat.Prime.exists_dvd_eval_map_iff`. The hypothesis on `ZMod p` is a finite
search. -/
theorem not_dvd_eval_map_of_forall_ne_zero {p : ℕ} (hp : p.Prime) {R : Type*} [CommRing R]
    (hu : ¬ IsUnit (p : R)) (hR : ∀ x : R, ∃ n : ℤ, (p : R) ∣ x - n) {f : ℤ[X]}
    (hf : ∀ x : ZMod p, (f.map (Int.castRingHom (ZMod p))).eval x ≠ 0) (s : R) :
    ¬ (p : R) ∣ (f.map (Int.castRingHom R)).eval s := fun hs ↦
  let ⟨x, hx⟩ := (hp.exists_dvd_eval_map_iff hu hR f).1 ⟨s, hs⟩
  hf x hx

end Nat.Prime

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassNumberOne.FourthPowerCubic
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Prime
import TauCeti.Algebra.QuadraticAlgebra.Discriminant
import TauCeti.NumberTheory.NumberField.Quadratic.ClassNumber

/-!
# The integer points of the Heegner quartic `y² = 2u(u³ + 1)`

In Heegner's and Stark's proof of the class number one theorem, the values of `γ₂` at the CM
points of class number one are read off from the integer points of the quartic

  `y² = 2u(u³ + 1)`

(see `TauCeti.tschirnhausPolynomial_X_pow_four_eq_iff`). This file determines these points: they
are `(u, y) = (-1, 0), (0, 0), (1, ±2), (2, ±6)`. Consequently the integer cubics whose
fourth-power cubic is `X³ - γ X - 16` are twelve explicit cubics, and `γ` is one of
`0, -32, -96, -960, -5280, -640320`.

The proof is a descent through coprime factorizations. The factors `u` and `u³ + 1` are coprime,
so after removing the powers of `2` each of them is a square up to sign. This leaves three
equations in which a sixth power appears:

* `x³ = 2 y² + 1` forces `y = 0`. In `ℤ[√-2]`, a principal ideal domain whose only units are
  `±1`, the coprime factors of `(1 + y √-2)(1 - y √-2) = x³` are cubes, and comparing rational
  parts in `1 + y √-2 = (p + q √-2)³` gives `p (p² - 6 q²) = 1`, hence `q = 0`.
* `m⁶ + 1 = 2 s²` forces `m² = 1`, because the odd coprime factor `m⁴ - m² + 1` of `m⁶ + 1` must
  be a square, and it lies strictly between `(m² - 1)²` and `(m²)²` once `m² > 1`.
* `s² = 8 m⁶ + 1` forces `m = 0` or `m² = 1`. Writing `s = 4 β + 1` gives
  `β (2 β + 1) = m⁶` with coprime factors, so both are sixth powers up to sign, and the two
  previous equations apply.

## Main results

* `TauCeti.eq_zero_of_pow_three_eq_two_mul_sq_add_one`: every integer solution of
  `x³ = 2 y² + 1` has `y = 0`.
* `TauCeti.sq_eq_one_of_pow_six_add_one_eq_two_mul_sq` and
  `TauCeti.eq_zero_or_sq_eq_one_of_sq_eq_eight_mul_pow_six_add_one`: the integer solutions of
  `m⁶ + 1 = 2 s²` have `m² = 1`, and those of `s² = 8 m⁶ + 1` have `m = 0` or `m² = 1`.
* `TauCeti.sq_eq_two_mul_mul_pow_three_add_one_iff`: the integer points of `y² = 2u(u³ + 1)` are
  exactly `(-1, 0), (0, 0), (1, ±2), (2, ±6)`.
* `TauCeti.mem_of_tschirnhausPolynomial_X_pow_four_eq` and
  `TauCeti.mem_image_intCast_of_tschirnhausPolynomial_X_pow_four_eq`: the integer cubics whose
  fourth-power cubic is `X³ - γ X - 16`, and the six possible values of `γ`.

## References

* H. M. Stark, *On the “gap” in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
* L. J. Mordell, *Diophantine Equations*, Academic Press, 1969 (equations `y² = x³ + k` by
  factorization in imaginary quadratic fields, as for `x³ = 2 y² + 1` in `ℤ[√-2]`).
-/

public section

open Polynomial QuadraticAlgebra

namespace TauCeti

/-- **The equation `x³ = 2 y² + 1`.** Every integer solution has `y = 0`, so `(x, y) = (1, 0)` is
the only one. -/
theorem eq_zero_of_pow_three_eq_two_mul_sq_add_one {x y : ℤ} (h : x ^ 3 = 2 * y ^ 2 + 1) :
    y = 0 := by
  have hsf : Squarefree (-2 : ℤ) := (Prime.neg Int.prime_two).squarefree
  have : Fact (¬ IsSquare (-2 : ℤ)) := ⟨fun ⟨r, hr⟩ ↦ by nlinarith [mul_self_nonneg r]⟩
  have : Fact (¬ IsSquare (discr (-2 : ℤ) 0)) :=
    ⟨fun ⟨r, hr⟩ ↦ by rw [discr_def] at hr; nlinarith [mul_self_nonneg r]⟩
  have : IsPrincipalIdealRing (QuadraticAlgebra ℤ (-2) 0) :=
    (classNumber_eq_one_iff_isPrincipalIdealRing_of_mod_four_ne_one hsf (by decide)).1
      (classNumber_eq_one_of_mod_four_ne_one_of_natAbs_le_two hsf (by decide) (by decide))
  -- Factor `x³ = (1 + y √-2)(1 - y √-2)` in the principal ideal domain `ℤ[√-2]`.
  set α : QuadraticAlgebra ℤ (-2) 0 := ⟨1, y⟩ with hα
  -- `α ᾱ = 1 + 2 y² = x³`, and `α + ᾱ = 2` is coprime to `x³`, so `α` and `ᾱ` are coprime.
  have hprod : α * star α = (x : QuadraticAlgebra ℤ (-2) 0) ^ 3 := by
    -- Keep `2 y² + 1` as a single integer cast, whose coordinates are `re_intCast`/`im_intCast`.
    rw [← Int.cast_pow, h]
    ext <;> simp [hα, -Int.cast_pow, -Int.cast_add, -Int.cast_mul]
    ring
  have hodd : Odd (x ^ 3) := ⟨y ^ 2, h⟩
  obtain ⟨r, s, hrs⟩ := Int.isCoprime_two_left.2 hodd
  have hcop : IsCoprime α (star α) := by
    refine ⟨r + s * star α, r, ?_⟩
    ext <;> simp [hα]
    · linear_combination hrs - s * h
    · ring
  -- So `α` is a cube up to a unit, and the units of `ℤ[√-2]` are `±1`.
  obtain ⟨δ, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  have hnorm : QuadraticAlgebra.norm (u : QuadraticAlgebra ℤ (-2) 0) = 1 := by
    have hn := Int.isUnit_iff.1 (u.isUnit.map QuadraticAlgebra.norm)
    have hnn :=
      norm_nonneg_of_discr_nonpos (by norm_num [discr_def]) (u : QuadraticAlgebra ℤ (-2) 0)
    omega
  rw [norm_def] at hnorm
  have him : (u : QuadraticAlgebra ℤ (-2) 0).im = 0 := by
    nlinarith [mul_self_nonneg (u : QuadraticAlgebra ℤ (-2) 0).re,
      mul_self_nonneg (u : QuadraticAlgebra ℤ (-2) 0).im]
  have hu2 : (u : QuadraticAlgebra ℤ (-2) 0) ^ 2 = 1 := by
    simp only [him, mul_zero, sub_zero, add_zero] at hnorm
    ext <;> simp [sq, him, hnorm]
  -- Write `α = (p + q √-2)³` and compare coordinates.
  have hcube : (δ * u) ^ 3 = α := by
    rw [mul_pow, pow_succ (u : QuadraticAlgebra ℤ (-2) 0) 2, hu2, one_mul, hu]
  generalize δ * (u : QuadraticAlgebra ℤ (-2) 0) = ε at hcube
  obtain ⟨p, q⟩ := ε
  have hre := congrArg QuadraticAlgebra.re hcube
  have hy := congrArg QuadraticAlgebra.im hcube
  simp only [pow_succ, pow_zero, one_mul, re_mul, im_mul, hα] at hre hy
  have hp : p * (p ^ 2 - 6 * q ^ 2) = 1 := by linear_combination hre
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hp with rfl | rfl
  · have hq : q ^ 2 = 0 := by linarith
    rw [pow_eq_zero_iff two_ne_zero] at hq
    subst hq
    linarith
  · omega

/-- **The equation `m⁶ + 1 = 2 s²`.** Every integer solution has `m² = 1`. -/
theorem sq_eq_one_of_pow_six_add_one_eq_two_mul_sq {m s : ℤ} (h : m ^ 6 + 1 = 2 * s ^ 2) :
    m ^ 2 = 1 := by
  obtain ⟨k, hk⟩ : Odd m := by
    rcases Int.even_or_odd m with hm | hm
    · have h1 : Even (m ^ 6 + 1) := ⟨s ^ 2, by rw [h]; ring⟩
      exact absurd (Int.even_pow.2 ⟨hm, by norm_num⟩) (Int.even_add_one.1 h1)
    · exact hm
  -- `m² + 1 = 2 e` and `(m⁴ - m² + 1) e = s²`, so the odd factor `m⁴ - m² + 1` will be a square.
  set e := 2 * k ^ 2 + 2 * k + 1 with he_def
  have he : m ^ 2 + 1 = 2 * e := by rw [hk]; ring
  have hprod : (m ^ 4 - m ^ 2 + 1) * e = s ^ 2 :=
    mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by rw [hk] at h ⊢; linear_combination h)
  -- `e² ≡ 1 (mod 3)` and `m⁴ - m² + 1 = 2 e (m² - 2) + 3`, so the two factors are coprime.
  have h3 : ((e ^ 2 - 1 : ℤ) : ZMod 3) = 0 := by
    rw [he_def]
    push_cast
    generalize (k : ZMod 3) = t
    revert t
    decide
  obtain ⟨r, hr⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h3
  push_cast at hr
  have hcop : IsCoprime (m ^ 4 - m ^ 2 + 1) e :=
    ⟨-r, e + 2 * r * (m ^ 2 - 2), by linear_combination hr - r * (m ^ 2 - 2) * he⟩
  have hm1 : 1 ≤ m ^ 2 := by
    have : m ≠ 0 := by omega
    have : 0 < m ^ 2 := by positivity
    omega
  obtain ⟨q, hq | hq⟩ := Int.sq_of_isCoprime hcop hprod
  · -- The square `m⁴ - m² + 1` lies strictly between `(m² - 1)²` and `(m²)²` unless `m² = 1`.
    by_contra hne
    have hm2 : 2 ≤ m ^ 2 := by omega
    have h1 : |m ^ 2 - 1| < |q| := sq_lt_sq.1 (by nlinarith)
    have h2 : |q| < |m ^ 2| := sq_lt_sq.1 (by nlinarith)
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ m ^ 2 - 1)] at h1
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ m ^ 2)] at h2
    omega
  · nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg m) (sub_nonneg.2 hm1)]

/-- **The equation `s² = 8 m⁶ + 1`.** Every integer solution has `m = 0` or `m² = 1`. -/
theorem eq_zero_or_sq_eq_one_of_sq_eq_eight_mul_pow_six_add_one {m s : ℤ}
    (h : s ^ 2 = 8 * m ^ 6 + 1) : m = 0 ∨ m ^ 2 = 1 := by
  have hs : Odd s := by
    rcases Int.even_or_odd s with hs | hs
    · exact absurd (⟨4 * m ^ 6, by rw [h]; ring⟩ : Odd (s ^ 2))
        (Int.not_odd_iff_even.2 (Int.even_pow.2 ⟨hs, two_ne_zero⟩))
    · exact hs
  -- Replacing `s` by `-s` if necessary, `s = 4 β + 1`.
  wlog hs4 : s % 4 = 1 generalizing s with H
  · have := Int.odd_iff.1 hs
    exact H (s := -s) (by rw [neg_sq, h]) hs.neg (by omega)
  set β := s / 4
  have hprod : β * (2 * β + 1) = m ^ 6 :=
    mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) <| by
      rw [show s = 4 * β + 1 by omega] at h
      linear_combination h
  -- The coprime factors `β` and `2 β + 1` are sixth powers up to sign, which leads to the
  -- equations `x³ = 2 y² + 1` and `m⁶ + 1 = 2 s²`.
  have hcop : IsCoprime β (2 * β + 1) := ⟨-2, 1, by ring⟩
  obtain ⟨a, ha⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  obtain ⟨b, hb⟩ := exists_associated_pow_of_mul_eq_pow' hcop.symm (by rw [mul_comm, hprod])
  have ha6 : 0 ≤ a ^ 6 := by positivity
  have hb6 : 0 ≤ b ^ 6 := by positivity
  have hβ0 (hβ : β = 0) : m = 0 := by
    rw [hβ, zero_mul, eq_comm, pow_eq_zero_iff (by norm_num)] at hprod
    exact hprod
  rcases Int.associated_iff.1 ha with ha | ha <;> rcases Int.associated_iff.1 hb with hb | hb
  · -- `b⁶ = 2 a⁶ + 1`, so `a = 0`.
    have := eq_zero_of_pow_three_eq_two_mul_sq_add_one (x := b ^ 2) (y := a ^ 3)
      (by linear_combination hb - 2 * ha)
    rw [pow_eq_zero_iff (by norm_num)] at this
    exact .inl (hβ0 (by rw [← ha, this]; ring))
  · linarith
  · exact .inl (hβ0 (by omega))
  · -- `b⁶ + 1 = 2 a⁶`, so `b² = 1`, `β = -1` and `m⁶ = 1`.
    have hb2 := sq_eq_one_of_pow_six_add_one_eq_two_mul_sq (m := b) (s := a ^ 3)
      (by linear_combination hb - 2 * ha)
    have hβ : β = -1 := by
      have : b ^ 6 = (b ^ 2) ^ 3 := by ring
      rw [this, hb2] at hb
      omega
    rw [hβ] at hprod
    refine .inr ((pow_eq_one_iff_of_nonneg (sq_nonneg m) (by norm_num : 3 ≠ 0)).1 ?_)
    linear_combination -hprod

/-- The even case `u = 2 w` of the Heegner quartic: `w (8 w³ + 1)` is a square only for
`w = 0, 1`. -/
private theorem eq_zero_or_eq_one_of_mul_eight_mul_pow_three_add_one_eq_sq {w t : ℤ}
    (h : w * (8 * w ^ 3 + 1) = t ^ 2) : w = 0 ∨ w = 1 := by
  -- The factors `w` and `8 w³ + 1` are coprime, so both are squares up to sign.
  have hcop : IsCoprime w (8 * w ^ 3 + 1) := ⟨-8 * w ^ 2, 1, by ring⟩
  obtain ⟨m, hm | hm⟩ := Int.sq_of_isCoprime hcop h <;>
    obtain ⟨s, hs | hs⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm, h])
  · -- `s² = 8 m⁶ + 1`.
    rcases eq_zero_or_sq_eq_one_of_sq_eq_eight_mul_pow_six_add_one (m := m) (s := s)
      (by rw [← hs, hm]; ring) with rfl | hm1
    · simp [hm]
    · simp [hm, hm1]
  · nlinarith [pow_nonneg (hm ▸ sq_nonneg m : 0 ≤ w) 3, sq_nonneg s]
  · -- `8 w³ + 1 = s² ≥ 0` with `w ≤ 0` forces `w = 0`.
    have hw3 : w ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) (hm ▸ neg_nonpos.2 (sq_nonneg m))
    have : w ^ 3 = 0 := by nlinarith [sq_nonneg s]
    exact .inl ((pow_eq_zero_iff (by norm_num)).1 this)
  · -- `s² + 1 = -8 w³` is impossible modulo `4`.
    exfalso
    rcases Int.even_or_odd s with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> ring_nf at hs <;> omega

/-- The odd case of the Heegner quartic: if `u³ + 1 = 2 v` and `u v` is a square, then
`u = ±1`. -/
private theorem eq_neg_one_or_eq_one_of_mul_eq_sq {u v t : ℤ} (hv : u ^ 3 + 1 = 2 * v)
    (h : u * v = t ^ 2) : u = -1 ∨ u = 1 := by
  -- The factors `u` and `v` are coprime, so both are squares up to sign.
  have hcop : IsCoprime u v := ⟨-u ^ 2, 2, by linear_combination -hv⟩
  obtain ⟨m, hm | hm⟩ := Int.sq_of_isCoprime hcop h
  · have hu : 0 ≤ u := hm ▸ sq_nonneg m
    obtain ⟨s, hs | hs⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm, h])
    · -- `m⁶ + 1 = 2 s²`.
      have := sq_eq_one_of_pow_six_add_one_eq_two_mul_sq (m := m) (s := s)
        (by rw [← hs, ← hv, hm]; ring)
      simp [hm, this]
    · nlinarith [pow_nonneg hu 3, sq_nonneg s]
  · -- `u ≤ 0` and `u³ + 1 = ± 2 s²`; in both cases `u³ = -1`.
    have hu : u ≤ 0 := hm ▸ neg_nonpos.2 (sq_nonneg m)
    suffices hu3 : (-u) ^ 3 = 1 by
      have := (pow_eq_one_iff_of_nonneg (neg_nonneg.2 hu) (by norm_num)).1 hu3
      omega
    obtain ⟨s, hs | hs⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm, h])
    · -- `u ≠ 0`, since `u³ + 1 = 2 v` is even.
      have hu1 : u ≤ -1 := by
        rcases hu.lt_or_eq with hu | rfl
        · omega
        · norm_num at hv; omega
      nlinarith [sq_nonneg s, sq_nonneg u, mul_nonneg (neg_nonneg.2 hu) (sq_nonneg u)]
    · -- `m⁶ = 2 s² + 1`.
      have := eq_zero_of_pow_three_eq_two_mul_sq_add_one (x := m ^ 2) (y := s)
        (by linear_combination -hv - 2 * hs + (m ^ 4 - m ^ 2 * u + u ^ 2) * hm)
      rw [this] at hs
      linear_combination -hv - 2 * hs

/-- **The integer points of the Heegner quartic.** The integer solutions of `y² = 2u(u³ + 1)` are
exactly `(u, y) = (-1, 0), (0, 0), (1, ±2), (2, ±6)`. -/
theorem sq_eq_two_mul_mul_pow_three_add_one_iff {u y : ℤ} :
    y ^ 2 = 2 * u * (u ^ 3 + 1) ↔
      (u, y) ∈ ({(-1, 0), (0, 0), (1, 2), (1, -2), (2, 6), (2, -6)} : Finset (ℤ × ℤ)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  refine ⟨fun h ↦ ?_, ?_⟩
  swap
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num
  -- It suffices to show `u ∈ {-1, 0, 1, 2}`, since `y` is then determined up to sign by `y²`.
  suffices hu : u = -1 ∨ u = 0 ∨ u = 1 ∨ u = 2 by
    have hy (c : ℤ) (hc : y ^ 2 = c ^ 2) : y = c ∨ y = -c := sq_eq_sq_iff_eq_or_eq_neg.1 hc
    rcases hu with rfl | rfl | rfl | rfl
    · rcases hy 0 (by linarith) with rfl | rfl <;> simp
    · rcases hy 0 (by linarith) with rfl | rfl <;> simp
    · rcases hy 2 (by linarith) with rfl | rfl <;> simp
    · rcases hy 6 (by linarith) with rfl | rfl <;> simp
  -- `y = 2 t` with `2 t² = u (u³ + 1)`; split according to the parity of `u`.
  obtain ⟨t, rfl⟩ : Even y := (Int.even_pow.1 ⟨u * (u ^ 3 + 1), by rw [h]; ring⟩).1
  have ht : 2 * t ^ 2 = u * (u ^ 3 + 1) :=
    mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination h)
  rcases Int.even_or_odd u with ⟨w, rfl⟩ | ⟨k, hk⟩
  · rcases eq_zero_or_eq_one_of_mul_eight_mul_pow_three_add_one_eq_sq (w := w) (t := t)
      (mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination -ht)) with rfl | rfl <;>
      simp
  · obtain ⟨v, hv⟩ : ∃ v, u ^ 3 + 1 = 2 * v :=
      ⟨4 * k ^ 3 + 6 * k ^ 2 + 3 * k + 1, by rw [hk]; ring⟩
    rcases eq_neg_one_or_eq_one_of_mul_eq_sq (t := t) hv
      (mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination -ht - u * hv)) with
      rfl | rfl <;> simp

/-- **The integer cubics with fourth-power cubic `X³ - γ X - 16`.** If the Tschirnhaus transform
by `X⁴` of `X³ + a X² + b X + c`, with `a, b, c ∈ ℤ`, is `X³ - γ X - 16`, then `(a, b, c)` is one of
twelve explicit triples. -/
theorem mem_of_tschirnhausPolynomial_X_pow_four_eq {R : Type*} [CommRing R] [CharZero R]
    {a b c : ℤ} {γ : R}
    (h : tschirnhausPolynomial (X ^ 3 + C (a : R) * X ^ 2 + C (b : R) * X + C (c : R)) (X ^ 4) =
      X ^ 3 - C γ * X - 16) :
    (a, b, c) ∈ ({(-4, 28, 2), (-4, 4, 2), (-2, 8, 2), (-2, 0, 2), (0, 0, 2), (2, 4, 2),
      (-2, 4, -2), (0, 0, -2), (2, 8, -2), (2, 0, -2), (4, 28, -2), (4, 4, -2)} :
        Finset (ℤ × ℤ × ℤ)) := by
  obtain ⟨hc, u, y, hy, rfl, rfl, -⟩ := tschirnhausPolynomial_X_pow_four_eq_iff.1 h
  have := sq_eq_two_mul_mul_pow_three_add_one_iff.1 hy
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
  rcases hc with rfl | rfl <;>
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide

/-- **The six values of `γ`.** If the Tschirnhaus transform by `X⁴` of an integer cubic
`X³ + a X² + b X + c` is `X³ - γ X - 16`, then `γ` is one of `0, -32, -96, -960, -5280, -640320`.
These are the values of `γ₂` at the CM points of discriminants `-3, -11, -19, -43, -67, -163`. -/
theorem mem_image_intCast_of_tschirnhausPolynomial_X_pow_four_eq {R : Type*} [CommRing R]
    [CharZero R] {a b c : ℤ} {γ : R}
    (h : tschirnhausPolynomial (X ^ 3 + C (a : R) * X ^ 2 + C (b : R) * X + C (c : R)) (X ^ 4) =
      X ^ 3 - C γ * X - 16) :
    γ ∈ (Int.cast '' {0, -32, -96, -960, -5280, -640320} : Set R) := by
  obtain ⟨-, u, y, hy, -, -, rfl⟩ := tschirnhausPolynomial_X_pow_four_eq_iff.1 h
  exact Set.mem_image_of_mem _ <| by
    simpa using heegnerGamma_mem (sq_eq_two_mul_mul_pow_three_add_one_iff.1 hy)

end TauCeti

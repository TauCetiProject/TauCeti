/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.StronglyDvd

import Mathlib.FieldTheory.Finite.Polynomial
import TauCeti.Algebra.MvPolynomial.Eval

/-!
# Multivariate polynomials that are squares modulo four

A squared power of a variable can be cancelled from a square modulo four over the integers.
Over any commutative ring, the values of a polynomial that is a square modulo four agree
modulo four on each coefficient class modulo two.
-/

public section

namespace MvPolynomial

open UniqueFactorizationMonoid

/-- Cancel a squared power of a variable from a polynomial that is a square modulo four.
Reduce modulo two to extract a factor from the square root, then cancel modulo four. -/
theorem exists_eq_sq_sub_four_mul_of_X_pow_mul {σ : Type*} (i : σ) (k : ℕ)
    {d s t : MvPolynomial σ ℤ} (h : (MvPolynomial.X i ^ k) ^ 2 * d = s ^ 2 - 4 * t) :
    ∃ u v : MvPolynomial σ ℤ, d = u ^ 2 - 4 * v := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ₂ := MvPolynomial.map (Int.castRingHom (ZMod 2)) (σ := σ)
  let ρ₄ := MvPolynomial.map (Int.castRingHom (ZMod 4)) (σ := σ)
  have h4₂ : (4 : MvPolynomial σ (ZMod 2)) = 0 := by
    have h2 : (2 : MvPolynomial σ (ZMod 2)) = 0 :=
      CharP.cast_eq_zero (MvPolynomial σ (ZMod 2)) 2
    calc
      (4 : MvPolynomial σ (ZMod 2)) = 2 * 2 := by ring
      _ = 0 := by rw [h2, zero_mul]
  have h4₄ : (4 : MvPolynomial σ (ZMod 4)) = 0 := by
    exact CharP.cast_eq_zero (MvPolynomial σ (ZMod 4)) 4
  have h₂ : ((MvPolynomial.X i : MvPolynomial σ (ZMod 2)) ^ k) ^ 2 * ρ₂ d = (ρ₂ s) ^ 2 := by
    simpa [ρ₂, h4₂] using congrArg ρ₂ h
  have hdiv : (MvPolynomial.X i : MvPolynomial σ (ZMod 2)) ^ k ∣ ρ₂ s :=
    (pow_dvd_pow_iff_dvd two_ne_zero).mp ⟨ρ₂ d, h₂.symm⟩
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨u, hu⟩ := MvPolynomial.map_surjective (σ := σ)
    (f := Int.castRingHom (ZMod 2)) ZMod.intCast_surjective q
  have heven : MvPolynomial.C (2 : ℤ) ∣ s - MvPolynomial.X i ^ k * u := by
    refine (C_dvd_iff_zmod 2 _).2 ?_
    simpa [ρ₂, hu] using sub_eq_zero.mpr hq
  obtain ⟨b, hb⟩ := heven
  have hb' : s = MvPolynomial.X i ^ k * u + 2 * b := by
    rw [sub_eq_iff_eq_add] at hb
    simpa [add_comm] using hb
  have h₄ : ((MvPolynomial.X i : MvPolynomial σ (ZMod 4)) ^ k) ^ 2 * ρ₄ d =
      (ρ₄ s) ^ 2 := by
    simpa [ρ₄, h4₄] using congrArg ρ₄ h
  have hsq : (ρ₄ s) ^ 2 =
      ((MvPolynomial.X i : MvPolynomial σ (ZMod 4)) ^ k) ^ 2 * (ρ₄ u) ^ 2 := by
    have hs : ρ₄ s = MvPolynomial.X i ^ k * ρ₄ u + 2 * ρ₄ b := by
      simp only [hb', map_add, map_mul, map_pow, map_ofNat, ρ₄, MvPolynomial.map_X]
    rw [hs, ← mul_pow]
    linear_combination (MvPolynomial.X i ^ k * ρ₄ u * ρ₄ b + (ρ₄ b) ^ 2) * h4₄
  have hd : ρ₄ d = (ρ₄ u) ^ 2 :=
    ((MvPolynomial.isRegular_X_pow (R := ZMod 4) (n := i) k).pow 2).left (h₄.trans hsq)
  have hfour : MvPolynomial.C (4 : ℤ) ∣ u ^ 2 - d := by
    refine (C_dvd_iff_zmod 4 _).2 ?_
    simp [← hd, ρ₄]
  obtain ⟨v, hv⟩ := hfour
  rw [map_ofNat] at hv
  exact ⟨u, v, by linear_combination -hv⟩

/-- A polynomial that is a square modulo four has congruent values modulo four at points
that agree coordinatewise modulo two. -/
theorem four_dvd_eval_sub_eval_of_eq_sq_sub_four_mul {σ R : Type*} [CommRing R]
    {d s t : MvPolynomial σ R} {a b : σ → R} (h : d = s ^ 2 - 4 * t)
    (hab : ∀ i, 2 ∣ b i - a i) : 4 ∣ eval b d - eval a d := by
  obtain ⟨c, hc⟩ := dvd_eval_sub_eval s hab
  have hb : eval b s = eval a s + 2 * c := by linear_combination hc
  refine ⟨c * (eval a s + c) - (eval b t - eval a t), ?_⟩
  simp only [h, map_sub, map_pow, map_mul, map_ofNat, hb]
  ring

/-- For a polynomial that is a square modulo four, divisibility by four at one point implies
divisibility by four throughout its class modulo two. -/
theorem not_weaklyDvdAt_of_eq_sq_sub_four_mul {σ R : Type*} [CommRing R]
    {d s t : MvPolynomial σ R} {a : σ → R} (h : d = s ^ 2 - 4 * t) :
    ¬ d.WeaklyDvdAt 2 4 a := by
  have hstrong : d.StronglyDvdAt 2 4 a ↔ d.StronglyDvdAt 4 4 a := by
    rw [stronglyDvdAt_self_iff]
    exact ⟨StronglyDvdAt.dvd_eval, fun ha ↦ stronglyDvdAt_iff.mpr fun b hb ↦
      (dvd_iff_dvd_of_dvd_sub (four_dvd_eval_sub_eval_of_eq_sq_sub_four_mul h hb)).2 ha⟩
  simpa only [weaklyDvdAt_iff, hstrong] using
    (not_weaklyDvdAt_of_dvd (f := d) (a := a) (dvd_rfl : (4 : R) ∣ 4))

end MvPolynomial

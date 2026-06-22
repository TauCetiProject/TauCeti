/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Legendre symbols and square-class changes of radicand

The prime-splitting law for multiquadratic fields is naturally stated for square classes:
replacing a radicand `d` by `d * u^2`, with `p ∤ u`, should not change whether `d` is a
quadratic residue modulo `p`. This file records that elementary Legendre-symbol API in the
form consumed by the multiquadratic splitting theorem.

The main point is `legendreSym_mul_sq`, plus the finite-family wrapper
`forall_legendreSym_eq_of_forall_eq_mul_sq`. The companion divisibility lemmas show that the
unramified side condition `p ∤ d` is also invariant under the same square-class change.
-/

namespace TauCeti.Multiquadratic

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-- An integer prime from the ambient natural prime `p`. -/
private theorem prime_intCast_of_fact : Prime (p : ℤ) :=
  Nat.prime_iff_prime_int.mp Fact.out

/-- If `p ∤ u`, then `p` does not divide `u^2`. -/
theorem not_dvd_sq_of_not_dvd {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    ¬ (p : ℤ) ∣ u ^ 2 := by
  rw [pow_two]
  intro hsq
  rcases (prime_intCast_of_fact (p := p)).dvd_mul.mp hsq with hu' | hu'
  · exact hu hu'
  · exact hu hu'

/-- Multiplication by a square prime to `p` preserves non-divisibility by `p`. -/
theorem not_dvd_mul_sq_iff {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    ¬ (p : ℤ) ∣ a * u ^ 2 ↔ ¬ (p : ℤ) ∣ a := by
  constructor
  · intro h ha
    exact h (dvd_mul_of_dvd_left ha _)
  · intro ha hmul
    rcases (prime_intCast_of_fact (p := p)).dvd_mul.mp hmul with ha' | hu2
    · exact ha ha'
    · exact not_dvd_sq_of_not_dvd hu hu2

/-- The same non-divisibility invariance with the square on the left. -/
theorem not_dvd_sq_mul_iff {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    ¬ (p : ℤ) ∣ u ^ 2 * a ↔ ¬ (p : ℤ) ∣ a := by
  rw [mul_comm, not_dvd_mul_sq_iff hu]

/-- The Legendre symbol of a square prime to `p` is `1`. -/
theorem legendreSym_sq_of_not_dvd {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p (u ^ 2) = 1 := by
  exact legendreSym.sq_one' p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])

/-- Multiplying an integer by a square prime to `p` does not change its Legendre symbol. -/
theorem legendreSym_mul_sq {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p (a * u ^ 2) = legendreSym p a := by
  rw [legendreSym.mul, legendreSym_sq_of_not_dvd hu, mul_one]

/-- Multiplying an integer on the left by a square prime to `p` does not change its Legendre
symbol. -/
theorem legendreSym_sq_mul {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p (u ^ 2 * a) = legendreSym p a := by
  rw [mul_comm, legendreSym_mul_sq hu]

/-- The quadratic-residue condition is invariant under multiplying the radicand by a square
prime to `p`. -/
theorem legendreSym_mul_sq_eq_one_iff {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p (a * u ^ 2) = 1 ↔ legendreSym p a = 1 := by
  rw [legendreSym_mul_sq hu]

/-- The left-multiplication version of `legendreSym_mul_sq_eq_one_iff`. -/
theorem legendreSym_sq_mul_eq_one_iff {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p (u ^ 2 * a) = 1 ↔ legendreSym p a = 1 := by
  rw [legendreSym_sq_mul hu]

/-- Equality to a square-class representative preserves the Legendre-symbol residue condition. -/
theorem legendreSym_eq_one_iff_of_eq_mul_sq {a b u : ℤ}
    (hb : b = a * u ^ 2) (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p b = 1 ↔ legendreSym p a = 1 := by
  rw [hb, legendreSym_mul_sq_eq_one_iff hu]

/-- Equality to a square-class representative preserves the Legendre symbol itself. -/
theorem legendreSym_eq_of_eq_mul_sq {a b u : ℤ} (hb : b = a * u ^ 2)
    (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p b = legendreSym p a := by
  rw [hb, legendreSym_mul_sq hu]

/-- Equality to a left square multiple preserves the Legendre symbol itself. -/
theorem legendreSym_eq_of_eq_sq_mul {a b u : ℤ} (hb : b = u ^ 2 * a)
    (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p b = legendreSym p a := by
  rw [hb, legendreSym_sq_mul hu]

/-- Equality to a square-class representative preserves the non-divisibility condition. -/
theorem not_dvd_iff_of_eq_mul_sq {a b u : ℤ} (hb : b = a * u ^ 2)
    (hu : ¬ (p : ℤ) ∣ u) :
    ¬ (p : ℤ) ∣ b ↔ ¬ (p : ℤ) ∣ a := by
  rw [hb, not_dvd_mul_sq_iff hu]

/-- A finite family of Legendre-symbol residue conditions is unchanged by multiplying each
radicand by a square prime to `p`. -/
theorem forall_legendreSym_mul_sq_eq_one_iff {ι : Type*} {d u : ι → ℤ}
    (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, legendreSym p (d i * u i ^ 2) = 1) ↔ ∀ i, legendreSym p (d i) = 1 := by
  simp_rw [legendreSym_mul_sq_eq_one_iff (p := p) (hu _)]

/-- Multiplying each radicand in a family by a square prime to `p` preserves all Legendre
symbols pointwise. -/
theorem forall_legendreSym_mul_sq_eq {ι : Type*} {d u : ι → ℤ}
    (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, legendreSym p (d i * u i ^ 2) = legendreSym p (d i)) := fun i =>
  legendreSym_mul_sq (p := p) (hu i)

/-- A finite family of unramifiedness conditions is unchanged by multiplying each radicand by a
square prime to `p`. -/
theorem forall_not_dvd_mul_sq_iff {ι : Type*} {d u : ι → ℤ}
    (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, ¬ (p : ℤ) ∣ d i * u i ^ 2) ↔ ∀ i, ¬ (p : ℤ) ∣ d i := by
  simp_rw [not_dvd_mul_sq_iff (p := p) (hu _)]

/-- Pointwise square-class representatives preserve all Legendre-symbol residue conditions in a
family. -/
theorem forall_legendreSym_eq_one_iff_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, legendreSym p (e i) = 1) ↔ ∀ i, legendreSym p (d i) = 1 := by
  constructor
  · intro h i
    exact (legendreSym_eq_one_iff_of_eq_mul_sq (p := p) (he i) (hu i)).mp (h i)
  · intro h i
    exact (legendreSym_eq_one_iff_of_eq_mul_sq (p := p) (he i) (hu i)).mpr (h i)

/-- Pointwise square-class representatives preserve the Legendre symbols of a family. -/
theorem forall_legendreSym_eq_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    ∀ i, legendreSym p (e i) = legendreSym p (d i) := fun i =>
  legendreSym_eq_of_eq_mul_sq (p := p) (he i) (hu i)

/-- Pointwise square-class representatives preserve all unramifiedness conditions in a family. -/
theorem forall_not_dvd_iff_of_forall_eq_mul_sq {ι : Type*} {d e u : ι → ℤ}
    (he : ∀ i, e i = d i * u i ^ 2) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) :
    (∀ i, ¬ (p : ℤ) ∣ e i) ↔ ∀ i, ¬ (p : ℤ) ∣ d i := by
  constructor
  · intro h i
    exact (not_dvd_iff_of_eq_mul_sq (p := p) (he i) (hu i)).mp (h i)
  · intro h i
    exact (not_dvd_iff_of_eq_mul_sq (p := p) (he i) (hu i)).mpr (h i)

end TauCeti.Multiquadratic

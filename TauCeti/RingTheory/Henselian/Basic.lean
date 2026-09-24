/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian

/-!
# Henselian rings

This file gathers the basic consequences of Henselianity that Mathlib does not provide.

Mathlib has both halves of the comparison between `HenselianRing R I`, which lifts a simple root
over `R ⧸ I`, and `HenselianLocalRing R`, which lifts a simple root over the residue field, except
for the step that produces the local class from the ideal-theoretic one at `I = 𝔪`. So
`IsAdicComplete.henselianRing` never reaches `HenselianLocalRing`, and the Henselian API is
unavailable for a complete local ring such as the integers of a complete discretely valued field.

The step is short: the two differ only in their simplicity hypothesis, `IsUnit (f' a₀)` against
`IsUnit (Ideal.Quotient.mk 𝔪 (f' a₀))`, and over a local ring a unit maps to a unit.

The second half of the file extracts roots. Let `R` be a ring that is Henselian at an ideal `J`,
and let `n` be a natural number that is invertible in `R`. Then every element `w` congruent to `1`
modulo an ideal `I ≤ J` has an `n`-th root that is itself congruent to `1` modulo `I`.

This is the standard source of `n`-th roots of principal units away from the residue
characteristic: over the integer ring of a local field it shows that each positive-depth step of
the unit filtration is carried onto itself by the `n`-th power map.

Without assuming `2` invertible, every element of `1 + 4J` is a square. This supplies deep
square roots in residue characteristic two, by solving `t² + t = c` for `c ∈ J`.

## Main results

* `TauCeti.HenselianRing.henselianLocalRing`: a local ring that is Henselian at its maximal ideal
  is a Henselian local ring.
* `TauCeti.IsAdicComplete.henselianLocalRing`: a local ring that is complete for the adic topology
  of its maximal ideal is a Henselian local ring.
* `TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq`: a simple power root in the
  residue field lifts to a root with the same residue.
* `TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem`: if `n` is invertible,
  `I ≤ J` and `w ≡ 1 mod I`, then `w = a ^ n` for some `a ≡ 1 mod I`.

## Implementation notes

Hensel's lemma applied to `X ^ n - w` at the approximate root `1` produces a root `a` with
`a ≡ 1` modulo `J` only. The congruence is then sharpened to `I` through the factorization
`a ^ n - 1 = (1 + a + ⋯ + a ^ (n - 1)) * (a - 1)`, whose first factor reduces to `n` modulo `J`
and is therefore a unit, `J` lying in the Jacobson radical.
-/

public section

open Polynomial

namespace TauCeti

open IsLocalRing

/-- A local ring that is Henselian at its maximal ideal is a Henselian local ring. The two
hypotheses differ only in their simplicity condition, which asks the derivative to be a unit in the
residue field rather than in the ring, and over a local ring the image of a unit is a unit.

This is not an instance: Mathlib already registers the converse implication as one, so the pair
would form an instance cycle. -/
theorem HenselianRing.henselianLocalRing (R : Type*) [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] : HenselianLocalRing R where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _)

/-- A local ring that is complete for the adic topology of its maximal ideal is a Henselian local
ring. This is Mathlib's `IsAdicComplete.henselianRing` at `I = 𝔪`, read through
`TauCeti.HenselianRing.henselianLocalRing`. -/
instance IsAdicComplete.henselianLocalRing (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R :=
  HenselianRing.henselianLocalRing R

namespace HenselianLocalRing

/-- If `n` is a unit, a unit residue root of `X ^ n - u` lifts to a root with the same residue. -/
theorem exists_pow_eq_of_residue_pow_eq {R : Type*} [CommRing R] [HenselianLocalRing R]
    {n : ℕ} (hn : IsUnit (n : R)) {x₀ u : R} (hx₀ : IsUnit x₀)
    (h : residue R x₀ ^ n = residue R u) :
    ∃ x : R, x ^ n = u ∧ residue R x = residue R x₀ := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨x₀, Subsingleton.elim _ _, rfl⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have heval : (X ^ n - C u).eval x₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    simp [map_sub, map_pow, h]
  have hder : IsUnit ((X ^ n - C u).derivative.eval x₀) := by
    have hd : (X ^ n - C u).derivative.eval x₀ = (n : R) * x₀ ^ (n - 1) := by
      simp [derivative_X_pow]
    exact hd ▸ hn.mul (hx₀.pow _)
  obtain ⟨x, hx, hres⟩ := HenselianLocalRing.is_henselian _
    (monic_X_pow_sub_C u hn0) x₀ heval hder
  refine ⟨x, by simpa [sub_eq_zero] using hx, ?_⟩
  exact (Ideal.Quotient.eq).mpr hres

end HenselianLocalRing

namespace HenselianRing

variable {R : Type*} [CommRing R]

/-- In a ring Henselian at an ideal `J`, if `n` is invertible then every element congruent to `1`
modulo an ideal `I ≤ J` is the `n`-th power of an element congruent to `1` modulo `I`. -/
theorem exists_pow_eq_and_sub_one_mem_of_sub_one_mem {I J : Ideal R} [HenselianRing R J]
    (hI : I ≤ J) {n : ℕ} (hn : IsUnit (n : R)) {w : R} (hw : w - 1 ∈ I) :
    ∃ a : R, a ^ n = w ∧ a - 1 ∈ I := by
  -- Over the zero ring `IsUnit (n : R)` says nothing, so `n = 0` is not excluded there.
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨1, Subsingleton.elim _ _, by simp⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have heval : (X ^ n - C w).eval (1 : R) ∈ J := by
    simpa using J.neg_mem_iff.mpr (hI hw)
  obtain ⟨a, ha, ha1⟩ := HenselianRing.is_henselian (X ^ n - C w)
    (monic_X_pow_sub_C w hn0) 1 heval
    (by simpa [derivative_X_pow] using hn.map (Ideal.Quotient.mk J))
  have hpow : a ^ n = w := by simpa [sub_eq_zero] using ha
  refine ⟨a, hpow, ?_⟩
  -- The geometric sum `1 + a + ⋯ + a ^ (n - 1)` reduces to `n` modulo `J`, hence is a unit.
  have ha_quot : Ideal.Quotient.mk J a = 1 := by
    rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    exact ha1
  have := isLocalHom_of_le_jacobson_bot J HenselianRing.jac
  have hunit : IsUnit (∑ j ∈ Finset.range n, a ^ j) :=
    isUnit_of_map_unit (Ideal.Quotient.mk J) _
      (by simpa [ha_quot] using hn.map (Ideal.Quotient.mk J))
  obtain ⟨u, hu⟩ := hunit
  have hsub : a - 1 = ↑u⁻¹ * (w - 1) := by
    rw [← hpow, ← geom_sum_mul, ← hu, Units.inv_mul_cancel_left]
  rw [hsub]
  exact I.mul_mem_left _ hw

/-- In a ring Henselian at `J`, an element `c ∈ J` has the form `t² + t` for some `t ∈ J`.
This is the simple-root form of Hensel's lemma that also works in residue characteristic two. -/
theorem exists_sq_add_eq_of_mem {J : Ideal R} [HenselianRing R J] {c : R} (hc : c ∈ J) :
    ∃ t ∈ J, t ^ 2 + t = c := by
  obtain ⟨t, ht, htJ⟩ := HenselianRing.is_henselian (X ^ 2 + X - C c)
    (by
      rw [add_sub_assoc]
      exact monic_X_pow_add (lt_of_le_of_lt (degree_X_sub_C_le c) (by decide)))
    0 (by simpa using J.neg_mem hc) (by simp)
  exact ⟨t, by simpa using htJ, by simpa [sub_eq_zero] using ht⟩

/-- In a ring Henselian at `J`, every element of `1 + 4J` is a square. No invertibility
assumption on `2` in the ring or its residue rings is needed. -/
theorem isSquare_one_add_four_mul_of_mem {J : Ideal R} [HenselianRing R J]
    {c : R} (hc : c ∈ J) : IsSquare (1 + 4 * c) := by
  obtain ⟨t, -, ht⟩ := exists_sq_add_eq_of_mem hc
  refine ⟨1 + 2 * t, ?_⟩
  rw [← ht]
  ring

end HenselianRing

end TauCeti

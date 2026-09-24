/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Henselian

/-!
# Binary forms with unit coefficients over a Henselian local ring

Let `R` be a Henselian local ring whose residue field is finite and in which `2` is a unit. Then
every binary form `a x² + b y²` with unit coefficients represents every unit `c` of `R`.

Over the finite residue field of odd characteristic this is the universality of regular binary
forms. Since `c` is a unit, one of the two coordinates of a residue solution is nonzero; the
other coordinate is lifted arbitrarily, and the nonzero one is lifted by Hensel's lemma, which
applies because the derivative `2x` of `X² - u` is a unit there.

A consequence is that a diagonal quadratic form with at least three unit coefficients is
isotropic: `a x² + b y² = -c` gives the nonzero isotropic vector `(x, y, 1)`. Over the ring of
integers of a nonarchimedean local field of odd residue characteristic, this makes a fixed
regular form over a number field isotropic at almost every finite place.

## Main results

* `TauCeti.exists_mul_sq_add_mul_sq_eq_of_isUnit`: `a x² + b y² = c` is solvable in `R` when
  `a`, `b` and `c` are units.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter I, §2 (quadratic forms over finite fields) and
  Chapter II, §2 (lifting solutions by Hensel's lemma).
-/

public section

open Polynomial IsLocalRing

namespace TauCeti

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- Lift a residue solution of `a x² + b y² = c` whose first coordinate is nonzero. -/
private theorem exists_mul_sq_add_mul_sq_eq_of_residue (h2 : IsUnit (2 : R)) {a b c : R}
    (ha : IsUnit a) {s t : ResidueField R} (hs : s ≠ 0)
    (hst : residue R a * s ^ 2 + residue R b * t ^ 2 = residue R c) :
    ∃ x y : R, a * x ^ 2 + b * y ^ 2 = c := by
  obtain ⟨x₀, rfl⟩ := residue_surjective s
  obtain ⟨y, rfl⟩ := residue_surjective t
  obtain ⟨a', ha'⟩ := ha.exists_right_inv
  -- Hensel's lemma for `X² - u`, with `u = a⁻¹ (c - b y²)`, at the approximate root `x₀`.
  set u := a' * (c - b * y ^ 2) with hu
  have heval : (X ^ 2 - C u).eval x₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, eval_sub, eval_pow, eval_X, eval_C, hu]
    have hres := congrArg (residue R) ha'
    simp only [map_mul, map_one] at hres
    simp only [map_sub, map_pow, map_mul]
    linear_combination residue R a' * hst - residue R x₀ ^ 2 * hres
  have hder : IsUnit ((X ^ 2 - C u).derivative.eval x₀) := by
    have hx₀ : IsUnit x₀ := (residue_ne_zero_iff_isUnit x₀).mp hs
    have h : (X ^ 2 - C u).derivative.eval x₀ = 2 * x₀ := by
      simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
        eval_X, eval_C, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    exact h ▸ h2.mul hx₀
  obtain ⟨x, hx, -⟩ := HenselianLocalRing.is_henselian _ (monic_X_pow_sub_C u two_ne_zero)
    x₀ heval hder
  refine ⟨x, y, ?_⟩
  have hx' : x ^ 2 = u := by
    simpa [sub_eq_zero] using hx
  linear_combination a * hx' + (c - b * y ^ 2) * ha'

/-- **Binary forms with unit coefficients are universal over a Henselian local ring.** If the
residue field of the Henselian local ring `R` is finite and `2` is a unit of `R`, then for units
`a`, `b` and `c` there are `x` and `y` with `a x² + b y² = c`. -/
theorem exists_mul_sq_add_mul_sq_eq_of_isUnit [Finite (ResidueField R)] (h2 : IsUnit (2 : R))
    {a b c : R} (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) :
    ∃ x y : R, a * x ^ 2 + b * y ^ 2 = c := by
  let _ := Fintype.ofFinite (ResidueField R)
  have hunit {r : R} (hr : IsUnit r) : residue R r ≠ 0 := (hr.map (residue R)).ne_zero
  -- The residue field has odd cardinality, since `2` is nonzero in it.
  have hchar : ringChar (ResidueField R) ≠ 2 := fun h ↦ hunit h2 <| by
    rw [map_ofNat]
    exact_mod_cast (ringChar.spec (ResidueField R) 2).mpr (h ▸ dvd_rfl)
  -- Solve the equation over the residue field.
  have hdeg {r : R} (hr : IsUnit r) (d : ResidueField R) :
      degree (C (residue R r) * X ^ 2 + C d) = 2 := by
    rw [degree_add_C (by rw [degree_C_mul_X_pow 2 (hunit hr)]; norm_num),
      degree_C_mul_X_pow 2 (hunit hr)]
    rfl
  obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic (hdeg ha (-residue R c))
    (hdeg hb 0) (FiniteField.odd_card_of_char_ne_two hchar)
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, map_zero, add_zero] at hst
  have hst' : residue R a * s ^ 2 + residue R b * t ^ 2 = residue R c := by
    linear_combination hst
  -- One of the two residue coordinates is nonzero, since `c` is a unit; lift from it.
  by_cases hs : s = 0
  · have ht : t ≠ 0 := by
      rintro rfl
      exact hunit hc (by simpa [hs] using hst'.symm)
    obtain ⟨y, x, h⟩ := exists_mul_sq_add_mul_sq_eq_of_residue (a := b) (b := a) (c := c)
      (t := s) h2 hb ht (by linear_combination hst')
    exact ⟨x, y, by linear_combination h⟩
  · exact exists_mul_sq_add_mul_sq_eq_of_residue h2 ha hs hst'

end TauCeti

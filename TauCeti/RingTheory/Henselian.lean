/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian

/-!
# Roots of elements congruent to one in a Henselian local ring

In a Henselian local ring `R`, let `n` be a natural number that is invertible in `R`. Then every
element `w` congruent to `1` modulo an ideal `I` contained in the maximal ideal has an `n`-th root
that is itself congruent to `1` modulo `I`.

This is the standard source of `n`-th roots of principal units away from the residue
characteristic: over the integer ring of a local field it shows that each positive-depth step of
the unit filtration is carried onto itself by the `n`-th power map.

## Main results

* `TauCeti.HenselianLocalRing.exists_pow_eq_of_sub_one_mem`: if `n` is invertible, `I` lies in
  the maximal ideal and `w ≡ 1 mod I`, then `w = a ^ n` for some `a ≡ 1 mod I`.

## Implementation notes

Hensel's lemma applied to `X ^ n - w` at the approximate root `1` produces a root `a` with
`a ≡ 1` modulo the maximal ideal only. The congruence is then sharpened to `I` through the
factorization `a ^ n - 1 = (1 + a + ⋯ + a ^ (n - 1)) * (a - 1)`, whose first factor reduces to
`n` and is therefore a unit.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti

namespace HenselianLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- In a Henselian local ring, if `n` is invertible then every element congruent to `1` modulo an
ideal `I` contained in the maximal ideal is the `n`-th power of an element congruent to `1`
modulo `I`. -/
theorem exists_pow_eq_of_sub_one_mem {I : Ideal R} (hI : I ≤ maximalIdeal R) {n : ℕ}
    (hn : IsUnit (n : R)) {w : R} (hw : w - 1 ∈ I) :
    ∃ a : R, a ^ n = w ∧ a - 1 ∈ I := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have heval : (X ^ n - C w).eval (1 : R) ∈ maximalIdeal R := by
    simpa using (maximalIdeal R).neg_mem_iff.mpr (hI hw)
  obtain ⟨a, ha, ha1⟩ := HenselianLocalRing.is_henselian (X ^ n - C w)
    (monic_X_pow_sub_C w hn0) 1 heval (by simpa [derivative_X_pow] using hn)
  have hpow : a ^ n = w := by simpa [sub_eq_zero] using ha
  refine ⟨a, hpow, ?_⟩
  -- The geometric sum `1 + a + ⋯ + a ^ (n - 1)` reduces to `n`, hence is a unit.
  have ha_res : residue R a = 1 := by
    rw [← sub_eq_zero, ← map_one (residue R), ← map_sub, residue_eq_zero_iff]
    exact ha1
  have hunit : IsUnit (∑ j ∈ Finset.range n, a ^ j) :=
    isUnit_of_map_unit (residue R) _ (by simpa [ha_res] using hn.map (residue R))
  obtain ⟨u, hu⟩ := hunit
  have hsub : a - 1 = ↑u⁻¹ * (w - 1) := by
    rw [← hpow, ← geom_sum_mul, ← hu, Units.inv_mul_cancel_left]
  rw [hsub]
  exact I.mul_mem_left _ hw

end HenselianLocalRing

end TauCeti

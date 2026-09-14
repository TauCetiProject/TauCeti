/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian

/-!
# Roots of elements congruent to one in a Henselian ring

Let `R` be a ring that is Henselian at an ideal `J`, and let `n` be a natural number that is
invertible in `R`. Then every element `w` congruent to `1` modulo an ideal `I ≤ J` has an `n`-th
root that is itself congruent to `1` modulo `I`.

This is the standard source of `n`-th roots of principal units away from the residue
characteristic: over the integer ring of a local field it shows that each positive-depth step of
the unit filtration is carried onto itself by the `n`-th power map.

## Main results

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

end HenselianRing

end TauCeti

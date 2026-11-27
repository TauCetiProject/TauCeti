/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Powers of monic polynomials over an integrally closed domain

Let `R` be an integrally closed domain with fraction field `K`. If a monic polynomial `p` over `R`
is a `j`-th power `Q ^ j` over `K`, then it is already the `j`-th power of a polynomial over `R`
(`Polynomial.Monic.exists_eq_pow_of_map_eq_pow`). This is Gauss's lemma in the form of Mathlib's
`IsIntegrallyClosed.eq_map_mul_C_of_dvd`: the divisor `Q` of the monic integral polynomial `p` is
integral up to its leading coefficient, and that coefficient is a `j`-th root of unity.

It is used to show that a characteristic polynomial is not a proper power, by reducing a power
decomposition over a field to one over its ring of integers and then modulo the maximal ideal.

The statement and its proof follow `New.exists_eq_pow_of_monic_of_map_eq_pow` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/TraceFormula/TestFunction.lean`.
-/

public section

open Polynomial

namespace Polynomial

variable {R K : Type*} [CommRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **Gauss's lemma for powers.** Over an integrally closed domain `R` with fraction field `K`, a
monic polynomial that is a `j`-th power over `K` is the `j`-th power of a polynomial over `R`. -/
theorem Monic.exists_eq_pow_of_map_eq_pow {p : R[X]} (hp : p.Monic) {Q : K[X]} {j : ℕ}
    (h_map : p.map (algebraMap R K) = Q ^ j) : ∃ P : R[X], p = P ^ j := by
  rcases eq_or_ne j 0 with rfl | hj
  · refine ⟨1, map_injective _ (IsFractionRing.injective R K) ?_⟩
    simpa using h_map
  -- Up to its leading coefficient `Q` is integral, as it divides a monic integral polynomial.
  obtain ⟨P, hP⟩ : ∃ P : R[X], P.map (algebraMap R K) * C Q.leadingCoeff = Q :=
    IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp (h_map ▸ dvd_pow_self Q hj)
  have h_lead : Q.leadingCoeff ^ j = 1 := by
    rw [← leadingCoeff_pow, ← h_map, (hp.map _).leadingCoeff]
  refine ⟨P, map_injective _ (IsFractionRing.injective R K) ?_⟩
  calc p.map (algebraMap R K) = (P.map (algebraMap R K) * C Q.leadingCoeff) ^ j := by
        rw [h_map, hP]
    _ = (P ^ j).map (algebraMap R K) := by
        rw [mul_pow, ← C_pow, h_lead]
        simp

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Basic

/-!
# Spherical Hecke polynomials

For natural numbers `q` and `N` and a sequence of eigenvalues `t : ℕ → R` in a commutative ring
`R`, the spherical Hecke polynomial is
`∑ j ∈ Finset.range (N + 1), C ((-1) ^ j * (q : R) ^ j.choose 2 * t j) * X ^ (N - j)`.

## Main definitions and results

* `TauCeti.heckePoly`: the spherical Hecke polynomial `heckePoly q N t`.
* `TauCeti.coeff_heckePoly`: explicit coefficient formula for `k ≤ N`.
* `TauCeti.coeff_heckePoly_eq_zero`: coefficients vanish for `N < k`.
* `TauCeti.map_heckePoly`: naturality under ring homomorphisms.
* `TauCeti.isMonicOfDegree_heckePoly`: `heckePoly q N t` is monic of degree `N` when `t 0 = 1`.

## Provenance

Adapted from `New.heckePoly` and `New.HasHeckePolyAt.isMonicOfDegree` in
`src/Lib/GaloisRep/Main/Defs.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Finset Polynomial

section HeckePoly

variable {R : Type*} [CommRing R]

/-- For natural numbers `q, N` and a sequence `t : ℕ → R` in a commutative ring `R`, the spherical
Hecke polynomial `∑ j = 0..N, (-1)^j * q^(j.choose 2) * t j * X^(N - j)`. -/
noncomputable def heckePoly (q N : ℕ) (t : ℕ → R) : R[X] :=
  ∑ j ∈ range (N + 1), C ((-1) ^ j * (q : R) ^ j.choose 2 * t j) * X ^ (N - j)

/-- For `k ≤ N`, the `k`-th coefficient of `heckePoly q N t` is
`(-1) ^ (N - k) * q ^ (N - k).choose 2 * t (N - k)`. -/
theorem coeff_heckePoly (q N : ℕ) (t : ℕ → R) {k : ℕ} (hk : k ≤ N) :
    (heckePoly q N t).coeff k =
      (-1) ^ (N - k) * (q : R) ^ (N - k).choose 2 * t (N - k) := by
  rw [heckePoly, ← lcoeff_apply (R := R) k, map_sum, sum_eq_single (N - k)]
  · rw [lcoeff_apply, coeff_C_mul_X_pow, ite_eq_left (by omega)]
  · intro j hj hne
    rw [mem_range] at hj
    rw [lcoeff_apply, coeff_C_mul_X_pow, ite_eq_right (by omega)]
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/-- All coefficients of `heckePoly q N t` above degree `N` vanish. -/
theorem coeff_heckePoly_eq_zero (q N : ℕ) (t : ℕ → R) {k : ℕ} (hk : N < k) :
    (heckePoly q N t).coeff k = 0 := by
  rw [heckePoly, ← lcoeff_apply (R := R) k, map_sum]
  refine sum_eq_zero fun j hj ↦ ?_
  rw [mem_range] at hj
  rw [lcoeff_apply, coeff_C_mul_X_pow, ite_eq_right (by omega)]

/-- Mapping `heckePoly q N t` along a ring homomorphism `f : R →+* S` gives
`heckePoly q N (f ∘ t)`. -/
theorem map_heckePoly {S : Type*} [CommRing S] (f : R →+* S) (q N : ℕ) (t : ℕ → R) :
    (heckePoly q N t).map f = heckePoly q N (f ∘ t) := by
  simp [heckePoly, Polynomial.map_sum]

/-- When `t 0 = 1` over a nontrivial commutative ring, the spherical Hecke polynomial
`heckePoly q N t` is monic of degree `N`. -/
theorem isMonicOfDegree_heckePoly [Nontrivial R] (q N : ℕ) (t : ℕ → R) (ht : t 0 = 1) :
    (heckePoly q N t).IsMonicOfDegree N := by
  have hle : (heckePoly q N t).natDegree ≤ N :=
    natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ coeff_heckePoly_eq_zero q N t hk
  have hN : (heckePoly q N t).coeff N = 1 := by
    simpa [ht] using coeff_heckePoly q N t le_rfl
  have hdeg : (heckePoly q N t).natDegree = N :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hN]; exact one_ne_zero))
  exact ⟨hdeg, by rw [Monic, leadingCoeff, hdeg, hN]⟩

end HeckePoly

end TauCeti

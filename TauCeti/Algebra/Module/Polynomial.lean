/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomial modules

Elementary facts about modules over a polynomial ring `k[X]`.

## Main results

* `LinearMap.map_smul_eq_sum_support_coeff_smul`: a `k`-linear map on a `k[X]`-module
  evaluates on `a • z` as a coefficient-weighted sum of the values on `X ^ n • z`.
* `LinearMap.map_X_pow_smul_smul_eq`: the values of such a functional on `X ^ j • a • t`, when it
  is `1` on `X ^ n • t` and `0` on the other `X ^ l • t`.
* `TauCeti.Polynomial.torsionOf_eq_span_X_pow`: if `X ^ m` kills `t` but `X ^ (m - 1)` does not,
  the annihilator of `t` is `(X ^ m)`.
-/

public section

open Polynomial

section EvaluateLinearMap

variable {k M N : Type*} [CommSemiring k] [AddCommMonoid M] [Module k M] [Module k[X] M]
  [IsScalarTower k k[X] M]

namespace LinearMap

/-- A `k`-linear map on a `k[X]`-module evaluates on `a • z` as the sum of the values on
`X ^ n • z`, weighted by the coefficients of `a`. -/
theorem map_smul_eq_sum_support_coeff_smul [AddCommMonoid N] [Module k N] (φ : M →ₗ[k] N)
    (a : k[X]) (z : M) :
    φ (a • z) = ∑ n ∈ a.support, a.coeff n • φ ((X ^ n : k[X]) • z) := by
  conv_lhs => rw [a.as_sum_support_C_mul_X_pow, Finset.sum_smul]
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [mul_smul, ← algebraMap_eq, algebraMap_smul, map_smul]

/-- If `φ` is `1` on `X ^ n • t` and `0` on the other `X ^ l • t`, then on `X ^ j • a • t` it
reads off the coefficient `a.coeff (n - j)` when `j ≤ n`, and is `0` otherwise. -/
theorem map_X_pow_smul_smul_eq (φ : M →ₗ[k] k) {n : ℕ} {t : M}
    (hφt : ∀ l : ℕ, φ ((X ^ l : k[X]) • t) = if l = n then 1 else 0) (a : k[X]) (j : ℕ) :
    φ ((X ^ j : k[X]) • a • t) = if j ≤ n then a.coeff (n - j) else 0 := by
  rw [smul_comm, map_smul_eq_sum_support_coeff_smul]
  simp_rw [← mul_smul, ← pow_add, hφt, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  split_ifs with hj
  · by_cases hc : a.coeff (n - j) = 0
    · refine (Finset.sum_eq_zero fun i hi ↦ ?_).trans hc.symm
      rw [Finset.mem_filter] at hi
      rwa [show i = n - j by omega]
    · rw [Finset.sum_eq_single_of_mem (n - j)
        (Finset.mem_filter.mpr ⟨mem_support_iff.mpr hc, by omega⟩)]
      intro i hi hne
      rw [Finset.mem_filter] at hi
      omega
  · exact Finset.sum_eq_zero fun i hi ↦ by
      rw [Finset.mem_filter] at hi
      omega

end LinearMap

end EvaluateLinearMap

section AnnihilatorOfMaximalOrder

variable {k M : Type*} [Field k] [AddCommMonoid M] [Module k[X] M]

namespace TauCeti.Polynomial

/-- If `X ^ m` kills `t` but `X ^ (m - 1)` does not, the annihilator of `t` is `(X ^ m)`. -/
theorem torsionOf_eq_span_X_pow {m : ℕ} {t : M} (hm : (X ^ m : k[X]) • t = 0)
    (ht : (X ^ (m - 1) : k[X]) • t ≠ 0) : Ideal.torsionOf k[X] M t = Ideal.span {X ^ m} := by
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.torsionOf k[X] M t)).principal
  have hmem (n : ℕ) : X ^ n ∈ Ideal.torsionOf k[X] M t ↔ g ∣ X ^ n := by
    rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  obtain ⟨i, him, hgi⟩ := (dvd_prime_pow prime_X m).mp
    ((hmem m).mp ((Ideal.mem_torsionOf_iff _ _).mpr hm))
  have him' : i = m := by
    by_contra hne
    refine ht ((Ideal.mem_torsionOf_iff _ _).mp ((hmem (m - 1)).mpr ?_))
    exact hgi.dvd.trans (pow_dvd_pow X (by omega))
  rw [hg, Ideal.submodule_span_eq, Ideal.span_singleton_eq_span_singleton.mpr hgi, him']

end TauCeti.Polynomial

end AnnihilatorOfMaximalOrder

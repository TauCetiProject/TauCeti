/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Membership in a localization realized inside the fraction field

Mathlib's `Localization.subalgebra.ofField K S hS` is the localization of a ring `A` at a
submonoid `S` of non-zero-divisors, realized as the `A`-subalgebra of the fraction field `K` of
`A` consisting of the quotients `a / s` with `a ∈ A` and `s ∈ S`. This file adds the membership
tests that make it usable as a subring of `K`: an element `z : K` lies in it exactly when some
`s ∈ S` clears its denominator, `s * z ∈ A`, and for `S = powers x` exactly when some power of
`x` does so. It also records that the localization of a Dedekind domain, so realized, is again a
Dedekind domain.

## Main results

* `Localization.subalgebra.mem_ofField_iff_exists_mul_mem_range` and
  `Localization.subalgebra.mem_ofField_powers_iff`: membership in `A[S⁻¹] ⊆ K`, respectively in
  `A[1/x] ⊆ K`, by clearing denominators.
* `Localization.subalgebra.isDedekindDomain_ofField`: `A[S⁻¹] ⊆ K` is a Dedekind domain when `A`
  is.
-/

public section

namespace Localization.subalgebra

open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  (S : Submonoid A) (hS : S ≤ A⁰)

/-- **Membership in `A[S⁻¹] ⊆ K` by clearing denominators**: `z` lies in the localization exactly
when some `s ∈ S` has `s * z ∈ A`. -/
theorem mem_ofField_iff_exists_mul_mem_range {z : K} :
    z ∈ ofField K S hS ↔ ∃ s ∈ S, algebraMap A K s * z ∈ (algebraMap A K).range := by
  rw [ofField, Subalgebra.copy_eq, mem_range_mapToFractionRing_iff_ofField, exists_comm]
  refine exists_congr fun s ↦ ?_
  simp only [exists_prop, RingHom.mem_range, exists_and_left]
  refine and_congr_right fun hs ↦ exists_congr fun a ↦ ?_
  rw [eq_mul_inv_iff_mul_eq₀ (map_isUnit_of_le K S hS ⟨s, hs⟩).ne_zero, mul_comm, eq_comm]

/-- **Membership in `A[1/x] ⊆ K`**: `z` lies in the localization of `A` away from `x` exactly when
some power of `x` clears its denominator, `x ^ n * z ∈ A`. -/
theorem mem_ofField_powers_iff (x : A) (hx : Submonoid.powers x ≤ A⁰) {z : K} :
    z ∈ ofField K (Submonoid.powers x) hx ↔
      ∃ n : ℕ, algebraMap A K x ^ n * z ∈ (algebraMap A K).range := by
  simp [mem_ofField_iff_exists_mul_mem_range, Submonoid.mem_powers_iff]

/-- The localization of a Dedekind domain at a submonoid of nonzero elements, realized inside its
fraction field, is a Dedekind domain. -/
instance isDedekindDomain_ofField [IsDedekindDomain A] : IsDedekindDomain (ofField K S hS) :=
  IsLocalization.isDedekindDomain A hS _

end Localization.subalgebra

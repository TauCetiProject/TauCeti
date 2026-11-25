/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Localizations realized inside fraction fields

Mathlib's `Localization.subalgebra.ofField K S hS` is the localization of a ring `A` at a
submonoid `S` of non-zero-divisors, realized as the `A`-subalgebra of the fraction field `K` of
`A` consisting of the quotients `a / s` with `a ∈ A` and `s ∈ S`. This file records that an
element `z : K` lies in it exactly when it is such a quotient, and that the localization of a
Dedekind domain at nonzero denominators, so realized, is again a Dedekind domain.

## Main results

* `Localization.subalgebra.mem_ofField_iff`: membership in `A[S⁻¹] ⊆ K` as a quotient `a / s`.
* `Localization.subalgebra.isDedekindDomain_ofField`: `A[S⁻¹] ⊆ K` is a Dedekind domain when `A`
  is.
-/

public section

namespace Localization.subalgebra

open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  (S : Submonoid A) (hS : S ≤ A⁰)

/-- **Membership in `A[S⁻¹] ⊆ K` as a fraction**: `z` lies in the localization exactly when it is
a quotient `a / s` with `a ∈ A` and `s ∈ S`. -/
theorem mem_ofField_iff {z : K} :
    z ∈ ofField K S hS ↔ ∃ a, ∃ s ∈ S, z = algebraMap A K a * (algebraMap A K s)⁻¹ := by
  rw [ofField, ← SetLike.mem_coe, Subalgebra.coe_copy, Set.mem_ofPred_eq]
  simp only [exists_prop]

/-- The localization of a Dedekind domain at a submonoid of nonzero elements, realized inside its
fraction field, is a Dedekind domain. -/
instance isDedekindDomain_ofField [IsDedekindDomain A] : IsDedekindDomain (ofField K S hS) :=
  IsLocalization.isDedekindDomain A hS _

end Localization.subalgebra

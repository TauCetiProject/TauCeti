/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Dedekind localizations inside fraction fields

Mathlib's `Localization.subalgebra.ofField K S hS` realizes the localization of a ring `A` at a
submonoid `S` of non-zero-divisors inside the fraction field `K` of `A`. This file records that
its elements are exactly the quotients `a / s` with `s ∈ S`, and that the localization of a
Dedekind domain, so realized, is again a Dedekind domain. For the localization at a prime `P`, the
hypothesis `S ≤ A⁰` holds for any ring with a fraction field.

## Main results

* `Ideal.primeCompl_le_nonZeroDivisors_of_isFractionRing`: the complement of a prime ideal of a
  ring with a fraction field consists of non-zero-divisors.
* `Ideal.algebraMap_ne_zero_of_notMem`: an element outside an ideal has nonzero image in the
  fraction field.
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

namespace Ideal

open scoped nonZeroDivisors

variable {A : Type*} {K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- An element outside an ideal has nonzero image in the fraction field, as `0` lies in the
ideal. -/
theorem algebraMap_ne_zero_of_notMem {P : Ideal A} {s : A} (hs : s ∉ P) : algebraMap A K s ≠ 0 :=
  fun h ↦ hs (IsFractionRing.to_map_eq_zero_iff.mp h ▸ P.zero_mem)

variable (K) (P : Ideal A) [P.IsPrime]

include K in
/-- The complement of a prime ideal of a ring with a fraction field consists of
non-zero-divisors. This is the hypothesis under which Mathlib realizes the localization at `P`
inside the fraction field (`Localization.subalgebra.ofField`). -/
theorem primeCompl_le_nonZeroDivisors_of_isFractionRing : P.primeCompl ≤ A⁰ :=
  have : IsDomain A := (IsFractionRing.isDomain_iff_isField (K := K)).mpr (Field.toIsField K)
  P.primeCompl_le_nonZeroDivisors

end Ideal

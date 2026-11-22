/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import TauCeti.RingTheory.Localization.DenIdeal
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Membership in embedded localizations

A subalgebra that localizes a commutative semiring consists of the ambient elements whose
denominator ideal meets the denominator monoid. This characterizes membership for arbitrary
ambient commutative semirings, without a field or total-quotient-ring hypothesis.
It applies to `Localization.subalgebra` and its fraction-field model `ofField`.

The localization of a Dedekind domain inside its fraction field is again Dedekind.
-/

public section

namespace TauCeti.Localization.subalgebra

variable {R K : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]

/-- An element belongs to an embedded localization precisely when its denominator ideal
`Algebra.denIdeal K x` meets the denominator monoid. -/
theorem mem_iff_exists_mem_denIdeal (S : Submonoid R) (A : Subalgebra R K)
    [IsLocalization S A] (x : K) :
    x ∈ A ↔ ∃ s ∈ S, s ∈ Algebra.denIdeal K x := by
  constructor
  · intro hx
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj S (⟨x, hx⟩ : A)
    have h := congrArg (fun y : A ↦ (y : K)) he
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at h
    exact ⟨s, s.property, (Algebra.mem_denIdeal_iff K).mpr
      ⟨r, by simpa only [mul_comm] using h⟩⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨r, hr⟩ := (Algebra.mem_denIdeal_iff K).mp hx
    obtain ⟨v, hv⟩ := IsLocalization.map_units A (⟨s, hs⟩ : S)
    have hvK : ((v : A) : K) = algebraMap R K s := by
      simpa only [Subalgebra.coe_algebraMap] using
        congrArg (fun y : A ↦ (y : K)) hv
    have he : x = (((v⁻¹ : Aˣ) : A) : K) * algebraMap R K r := by
      rw [← hr, ← hvK, ← mul_assoc, ← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one,
        one_mul]
    rw [he]
    exact A.mul_mem (v⁻¹).val.property (A.algebraMap_mem r)

end TauCeti.Localization.subalgebra

namespace Localization.subalgebra

open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  (S : Submonoid A) (hS : S ≤ A⁰)

/-- The localization of a Dedekind domain at a submonoid of nonzero elements, realized inside its
fraction field, is a Dedekind domain. -/
instance isDedekindDomain_ofField [IsDedekindDomain A] : IsDedekindDomain (ofField K S hS) :=
  IsLocalization.isDedekindDomain A hS _

end Localization.subalgebra

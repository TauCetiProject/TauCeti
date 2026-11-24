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

namespace TauCeti.IsLocalization

variable {R K : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]

/-- An element belongs to an embedded localization precisely when its denominator ideal
`Algebra.denIdeal K x` meets the denominator monoid. -/
theorem mem_subalgebra_iff_exists_mem_denIdeal (S : Submonoid R) (A : Subalgebra R K)
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
    let u : Kˣ := Units.map (A.val : A →* K) v
    have hu : (u : K) = algebraMap R K s := by
      simpa only [u, Units.coe_map, AlgHom.coe_toMonoidHom, Subalgebra.val_apply] using hvK
    have he : x = (↑u⁻¹ : K) * algebraMap R K r := by
      rw [← hr, ← hu]
      exact (Units.inv_mul_cancel_left u x).symm
    rw [he]
    exact A.mul_mem (by
      simpa only [u, Units.coe_map_inv, AlgHom.coe_toMonoidHom, Subalgebra.val_apply] using
        (v⁻¹).val.property) (A.algebraMap_mem r)

/-- In a principal embedded localization, membership means that some power of the
localizing element clears the denominator into the coefficient image. -/
theorem mem_subalgebra_iff_exists_pow_mul_mem_range (a : R) (A : Subalgebra R K)
    [IsLocalization (Submonoid.powers a) A] (x : K) :
    x ∈ A ↔ ∃ n : ℕ, algebraMap R K a ^ n * x ∈ Set.range (algebraMap R K) := by
  rw [mem_subalgebra_iff_exists_mem_denIdeal (Submonoid.powers a) A x]
  simp only [Submonoid.mem_powers_iff, exists_exists_eq_and]
  simp only [Algebra.mem_denIdeal_iff, map_pow, Set.mem_range, eq_comm]

end TauCeti.IsLocalization

namespace Localization.subalgebra

open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  (S : Submonoid A) (hS : S ≤ A⁰)

/-- The localization of a Dedekind domain at a submonoid of nonzero elements, realized inside its
fraction field, is a Dedekind domain. -/
instance isDedekindDomain_ofField [IsDedekindDomain A] : IsDedekindDomain (ofField K S hS) :=
  IsLocalization.isDedekindDomain A hS _

end Localization.subalgebra

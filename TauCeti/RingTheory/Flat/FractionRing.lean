/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TauCeti.Algebra.Module.LocalizedModule.Basic

/-!
# Flatness of localizations at nonzerodivisors

An `IsFractionRing R K` algebra is a localization of the commutative semiring `R` at its
nonzerodivisors. Mathlib's `IsLocalization.flat` proves that every localization is flat over
its base, but its submonoid parameter prevents using it as a general instance. For
`IsFractionRing R K`, the inverted submonoid is determined by `R`, so this specialization
makes the flatness of `K` over `R` available to instance search.

This applies to `ℚ≥0` over `ℕ`, fraction fields, and total quotient rings of rings with zero
divisors. In particular, `ℚ_p` is flat over `ℤ_p`, which makes base change to `ℚ_p` preserve
injectivity.

If every nonzero scalar acts bijectively on a module, the module is flat. For a nontrivial
module the scalar action forces the base ring to be a domain; the action extends to its fraction
field, where flatness follows from freeness of vector spaces.

## Main results

* `Module.Flat.of_bijective_smul`: a module on which every nonzero scalar acts bijectively is flat.
* `IsFractionRing.flat`: a localization of `R` at its nonzerodivisors is a flat `R`-module.
-/

public section

/-- A localization at the nonzerodivisors of a commutative semiring is flat over that semiring. -/
instance IsFractionRing.flat (R K : Type*) [CommSemiring R] [CommSemiring K] [Algebra R K]
    [IsFractionRing R K] : Module.Flat R K :=
  IsLocalization.flat K (nonZeroDivisors R)

namespace Module.Flat

/-- A module is flat if every nonzero scalar acts bijectively. -/
theorem of_bijective_smul {R M : Type*} [CommRing R]
  [AddCommMonoid M] [Module R M]
    (h : ∀ r : R, r ≠ 0 → Function.Bijective (fun x
      : M ↦ r • x)) : Flat R M := by
  let := Module.addCommMonoidToAddCommGroup R (M := M)
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Module.Free R M := Module.Free.of_subsingleton R M
    infer_instance
  · have : Nontrivial R := Module.nontrivial R M
    have : NoZeroDivisors R := ⟨fun {a b} hab ↦ by
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      by_contra hb
      obtain ⟨m, hm⟩ := exists_ne (0 : M)
      apply hm
      apply (h b hb).injective
      apply (h a ha).injective
      simp only [← mul_smul, hab, zero_smul, smul_zero]⟩
    have : IsDomain R := NoZeroDivisors.to_isDomain R
    let S := nonZeroDivisors R
    have : IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) :=
      TauCeti.isLocalizedModule_id_of_bijective_smul (S := S)
        (fun s hs ↦ h s (nonZeroDivisors.ne_zero hs))
    have : Flat R (LocalizedModule S M) :=
      (Module.flat_iff_of_isLocalization (FractionRing R) S _).mp inferInstance
    exact Flat.of_linearEquiv (IsLocalizedModule.iso S (LinearMap.id : M
      →ₗ[R] M)).symm

end Module.Flat

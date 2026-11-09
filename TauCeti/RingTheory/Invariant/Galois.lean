/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral elements fixed by a Galois group

Let `R` be integrally closed in a field `K` and let `L / K` be a Galois extension, possibly
infinite. An element of `L` lies in the image of `R` exactly when it is integral over `R` and
fixed by every `K`-automorphism of `L`. This combines the fixed-field theorem for infinite Galois
extensions with the integral closedness of `R` in `K`. For instance, an algebraic integer in an
algebraic closure of `ℚ` fixed by the absolute Galois group is a rational integer.

Mathlib's `Algebra.isInvariant_of_isGalois` records the analogous fact for a finite Galois
extension of the fraction field of an integrally closed domain, phrased through the integral
closure of that domain in `L`.

## Main result

* `TauCeti.InfiniteGalois.mem_range_algebraMap_iff_isIntegral_and_fixed`: an element of a Galois
  extension `L / K` comes from `R` if and only if it is integral over `R` and fixed by `Gal(L/K)`.
-/

public section

namespace TauCeti.InfiniteGalois

variable {R K L : Type*} [CommRing R] [Field K] [Field L] [Algebra R K] [Algebra K L]
  [Algebra R L] [IsScalarTower R K L] [IsIntegrallyClosedIn R K] [IsGalois K L]

variable (K) in
/-- For `R` integrally closed in `K` and a Galois extension `L / K`, an element of `L` comes from
`R` if and only if it is integral over `R` and fixed by every `K`-automorphism of `L`. -/
theorem mem_range_algebraMap_iff_isIntegral_and_fixed (x : L) :
    x ∈ Set.range (algebraMap R L) ↔ IsIntegral R x ∧ ∀ τ : Gal(L/K), τ x = x := by
  refine ⟨?_, fun ⟨hx, hfix⟩ ↦ ?_⟩
  · rintro ⟨r, rfl⟩
    refine ⟨isIntegral_algebraMap, fun τ ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply R K L, τ.commutes]
  obtain ⟨q, rfl⟩ := (_root_.InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
  obtain ⟨r, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (isIntegral_algHom_iff ((Algebra.ofId K L).restrictScalars R)
      (algebraMap K L).injective).mp hx
  exact ⟨r, IsScalarTower.algebraMap_apply R K L r⟩

end TauCeti.InfiniteGalois

end

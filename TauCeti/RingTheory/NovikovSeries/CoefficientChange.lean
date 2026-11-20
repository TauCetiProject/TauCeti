/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import TauCeti.RingTheory.Localization.Defs
public import TauCeti.RingTheory.NovikovSeries.TotalQuotient
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import TauCeti.RingTheory.KrullDimension.Zero
import TauCeti.RingTheory.Norm.NonZeroDivisors

/-!
# Changing the coefficients of Novikov series

Let `H` be a finitely generated abelian group, possibly with torsion, `N : H →+ ℝ` a period
homomorphism and `ρ : R →+* S` an injective ring homomorphism into a domain, such as the inclusion
`ℤ →+* ℚ`. Applying `ρ` to every coefficient is the ring homomorphism
`P_ρ = mapRingHom ρ (AddMonoidHom.id H) _ : Nov(R, H, N) →+* Nov(S, H, N)`. This file shows that
`P_ρ` preserves and reflects non-zero-divisors
(`TauCeti.NovikovSeries.mapRingHom_mem_nonZeroDivisors_iff`), so it induces an injective map from
the total ring of fractions of `Nov(R, H, N)` to that of `Nov(S, H, N)`
(`TauCeti.NovikovSeries.map_mapRingHom_injective`). Torsion of a based complex over the integral
Novikov ring, which lives in its total ring of fractions, can therefore be compared with torsion
over the rational Novikov ring. The rational Novikov ring is not the tensor product
`ℚ ⊗ Nov(ℤ, H, N)`: a rational series may have unbounded denominators. So the comparison has to
go through `P_ρ` itself.

Since `H` may have torsion, neither Novikov ring need be a domain, and preservation of
non-zero-divisors is not automatic. The proof passes to a torsion-free subgroup `K ≤ H` of finite
index, for which `Nov(S, K, N|K)` is a domain. Then `Nov(R, H, N)` is free over `Nov(R, K, N|K)` in
the basis of coset monomials (`TauCeti.NovikovSeries.cosetBasis`), and a series is a
non-zero-divisor exactly when its norm over `Nov(R, K, N|K)` is a non-zero-divisor
(`Algebra.norm_mem_nonZeroDivisors_iff`). Changing coefficients commutes with taking coordinates
in this basis, hence with the matrices of multiplication, the norm and the trace
(`TauCeti.NovikovSeries.norm_mapRingHom`, `TauCeti.NovikovSeries.trace_mapRingHom`). The norm of
a non-zero-divisor is nonzero, it stays nonzero under the injective map `P_ρ` on `K`, and a
nonzero element of the domain `Nov(S, K, N|K)` is a non-zero-divisor.

The total rings of fractions are Artinian
(`TauCeti.NovikovSeries.isArtinianRing_of_isFractionRing`). Under the injective map between them,
every prime ideal of the source is the preimage of a prime ideal of the target
(`TauCeti.NovikovSeries.comap_map_mapRingHom_surjective`), and an element is a unit exactly when its
image is (`TauCeti.NovikovSeries.isUnit_map_mapRingHom_iff`). When both rings are reduced, so that
they are finite products of fields, this says that each field component of the integral total ring
of fractions embeds into a field component of the rational one. In that case the naturality
`HomologicalComplex.map_componentwiseReidemeisterTorsion` shows that the induced map sends the
componentwise torsion of a based complex over `Nov(R, H, N)` to its componentwise torsion along
`Nov(R, H, N) → Nov(S, H, N) → Q(Nov(S, H, N))`, which is the componentwise torsion of any based
complex over `Nov(S, H, N)` whose differentials have the images under `P_ρ` of its matrices
(`HomologicalComplex.componentwiseReidemeisterTorsion_eq_of_toMatrix_eq`). So the integral torsion
is a unit, or zero, exactly when the rational one is.

## Main results

* `TauCeti.NovikovSeries.mapRingHom_mem_nonZeroDivisors_iff`: changing coefficients along an
  injective map into a domain preserves and reflects non-zero-divisors.
* `TauCeti.NovikovSeries.map_mapRingHom_injective`: the induced map of total rings of fractions is
  injective.
* `TauCeti.NovikovSeries.comap_map_mapRingHom_surjective`: every prime ideal of the source total
  ring of fractions is the preimage of one of the target.
* `TauCeti.NovikovSeries.isUnit_map_mapRingHom_iff`: the induced map of total rings of fractions
  reflects units.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2 and Appendix A.
* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
-/

public section

noncomputable section

open scoped nonZeroDivisors

namespace TauCeti

namespace NovikovSeries

variable {R S H : Type*} [AddCommGroup H] {N : H →+ ℝ} [CommRing R] [CommRing S]

section NonZeroDivisors

variable [IsDomain S] [AddGroup.FG H] {ρ : R →+* S}

/-- **Changing coefficients preserves and reflects non-zero-divisors.** For a finitely generated
abelian group `H` and an injective ring homomorphism `ρ` into a domain, a Novikov series is a
non-zero-divisor exactly when the series obtained by applying `ρ` to its coefficients is one. -/
theorem mapRingHom_mem_nonZeroDivisors_iff (hρ : Function.Injective ρ)
    {a : NovikovSeries R H N} :
    mapRingHom ρ (AddMonoidHom.id H) exists_period_rescale_id a ∈ (NovikovSeries S H N)⁰ ↔
      a ∈ (NovikovSeries R H N)⁰ := by
  refine ⟨mem_nonZeroDivisors_of_injective (mapRingHom_injective _ _ _ hρ Function.injective_id),
    fun ha ↦ ?_⟩
  have := ρ.domain_nontrivial
  obtain ⟨K, _, _⟩ := exists_finiteIndex_isDomain (R := S) N
  -- The norm over `Nov(R, K, N|K)` of a non-zero-divisor is a non-zero-divisor, hence nonzero, and
  -- it stays nonzero in the domain `Nov(S, K, N|K)`.
  rw [← Algebra.norm_mem_nonZeroDivisors_iff (R := NovikovSeries S K (N.comp K.subtype)),
    norm_mapRingHom]
  exact mem_nonZeroDivisors_of_ne_zero <| map_ne_zero_of_mem_nonZeroDivisors _
    (mapRingHom_injective _ _ _ hρ Function.injective_id)
    (Algebra.norm_mem_nonZeroDivisors_iff.2 ha)

/-- Changing coefficients along an injective ring homomorphism into a domain maps
non-zero-divisors to non-zero-divisors. -/
theorem nonZeroDivisors_le_comap_mapRingHom (hρ : Function.Injective ρ) :
    (NovikovSeries R H N)⁰ ≤
      (NovikovSeries S H N)⁰.comap (mapRingHom ρ (AddMonoidHom.id H) exists_period_rescale_id) :=
  fun _ ha ↦ (mapRingHom_mem_nonZeroDivisors_iff hρ).2 ha

section TotalQuotient

variable (Q Q' : Type*) [CommRing Q] [CommRing Q'] [Algebra (NovikovSeries R H N) Q]
  [IsFractionRing (NovikovSeries R H N) Q] [Algebra (NovikovSeries S H N) Q']
  [IsFractionRing (NovikovSeries S H N) Q'] (hρ : Function.Injective ρ)

/-- Changing coefficients along an injective ring homomorphism into a domain induces an injective
map from the total ring of fractions of `Nov(R, H, N)` to that of `Nov(S, H, N)`. -/
theorem map_mapRingHom_injective :
    Function.Injective (IsLocalization.map Q'
      (mapRingHom (N := N) (N' := N) ρ (AddMonoidHom.id H) exists_period_rescale_id)
      (nonZeroDivisors_le_comap_mapRingHom hρ) : Q →+* Q') :=
  IsLocalization.map_injective_of_injective_of_le_nonZeroDivisors Q Q'
    (mapRingHom_injective _ _ _ hρ Function.injective_id) _ le_rfl

/-- **Component compatibility.** Every prime ideal of the total ring of fractions of `Nov(R, H, N)`
is the preimage of a prime ideal of the total ring of fractions of `Nov(S, H, N)` under the map
induced by changing coefficients. -/
theorem comap_map_mapRingHom_surjective :
    Function.Surjective (PrimeSpectrum.comap (IsLocalization.map Q'
      (mapRingHom (N := N) (N' := N) ρ (AddMonoidHom.id H) exists_period_rescale_id)
      (nonZeroDivisors_le_comap_mapRingHom hρ) : Q →+* Q')) := by
  have : IsDomain R := Function.Injective.isDomain ρ hρ
  have := isArtinianRing_of_isFractionRing R N Q
  exact PrimeSpectrum.comap_surjective_of_injective_of_krullDimLE_zero
    (map_mapRingHom_injective Q Q' hρ)

/-- An element of the total ring of fractions of `Nov(R, H, N)` is a unit exactly when its image
in the total ring of fractions of `Nov(S, H, N)` is a unit. -/
theorem isUnit_map_mapRingHom_iff {x : Q} :
    IsUnit (IsLocalization.map Q'
      (mapRingHom (N := N) (N' := N) ρ (AddMonoidHom.id H) exists_period_rescale_id)
      (nonZeroDivisors_le_comap_mapRingHom hρ) x : Q') ↔ IsUnit x := by
  have : IsDomain R := Function.Injective.isDomain ρ hρ
  have := isArtinianRing_of_isFractionRing R N Q
  exact isUnit_map_iff_of_injective_of_krullDimLE_zero (map_mapRingHom_injective Q Q' hρ)

end TotalQuotient

end NonZeroDivisors

end NovikovSeries

end TauCeti

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
import TauCeti.Algebra.MonoidAlgebra.Localization
import TauCeti.RingTheory.KrullDimension.Zero
import TauCeti.RingTheory.Norm.NonZeroDivisors
import TauCeti.RingTheory.NovikovSeries.MinimalPrimes

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
is a unit, or zero, exactly when the rational one is. Component by component, the integral torsion
lies in the preimage of a prime of the rational total ring of fractions exactly when the rational
torsion lies in that prime, by `HomologicalComplex.map_componentwiseReidemeisterTorsion` (or
`HomologicalComplex.map_componentwiseParityTorsion` for two-periodic complexes) together with
`IsLocalization.map_comp` and `Ideal.mem_comap`.

When `S` is moreover Noetherian and a localization of `R`, as `ℚ` is of `ℤ`, the components
correspond one to one: two primes of the rational total ring of fractions with the same preimage are
equal (`TauCeti.NovikovSeries.comap_map_mapRingHom_injective_of_isLocalization`), so the preimage
is a bijection between the primes of the two total rings of fractions
(`TauCeti.NovikovSeries.comap_map_mapRingHom_bijective_of_isLocalization`). The primes of each
contract to minimal primes of its Novikov ring, and these are determined by their intersection with
the group ring of the torsion subgroup `T` of `H`
(`TauCeti.NovikovSeries.primeSpectrum_ext_of_comap_torsion_eq`). Two primes of `S[T]` with the same
preimage in `R[T]` are equal, since every element of `S[T]` lands in the image of `R[T]` after
multiplication by a denominator from `R`, which is a unit of `S`. So, for reduced total rings of
fractions, the zero components of the integral torsion are exactly those of the rational torsion,
read through this bijection.

The localization hypothesis cannot be dropped. For `H = ℤ/4`, `N = 0` and the inclusion
`ℤ →+* ℤ[i]`, the integral total ring of fractions is `ℚ[ℤ/4] ≅ ℚ × ℚ × ℚ(i)`, with
three components, and the one over `ℤ[i]` is `ℚ(i)[ℤ/4] ≅ ℚ(i)⁴`, with four: the two
characters of order `4` are conjugate over `ℚ` and give the single component `ℚ(i)`.

## Main results

* `TauCeti.NovikovSeries.mapRingHom_mem_nonZeroDivisors_iff`: changing coefficients along an
  injective map into a domain preserves and reflects non-zero-divisors.
* `TauCeti.NovikovSeries.map_mapRingHom_injective`: the induced map of total rings of fractions is
  injective.
* `TauCeti.NovikovSeries.comap_map_mapRingHom_surjective`: every prime ideal of the source total
  ring of fractions is the preimage of one of the target.
* `TauCeti.NovikovSeries.isUnit_map_mapRingHom_iff`: the induced map of total rings of fractions
  reflects units.
* `TauCeti.NovikovSeries.comap_map_mapRingHom_bijective_of_isLocalization`: when `S` is a
  localization of `R`, such as `ℚ` of `ℤ`, the field components of the two total rings of fractions
  correspond one to one.

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

/-! ### Localizations: the field components correspond one to one -/

section Localization

open scoped AlgebraMonoidAlgebra

variable [IsNoetherianRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  (hS : Function.Injective (algebraMap R S))
  (Q Q' : Type*) [CommRing Q] [CommRing Q'] [Algebra (NovikovSeries R H N) Q]
  [IsFractionRing (NovikovSeries R H N) Q] [Algebra (NovikovSeries S H N) Q']
  [IsFractionRing (NovikovSeries S H N) Q']

include M in
/-- **Distinct components stay distinct.** If a Noetherian domain `S` is a localization of `R`
with injective localization map, as `ℚ` is of `ℤ`, two primes of the total ring of fractions of
`Nov(S, H, N)` with the same preimage in that of `Nov(R, H, N)` are equal. -/
theorem comap_map_mapRingHom_injective_of_isLocalization :
    Function.Injective (PrimeSpectrum.comap (IsLocalization.map Q'
      (mapRingHom (N := N) (N' := N) (algebraMap R S) (AddMonoidHom.id H) exists_period_rescale_id)
      (nonZeroDivisors_le_comap_mapRingHom hS) : Q →+* Q')) := by
  have := isArtinianRing_of_isFractionRing S N Q'
  -- Both primes contract to minimal primes of `Nov(S, H, N)`, which are determined by their
  -- traces on the group ring `S[T]` of the torsion `T` of `H`; these traces are determined by
  -- their preimages in `R[T]`, which are read off the preimages of the primes in `Q`.
  intro m₁ m₂ h
  let P := mapRingHom (N := N) (N' := N) (algebraMap R S) (AddMonoidHom.id H)
    exists_period_rescale_id
  -- The inclusions of the group rings of the torsion commute with the change of coefficients.
  let ιR : AddMonoidAlgebra R (AddCommGroup.torsion H) →+* NovikovSeries R H N :=
    ofAddMonoidAlgebra.comp (AddMonoidAlgebra.mapDomainRingHom R (AddCommGroup.torsion H).subtype)
  let ιS : AddMonoidAlgebra S (AddCommGroup.torsion H) →+* NovikovSeries S H N :=
    ofAddMonoidAlgebra.comp (AddMonoidAlgebra.mapDomainRingHom S (AddCommGroup.torsion H).subtype)
  have hι : P.comp ιR = ιS.comp (algebraMap _ (AddMonoidAlgebra S (AddCommGroup.torsion H))) := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun t => ?_ <;>
      simp [P, ιR, ιS, ofAddMonoidAlgebra_single, mapRingHom_apply, map_single]
  -- So the preimage in `R[T]` of the trace of a prime on `S[T]` is read off its preimage in `Q`.
  have hcomap (m : PrimeSpectrum Q') :
      ((m.asIdeal.comap (algebraMap _ Q')).comap ιS).comap
          (algebraMap _ (AddMonoidAlgebra S (AddCommGroup.torsion H))) =
        ((PrimeSpectrum.comap (IsLocalization.map Q' P
          (nonZeroDivisors_le_comap_mapRingHom hS) : Q →+* Q')
            m).asIdeal.comap (algebraMap _ Q)).comap ιR := by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, Ideal.comap_comap, Ideal.comap_comap,
      Ideal.comap_comap]
    congr 1
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, IsLocalization.map_eq]
    rw [← RingHom.comp_apply P ιR, hι]
    -- Both sides are `algebraMap _ Q' (ιS (algebraMap _ _ x))`; `simp only` unfolded `ιS` on the
    -- left only.
    rfl
  -- Localizing the coefficients localizes the group ring `R[T]`, whose ideals then determine
  -- those of `S[T]`.
  have := AddMonoidAlgebra.isLocalization_coefficients R (M := AddCommGroup.torsion H) (S := S) M
  let p (m : PrimeSpectrum Q') := (m.asIdeal.comap (algebraMap _ Q')).comap ιS
  have hp : (p m₁).comap (algebraMap (AddMonoidAlgebra R (AddCommGroup.torsion H)) _) =
      (p m₂).comap (algebraMap (AddMonoidAlgebra R (AddCommGroup.torsion H)) _) := by
    rw [hcomap, hcomap, h]
  exact primeSpectrum_ext_of_comap_torsion_eq <|
    (IsLocalization.orderEmbedding (Algebra.algebraMapSubmonoid _ M)
      (AddMonoidAlgebra S (AddCommGroup.torsion H))).injective hp

include M in
/-- **Component compatibility.** If a Noetherian domain `S` is a localization of `R` with injective
localization map, as `ℚ` is of `ℤ`, the preimage under the map induced by changing coefficients
is a bijection from the primes of the total ring of fractions of `Nov(S, H, N)` to those of
`Nov(R, H, N)`. When both are reduced, these primes index their field components. -/
theorem comap_map_mapRingHom_bijective_of_isLocalization :
    Function.Bijective (PrimeSpectrum.comap (IsLocalization.map Q'
      (mapRingHom (N := N) (N' := N) (algebraMap R S) (AddMonoidHom.id H) exists_period_rescale_id)
      (nonZeroDivisors_le_comap_mapRingHom hS) : Q →+* Q')) :=
  ⟨comap_map_mapRingHom_injective_of_isLocalization M hS Q Q',
    comap_map_mapRingHom_surjective Q Q' hS⟩

end Localization

end NonZeroDivisors

end NovikovSeries

end TauCeti

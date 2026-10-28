/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.LocalRing.Etale
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Flat
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Étale extensions of a discrete valuation ring with prescribed residue field

Let `R` be a discrete valuation ring with uniformizer `π` and residue field `k`. A flat local
homomorphism `R → S` to a Noetherian local domain under which `π` generates the maximal ideal of
`S` makes `S` a discrete valuation ring with uniformizer `π`. This applies to finite étale local
extensions of `R`, which therefore realise every finite separable extension `l / k` as the residue
field extension of a finite étale extension of discrete valuation rings `R → R'` in which `π`
remains a uniformizer.

Such extensions are the base changes in étale-local statements over a discrete valuation ring:
they enlarge the residue field, for instance to make a closed point of the special fibre of a
scheme over `R` rational, without ramifying `R`, so that orders of vanishing measured by `π` are
unchanged.

## Main results

* `TauCeti.IsDiscreteValuationRing.of_flat_of_map_maximalIdeal_eq`: a Noetherian local domain,
  flat over a discrete valuation ring whose maximal ideal generates its own, is a discrete
  valuation ring.
* `TauCeti.IsDiscreteValuationRing.irreducible_algebraMap_of_map_maximalIdeal_eq`: a uniformizer
  of `R` remains a uniformizer in such an extension.
* `TauCeti.IsDiscreteValuationRing.exists_etale_residueField_algEquiv`: every finite separable
  extension of the residue field is the residue field of a finite étale extension of discrete
  valuation rings in which every uniformizer of `R` remains a uniformizer.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5: unramified extensions with a
  prescribed residue extension, obtained by lifting the minimal polynomial of a primitive element.
-/

public section

open IsLocalRing

universe u

namespace TauCeti.IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S]

/-- **A flat unramified local extension of a discrete valuation ring is a discrete valuation
ring.** If `S` is a Noetherian local domain, flat over the discrete valuation ring `R`, and the
maximal ideal of `R` generates the maximal ideal of `S`, then `S` is a discrete valuation ring.
That `S` is a domain is automatic, by `TauCeti.IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq`
and `TauCeti.IsRegularLocalRing.isDomain`. -/
theorem of_flat_of_map_maximalIdeal_eq [IsLocalRing S] [IsNoetherianRing S] [IsDomain S]
    [Module.Flat R S] (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    IsDiscreteValuationRing S := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hS : maximalIdeal S = Ideal.span {algebraMap R S π} := by
    rw [← h, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  -- `π` is a nonzerodivisor of `R`, so multiplication by it is injective on the flat module `S`.
  have hπS : algebraMap R S π ≠ 0 := fun h0 ↦ by
    have hreg : IsSMulRegular S π :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
    exact one_ne_zero (hreg (by simp [Algebra.smul_def, h0] : π • (1 : S) = π • 0))
  have hfield : ¬IsField S := fun hS' ↦ hπS <| by
    have : maximalIdeal S = ⊥ := (isField_iff_maximalIdeal_eq.mp hS')
    rw [hS, Ideal.span_singleton_eq_bot] at this
    exact this
  have hprin : (maximalIdeal S).IsPrincipal := ⟨⟨_, hS⟩⟩
  exact ((IsDiscreteValuationRing.TFAE S hfield).out 1 5).mpr hprin

/-- **A uniformizer remains a uniformizer in an unramified extension.** If `R → S` is a
homomorphism of discrete valuation rings under which the maximal ideal of `R` generates the
maximal ideal of `S`, then every uniformizer of `R` maps to a uniformizer of `S`. -/
theorem irreducible_algebraMap_of_map_maximalIdeal_eq [IsDomain S] [IsDiscreteValuationRing S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R S π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← h, hπ.maximalIdeal_eq,
    Ideal.map_span, Set.image_singleton]

/-- **Every finite separable extension of the residue field of a discrete valuation ring lifts to
an étale extension of discrete valuation rings.** For a discrete valuation ring `R` with residue
field `k` and a finite separable field extension `L / k`, there is a discrete valuation ring `R'`
which is a finite étale `R`-algebra, with `R → R'` a local homomorphism, whose residue field is
isomorphic to `L` as a `k`-algebra, and in which every uniformizer of `R` remains a uniformizer.
One may take `R' = R[X] ⧸ (g)` for a monic lift `g` of the minimal polynomial of a primitive
element of `L / k`. -/
theorem exists_etale_residueField_algEquiv (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (L : Type*) [Field L] [Algebra (ResidueField R) L]
    [FiniteDimensional (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')),
      Module.Finite R R' ∧ Algebra.Etale R R' ∧
        (∀ π : R, Irreducible π → Irreducible (algebraMap R R' π)) ∧
        Nonempty (ResidueField R' ≃ₐ[ResidueField R] L) := by
  obtain ⟨R', _, _, _, _, hfin, hetale, he⟩ := IsLocalRing.exists_etale_residueField_algEquiv R L
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have h := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := R')
  have : _root_.IsRegularLocalRing R' := IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq h
  have : IsDiscreteValuationRing R' := of_flat_of_map_maximalIdeal_eq h
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfin,
    hetale, fun _ hπ ↦ irreducible_algebraMap_of_map_maximalIdeal_eq h hπ, he⟩

end TauCeti.IsDiscreteValuationRing

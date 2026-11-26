/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import TauCeti.RingTheory.Support.Basic
import TauCeti.RingTheory.Flat.LocalCriterion
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.RingTheory.Spectrum.Prime.GenericFreeness
import TauCeti.RingTheory.Localization.Module.TensorProduct
import TauCeti.RingTheory.Spectrum.Prime.Noetherian

/-!
# Openness of the flat locus

Let `R` be Noetherian, `S` a finite-type `R`-algebra, and `M` a finite `S`-module. The set of primes
`q` of `S` for which `M_q` is flat over `R` is open. In particular, flatness at one prime holds
throughout some principal neighbourhood.

The proof combines generic freeness on each fibre with the local criterion for flatness.
Generic freeness kills tensor kernels by powers of one base element; uniform annihilation
of the finite remaining kernel gives a principal neighbourhood. Generalization stability then turns
these relative neighbourhoods into open subsets of `Spec S`.

## References

* The Stacks Project, Tag 00RC, openness of flatness, in the Noetherian case.
* Matsumura, *Commutative Ring Theory*, Theorems 24.2 and 24.3.
-/

public section

open TensorProduct LinearMap Topology

namespace Module

universe u v w

variable {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

private theorem exists_notMem_kill_tensor_kernel [IsNoetherianRing R]
    [Algebra.FiniteType R S] [Module.Finite S M] (q : Ideal S) [q.IsPrime]
    (hq : Module.Flat R (LocalizedModule q.primeCompl M)) :
    let p := q.comap (algebraMap R S)
    ∃ c ∉ q, ∀ t ∈ LinearMap.ker (AlgebraTensorModule.lTensor S M p.subtype), c • t = 0 := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let p := q.comap (algebraMap R S)
  let K := LinearMap.ker (AlgebraTensorModule.lTensor S M p.subtype)
  have : Module.Finite R p := inferInstance
  have : Module.Finite S (M ⊗[R] p) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange R S S M p)
  obtain ⟨c, hc, hcK⟩ := exists_notMem_forall_smul_eq_zero (P := q) K fun t ↦ by
    obtain ⟨b, hb, hbt⟩ := (IsLocalizedModule.lTensor_injective_iff q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl M) p.subtype).mp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective) t t.property
    exact ⟨b, hb, Subtype.ext hbt⟩
  exact ⟨c, hc, fun t ht ↦ congrArg Subtype.val (hcK ⟨t, ht⟩)⟩

private theorem relative_flat_neighborhood [IsNoetherianRing R] [Algebra.FiniteType R S]
    [Module.Finite S M] (q : Ideal S) [q.IsPrime]
    (hq : Module.Flat R (LocalizedModule q.primeCompl M)) :
    ∃ a ∉ q, ∀ (q' : Ideal S) [q'.IsPrime], q ≤ q' → a ∉ q' →
      Module.Flat R (LocalizedModule q'.primeCompl M) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let p := q.comap (algebraMap R S)
  obtain ⟨c, hc, hcK⟩ := exists_notMem_kill_tensor_kernel q hq
  obtain ⟨d, hd, hdker⟩ :=
    exists_notMem_pow_smul_eq_zero_of_tensor_kernel (S := S) (M := M) p
  refine ⟨c * algebraMap R S d, fun h ↦
    ((Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹q.IsPrime›).mp h).elim hc hd, ?_⟩
  intro q' _ hqq' hcd
  have hc' : c ∉ q' := fun h ↦ hcd (q'.mul_mem_right _ h)
  have hd' : algebraMap R S d ∉ q' := fun h ↦ hcd (q'.mul_mem_left _ h)
  have hjac : p.map (algebraMap R (Localization.AtPrime q')) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.AtPrime q'),
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q') q']
    exact hqq' hr
  refine Module.Flat.of_lTensor_injective (S := Localization.AtPrime q') p hjac ?_ ?_
  · intro N _ _ hN N'
    rw [IsLocalizedModule.lTensor_injective_iff q'.primeCompl
      (LocalizedModule.mkLinearMap q'.primeCompl M)]
    intro t ht
    obtain ⟨n, hn⟩ := hdker N' N hN N'.subtype Subtype.val_injective _ ht
    refine ⟨algebraMap R S d ^ n,
      fun h ↦ hd' (Ideal.IsPrime.mem_of_pow_mem ‹q'.IsPrime› n h), ?_⟩
    rw [← map_pow, algebraMap_smul, hn]
  · rw [IsLocalizedModule.lTensor_injective_iff q'.primeCompl
      (LocalizedModule.mkLinearMap q'.primeCompl M)]
    intro t ht
    exact ⟨c, hc', hcK t ht⟩

/-- The flat locus of a finite module over a finite-type algebra over a Noetherian base is open
in the spectrum of the algebra. -/
theorem isOpen_setOf_flat_localizedModule [IsNoetherianRing R] [Algebra.FiniteType R S]
    [Module.Finite S M] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)} := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_exists_notMem
  · intro q q' hspec hflat
    have hle : q'.asIdeal ≤ q.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hspec
    have : Module.Flat R (LocalizedModule q.asIdeal.primeCompl M) := hflat
    refine Module.Flat.iff_lTensor_injective'.mpr fun J ↦ ?_
    rw [IsLocalizedModule.lTensor_injective_iff q'.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q'.asIdeal.primeCompl M)]
    intro t ht
    obtain ⟨s, hs, hst⟩ := (IsLocalizedModule.lTensor_injective_iff q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) J.subtype).mp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective) t ht
    exact ⟨s, fun h ↦ hs (hle h), hst⟩
  · intro q hflat
    obtain ⟨a, ha, h⟩ := relative_flat_neighborhood (M := M) q.asIdeal hflat
    exact ⟨a, ha, fun q' hle haq' ↦ h q'.asIdeal hle haq'⟩

/-- Flatness of a finite module over a finite-type algebra over a Noetherian ring holds on a
principal neighbourhood of each flat point of the algebra spectrum. -/
theorem Flat.exists_notMem_forall_flat_localizedModule [IsNoetherianRing R] [Algebra.FiniteType R S]
    [Module.Finite S M] (q : Ideal S) [q.IsPrime]
    (hq : Module.Flat R (LocalizedModule q.primeCompl M)) :
    ∃ a ∉ q, ∀ (q' : Ideal S) [q'.IsPrime], a ∉ q' →
      Module.Flat R (LocalizedModule q'.primeCompl M) := by
  obtain ⟨_, ⟨a, rfl⟩, ha, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp
      ((isOpen_setOf_flat_localizedModule (R := R) (S := S) (M := M)).mem_nhds
        (x := (⟨q, inferInstance⟩ : PrimeSpectrum S)) hq)
  refine ⟨a, ha, fun q' _ haq' ↦ ?_⟩
  have hmem : (⟨q', inferInstance⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen a := by
    rw [PrimeSpectrum.mem_basicOpen]
    exact haq'
  exact hsub hmem

end Module

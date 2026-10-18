/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Density.Chebotarev
public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# Chebotarev for residue degrees in nonnormal subfields

Let `L/K` be a finite Galois extension of number fields, `H ≤ Gal(L/K)`, and `E = L ^ H`.
The field `E/K` need not be normal. At a prime of `K` unramified in `L`, there is a prime of
`E` of residue degree `n` exactly when the Frobenius class contains an element `σ` with
`H.relIndex (Subgroup.zpowers σ) = n`. This index is the least positive exponent sending
`σ` into `H`, so for `n = 1` the condition is that the class meets `H`.

The relevant classes give a disjoint union of Frobenius fibres. Chebotarev computes its
Dirichlet density as the sum of their class sizes divided by `#Gal(L/K)`. The primes ramified
in `L` form a finite exceptional set, so the same density holds without an unramifiedness
restriction. Each base prime is counted once, even if several primes above it have degree `n`.
Taking `L` to be a Galois closure gives the non-Galois residue-degree form of Chebotarev.

## Main results

* `NumberField.Chebotarev.exists_inertiaDeg_eq_iff_of_mem_frobeniusPrimeSet`: the arithmetic
  characterization within one Frobenius fibre.
* `NumberField.Chebotarev.setOf_exists_inertiaDeg_eq_inter_compl_ramifiedPrimes`: the exact
  union of the selected fibres away from ramification in the Galois extension.
* `NumberField.Chebotarev.hasDirichletDensity_setOf_exists_inertiaDeg_eq`: the resulting
  density, including all base primes.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter VII, §13.
* The arithmetic input is `Ideal.inertiaDeg_under_fixedField_eq_relIndex`; the analytic input
  is `NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet`.
-/

public section

open IntermediateField IsDedekindDomain
open scoped NumberField symmDiff

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Within an unramified Frobenius fibre, a prime admits a prime of residue degree `n` in
`L ^ H` exactly when some representative of its Frobenius class has cyclic relative index `n`.
No normality of `H` is required. -/
theorem exists_inertiaDeg_eq_iff_of_mem_frobeniusPrimeSet
    {H : Subgroup (L ≃ₐ[K] L)} {n : ℕ} {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} (h𝔭 : 𝔭 ∈ frobeniusPrimeSet K L C) :
    (∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixedField H)),
      𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = n) ↔
      ∃ σ ∈ C.carrier, H.relIndex (Subgroup.zpowers σ) = n := by
  classical
  have : IsScalarTower K ↥(fixedField H) L := (fixedField H).isScalarTower_mid'
  constructor
  · rintro ⟨𝔓, h𝔓, hn⟩
    obtain ⟨Q, hQ⟩ := HeightOneSpectrum.under_surjective (𝓞 ↥(fixedField H)) (𝓞 L) 𝔓
    have hQp : Q.under (𝓞 K) = 𝔭 := by
      rw [← HeightOneSpectrum.under_under (𝓞 ↥(fixedField H)) (A := 𝓞 K) Q, hQ, h𝔓]
    have : Q.asIdeal.LiesOver 𝔭.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal hQp).symm⟩
    have : Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal :=
      isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q.asIdeal
    obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K Q.asIdeal Q.ne_bot
    refine ⟨σ, ConjClasses.mem_carrier_iff_mk_eq.mpr ?_, ?_⟩
    · exact (artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal
        (isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭) Q.asIdeal σ hσ).symm.trans
          ((mem_frobeniusPrimeSet_iff.mp h𝔭).choose_spec)
    · rw [← Ideal.inertiaDeg_under_fixedField_eq_relIndex Q.asIdeal Q.ne_bot H hσ,
        ← HeightOneSpectrum.under_asIdeal, hQ, hn]
  · rintro ⟨σ, hσC, hn⟩
    have hpσ : 𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) :=
      (ConjClasses.mem_carrier_iff_mk_eq.mp hσC).symm ▸ h𝔭
    obtain ⟨Q, hσ⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hpσ
    have : Algebra.IsUnramifiedAt (𝓞 K) Q.1 :=
      isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q.1
    let Q' : HeightOneSpectrum (𝓞 L) := HeightOneSpectrum.ofPrime
      (Ideal.prime_of_isPrime hσ.ne_bot inferInstance)
    refine ⟨Q'.under (𝓞 ↥(fixedField H)), ?_, ?_⟩
    · rw [HeightOneSpectrum.under_under]
      exact HeightOneSpectrum.ext Q.2.2.over.symm
    · rw [HeightOneSpectrum.under_asIdeal]
      exact (Ideal.inertiaDeg_under_fixedField_eq_relIndex Q.1 hσ.ne_bot H hσ).trans hn

variable (K L) in
open scoped Classical in
/-- Away from primes ramified in `L`, the primes admitting residue degree `n` in `L ^ H`
are exactly the union of the Frobenius fibres whose class contains an element of cyclic
relative index `n`. -/
theorem setOf_exists_inertiaDeg_eq_inter_compl_ramifiedPrimes
    (H : Subgroup (L ≃ₐ[K] L)) (n : ℕ) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | ∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixedField H)),
      𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = n} ∩
        (↑(ramifiedPrimes K L) : Set (HeightOneSpectrum (𝓞 K)))ᶜ =
      ⋃ C ∈ Finset.univ.filter
        (fun C : ConjClasses (L ≃ₐ[K] L) ↦ ∃ σ ∈ C.carrier,
          H.relIndex (Subgroup.zpowers σ) = n), frobeniusPrimeSet K L C := by
  ext 𝔭
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, Finset.mem_coe,
    Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hn, hur⟩
    obtain ⟨C, hC, -⟩ := existsUnique_mem_frobeniusPrimeSet hur
    exact ⟨C, (exists_inertiaDeg_eq_iff_of_mem_frobeniusPrimeSet hC).mp hn, hC⟩
  · rintro ⟨C, hn, hC⟩
    exact ⟨(exists_inertiaDeg_eq_iff_of_mem_frobeniusPrimeSet hC).mpr hn,
      frobeniusPrimeSet_subset_compl_ramifiedPrimes C hC⟩

variable (K L) in
open scoped Classical in
/-- **Non-Galois residue-degree Chebotarev.** The primes of `K` admitting a prime of residue
degree `n` in `L ^ H` have Dirichlet density the sum of `#C / #Gal(L/K)` over the classes `C`
containing an element `σ` with `[⟨σ⟩ : ⟨σ⟩ ∩ H] = n`. This includes primes ramified in `L`;
they can only change the selected union of Frobenius fibres by a finite set. -/
theorem hasDirichletDensity_setOf_exists_inertiaDeg_eq
    (H : Subgroup (L ≃ₐ[K] L)) (n : ℕ) :
    NumberField.Set.HasDirichletDensity
      {𝔭 : HeightOneSpectrum (𝓞 K) | ∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixedField H)),
        𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = n}
      (∑ C ∈ Finset.univ.filter
        (fun C : ConjClasses (L ≃ₐ[K] L) ↦ ∃ σ ∈ C.carrier,
          H.relIndex (Subgroup.zpowers σ) = n),
        (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
  classical
  have h := NumberField.Set.hasDirichletDensity_biUnion_finset
    (s := Finset.univ.filter (fun C : ConjClasses (L ≃ₐ[K] L) ↦
      ∃ σ ∈ C.carrier, H.relIndex (Subgroup.zpowers σ) = n))
    (fun C _ ↦ hasDirichletDensity_frobeniusPrimeSet K L C)
    (fun _ _ _ _ hne ↦ disjoint_frobeniusPrimeSet hne)
  rw [← setOf_exists_inertiaDeg_eq_inter_compl_ramifiedPrimes K L H n] at h
  refine h.of_finite_symmDiff ((ramifiedPrimes K L).finite_toSet.subset ?_)
  intro 𝔭 h𝔭
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_compl_iff] at h𝔭
  tauto

end NumberField.Chebotarev

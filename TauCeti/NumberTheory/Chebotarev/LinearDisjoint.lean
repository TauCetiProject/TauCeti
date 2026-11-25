/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
public import TauCeti.NumberTheory.NumberField.SplitsCompletely.LinearDisjoint
import TauCeti.NumberTheory.Chebotarev.Density.Chebotarev

/-!
# Finitely many primes whose Frobenius elements exhaust a Galois group

Let `L / K` be a finite Galois extension of number fields and `B` a finite set of primes of `𝓞 K`.
By the Chebotarev density theorem every conjugacy class of `Gal(L/K)` is the Artin class of
infinitely many primes, so one prime outside `B` can be chosen in each class. This gives a finite
set `T` of primes of `𝓞 K`, disjoint from `B` and unramified in `L`, such that every element of
`Gal(L/K)` is an arithmetic Frobenius at some prime of `𝓞 L` above `T`. In particular these
Frobenius elements generate `Gal(L/K)`.

Combined with `IntermediateField.linearDisjoint_of_closure_isArithFrobAt_eq_top`, this produces,
for a finite Galois extension `D / K`, finitely many primes outside any prescribed finite set such
that every finite extension of `K` in which they all split completely is linearly disjoint from
`D`. Imposing complete splitting at these primes is how one makes a field constructed with
prescribed local behaviour linearly disjoint from a given Galois extension, as in the construction
of soluble extensions with prescribed completions and in Moret-Bailly's theorem.

## Main results

* `NumberField.Chebotarev.exists_finset_forall_mem_frobeniusPrimeSet`: a finite set of unramified
  primes outside `B` meeting every Frobenius fibre.
* `NumberField.Chebotarev.exists_finset_closure_isArithFrobAt_eq_top`: a finite set of unramified
  primes outside `B` whose Frobenius elements generate `Gal(L/K)`.
* `IntermediateField.exists_finset_forall_linearDisjoint`: a finite set of primes outside `B`,
  unramified in `D`, at which complete splitting forces linear disjointness from `D`.

## References

* L. Clozel, M. Harris and R. Taylor, *Automorphy for some l-adic lifts of automorphic mod l
  Galois representations*, Publ. Math. IHÉS 108 (2008), proof of Lemma 4.1.2.
-/

public section

open IsDedekindDomain Module NumberField

namespace NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **Every Frobenius class is met outside a finite set.** For a finite Galois extension `L / K`
of number fields and a finite set `B` of primes of `𝓞 K`, there is a finite set `T` of primes of
`𝓞 K`, disjoint from `B` and unramified in `L`, containing a prime of every Artin class. -/
theorem exists_finset_forall_mem_frobeniusPrimeSet {B : Set (HeightOneSpectrum (𝓞 K))}
    (hB : B.Finite) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) B ∧
      (∀ v ∈ T, v ∉ ramifiedPrimes K L) ∧
        ∀ σ : L ≃ₐ[K] L, ∃ v ∈ T, v ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) := by
  have hC (C : ConjClasses (L ≃ₐ[K] L)) : (frobeniusPrimeSet K L C \ B).Nonempty :=
    ((infinite_frobeniusPrimeSet K L C).sdiff hB).nonempty
  choose f hf using hC
  refine ⟨(Set.finite_range f).toFinset, ?_, ?_, fun σ ↦ ⟨f (ConjClasses.mk σ), by simp, (hf _).1⟩⟩
  · rw [Set.Finite.coe_toFinset, Set.disjoint_left]
    rintro _ ⟨C, rfl⟩
    exact (hf C).2
  · simp only [Set.Finite.mem_toFinset, Set.forall_mem_range]
    exact fun C ↦ frobeniusPrimeSet_subset_compl_ramifiedPrimes C (hf C).1

/-- **Frobenius elements outside a finite set generate.** For a finite Galois extension `L / K`
of number fields and a finite set `B` of primes of `𝓞 K`, there is a finite set `T` of primes of
`𝓞 K`, disjoint from `B` and unramified in `L`, such that the arithmetic Frobenius elements at the
primes of `𝓞 L` above `T` generate `Gal(L/K)`. -/
theorem exists_finset_closure_isArithFrobAt_eq_top {B : Set (HeightOneSpectrum (𝓞 K))}
    (hB : B.Finite) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) B ∧
      (∀ v ∈ T, v ∉ ramifiedPrimes K L) ∧
        Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v ∈ T,
          ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
            IsArithFrobAt (𝓞 K) σ w.val.asIdeal} = ⊤ := by
  obtain ⟨T, hTB, hTram, hT⟩ := exists_finset_forall_mem_frobeniusPrimeSet K L hB
  refine ⟨T, hTB, hTram, eq_top_iff.2 fun σ _ ↦ Subgroup.subset_closure ?_⟩
  obtain ⟨v, hv, hσ⟩ := hT σ
  obtain ⟨⟨Q, _, _⟩, hQ⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hσ
  exact ⟨v, hv, ⟨⟨Q, ‹_›, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, ‹_›⟩, hQ⟩

end NumberField.Chebotarev

namespace IntermediateField

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

/-- **Complete splitting at finitely many primes forces linear disjointness.** Let `D / K` be a
finite Galois extension inside `Ω` and `B` a finite set of primes of `𝓞 K`. There is a finite set
`T` of primes of `𝓞 K`, disjoint from `B` and unramified in `D`, such that every finite extension
`E / K` inside `Ω` in which every prime of `T` splits completely is linearly disjoint from `D` over
`K`. -/
theorem exists_finset_forall_linearDisjoint (D : IntermediateField K Ω) [FiniteDimensional K D]
    [IsGalois K D] {B : Set (HeightOneSpectrum (𝓞 K))} (hB : B.Finite) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) B ∧
      (∀ v ∈ T, ∀ (Q : Ideal (𝓞 D)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
        ∀ (E : IntermediateField K Ω) [FiniteDimensional K E],
          (∀ v ∈ T, (v.asIdeal.primesOver (𝓞 E)).ncard = finrank K E) → E.LinearDisjoint D := by
  have : NumberField D := .of_module_finite K D
  obtain ⟨T, hTB, hTram, hT⟩ := Chebotarev.exists_finset_closure_isArithFrobAt_eq_top K D hB
  refine ⟨T, hTB, fun v hv ↦ ?_, fun E _ hE ↦ linearDisjoint_of_closure_isArithFrobAt_eq_top hT hE⟩
  exact not_not.mp ((Chebotarev.mem_ramifiedPrimes_iff v).not.mp (hTram v hv))

end IntermediateField

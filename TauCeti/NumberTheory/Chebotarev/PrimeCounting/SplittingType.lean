/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Density.SplittingType
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount

/-!
# Natural density of splitting types in nonnormal extensions

For an intermediate extension `E/K` of a finite Galois extension `L/K`, the splitting type of a
prime of `K` is the multiset of residue degrees of the primes of `E` above it. Away from the
primes ramified in `L`, the primes with a prescribed splitting type `μ` form the disjoint union
of the Frobenius fibres whose coset permutations on `Gal(L/K) ⧸ Gal(L/E)` have full cycle type
`μ` (`NumberField.Chebotarev.setOf_map_inertiaDeg_eq_sdiff_ramifiedPrimes`).

Natural-density Chebotarev applies to each of these fibres, natural density is additive on
finite disjoint unions, and the finitely many ramified primes do not change a natural density.
Hence the primes with splitting type `μ` have natural density equal to the proportion of
`Gal(L/K)` whose action on the cosets of `Gal(L/E)` has full cycle type `μ`. Since natural
density implies Dirichlet density, this strengthens
`NumberField.Chebotarev.hasDirichletDensity_setOf_map_inertiaDeg_eq`.

## Main results

* `NumberField.Chebotarev.hasNaturalDensity_setOf_map_inertiaDeg_eq`: the primes of `K` with
  residue-degree multiset `μ` in `E` have natural density the sum of `#C / #Gal(L/K)` over the
  conjugacy classes acting on Galois cosets with full cycle type `μ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter VII, §13.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)
open MulAction
open scoped NumberField

namespace NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
/-- **Natural-density Chebotarev for splitting types.** The primes with residue-degree multiset
`μ` in `E` have natural density the total proportion of elements whose action on
`Gal(L/K) ⧸ Gal(L/E)` has full cycle type `μ`, expressed as a sum of conjugacy-class
proportions. No normality of `E/K` or realizability hypothesis on `μ` is needed. -/
theorem hasNaturalDensity_setOf_map_inertiaDeg_eq
    (E : IntermediateField K L) (μ : Multiset ℕ) :
    NumberField.Set.HasNaturalDensity
      {𝔭 : HeightOneSpectrum (𝓞 K) |
        (Finset.univ : Finset (𝔭.asIdeal.primesOver (𝓞 E))).val.map
          (fun P => P.1.inertiaDeg (𝓞 K)) = μ}
      (∑ C ∈ Finset.univ.filter (fun C : ConjClasses (L ≃ₐ[K] L) =>
        (toPerm C.out : Equiv.Perm ((L ≃ₐ[K] L) ⧸ E.fixingSubgroup)).fullCycleType = μ),
          (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
  have hdensity := NumberField.Set.hasNaturalDensity_biUnion_finset
    (s := Finset.univ.filter (fun C : ConjClasses (L ≃ₐ[K] L) =>
      (toPerm C.out : Equiv.Perm ((L ≃ₐ[K] L) ⧸ E.fixingSubgroup)).fullCycleType = μ))
    (fun C _ => hasNaturalDensity_frobeniusPrimeSet K L C)
    ((pairwise_disjoint_frobeniusPrimeSet K L).set_pairwise _)
  rw [← setOf_map_inertiaDeg_eq_sdiff_ramifiedPrimes K L E μ] at hdensity
  apply hdensity.of_finite_symmDiff
  exact (ramifiedPrimes K L).finite_toSet.subset (by
    intro 𝔭 h𝔭
    simp only [Set.mem_symmDiff, Set.mem_sdiff] at h𝔭
    tauto)

end NumberField.Chebotarev

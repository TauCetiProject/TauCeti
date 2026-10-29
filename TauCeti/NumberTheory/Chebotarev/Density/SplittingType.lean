/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Density.Chebotarev
public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.SplittingType
import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible

/-!
# Chebotarev density for splitting types in nonnormal extensions

For any intermediate extension `E/K` of a finite Galois extension `L/K`, its splitting type
at a prime of `K` is the multiset of residue degrees of the primes of `E` above it. Outside the
primes ramified in `L`, this is the full cycle type of Frobenius on `Gal(L/K) ⧸ Gal(L/E)`.
Consequently the primes with a prescribed multiset `μ` have Dirichlet density equal to the sum
of `#C / #Gal(L/K)` over the conjugacy classes whose coset permutations have full cycle type `μ`.

The multiset records the entire splitting pattern, including multiplicities and degrees equal
to one. The intermediate extension need not be normal: any finite separable extension can be
realized inside its Galois closure. The density theorem includes ramified primes satisfying
the same residue-degree condition; they do not change the density since only finitely many
primes ramify in the Galois extension.

The arithmetic dictionary is
`Ideal.fullCycleType_toPerm_quotient_eq_map_inertiaDeg`. The density calculation uses
`hasDirichletDensity_frobeniusPrimeSet`, finite disjoint-union additivity, and finite
symmetric-difference invariance, without any additional analytic argument.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter VII, §13.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)
open IntermediateField MulAction NumberField
open scoped NumberField

namespace NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
/-- At a prime in a Frobenius fibre, the residue-degree multiset in the fixed field equals
the full cycle type of every representative of that class acting on Galois cosets. -/
theorem map_inertiaDeg_eq_fullCycleType_of_mem_frobeniusPrimeSet
    (E : IntermediateField K L) {𝔭 : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L}
    (h𝔭 : 𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ)) :
    (Finset.univ : Finset (𝔭.asIdeal.primesOver (𝓞 E))).val.map
        (fun P => P.1.inertiaDeg (𝓞 K)) =
      (toPerm σ : Equiv.Perm ((L ≃ₐ[K] L) ⧸ E.fixingSubgroup)).fullCycleType := by
  obtain ⟨Q, hQ⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
  have : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q.1
  -- Transport the whole residue-degree multiset along the Galois correspondence, preserving
  -- the dependent prime carrier and its finite enumeration together.
  have hE := congrArg (fun F : IntermediateField K L =>
    (Finset.univ : Finset (𝔭.asIdeal.primesOver (𝓞 F))).val.map
      (fun P => P.1.inertiaDeg (𝓞 K))) (IsGalois.fixedField_fixingSubgroup E)
  exact hE.symm.trans
    (Ideal.fullCycleType_toPerm_quotient_eq_map_inertiaDeg 𝔭.asIdeal Q.1 E.fixingSubgroup hQ).symm

open scoped Classical in
/-- Outside ramification in the Galois extension, a splitting-type condition is exactly
a disjoint union of Frobenius fibres. Fixed points and repeated cycle lengths are retained. -/
theorem setOf_map_inertiaDeg_eq_sdiff_ramifiedPrimes
    (E : IntermediateField K L) (μ : Multiset ℕ) :
    {𝔭 : HeightOneSpectrum (𝓞 K) |
      (Finset.univ : Finset (𝔭.asIdeal.primesOver (𝓞 E))).val.map
        (fun P => P.1.inertiaDeg (𝓞 K)) = μ} \ (ramifiedPrimes K L : Set _) =
      ⋃ C ∈ Finset.univ.filter (fun C : ConjClasses (L ≃ₐ[K] L) =>
        (toPerm C.out : Equiv.Perm ((L ≃ₐ[K] L) ⧸ E.fixingSubgroup)).fullCycleType = μ),
          frobeniusPrimeSet K L C := by
  ext 𝔭
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hμ, hur⟩
    obtain ⟨C, hC, -⟩ := existsUnique_mem_frobeniusPrimeSet (K := K) (L := L) (𝔭 := 𝔭)
      (by simpa only [Finset.mem_coe] using hur)
    have hout : ConjClasses.mk C.out = C := Quotient.out_eq C
    have htype := map_inertiaDeg_eq_fullCycleType_of_mem_frobeniusPrimeSet K L E
      (hout.symm ▸ hC)
    exact ⟨C, htype.symm.trans hμ, hC⟩
  · rintro ⟨C, hμ, hC⟩
    have hout : ConjClasses.mk C.out = C := Quotient.out_eq C
    exact ⟨(map_inertiaDeg_eq_fullCycleType_of_mem_frobeniusPrimeSet K L E
      (hout.symm ▸ hC)).trans hμ, frobeniusPrimeSet_subset_compl_ramifiedPrimes C hC⟩

open scoped Classical symmDiff in
/-- **Non-Galois Chebotarev for splitting types.** The primes with residue-degree multiset `μ`
in `E` have density the total proportion of elements whose action on `Gal(L/K) ⧸ Gal(L/E)`
has full cycle type `μ`, expressed as a sum of conjugacy-class proportions. No normality of
`E/K` or realizability hypothesis on `μ` is needed. -/
theorem hasDirichletDensity_setOf_map_inertiaDeg_eq
    (E : IntermediateField K L) (μ : Multiset ℕ) :
    NumberField.Set.HasDirichletDensity
      {𝔭 : HeightOneSpectrum (𝓞 K) |
        (Finset.univ : Finset (𝔭.asIdeal.primesOver (𝓞 E))).val.map
          (fun P => P.1.inertiaDeg (𝓞 K)) = μ}
      (∑ C ∈ Finset.univ.filter (fun C : ConjClasses (L ≃ₐ[K] L) =>
        (toPerm C.out : Equiv.Perm ((L ≃ₐ[K] L) ⧸ E.fixingSubgroup)).fullCycleType = μ),
          (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
  have hdensity := NumberField.Set.hasDirichletDensity_biUnion_finset
    (s := Finset.univ.filter (fun C : ConjClasses (L ≃ₐ[K] L) =>
      (toPerm C.out : Equiv.Perm ((L ≃ₐ[K] L) ⧸ E.fixingSubgroup)).fullCycleType = μ))
    (fun C _ => hasDirichletDensity_frobeniusPrimeSet K L C)
    ((pairwise_disjoint_frobeniusPrimeSet K L).set_pairwise _)
  rw [← setOf_map_inertiaDeg_eq_sdiff_ramifiedPrimes K L E μ] at hdensity
  apply hdensity.of_finite_symmDiff
  exact (ramifiedPrimes K L).finite_toSet.subset (by
    intro 𝔭 h𝔭
    simp only [Set.mem_symmDiff, Set.mem_sdiff] at h𝔭
    tauto)

end NumberField.Chebotarev

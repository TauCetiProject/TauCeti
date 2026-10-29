/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Density.ResidueDegree
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount

/-!
# Natural density of residue degrees in nonnormal subfields

Let `L/K` be a finite Galois extension of number fields, `H ≤ Gal(L/K)`, and `E = L ^ H`.
Away from the primes ramified in `L`, the primes of `K` admitting a prime of residue degree `n`
in `E` form the disjoint union of the Frobenius fibres whose class contains an element `σ` with
`H.relIndex (Subgroup.zpowers σ) = n`
(`NumberField.Chebotarev.setOf_exists_inertiaDeg_eq_inter_compl_ramifiedPrimes`).

Natural-density Chebotarev applies to each of these fibres, natural density is additive on
finite disjoint unions, and the finitely many ramified primes do not change a natural density.
This gives the natural-density form of the residue-degree theorem, strengthening
`NumberField.Chebotarev.hasDirichletDensity_setOf_exists_inertiaDeg_eq`. Each base prime is
counted once, even if several primes above it have degree `n`.

## Main results

* `NumberField.Chebotarev.hasNaturalDensity_setOf_exists_inertiaDeg_eq`: the primes of `K`
  admitting a prime of residue degree `n` in `L ^ H` have natural density the sum of
  `#C / #Gal(L/K)` over the selected conjugacy classes.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter VII, §13.
-/

public section

open IntermediateField IsDedekindDomain
open scoped NumberField

namespace NumberField.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
/-- **Natural-density residue-degree Chebotarev.** The primes of `K` admitting a prime of
residue degree `n` in `L ^ H` have natural density the sum of `#C / #Gal(L/K)` over the
classes `C` containing an element `σ` with `[⟨σ⟩ : ⟨σ⟩ ∩ H] = n`. This includes primes
ramified in `L`; they can only change the selected union of Frobenius fibres by a finite set. -/
theorem hasNaturalDensity_setOf_exists_inertiaDeg_eq
    (H : Subgroup (L ≃ₐ[K] L)) (n : ℕ) :
    NumberField.Set.HasNaturalDensity
      {𝔭 : HeightOneSpectrum (𝓞 K) | ∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixedField H)),
        𝔓.under (𝓞 K) = 𝔭 ∧ 𝔓.asIdeal.inertiaDeg (𝓞 K) = n}
      (∑ C ∈ Finset.univ.filter
        (fun C : ConjClasses (L ≃ₐ[K] L) ↦ ∃ σ ∈ C.carrier,
          H.relIndex (Subgroup.zpowers σ) = n),
        (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
  have h := NumberField.Set.hasNaturalDensity_biUnion_finset
    (s := Finset.univ.filter (fun C : ConjClasses (L ≃ₐ[K] L) ↦
      ∃ σ ∈ C.carrier, H.relIndex (Subgroup.zpowers σ) = n))
    (fun C _ ↦ hasNaturalDensity_frobeniusPrimeSet K L C)
    (fun _ _ _ _ hne ↦ disjoint_frobeniusPrimeSet hne)
  rw [← setOf_exists_inertiaDeg_eq_inter_compl_ramifiedPrimes K L H n] at h
  refine h.of_finite_symmDiff ((ramifiedPrimes K L).finite_toSet.subset ?_)
  intro 𝔭 h𝔭
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_compl_iff] at h𝔭
  tauto

end NumberField.Chebotarev

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt

/-!
# Frobenius `ψ` along a normal subextension

Let `K ⊆ M ⊆ L` be number fields with `L / K` and `M / K` Galois. Restriction to `M` is a group
homomorphism `Gal(L/K) → Gal(M/K)`, it carries the Artin class of a prime `𝔭` of `𝓞 K` to the
Artin class of `𝔭` for `M / K` with no power taken
(`NumberField.artinSymbol_map_restrictNormalHom`), and it commutes with powers of conjugacy
classes. So a prime power `𝔭 ^ j` counted by `frobeniusPsi K L D` for a class `D` of `Gal(L/K)` is
counted by `frobeniusPsi K M C` for the single class `C = ConjClasses.map _ D`, and the classes `D`
lying over a fixed `C` contribute to it disjointly.

This file records that refinement. Pointwise, the Frobenius weights of the classes over `C` add up
to the Frobenius weight of `C` itself, except at prime powers based at a prime ramifying in `L`,
where the upper weights all vanish while the lower one need not. Summing over prime powers, any
family of distinct classes over `C` gives a lower bound for `frobeniusPsi K M C`, and the full
family misses only the finitely many primes of `ramifiedPrimes K L`, hence accounts for
`frobeniusPsi K M C` up to `O(log x)`.

The lower bound is the shape the cyclotomic crossing consumes: over the compositum `M(μ_q)` of `M`
with an auxiliary cyclotomic field, the classes of the tagged elements `(σ, τ)` for distinct `τ`
are distinct classes over the class of `σ`, so the weighted asymptotics of their fibres add up to a
lower bound for the weighted asymptotics of the fibre of `σ`.

There is no companion upper bound for a proper subfamily, and none is needed: the crossing closes
by summing the lower bounds over all of `Gal(M/K)` against `ψ_M`, which
`NumberField.Chebotarev.primePsi_univ_sub_sum_frobeniusPsi_isBigO_log` supplies.

## Main results

* `NumberField.Chebotarev.sum_frobeniusPrimePowerWeight_map_restrictNormalHom`: at a single prime
  power, the Frobenius weights of the classes of `Gal(L/K)` over `C` add up to the Frobenius weight
  of `C`, unless the base ramifies in `L`, in which case they add up to `0`.
* `NumberField.Chebotarev.sum_frobeniusPsi_le_frobeniusPsi`: the Frobenius `ψ` functions of any
  finite family of distinct classes over `C` add up to at most `frobeniusPsi K M C`.
* `NumberField.Chebotarev.frobeniusPsi_sub_sum_frobeniusPsi_le_primePsi`: over the full family,
  the defect is at most `ψ` of the finite set `ramifiedPrimes K L`.
* `NumberField.Chebotarev.frobeniusPsi_sub_sum_frobeniusPsi_isBigO_log`: hence the defect is
  `O(log x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter VII, §13.
* R. Sharifi, *Algebraic Number Theory*, the proof of Theorem 7.2.2, where the weighted count over
  an auxiliary compositum is bounded by the weighted count downstairs.
-/

public section

namespace NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra M L] [IsScalarTower K M L] [IsGalois K L]
  [IsGalois K M]

open scoped Classical in
/-- **The Frobenius weights over a class add up to its own weight.** For a tower `K ⊆ M ⊆ L` with
both `L / K` and `M / K` Galois and a conjugacy class `C` of `Gal(M/K)`, the powered Frobenius
weights at a prime power `𝔭 ^ j` of the classes of `Gal(L/K)` restricting to `C` add up to the
powered Frobenius weight of `C`, provided `𝔭` is unramified in `L`; if `𝔭` ramifies in `L` they add
up to `0`, whatever the weight of `C` is.

At most one summand is ever nonzero, namely the one indexed by the `j`-th power of the Artin class
of `𝔭` in `L / K`; restriction carries it to the `j`-th power of the Artin class of `𝔭` in
`M / K`. -/
theorem sum_frobeniusPrimePowerWeight_map_restrictNormalHom (C : ConjClasses (M ≃ₐ[K] M))
    (A : IdealPrimePower K) :
    ∑ D ∈ {D : ConjClasses (L ≃ₐ[K] L) |
        ConjClasses.map (AlgEquiv.restrictNormalHom M) D = C},
        frobeniusPrimePowerWeight K L D A =
      {B : IdealPrimePower K | primePowerBase B ∉ ramifiedPrimes K L}.indicator
        (frobeniusPrimePowerWeight K M C) A := by
  by_cases hA : primePowerBase A ∈ ramifiedPrimes K L
  · -- Every class of `Gal(L/K)` needs an unramifiedness witness in `L`, so all summands vanish.
    rw [Set.indicator_of_notMem (by simpa using hA)]
    refine Finset.sum_eq_zero fun D _ ↦ frobeniusPrimePowerWeight_of_notMem ?_
    intro h
    obtain ⟨hur, -⟩ := mem_frobeniusPrimePowerSet_iff.mp h
    exact (mem_ramifiedPrimes_iff _).mp hA hur
  · rw [Set.indicator_of_mem (by simpa using hA)]
    have hurL := not_not.mp ((mem_ramifiedPrimes_iff _).not.mp hA)
    have hurM := not_not.mp ((mem_ramifiedPrimes_iff (L := M) _).not.mp
      fun h ↦ hA (ramifiedPrimes_subset_ramifiedPrimes h))
    -- The unique class of `Gal(L/K)` that can contribute, and its restriction.
    set D₀ := artinSymbol (primePowerBase A).asIdeal hurL ^ primePowerExponent A with hD₀def
    have hmap : ConjClasses.map (AlgEquiv.restrictNormalHom M) D₀ =
        artinSymbol (primePowerBase A).asIdeal hurM ^ primePowerExponent A := by
      rw [hD₀def, ConjClasses.map_pow, artinSymbol_map_restrictNormalHom]
    -- Membership in the upper fibre of `D` pins `D` down to `D₀`.
    have hmem : ∀ D : ConjClasses (L ≃ₐ[K] L),
        A ∈ frobeniusPrimePowerSet K L D ↔ D = D₀ := fun D ↦ by
      rw [mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hurL D, hD₀def, eq_comm]
    by_cases hC : ConjClasses.map (AlgEquiv.restrictNormalHom M) D₀ = C
    · have hD₀ : D₀ ∈ ({D : ConjClasses (L ≃ₐ[K] L) |
          ConjClasses.map (AlgEquiv.restrictNormalHom M) D = C} : Finset _) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩
      rw [Finset.sum_eq_single_of_mem D₀ hD₀
        (fun D _ hD ↦ frobeniusPrimePowerWeight_of_notMem (fun h ↦ hD ((hmem D).mp h))),
        frobeniusPrimePowerWeight_of_mem ((hmem D₀).mpr rfl),
        frobeniusPrimePowerWeight_of_artinSymbol_pow_eq hurM (hmap.symm.trans hC)]
    · rw [Finset.sum_eq_zero fun D hD ↦ frobeniusPrimePowerWeight_of_notMem fun h ↦
        hC ((hmem D).mp h ▸ (Finset.mem_filter.mp hD).2)]
      refine (frobeniusPrimePowerWeight_of_notMem fun h ↦ hC ?_).symm
      rw [hmap]
      exact (mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hurM C).mp h

open scoped Classical in
/-- **Distinct classes over `C` give a lower bound for its Frobenius `ψ`.** For a tower
`K ⊆ M ⊆ L` with both `L / K` and `M / K` Galois, the Frobenius `ψ` functions of a finite family of
distinct conjugacy classes of `Gal(L/K)`, each restricting to `C`, add up to at most the Frobenius
`ψ` function of `C`.

This is the form the cyclotomic crossing uses: the tagged classes over an auxiliary compositum are
distinct and all restrict to the class being counted, so their weighted contributions add. -/
theorem sum_frobeniusPsi_le_frobeniusPsi (C : ConjClasses (M ≃ₐ[K] M))
    (S : Finset (ConjClasses (L ≃ₐ[K] L)))
    (hS : ∀ D ∈ S, ConjClasses.map (AlgEquiv.restrictNormalHom M) D = C) (x : ℝ) :
    ∑ D ∈ S, frobeniusPsi K L D x ≤ frobeniusPsi K M C x := by
  calc ∑ D ∈ S, frobeniusPsi K L D x
      ≤ ∑ D ∈ {D : ConjClasses (L ≃ₐ[K] L) |
          ConjClasses.map (AlgEquiv.restrictNormalHom M) D = C}, frobeniusPsi K L D x :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun D hD ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS D hD⟩)
          fun D _ _ ↦ frobeniusPsi_nonneg D x
    _ ≤ frobeniusPsi K M C x := by
        simp only [frobeniusPsi_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun A _ ↦ ?_
        rw [sum_frobeniusPrimePowerWeight_map_restrictNormalHom C A]
        exact Set.indicator_apply_le' (fun _ ↦ le_rfl)
          fun _ ↦ frobeniusPrimePowerWeight_nonneg C A

open scoped Classical in
/-- **The classes over `C` account for its Frobenius `ψ` up to the ramified primes.** The prime
powers counted by `frobeniusPsi K M C` and by no class of `Gal(L/K)` over `C` can only be based at
a prime of `ramifiedPrimes K L`, so the resulting defect is at most `ψ` of that finite set. -/
theorem frobeniusPsi_sub_sum_frobeniusPsi_le_primePsi (C : ConjClasses (M ≃ₐ[K] M)) (x : ℝ) :
    frobeniusPsi K M C x - ∑ D ∈ {D : ConjClasses (L ≃ₐ[K] L) |
        ConjClasses.map (AlgEquiv.restrictNormalHom M) D = C}, frobeniusPsi K L D x ≤
      primePsi K (ramifiedPrimes K L : Set (HeightOneSpectrum (𝓞 K))) x := by
  have hsum : ∑ D ∈ {D : ConjClasses (L ≃ₐ[K] L) |
      ConjClasses.map (AlgEquiv.restrictNormalHom M) D = C}, frobeniusPsi K L D x =
      ∑ A ∈ primePowersLE K x, {B : IdealPrimePower K |
        primePowerBase B ∉ ramifiedPrimes K L}.indicator
          (frobeniusPrimePowerWeight K M C) A := by
    simp only [frobeniusPsi_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun A _ ↦
      sum_frobeniusPrimePowerWeight_map_restrictNormalHom C A
  rw [hsum, frobeniusPsi_apply, primePsi_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun A _ ↦ ?_
  by_cases hA : primePowerBase A ∈ ramifiedPrimes K L
  · rw [Set.indicator_of_notMem (by simpa using hA), sub_zero,
      Set.indicator_of_mem (by simpa using hA)]
    exact frobeniusPrimePowerWeight_le C A
  · rw [Set.indicator_of_mem (by simpa using hA), sub_self,
      Set.indicator_of_notMem (by simpa using hA)]

open scoped Classical in
/-- **The classes over `C` account for its Frobenius `ψ` up to `O(log x)`.** Only the prime powers
based at the finitely many primes of `ramifiedPrimes K L` are missed. -/
theorem frobeniusPsi_sub_sum_frobeniusPsi_isBigO_log (C : ConjClasses (M ≃ₐ[K] M)) :
    (fun x : ℝ ↦ frobeniusPsi K M C x - ∑ D ∈ {D : ConjClasses (L ≃ₐ[K] L) |
        ConjClasses.map (AlgEquiv.restrictNormalHom M) D = C}, frobeniusPsi K L D x) =O[atTop]
      Real.log := by
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_of_le _ fun x ↦ ?_)
    (primePsi_isBigO_log_of_finite (K := K) (ramifiedPrimes K L).finite_toSet)
  rw [Real.norm_of_nonneg (sub_nonneg.2 (sum_frobeniusPsi_le_frobeniusPsi C _
      (fun _ hD ↦ (Finset.mem_filter.mp hD).2) x)),
    Real.norm_of_nonneg (primePsi_nonneg _ x)]
  exact frobeniusPsi_sub_sum_frobeniusPsi_le_primePsi C x

end NumberField.Chebotarev

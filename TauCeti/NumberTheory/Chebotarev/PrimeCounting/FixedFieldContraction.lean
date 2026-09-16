/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FixedField.FiberCount
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt
public import TauCeti.NumberTheory.Chebotarev.PrimesAboveRamifiedPrimes

/-!
# Contracting Frobenius `ϑ` from a cyclic fixed field

Let `L / K` be a finite Galois extension of number fields, let `C` be a conjugacy class of
`Gal(L/K)`, choose `sigma ∈ C`, and put `E = L ^ <sigma>`.  This file proves the exact identity

```text
∑_{𝔓 ∈ S_E, N 𝔓 ≤ x} log N 𝔓 = (#G / (#C * orderOf sigma)) * ϑ_C(x),
```

where `S_E` is the set of primes `𝔓` of `E` whose relative Artin class in `L / E` is represented by
`sigma`, that do not lie above `ramifiedPrimes K L`, and that have residue degree one over `K`.

There is no error term.  Away from the ramified primes, a prime `𝔓` of the relative fibre has
residue degree one over `K` exactly when the prime `𝔭` of `K` below it lies in the Frobenius fibre
of `C` (`NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`); then
`N 𝔓 = N 𝔭`, and over each such `𝔭` there are exactly `#G / (#C * orderOf sigma)` of them
(`NumberField.Chebotarev.fixedField_frobenius_fiber_card`).

The identity concerns `ϑ` at residue degree one only.  The other primes of the relative fibre have
residue degree at least two over `ℚ` or lie above `ramifiedPrimes K L`, so they are majorized by
the unrestricted sums appearing in `NumberField.Chebotarev.frobeniusDiscard_isLittleO` over
`L ^ <sigma>`.  There is no such identity for `ψ`: a prime power `𝔓 ^ m` with `m ≥ 2` is selected
by the `m`-th power of its Frobenius, and the prime of `K` below it need not have class `C`.

## Main result

* `NumberField.Chebotarev.primeTheta_fixedField_eq_mul_frobeniusTheta`: the residue-degree-one
  part of the relative Frobenius `ϑ` over `L ^ <sigma>`, away from the primes above
  `ramifiedPrimes K L`, is the fixed-field multiplicity times `frobeniusTheta K L C`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter I, §5.
-/

public section

open IntermediateField
open scoped NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

open TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Grouping by the prime below: a set of primes of `L ^ <sigma>` consisting exactly of the
members of the relative fiber of `sigma` lying over the Frobenius fiber of `sigma` has
`primeTheta` equal to the fixed-field multiplicity times `frobeniusTheta`. -/
private theorem primeTheta_eq_mul_frobeniusTheta_of_forall_mem_iff (sigma : L ≃ₐ[K] L)
    {S : Set (HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers sigma))))}
    (hS : ∀ P, P ∈ S ↔
      P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers sigma)) L
          (ConjClasses.mk sigma.toFixedFieldAlgEquiv) ∧
        P.under (𝓞 K) ∈ frobeniusPrimeSet K L (ConjClasses.mk sigma)) (x : ℝ) :
    primeTheta ↥(fixedField (Subgroup.zpowers sigma)) S x =
      ((Nat.card (L ≃ₐ[K] L) /
          (Nat.card (ConjClasses.mk sigma).carrier * orderOf sigma) : ℕ) : ℝ) *
        frobeniusTheta K L (ConjClasses.mk sigma) x := by
  classical
  -- Every member of `S` has residue degree one over `K`, hence the norm of the prime below.
  have hnorm : ∀ P ∈ S, Ideal.absNorm P.asIdeal = Ideal.absNorm (P.under (𝓞 K)).asIdeal := by
    intro P hPS
    obtain ⟨hP, hp⟩ := (hS P).mp hPS
    have hdeg := (inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet sigma hP fun h ↦
      frobeniusPrimeSet_subset_compl_ramifiedPrimes _ hp (Finset.mem_coe.mpr h)).mpr hp
    have : P.asIdeal.LiesOver (P.under (𝓞 K)).asIdeal := ⟨HeightOneSpectrum.under_asIdeal _ P⟩
    rw [← Ideal.absNorm_pow_inertiaDeg (P.under (𝓞 K)).asIdeal P.asIdeal, hdeg, pow_one]
  rw [primeTheta_apply, frobeniusTheta_apply]
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.mul_sum]
  refine (Finset.sum_fiberwise_of_maps_to (g := fun P ↦ P.under (𝓞 K)) ?_ _).symm.trans
    (Finset.sum_congr rfl fun p hp ↦ ?_)
  · intro P hP
    simp only [Finset.mem_filter, mem_normLE] at hP ⊢
    exact ⟨hnorm P hP.2 ▸ hP.1, ((hS P).mp hP.2).2⟩
  simp only [Finset.mem_filter, mem_normLE] at hp
  rw [Finset.sum_congr rfl fun P hP ↦ by
    simp only [Finset.mem_filter] at hP
    rw [hnorm P hP.1.2, hP.2], Finset.sum_const, nsmul_eq_mul]
  -- The primes of `E` counted over `p` are exactly those of `fixedField_frobenius_fiber_card`.
  rw [← fixedField_frobenius_fiber_card _ sigma ConjClasses.mem_carrier_mk p hp.2,
    ← Nat.card_eq_finsetCard]
  refine congrArg (· * _) (congrArg Nat.cast (Nat.card_congr
    (Equiv.subtypeEquivRight fun P ↦ ?_)))
  simp only [Finset.mem_filter, mem_normLE]
  refine ⟨fun ⟨⟨_, hPS⟩, hPp⟩ ↦ ⟨hPp, ((hS P).mp hPS).1⟩, fun ⟨hPp, hP⟩ ↦ ?_⟩
  have hPS : P ∈ S := (hS P).mpr ⟨hP, hPp ▸ hp.2⟩
  exact ⟨⟨by rw [hnorm P hPS, hPp]; exact hp.1, hPS⟩, hPp⟩

/-- **The exact residue-degree-one contraction of Frobenius `ϑ`.** Let `sigma` represent `C` and
let `E = L ^ <sigma>`.  Sum `log N 𝔓` over the primes `𝔓` of `E` of norm at most `x` whose relative
Artin class in `L / E` is represented by `sigma.toFixedFieldAlgEquiv`, that do not lie above a prime
of `K` ramified in `L`, and that have residue degree one over `K`.  The result is exactly

```text
(#Gal(L/K) / (#C * orderOf sigma)) * frobeniusTheta K L C x.
```

The natural-number division is exact by `ConjClasses.card_carrier_mul_orderOf_dvd`. -/
theorem primeTheta_fixedField_eq_mul_frobeniusTheta (C : ConjClasses (L ≃ₐ[K] L))
    (sigma : L ≃ₐ[K] L) (hsigma : sigma ∈ C.carrier) (x : ℝ) :
    primeTheta ↥(fixedField (Subgroup.zpowers sigma))
        {P | P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers sigma)) L
            (ConjClasses.mk sigma.toFixedFieldAlgEquiv) ∧
          P ∉ primesAboveRamifiedPrimes K L ↥(fixedField (Subgroup.zpowers sigma)) ∧
          P.asIdeal.inertiaDeg (𝓞 K) = 1} x =
      ((Nat.card (L ≃ₐ[K] L) / (Nat.card C.carrier * orderOf sigma) : ℕ) : ℝ) *
        frobeniusTheta K L C x := by
  obtain rfl : ConjClasses.mk sigma = C := ConjClasses.mem_carrier_iff_mk_eq.mp hsigma
  refine primeTheta_eq_mul_frobeniusTheta_of_forall_mem_iff sigma (fun P ↦ ?_) x
  rw [Set.mem_ofPred_eq, mem_primesAboveRamifiedPrimes_iff]
  refine ⟨fun ⟨hP, hram, hdeg⟩ ↦
    ⟨hP, (inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet sigma hP hram).mp hdeg⟩,
    fun ⟨hP, hp⟩ ↦ ?_⟩
  have hram : P.under (𝓞 K) ∉ ramifiedPrimes K L := fun h ↦
    frobeniusPrimeSet_subset_compl_ramifiedPrimes _ hp (Finset.mem_coe.mpr h)
  exact ⟨hP, hram, (inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet sigma hP hram).mpr hp⟩

end NumberField.Chebotarev

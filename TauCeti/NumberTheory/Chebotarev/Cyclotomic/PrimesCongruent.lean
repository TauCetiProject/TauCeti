/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Crossing.CompositumFrobenius
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Basic
public import TauCeti.NumberTheory.Chebotarev.Density.PrimesCongruent
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Cyclotomic Frobenius fibres and arithmetic progressions

Away from the cyclotomic level, the fibre of an automorphism is the set of primes whose norm
reduces to its cyclotomic character. This identifies the arithmetic Frobenius convention with
arithmetic progressions: the residue is the character itself, not its inverse.

For a cyclotomic extension of `ℚ` of odd prime level, the identification holds at every prime:
the only excluded rational prime is totally ramified and its residue is not a unit. In particular,
the four Frobenius fibres of `ℚ(ζ₅)` are precisely the four invertible residue classes modulo five.
Their Dirichlet densities agree with the arithmetic-progression theorem.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
* The Frobenius computation is the existing
  `mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow`, specialized to a trivial lower extension.
-/

public section

open NumberField IsDedekindDomain
open IsCyclotomicExtension

namespace NumberField.Chebotarev

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F]

/-- Away from the level, the cyclotomic Frobenius fibre is characterized by the norm modulo
that level. Unramifiedness follows from the condition on the level. -/
theorem mem_frobeniusPrimeSet_iff_autToPow_eq {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (σ : F ≃ₐ[K] F) {𝔭 : HeightOneSpectrum (𝓞 K)} (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    𝔭 ∈ frobeniusPrimeSet K F (ConjClasses.mk σ) ↔
      (hζ.autToPow K σ : ZMod m) = Ideal.absNorm 𝔭.asIdeal := by
  have hur (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
      Algebra.IsUnramifiedAt (𝓞 K) Q :=
    isUnramifiedAt_of_notMem_cyclotomicModulus_support F m
      (mem_cyclotomicModulus_support_iff.not.mpr hm) Q
  rw [mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow (L := K) hm hur hζ]
  have hself : 𝔭 ∈ frobeniusPrimeSet K K (ConjClasses.mk (σ.restrictNormal K)) := by
    rw [mem_frobeniusPrimeSet_iff]
    have : Subsingleton (ConjClasses (K ≃ₐ[K] K)) := Quot.Subsingleton
    refine ⟨?_, Subsingleton.elim _ _⟩
    have : IsCyclotomicExtension {1} K K :=
      IsCyclotomicExtension.singleton_one_of_algebraMap_bijective fun x ↦ ⟨x, rfl⟩
    intro Q _ _
    exact isUnramifiedAt_of_notMem_cyclotomicModulus_support K 1
      (mem_cyclotomicModulus_support_iff.not.mpr (by simpa using 𝔭.asIdeal.one_notMem)) Q
  exact and_iff_right hself

section Rational

variable (F : Type*) [Field F] [NumberField F] (q : ℕ) [Fact q.Prime]
  [IsCyclotomicExtension {q} ℚ F] [IsGalois ℚ F]

/-- For odd prime level, a cyclotomic Frobenius fibre over `ℚ` is exactly an invertible
arithmetic progression. The prime equal to the level belongs to neither side. -/
theorem frobeniusPrimeSet_cyclotomic_rat_eq_primesCongruent (hq : 2 < q) (a : (ZMod q)ˣ) :
    frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod q F).symm a)) =
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | (Ideal.absNorm 𝔭.asIdeal : ZMod q) = a} := by
  ext 𝔭
  by_cases hm : (q : 𝓞 ℚ) ∈ 𝔭.asIdeal
  · have hnorm : Ideal.absNorm 𝔭.asIdeal = q := by
      rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
      have hdvd : Rat.HeightOneSpectrum.natGenerator 𝔭 ∣ q := by
        rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
        simpa using Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hm
      exact (Nat.dvd_prime (Fact.out : q.Prime)).mp hdvd |>.resolve_left
        (Rat.HeightOneSpectrum.prime_natGenerator 𝔭).ne_one
    have hram : 𝔭 ∉ frobeniusPrimeSet ℚ F
        (ConjClasses.mk ((Rat.galEquivZMod q F).symm a)) := by
      intro h
      obtain ⟨Q, _⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h
      have : Q.1.IsPrime := Q.2.1
      have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
      have hqQ : (q : 𝓞 F) ∈ Q.1 := by
        simpa using (Ideal.mem_of_liesOver Q.1 𝔭.asIdeal (q : 𝓞 ℚ)).mp hm
      have : Q.1.LiesOver (Ideal.span {(q : ℤ)}) := by
        rw [Ideal.liesOver_iff]
        refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime q)
          Ideal.IsPrime.ne_top' ?_
        simpa [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap] using hqQ
      have := isUnramifiedAt_of_mem_frobeniusPrimeSet h Q.1
      have he := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := Q.1)
      rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int Q.1
        (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1),
        Rat.ramificationIdx_eq_of_prime q F Q.1] at he
      omega
    exact iff_of_false hram (by
      simpa only [Set.mem_ofPred_eq, hnorm, ZMod.natCast_self] using a.ne_zero.symm)
  · rw [mem_frobeniusPrimeSet_iff_autToPow_eq (zeta_spec q ℚ F) _ hm]
    -- The canonical Galois equivalence uses the character of `zeta_spec`.
    have hchar : (zeta_spec q ℚ F).autToPow ℚ ((Rat.galEquivZMod q F).symm a) = a :=
      (Rat.galEquivZMod q F).apply_symm_apply a
    simp only [hchar, Set.mem_ofPred_eq, eq_comm]

end Rational

/-- Each of the four arithmetic Frobenius fibres of a fifth cyclotomic field has Dirichlet
density `1/4`, by its identification with the corresponding arithmetic progression modulo five. -/
theorem hasDirichletDensity_frobeniusPrimeSet_cyclotomic_five
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {5} ℚ F] [IsGalois ℚ F]
    (a : (ZMod 5)ˣ) :
    NumberField.Set.HasDirichletDensity
      (frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod 5 F).symm a))) (1 / 4) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [frobeniusPrimeSet_cyclotomic_rat_eq_primesCongruent F 5 (by decide)]
  have ha : IsUnit ((a : ZMod 5).val : ZMod 5) := by simp
  have h := hasDirichletDensity_primesCongruent 5 (a : ZMod 5).val ha
  have hset : {𝔭 : HeightOneSpectrum (𝓞 ℚ) | (Ideal.absNorm 𝔭.asIdeal : ZMod 5) = a} =
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm 𝔭.asIdeal % 5 = (a : ZMod 5).val % 5} := by
    ext 𝔭
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← ZMod.natCast_eq_natCast_iff']
    simp
  rw [hset]
  norm_num [Nat.totient_prime (by decide : Nat.Prime 5)] at h ⊢
  exact h

end NumberField.Chebotarev

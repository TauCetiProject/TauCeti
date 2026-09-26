/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Crossing.CompositumFrobenius
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
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

## References

* L. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
* The Frobenius computation is the existing
  `mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow`, specialized to a trivial lower extension.
-/

public section

open NumberField IsDedekindDomain
open IsCyclotomicExtension

namespace NumberField.Chebotarev

variable (F : Type*) [Field F] [NumberField F] (q : ℕ) [Fact q.Prime]
  [IsCyclotomicExtension {q} ℚ F]

/-- The prime containing an odd prime cyclotomic level ramifies in the cyclotomic field. -/
theorem mem_ramifiedPrimes_of_natCast_mem (hq : 2 < q)
    {𝔭 : HeightOneSpectrum (𝓞 ℚ)} (hm : (q : 𝓞 ℚ) ∈ 𝔭.asIdeal) :
    𝔭 ∈ ramifiedPrimes ℚ F := by
  rw [mem_ramifiedPrimes_iff]
  intro hur
  let Q : 𝔭.asIdeal.primesOver (𝓞 F) := Classical.choice inferInstance
  have : Q.1.IsPrime := Q.2.1
  have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
  have hqQ : (q : 𝓞 F) ∈ Q.1 := by
    simpa using (Ideal.mem_of_liesOver Q.1 𝔭.asIdeal (q : 𝓞 ℚ)).mp hm
  have : Q.1.LiesOver (Ideal.span {(q : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime q)
      Ideal.IsPrime.ne_top' ?_
    simpa [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap] using hqQ
  have := hur Q.1
  have he := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := Q.1)
  rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int Q.1
    (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1),
    Rat.ramificationIdx_eq_of_prime q F Q.1] at he
  omega

variable [IsGalois ℚ F]

/-- For odd prime level, a cyclotomic Frobenius fibre over `ℚ` is exactly an invertible
arithmetic progression. The prime equal to the level belongs to neither side. -/
theorem frobeniusPrimeSet_galEquivZMod_symm_eq_primesCongruent (hq : 2 < q)
    (a : (ZMod q)ˣ) :
    frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod q F).symm a)) =
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | (Ideal.absNorm 𝔭.asIdeal : ZMod q) = a} := by
  ext 𝔭
  by_cases hm : (q : 𝓞 ℚ) ∈ 𝔭.asIdeal
  · have hnorm := Rat.HeightOneSpectrum.absNorm_asIdeal_eq_of_natCast_mem 𝔭 hm
    have hram : 𝔭 ∉ frobeniusPrimeSet ℚ F
        (ConjClasses.mk ((Rat.galEquivZMod q F).symm a)) := fun h ↦
      frobeniusPrimeSet_subset_compl_ramifiedPrimes _ h
        (mem_ramifiedPrimes_of_natCast_mem F q hq hm)
    exact iff_of_false hram (by
      simpa only [Set.mem_ofPred_eq, hnorm, ZMod.natCast_self] using a.ne_zero.symm)
  · rw [mem_frobeniusPrimeSet_mk_iff_autToPow_eq_absNorm (zeta_spec q ℚ F) _ hm,
      (zeta_spec q ℚ F).autToPow_eq_unitsMap_galEquivZMod dvd_rfl,
      ZMod.unitsMap_self, MonoidHom.id_apply, MulEquiv.apply_symm_apply]
    simp only [Set.mem_ofPred_eq, eq_comm]

end NumberField.Chebotarev

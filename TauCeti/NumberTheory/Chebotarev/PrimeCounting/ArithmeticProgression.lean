/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt
public import TauCeti.NumberTheory.Chebotarev.PrimesCongruent
import TauCeti.NumberTheory.Chebotarev.CyclotomicRamification

/-!
# Cyclotomic Frobenius von Mangoldt coefficients and arithmetic progressions

Over `ℚ` there is exactly one ideal of each norm, so for a Galois extension `L / ℚ` the Frobenius
von Mangoldt coefficient at `p ^ (k + 1)` is the powered Frobenius weight of the single prime power
`𝔭 ^ (k + 1)` of norm `p ^ (k + 1)`. For a cyclotomic field `F = ℚ(ζₙ)` the Artin class of a prime
`p ∤ n` is the class of the automorphism with cyclotomic character `p mod n`, so `𝔭 ^ (k + 1)` lies
in the powered fibre tagged by a unit `a` exactly when `p ^ (k + 1) ≡ a (mod n)`. Consequently the
Frobenius von Mangoldt coefficient of the fibre tagged by `a` is the classical von Mangoldt
function `Λ` restricted to the progression `m ≡ a (mod n)`. This is the prime-power counterpart of
`NumberField.Chebotarev.frobeniusPrimeSet_galEquivZMod_symm_eq_setOf_natCast_absNorm_eq`, which
identifies the unpowered fibres with arithmetic progressions of primes.

The fifth cyclotomic field is the smallest test of the power in the coefficient. There `2` has
order four modulo `5`, so the Frobenius `g` at `2` generates the cyclic Galois group of order
four. The term `log 2` at `2` lies in the fibre of `g`, while the term `log 2` at `4 = 2 ^ 2` lies
in the fibre of the class `[g] ^ 2` and not in that of `g`. A coefficient testing only the
unpowered Frobenius class would put the second term in the fibre of `g`.

## Main results

* `NumberField.Chebotarev.idealPrimePowerOf_mem_frobeniusPrimePowerSet_galEquivZMod_symm_iff`:
  away from the level, `𝔭 ^ (k + 1)` lies in the cyclotomic fibre tagged by `a` exactly when
  `N(𝔭) ^ (k + 1) ≡ a (mod n)`.
* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff_galEquivZMod_symm_of_coprime`: at every level,
  the cyclotomic coefficient tagged by `a` agrees with `Λ` on the progression `m ≡ a (mod n)` and
  vanishes off it, at every `m` prime to the level.
* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff_galEquivZMod_symm`: when `n % 4 ≠ 2`, this
  holds at every `m`.
* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff_cyclotomic_five_of_galEquivZMod_eq_two`: the
  degree-four test in the fifth cyclotomic field.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, Chapter 2, for cyclotomic Frobenius.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13, for the Frobenius von Mangoldt
  coefficient.
-/

public section

open IsDedekindDomain IsCyclotomicExtension TauCeti
open scoped NumberField ArithmeticFunction.vonMangoldt IsMulCommutative

namespace NumberField.Chebotarev

variable (F : Type*) [Field F] [NumberField F] (n : ℕ) [NeZero n]
  [IsCyclotomicExtension {n} ℚ F] [IsGalois ℚ F]

/-- Away from the level, the prime power `𝔭 ^ (k + 1)` of `𝓞 ℚ` lies in the powered cyclotomic
Frobenius fibre tagged by a unit `a` modulo `n` exactly when `N(𝔭) ^ (k + 1) ≡ a (mod n)`. -/
theorem idealPrimePowerOf_mem_frobeniusPrimePowerSet_galEquivZMod_symm_iff
    {𝔭 : HeightOneSpectrum (𝓞 ℚ)} (hm : (n : 𝓞 ℚ) ∉ 𝔭.asIdeal) (a : (ZMod n)ˣ) (k : ℕ) :
    𝔭.idealPrimePowerOf k ∈
        frobeniusPrimePowerSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod n F).symm a)) ↔
      ((Rat.HeightOneSpectrum.natGenerator 𝔭 ^ (k + 1) : ℕ) : ZMod n) = a := by
  have hcop : (Rat.HeightOneSpectrum.natGenerator 𝔭).Coprime n := by
    rw [Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd,
      Rat.HeightOneSpectrum.absNorm_asIdeal] at hm
    exact (Nat.Prime.coprime_iff_not_dvd (Rat.HeightOneSpectrum.prime_natGenerator 𝔭)).mpr hm
  -- The Artin class of `𝔭` is tagged by the unit `N(𝔭) mod n`.
  set u := ZMod.unitOfCoprime _ hcop
  have h𝔭 : 𝔭 ∈ frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod n F).symm u)) := by
    rw [mem_frobeniusPrimeSet_galEquivZMod_symm_iff F n hm, Rat.HeightOneSpectrum.absNorm_asIdeal,
      ZMod.coe_unitOfCoprime]
  have hpow : ConjClasses.mk ((Rat.galEquivZMod n F).symm u) ^ (k + 1) =
      ConjClasses.mk ((Rat.galEquivZMod n F).symm a) ↔
        ((Rat.HeightOneSpectrum.natGenerator 𝔭 ^ (k + 1) : ℕ) : ZMod n) = a := by
    -- The Galois group of `ℚ(ζₙ)` is abelian, so its conjugacy classes are singletons.
    have := IsCyclotomicExtension.isMulCommutative {n} ℚ F
    rw [ConjClasses.mk_pow, ← map_pow, ConjClasses.mk_injective.eq_iff, MulEquiv.apply_eq_iff_eq,
      Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_pow]
  obtain ⟨hur, hart⟩ := mem_frobeniusPrimeSet_iff.mp h𝔭
  rw [mem_frobeniusPrimePowerSet_iff, HeightOneSpectrum.primePowerExponent_idealPrimePowerOf,
    HeightOneSpectrum.primePowerBase_idealPrimePowerOf, ← hpow, ← hart]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hur, h⟩⟩

/-- **The cyclotomic Frobenius von Mangoldt coefficient on a progression.** At every level `n`,
the Frobenius von Mangoldt coefficient of the fibre of `ℚ(ζₙ) / ℚ` tagged by a unit `a` agrees,
at every `m` prime to `n`, with the von Mangoldt function `Λ` restricted to the progression
`m ≡ a (mod n)`. -/
theorem frobeniusVonMangoldtCoeff_galEquivZMod_symm_of_coprime (a : (ZMod n)ˣ) {m : ℕ}
    (hm : m.Coprime n) :
    frobeniusVonMangoldtCoeff ℚ F (ConjClasses.mk ((Rat.galEquivZMod n F).symm a)) m =
      if (m : ZMod n) = a then Λ m else 0 := by
  by_cases hpp : IsPrimePow m
  swap
  · rw [frobeniusVonMangoldtCoeff_eq_zero_of_not_isPrimePow _ hpp,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, ite_self]
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hj.ne'
  obtain ⟨𝔭, h𝔭⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
  rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at h𝔭
  subst h𝔭
  have hn : (n : 𝓞 ℚ) ∉ 𝔭.asIdeal := by
    rw [Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd,
      Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left
      (dvd_pow_self _ k.succ_ne_zero) hm)
  rw [frobeniusVonMangoldtCoeff_rat_natGenerator_pow,
    ArithmeticFunction.vonMangoldt_apply_pow k.succ_ne_zero,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  split_ifs with ha
  · rw [frobeniusPrimePowerWeight_of_mem
      ((idealPrimePowerOf_mem_frobeniusPrimePowerSet_galEquivZMod_symm_iff F n hn a k).mpr ha),
      primePowerWeight_eq_vonMangoldt_re, IdealArithmeticFunction.vonMangoldt_apply_of_eq_prime_pow
      (Ideal.prime_of_isPrime 𝔭.ne_bot 𝔭.isPrime) k.succ_pos (𝔭.coe_idealPrimePowerOf k).symm,
      Complex.ofReal_re, Rat.HeightOneSpectrum.absNorm_asIdeal]
  · exact frobeniusPrimePowerWeight_of_notMem fun hmem ↦ ha
      ((idealPrimePowerOf_mem_frobeniusPrimePowerSet_galEquivZMod_symm_iff F n hn a k).mp hmem)

/-- **The cyclotomic Frobenius von Mangoldt coefficient is `Λ` on a progression.** At a level
`n` with `n % 4 ≠ 2`, the Frobenius von Mangoldt coefficient of the fibre of `ℚ(ζₙ) / ℚ` tagged by
a unit `a` is the von Mangoldt function `Λ` restricted to the progression `m ≡ a (mod n)`.

The primes dividing such a level ramify in `ℚ(ζₙ)`, and their powers are not units modulo `n`, so
both sides vanish there. Levels `n ≡ 2 (mod 4)` are excluded: there the prime `2` is unramified
while `2 ^ j` is not a unit modulo `n`, so the identity can fail at powers of `2`. At every level,
`frobeniusVonMangoldtCoeff_galEquivZMod_symm_of_coprime` covers the inputs `m` coprime to `n`. -/
theorem frobeniusVonMangoldtCoeff_galEquivZMod_symm (hn : n % 4 ≠ 2) (a : (ZMod n)ˣ) (m : ℕ) :
    frobeniusVonMangoldtCoeff ℚ F (ConjClasses.mk ((Rat.galEquivZMod n F).symm a)) m =
      if (m : ZMod n) = a then Λ m else 0 := by
  by_cases hm : m.Coprime n
  · exact frobeniusVonMangoldtCoeff_galEquivZMod_symm_of_coprime F n a hm
  by_cases hpp : IsPrimePow m
  swap
  · rw [frobeniusVonMangoldtCoeff_eq_zero_of_not_isPrimePow _ hpp,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, ite_self]
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hj.ne'
  -- `m` is a power of a prime dividing the level, which is not a unit modulo `n`.
  have hpn : p ∣ n := by
    by_contra hpn
    exact hm (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn))
  have ha : ((p ^ (k + 1) : ℕ) : ZMod n) ≠ a := fun ha ↦
    hm ((ZMod.isUnit_iff_coprime _ n).mp (ha ▸ a.isUnit))
  obtain ⟨𝔭, h𝔭⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
  -- The prime `𝔭` above `p` ramifies in `ℚ(ζₙ)`, so it carries no Artin class.
  have hram : 𝔭 ∈ ramifiedPrimes ℚ F := mem_ramifiedPrimes_of_natCast_mem F n
    (fun h2 ↦ by rw [h𝔭] at h2; subst h2; omega)
    ((Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mpr (h𝔭 ▸ hpn))
  rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at h𝔭
  subst h𝔭
  rw [ite_eq_right ha, frobeniusVonMangoldtCoeff_rat_natGenerator_pow]
  refine frobeniusPrimePowerWeight_of_notMem fun hmem ↦ ?_
  obtain ⟨hur, -⟩ := mem_frobeniusPrimePowerSet_iff.mp hmem
  rw [HeightOneSpectrum.primePowerBase_idealPrimePowerOf] at hur
  exact frobeniusPrimeSet_subset_compl_ramifiedPrimes _ (mem_frobeniusPrimeSet_artinSymbol hur) hram

/-- **The degree-four test of the powered Frobenius filter.** In a fifth cyclotomic field, let `g`
be the automorphism with cyclotomic character `2`, the arithmetic Frobenius at `2`. It has order
four, so it generates the Galois group. The term `log 2` at `2` lies in the fibre of `g`, while the
term `log 2` at `4 = 2 ^ 2` lies in the fibre of the squared class `[g] ^ 2` and not in the fibre
of `g` itself. -/
theorem frobeniusVonMangoldtCoeff_cyclotomic_five_of_galEquivZMod_eq_two
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {5} ℚ F] [IsGalois ℚ F]
    {g : F ≃ₐ[ℚ] F} (hg : (Rat.galEquivZMod 5 F g : ZMod 5) = 2) :
    orderOf g = 4 ∧
      frobeniusVonMangoldtCoeff ℚ F (ConjClasses.mk g) 2 = Real.log 2 ∧
      frobeniusVonMangoldtCoeff ℚ F (ConjClasses.mk g) 4 = 0 ∧
      frobeniusVonMangoldtCoeff ℚ F (ConjClasses.mk g ^ 2) 4 = Real.log 2 := by
  have hg' : Rat.galEquivZMod 5 F g = ZMod.unitOfCoprime 2 (by decide) := Units.ext hg
  have hcoeff (b : (ZMod 5)ˣ) (m : ℕ) :=
    frobeniusVonMangoldtCoeff_galEquivZMod_symm F 5 (by decide) b m
  rw [← (Rat.galEquivZMod 5 F).symm_apply_apply g, hg']
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  · rw [hcoeff, ite_eq_left (by decide), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      Nat.cast_ofNat]
  · rw [hcoeff, ite_eq_right (by decide)]
  · have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [ConjClasses.mk_pow, ← map_pow, hcoeff, ite_eq_left (by decide),
      h4, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]

end NumberField.Chebotarev

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Crossing.CompositumFrobenius
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.Chebotarev.CyclotomicRamification
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification

/-!
# Cyclotomic Frobenius fibres and arithmetic progressions

Away from the cyclotomic level, the fibre of an automorphism is the set of primes whose norm
reduces to its cyclotomic character. This identifies the arithmetic Frobenius convention with
arithmetic progressions: the residue is the character itself, not its inverse.

For a cyclotomic extension of `ℚ` of nonzero level `n` with `n % 4 ≠ 2`, the identification
holds at every prime: primes dividing the level ramify and their residues are not units.
The restriction excludes levels twice an odd number, where `2` is unramified. In particular,
the four Frobenius fibres of `ℚ(ζ₅)` are precisely the four invertible residue classes modulo five.
At every nonzero level the symmetric difference is finite, which suffices to transfer density
from Frobenius fibres to arithmetic progressions.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
* The Frobenius computation is the existing
  `mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow`, specialized to a trivial lower extension.
-/

public section

open NumberField IsDedekindDomain
open IsCyclotomicExtension

namespace NumberField.Chebotarev

section Cyclotomic

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} [NeZero m]
  {F : Type*} [Field F] [NumberField F] [Algebra K F] [IsGalois K F]
  [IsCyclotomicExtension {m} K F]

/-- Away from the level, the cyclotomic Frobenius fibre is characterized by the norm modulo
that level. Unramifiedness follows from the condition on the level. -/
theorem mem_frobeniusPrimeSet_mk_iff_autToPow_eq_absNorm {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (σ : F ≃ₐ[K] F) {𝔭 : HeightOneSpectrum (𝓞 K)} (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    𝔭 ∈ frobeniusPrimeSet K F (ConjClasses.mk σ) ↔
      (hζ.autToPow K σ : ZMod m) = Ideal.absNorm 𝔭.asIdeal := by
  have hur (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
      Algebra.IsUnramifiedAt (𝓞 K) Q :=
    IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem F m hm Q
  rw [mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow (L := K) hm hur hζ]
  exact and_iff_right (mem_frobeniusPrimeSet_self 𝔭 _)

end Cyclotomic

variable (F : Type*) [Field F] [NumberField F] (n : ℕ) [NeZero n]
  [IsCyclotomicExtension {n} ℚ F]

variable [IsGalois ℚ F]

/-- At a nonzero level not congruent to two modulo four, a cyclotomic Frobenius fibre over
`ℚ` is exactly an invertible arithmetic progression. Primes dividing the level belong to neither
side. -/
-- Rewrite before simp expands the inverse cyclotomic Galois equivalence.
@[simp↓]
theorem frobeniusPrimeSet_galEquivZMod_symm_eq_setOf_natCast_absNorm_eq (hn : n % 4 ≠ 2)
    (a : (ZMod n)ˣ) :
    frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod n F).symm a)) =
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | (Ideal.absNorm 𝔭.asIdeal : ZMod n) = a} := by
  ext 𝔭
  by_cases hm : (n : 𝓞 ℚ) ∈ 𝔭.asIdeal
  · have hram : 𝔭 ∉ frobeniusPrimeSet ℚ F
        (ConjClasses.mk ((Rat.galEquivZMod n F).symm a)) := fun h ↦
      frobeniusPrimeSet_subset_compl_ramifiedPrimes _ h
        (mem_ramifiedPrimes_of_natCast_mem F n (fun h2 ↦ by
          have := (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mp hm
          rw [h2] at this
          omega) hm)
    refine iff_of_false hram fun ha ↦ ?_
    have hcop := (ZMod.isUnit_iff_coprime (Ideal.absNorm 𝔭.asIdeal) n).mp
      (ha.symm ▸ a.isUnit)
    have hdvd := (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mp hm
    have hp := Rat.HeightOneSpectrum.prime_natGenerator 𝔭
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hcop hdvd
    exact (hp.coprime_iff_not_dvd.mp hcop) hdvd
  · rw [mem_frobeniusPrimeSet_mk_iff_autToPow_eq_absNorm (zeta_spec n ℚ F) _ hm,
      (zeta_spec n ℚ F).autToPow_eq_unitsMap_galEquivZMod dvd_rfl,
      ZMod.unitsMap_self, MonoidHom.id_apply, MulEquiv.apply_symm_apply]
    simp only [Set.mem_ofPred_eq, eq_comm]

/-- At every nonzero level, the cyclotomic Frobenius fibre differs from its arithmetic
progression at only finitely many primes. This includes levels congruent to two modulo four,
where the prime above two can lie in the Frobenius fibre without lying in the progression. -/
theorem finite_symmDiff_frobeniusPrimeSet_galEquivZMod_symm (a : (ZMod n)ˣ) :
    (symmDiff
      (frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod n F).symm a)))
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | (Ideal.absNorm 𝔭.asIdeal : ZMod n) = a}).Finite := by
  have hn : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    simpa using (NeZero.ne (n : 𝓞 ℚ))
  refine (Ideal.finite_factors hn).subset fun 𝔭 h𝔭 ↦ ?_
  rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
  by_contra hm
  have hiff := mem_frobeniusPrimeSet_mk_iff_autToPow_eq_absNorm
    (zeta_spec n ℚ F) ((Rat.galEquivZMod n F).symm a) hm
  rw [(zeta_spec n ℚ F).autToPow_eq_unitsMap_galEquivZMod dvd_rfl,
    ZMod.unitsMap_self, MonoidHom.id_apply, MulEquiv.apply_symm_apply] at hiff
  rcases h𝔭 with ⟨hmem, hnot⟩ | ⟨hmem, hnot⟩
  · exact hnot (hiff.mp hmem).symm
  · exact hnot (hiff.mpr hmem.symm)

end NumberField.Chebotarev

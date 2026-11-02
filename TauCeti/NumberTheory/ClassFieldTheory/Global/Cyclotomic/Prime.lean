/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Frobenius
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Global Artin symbols in cyclotomic fields

At a prime not dividing the cyclotomic level, the global Artin symbol raises roots of unity
to the absolute norm of the prime. Over the rationals its cyclotomic coordinate is therefore
the residue class of the rational prime. In the fifth cyclotomic field the symbol at `2`
sends a primitive root to its square and has order four, distinguishing arithmetic Frobenius
from geometric Frobenius.

The maps are the existing global Artin map and Mathlib's `galEquivZMod`; no separate
cyclotomic reciprocity map is constructed.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3, and Chapter VII, Example 8.2.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public noncomputable section

open IsDedekindDomain NumberField IsCyclotomicExtension

namespace TauCeti.ClassFieldTheory

variable {m : ℕ} {K E : Type} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E] [IsCyclotomicExtension {m} K E] [IsGalois K E]

/-- The global Artin symbol at a prime not dividing the cyclotomic level raises every root
of unity of that level to the absolute norm of the prime. No primitivity is required. -/
theorem globalArtinMap_cyclotomic_prime (ι : E →ₐ[K] SeparableClosure K)
    {ζ : E} (hζ : ζ ^ m = 1) (v : HeightOneSpectrum (𝓞 K))
    (hm : (m : 𝓞 K) ∉ v.asIdeal) {σ : E ≃ₐ[K] E}
    (hσ : globalArtinMap K E ι (.ofMul (primeIdeleClass K v)) =
      .ofMul (Abelianization.of σ)) :
    σ ζ = ζ ^ Ideal.absNorm v.asIdeal := by
  classical
  let _ := IsCyclotomicExtension.isAbelianGalois {m} K E
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
  have := IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem E m hm Q
  exact (globalArtinMap_isArithFrobAt E ι v Q hσ).apply_eq_pow_absNorm_of_pow_eq_one hζ v hm Q

variable [NeZero m] [IsCyclotomicExtension {m} ℚ E] [IsGalois ℚ E]

/-- In a rational cyclotomic field, the coordinate of the global Artin symbol at a prime
not dividing the level is the absolute norm of that prime modulo the level. -/
theorem galEquivZMod_globalArtinMap_prime (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hm : (m : 𝓞 ℚ) ∉ v.asIdeal) {σ : E ≃ₐ[ℚ] E}
    (hσ : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) =
      .ofMul (Abelianization.of σ)) :
    (Rat.galEquivZMod m E σ : ZMod m) = Ideal.absNorm v.asIdeal := by
  let _ := IsCyclotomicExtension.isAbelianGalois {m} ℚ E
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
  have := IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem E m hm Q
  exact (TauCeti.NumberField.isArithFrobAt_iff_galEquivZMod_eq_absNorm v hm Q σ).1
    (globalArtinMap_isArithFrobAt E ι v Q hσ)

/-- In the fifth cyclotomic field, the global Artin symbol at `2` sends a primitive fifth
root to its square and has order four: its square is nontrivial and its fourth power is one. -/
theorem globalArtinMap_zeta5_two (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {5} ℚ E] [IsGalois ℚ E] (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Ideal.absNorm v.asIdeal = 2) {σ : E ≃ₐ[ℚ] E}
    (hσ : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) =
      .ofMul (Abelianization.of σ)) :
    σ ζ = ζ ^ 2 ∧ σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  have hm : (5 : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    have hd := (_root_.Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd v
      (n := 5)).mp h
    rw [hv] at hd
    norm_num at hd
  have hc : (Rat.galEquivZMod 5 E σ : ZMod 5) = 2 := by
    simpa only [hv, Nat.cast_ofNat] using galEquivZMod_globalArtinMap_prime ι v hm hσ
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hv] using globalArtinMap_cyclotomic_prime ι hζ.pow_eq_one v hm hσ
  · apply (Rat.galEquivZMod 5 E).injective
    apply Units.ext
    simp only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one, hc]
    decide
  · intro h
    have h' := congrArg (fun τ ↦ (Rat.galEquivZMod 5 E τ : ZMod 5)) h
    simp only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one, hc] at h'
    exact (by decide : (4 : ZMod 5) ≠ 1) h'

end TauCeti.ClassFieldTheory

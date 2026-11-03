/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Prime
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Global Artin symbols in the Gaussian rationals

For the fourth cyclotomic field over `ℚ`, the global Artin symbol of an odd prime is the
identity at primes congruent to `1` modulo `4`, and complex conjugation at primes congruent
to `3` modulo `4`. Conjugation is the existing cyclotomic automorphism with coordinate `-1`
under `IsCyclotomicExtension.Rat.galEquivZMod`; no second reciprocity map is constructed.

`globalArtinMap_Qi_prime` computes the actual abelianization-valued global Artin map.
`globalArtinMap_Qi_prime_apply` computes its action on any primitive fourth root, and
`globalArtinMap_Qi_prime_eq_zero_iff` characterizes triviality of the symbol.
The hypothesis that `4` does not belong to the prime ideal excludes precisely the ramified
prime `2`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3, and Chapter VII, Example 8.2.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public noncomputable section

open IsDedekindDomain NumberField IsCyclotomicExtension
open scoped IsMulCommutative

namespace TauCeti.ClassFieldTheory

variable {E : Type} [Field E] [NumberField E] [IsCyclotomicExtension {4} ℚ E]

local instance : IsGalois ℚ E := IsCyclotomicExtension.isGalois {4} ℚ E

/-- **The global Artin symbol in `ℚ(i)`.** At an odd prime it is the identity if the rational
prime is `1` modulo `4`, and otherwise it is conjugation, the cyclotomic automorphism with
coordinate `-1`. -/
theorem globalArtinMap_Qi_prime (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hm : (4 : 𝓞 ℚ) ∉ v.asIdeal) :
    globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) =
      if Ideal.absNorm v.asIdeal % 4 = 1 then 0
      else .ofMul (Abelianization.of ((Rat.galEquivZMod 4 E).symm (-1))) := by
  let _ := IsCyclotomicExtension.isAbelianGalois {4} ℚ E
  obtain ⟨σ, hσ⟩ := Abelianization.equivOfComm.surjective
    (globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v))).toMul
  have hs : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) =
      .ofMul (Abelianization.of σ) := by
    simpa only [Abelianization.equivOfComm_apply, ofMul_toMul] using
      congrArg Additive.ofMul hσ.symm
  have hc := galEquivZMod_globalArtinMap_prime ι v hm hs
  have hval : ((Rat.galEquivZMod 4 E σ : ZMod 4)).val = Ideal.absNorm v.asIdeal % 4 := by
    rw [hc, ZMod.val_natCast]
  have hu : Rat.galEquivZMod 4 E σ = 1 ∨ Rat.galEquivZMod 4 E σ = -1 :=
    (by decide : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1) _
  rcases hu with hu | hu
  · have hrem : Ideal.absNorm v.asIdeal % 4 = 1 := by
      rw [hu] at hval
      exact hval.symm
    have hσ1 : σ = 1 := (Rat.galEquivZMod 4 E).injective (hu.trans (map_one _).symm)
    rw [ite_eq_left hrem, hs, hσ1, map_one, ofMul_one]
  · have hrem : Ideal.absNorm v.asIdeal % 4 = 3 := by
      rw [hu] at hval
      exact hval.symm
    have hσneg : σ = (Rat.galEquivZMod 4 E).symm (-1) :=
      (Rat.galEquivZMod 4 E).injective (hu.trans (MulEquiv.apply_symm_apply _ _).symm)
    rw [ite_eq_right (by omega), hs, hσneg]

/-- An odd prime idele class has trivial Artin symbol in `ℚ(i)` exactly when the rational
prime is `1` modulo `4`. The simplifier instead normalizes this equality to membership in
the norm subgroup using `globalArtinMap_eq_zero_iff`. -/
theorem globalArtinMap_Qi_prime_eq_zero_iff (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hm : (4 : 𝓞 ℚ) ∉ v.asIdeal) :
    globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) = 0 ↔
      Ideal.absNorm v.asIdeal % 4 = 1 := by
  let _ := IsCyclotomicExtension.isAbelianGalois {4} ℚ E
  have hn : Abelianization.of ((Rat.galEquivZMod 4 E).symm (-1)) ≠ 1 := by
    intro h
    have h' : (Rat.galEquivZMod 4 E).symm (-1) = 1 :=
      Abelianization.equivOfComm.injective (by
        simpa only [Abelianization.equivOfComm_apply, map_one] using h)
    have h'' := congrArg (Rat.galEquivZMod 4 E) h'
    rw [MulEquiv.apply_symm_apply, map_one] at h''
    exact (by decide : (-1 : (ZMod 4)ˣ) ≠ 1) h''
  rw [globalArtinMap_Qi_prime ι v hm]
  split_ifs with h
  · exact iff_of_true rfl h
  · simp only [ofMul_eq_zero, hn, false_iff]
    exact h

/-- **The action of a Gaussian Artin symbol on `i`.** Any automorphism representing the
symbol of an odd prime sends a primitive fourth root to itself at primes `1` modulo `4`,
and to its negative at primes `3` modulo `4`. -/
theorem globalArtinMap_Qi_prime_apply (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    {ζ : E} (hζ : IsPrimitiveRoot ζ 4) (v : HeightOneSpectrum (𝓞 ℚ))
    (hm : (4 : 𝓞 ℚ) ∉ v.asIdeal) {σ : E ≃ₐ[ℚ] E}
    (hσ : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) =
      .ofMul (Abelianization.of σ)) :
    σ ζ = if Ideal.absNorm v.asIdeal % 4 = 1 then ζ else -ζ := by
  let _ := IsCyclotomicExtension.isAbelianGalois {4} ℚ E
  have heq := (globalArtinMap_Qi_prime ι v hm).symm.trans hσ
  split_ifs at heq ⊢ with h
  · have hs : σ = 1 := Abelianization.equivOfComm.injective (by
      simpa only [ofMul_one, Abelianization.equivOfComm_apply, map_one] using
        (Additive.ofMul.injective heq).symm)
    simp only [hs, AlgEquiv.one_apply]
  · have hs : σ = (Rat.galEquivZMod 4 E).symm (-1) :=
      Abelianization.equivOfComm.injective (Additive.ofMul.injective heq).symm
    rw [hs, Rat.galEquivZMod_apply_of_pow_eq 4 E _ hζ.pow_eq_one]
    rw [MulEquiv.apply_symm_apply]
    norm_num only [Units.val_neg, Units.val_one, ZMod.val_neg_one]
    rw [pow_succ, hζ.sq_eq_neg_one, neg_one_mul]

end TauCeti.ClassFieldTheory

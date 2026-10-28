/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Frobenius
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

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
open scoped nonZeroDivisors

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
  have hv : v ∉ TauCeti.NumberField.ramifiedSupport K E := by
    rw [TauCeti.NumberField.mem_ramifiedSupport,
      TauCeti.dvd_relDiscr_iff_exists_not_isUnramifiedAt v.ne_bot]
    rintro ⟨Q, hQ⟩
    exact hQ (IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem E m hm Q)
  let I : NumberFieldArithmetic.idealsAway K (TauCeti.NumberField.ramifiedSupport K E) :=
    ⟨v.unitOfPrime K, by
      rw [NumberFieldArithmetic.mem_idealsAway_iff]
      intro w hw
      rw [v.coe_unitOfPrime K]
      exact FractionalIdeal.count_maximal_coprime K w (fun h ↦ hv (h ▸ hw))⟩
  have hideal := globalArtinMap_ideal E ι (TauCeti.NumberField.ramifiedSupport K E)
    TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v hv I (v.coe_unitOfPrime K)
  let τ := NumberFieldArithmetic.artinHomAway (L := E) algEquiv_commute_of_isAbelianGalois
    (TauCeti.NumberField.ramifiedSupport K E)
    TauCeti.NumberField.isUnramifiedAway_ramifiedSupport I
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
  have := IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem E m hm Q
  obtain ⟨φ, hφ⟩ := NumberField.exists_isArithFrobAt K Q
    (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have hτ : τ = φ := NumberFieldArithmetic.artinHomAway_apply_prime _ _
    TauCeti.NumberField.isUnramifiedAway_ramifiedSupport I v hv (v.coe_unitOfPrime K) Q φ hφ
  have hinj : Function.Injective (Abelianization.of (G := E ≃ₐ[K] E)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [Abelianization.ker_of, commutator_eq_bot])
  have heq : σ = τ := hinj (Additive.ofMul.injective (hσ.symm.trans hideal))
  rw [heq, hτ]
  exact hφ.apply_eq_pow_absNorm_of_pow_eq_one hζ v hm Q

variable [NeZero m] [IsCyclotomicExtension {m} ℚ E] [IsGalois ℚ E]

/-- In a rational cyclotomic field, the coordinate of the global Artin symbol at a prime
not dividing the level is the absolute norm of that prime modulo the level. -/
theorem galEquivZMod_globalArtinMap_prime (ι : E →ₐ[ℚ] SeparableClosure ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hm : (m : 𝓞 ℚ) ∉ v.asIdeal) {σ : E ≃ₐ[ℚ] E}
    (hσ : globalArtinMap ℚ E ι (.ofMul (primeIdeleClass ℚ v)) =
      .ofMul (Abelianization.of σ)) :
    (Rat.galEquivZMod m E σ : ZMod m) = Ideal.absNorm v.asIdeal := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ E
  have h := hζ.coe_autToPow_eq_natCast (globalArtinMap_cyclotomic_prime ι hζ.pow_eq_one v hm hσ)
  rwa [hζ.autToPow_eq_unitsMap_galEquivZMod dvd_rfl, ZMod.unitsMap_self,
    MonoidHom.id_apply] at h

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

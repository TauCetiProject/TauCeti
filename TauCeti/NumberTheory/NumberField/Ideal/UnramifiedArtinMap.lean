/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Ideal.ArtinMap

/-!
# The Artin map of an everywhere-unramified extension

For an abelian Galois extension of number fields `L / K` which is unramified at every finite
prime, the ideal-theoretic Artin map is defined on the full group of invertible fractional ideals
of `K`. This file packages that specialization of `artinHomAway` without an artificial excluded
set.

The equivalence `idealsAwayEmptyEquiv` identifies ideals away from the empty set with all
invertible fractional ideals. Transporting `artinHomAway` across it gives `unramifiedArtinHom`.
Its API records the product formula, its value on a prime, determination by those prime values,
functoriality under restriction to an intermediate field, and the restriction to nonzero integral
ideals.

This is the natural Artin map for Hilbert and genus fields: their extensions over the base field
are unramified at every finite prime, so every ideal has an Artin automorphism.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter VI, §7.

## Main definitions

* `TauCeti.NumberFieldArithmetic.idealsAwayEmptyEquiv`: ideals away from no primes are all
  invertible fractional ideals.
* `TauCeti.NumberFieldArithmetic.unramifiedArtinHom`: the Artin map on all invertible fractional
  ideals in an everywhere-unramified abelian extension.
* `TauCeti.NumberFieldArithmetic.unramifiedArtinHomIntegral`: its restriction to nonzero integral
  ideals.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField IsMulCommutative

namespace TauCeti.NumberFieldArithmetic

variable {K : Type*} [Field K] [NumberField K]

/-! ### The unrestricted Artin map -/

section UnramifiedArtinHom

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (hur : ∀ (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- **The Artin map of an everywhere-unramified abelian extension.** This is the Artin map away
from the empty set, transported to the full group of invertible fractional ideals. -/
noncomputable def unramifiedArtinHom :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (L ≃ₐ[K] L) :=
  (artinHomAway (L := L) hab ∅ (fun v _ Q _ _ ↦ hur v Q)).comp
    idealsAwayEmptyEquiv.symm.toMonoidHom

/-- The unrestricted Artin map is the Artin map away from the empty set under the canonical
equivalence of their domains. -/
@[simp]
theorem unramifiedArtinHom_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    unramifiedArtinHom (L := L) hab hur I =
      artinHomAway (L := L) hab ∅ (fun v _ Q _ _ ↦ hur v Q)
        (idealsAwayEmptyEquiv.symm I) :=
  (rfl)

/-- **The unrestricted Artin map is the product of local Artin automorphisms.** The exponent at a
finite prime is its multiplicity in the fractional ideal. -/
theorem unramifiedArtinHom_apply_eq_finprod (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    unramifiedArtinHom (L := L) hab hur I =
      letI := isMulCommutative_galoisGroup_of_commute hab
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        artinElement hab v.asIdeal (hur v) ^
          FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [unramifiedArtinHom_apply, artinHomAway_apply]
  let _ := isMulCommutative_galoisGroup_of_commute hab
  rw [coe_idealsAwayEmptyEquiv_symm_apply]
  apply finprod_congr
  intro v
  rw [artinElementAway_eq_artinElement hab ∅ (fun w _ Q _ _ ↦ hur w Q) (by simp)]

/-- **The unrestricted Artin map sends a prime ideal to its Frobenius.** -/
theorem unramifiedArtinHom_apply_prime (v : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (σ : L ≃ₐ[K] L) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    unramifiedArtinHom (L := L) hab hur (v.unitOfPrime K) = σ := by
  rw [unramifiedArtinHom_apply]
  have hprime : (((idealsAwayEmptyEquiv.symm (v.unitOfPrime K) :
      idealsAway (K := K) ∅) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = v.asIdeal :=
    congrArg (fun I : (FractionalIdeal (𝓞 K)⁰ K)ˣ ↦
      (I : FractionalIdeal (𝓞 K)⁰ K))
        (coe_idealsAwayEmptyEquiv_symm_apply (v.unitOfPrime K)) |>.trans
          (v.coe_unitOfPrime K)
  exact artinHomAway_apply_prime hab ∅ (fun w _ P _ _ ↦ hur w P)
    (idealsAwayEmptyEquiv.symm (v.unitOfPrime K)) v (by simp)
    hprime Q σ hσ

/-- **Prime values determine the unrestricted Artin map.** A homomorphism on fractional ideals
which takes every prime ideal to its Frobenius is the Artin map. -/
theorem unramifiedArtinHom_eq_of_apply_prime
    (φ : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (L ≃ₐ[K] L))
    (hφ : ∀ (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L))
      (_ : Q.IsPrime) (_ : Q.LiesOver v.asIdeal) (σ : L ≃ₐ[K] L),
        IsArithFrobAt (𝓞 K) σ Q → φ (v.unitOfPrime K) = σ) :
    φ = unramifiedArtinHom (L := L) hab hur := by
  have key : φ.comp idealsAwayEmptyEquiv.toMonoidHom =
      artinHomAway (L := L) hab ∅ (fun v _ Q _ _ ↦ hur v Q) := by
    refine artinHomAway_eq_of_apply_prime hab ∅ (fun v _ Q _ _ ↦ hur v Q) _ ?_
    intro I v _ hI Q hQp hQl σ hσ
    have hunit : idealsAwayEmptyEquiv I = v.unitOfPrime K :=
      (idealsAwayEmptyEquiv_apply I).trans <|
        Units.ext (hI.trans (v.coe_unitOfPrime K).symm)
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hunit]
    exact hφ v Q hQp hQl σ hσ
  apply MonoidHom.ext
  intro I
  have hI := DFunLike.congr_fun key (idealsAwayEmptyEquiv.symm I)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    unramifiedArtinHom_apply] using hI

end UnramifiedArtinHom

/-! ### Restriction to an intermediate field -/

section Restrict

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (hur : ∀ (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- **The unrestricted Artin map is functorial in the top field.** Restricting automorphisms to a
normal intermediate field carries the Artin map of `L / K` to that of the intermediate field. -/
theorem unramifiedArtinHom_restrict (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [Algebra M L] [IsScalarTower K M L] [IsGalois K M] :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M).comp
        (unramifiedArtinHom (L := L) hab hur) =
      unramifiedArtinHom (L := M) (commute_of_tower (K := K) (L := L) (M := M) hab)
        (fun v Q _ _ ↦ isUnramifiedAway_of_intermediateField M ∅
          (fun w _ P _ _ ↦ hur w P) v (by simp) Q) := by
  apply MonoidHom.ext
  intro I
  have h := DFunLike.congr_fun
    (artinHomAway_restrict (L := L) hab ∅ (fun v _ Q _ _ ↦ hur v Q) M)
    (idealsAwayEmptyEquiv.symm I)
  simpa only [MonoidHom.comp_apply, unramifiedArtinHom_apply] using h

end Restrict

/-! ### Nonzero integral ideals -/

section Integral

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (hur : ∀ (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- The unrestricted Artin homomorphism on nonzero integral ideals. -/
noncomputable def unramifiedArtinHomIntegral :
    (Ideal (𝓞 K))⁰ →* (L ≃ₐ[K] L) :=
  (unramifiedArtinHom (L := L) hab hur).comp (FractionalIdeal.mk0 K)

/-- The integral Artin homomorphism is the unrestricted Artin map of the associated fractional
ideal. -/
@[simp]
theorem unramifiedArtinHomIntegral_apply (I : (Ideal (𝓞 K))⁰) :
    unramifiedArtinHomIntegral (L := L) hab hur I =
      unramifiedArtinHom (L := L) hab hur (FractionalIdeal.mk0 K I) :=
  (rfl)

/-- **The integral unrestricted Artin map sends a prime ideal to its Frobenius.** -/
theorem unramifiedArtinHomIntegral_apply_prime (v : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (σ : L ≃ₐ[K] L) (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    unramifiedArtinHomIntegral (L := L) hab hur
        ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ = σ := by
  rw [unramifiedArtinHomIntegral_apply]
  have hunit : FractionalIdeal.mk0 K
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ = v.unitOfPrime K := by
    apply Units.ext
    rw [FractionalIdeal.coe_mk0, v.coe_unitOfPrime]
  rw [hunit]
  exact unramifiedArtinHom_apply_prime hab hur v Q σ hσ

end Integral

end TauCeti.NumberFieldArithmetic

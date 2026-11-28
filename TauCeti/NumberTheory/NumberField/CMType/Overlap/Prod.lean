/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.Overlap.Descent
public import TauCeti.NumberTheory.NumberField.CMType.Prod
import TauCeti.Algebra.Ring.Aut
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.FieldTheory.IsAlgClosed.Automorphism

/-!
# Overlap characters of products of CM types

`CMType.overlap_prod` counts the two disjoint parts of the overlap of a product type.
`CMType.averageOverlap_prod` uses `CMType.averageOverlap_eq_inv_card_mul_sum` to average over
one common finite quotient, without assuming the orbit of the product is the product of
the orbits. `CMType.galoisAverageOverlap_prod` is the resulting sum of CM class functions on
the absolute Galois group.

## References

* F. Andreatta, E. Z. Goren, B. Howard and K. Madapusi Pera, *Faltings heights of abelian
  varieties with complex multiplication*, Ann. of Math. 187 (2018), §9.1.
-/

public section

namespace TauCeti.CMType

variable {E₁ E₂ : Type*} [CommRing E₁] [CommRing E₂] [StarCompCommute E₁] [StarCompCommute E₂]

/-- The overlap of a product CM type is the sum of the two overlaps. -/
@[simp]
theorem overlap_prod [Finite (E₁ →+* ℂ)] [Finite (E₂ →+* ℂ)] (Φ₁ : CMType E₁)
    (Φ₂ : CMType E₂) (σ : RingAut ℂ) :
    (Φ₁.prod Φ₂).overlap σ = Φ₁.overlap σ + Φ₂.overlap σ := by
  simp only [overlap_eq_ncard]
  have hsets : {φ : E₁ × E₂ →+* ℂ | φ ∈ Φ₁.prod Φ₂ ∧
      (σ : ℂ →+* ℂ).comp φ ∈ Φ₁.prod Φ₂} =
      (fun ψ : E₁ →+* ℂ ↦ ψ.comp (RingHom.fst E₁ E₂)) ''
        {ψ | ψ ∈ Φ₁ ∧ (σ : ℂ →+* ℂ).comp ψ ∈ Φ₁} ∪
      (fun ψ : E₂ →+* ℂ ↦ ψ.comp (RingHom.snd E₁ E₂)) ''
        {ψ | ψ ∈ Φ₂ ∧ (σ : ℂ →+* ℂ).comp ψ ∈ Φ₂} := by
    ext φ
    rcases φ.exists_eq_comp_fst_or_snd with ⟨ψ, rfl⟩ | ⟨ψ, rfl⟩ <;>
      simp only [Set.mem_ofPred_eq, ← RingHom.comp_assoc, comp_fst_mem_prod, comp_snd_mem_prod,
        RingHom.comp_fst_mem_union_iff, RingHom.comp_snd_mem_union_iff]
  rw [hsets, Set.ncard_union_eq (RingHom.disjoint_image_comp_fst_image_comp_snd _ _),
    Set.ncard_image_of_injective _ RingHom.comp_fst_injective,
    Set.ncard_image_of_injective _ RingHom.comp_snd_injective]

/-- Conjugacy averaging preserves the additivity of overlaps on product CM types. -/
@[simp]
theorem averageOverlap_prod [Finite (E₁ →+* ℂ)] [Finite (E₂ →+* ℂ)] (Φ₁ : CMType E₁)
    (Φ₂ : CMType E₂) (σ : RingAut ℂ) :
    (Φ₁.prod Φ₂).averageOverlap σ = Φ₁.averageOverlap σ + Φ₂.averageOverlap σ := by
  classical
  -- Use the same finite image for all three averages, including for the smaller factors.
  let ρ := RingAut.toPermRingHom (E₁ × E₂) ℂ
  let π := ρ.rangeRestrict
  let := Fintype.ofFinite ρ.range
  obtain ⟨s, hs⟩ := ρ.rangeRestrict_surjective.hasRightInverse
  have hprod (τ : RingAut ℂ) (hτ : π τ = 1) (φ : E₁ × E₂ →+* ℂ) :
      (τ : ℂ →+* ℂ).comp φ = φ := by
    have hp : RingAut.toPermRingHom (E₁ × E₂) ℂ τ = 1 := congrArg Subtype.val hτ
    simpa only [RingAut.toPermRingHom_apply, RingEquiv.toRingHom_eq_coe, Equiv.Perm.one_apply]
      using congrArg (fun p : Equiv.Perm (E₁ × E₂ →+* ℂ) ↦ p φ) hp
  have hfst (τ : RingAut ℂ) (hτ : π τ = 1) (φ : E₁ →+* ℂ) :
      (τ : ℂ →+* ℂ).comp φ = φ := by
    exact RingHom.comp_fst_injective (E₂ := E₂) (by
      simpa only [← RingHom.comp_assoc] using hprod τ hτ (φ.comp (RingHom.fst E₁ E₂)))
  have hsnd (τ : RingAut ℂ) (hτ : π τ = 1) (φ : E₂ →+* ℂ) :
      (τ : ℂ →+* ℂ).comp φ = φ := by
    exact RingHom.comp_snd_injective (E₁ := E₁) (by
      simpa only [← RingHom.comp_assoc] using hprod τ hτ (φ.comp (RingHom.snd E₁ E₂)))
  rw [averageOverlap_eq_inv_card_mul_sum π hprod hs, averageOverlap_eq_inv_card_mul_sum π hfst hs,
    averageOverlap_eq_inv_card_mul_sum π hsnd hs]
  simp only [overlap_prod, Nat.cast_add, Finset.sum_add_distrib, mul_add]

variable [Algebra ℚ E₁] [FiniteDimensional ℚ E₁] [Algebra ℚ E₂] [FiniteDimensional ℚ E₂]

/-- The absolute Galois overlap character of a product type is the sum of the characters of
its two factors. -/
@[simp]
theorem galoisAverageOverlap_prod (Φ₁ : CMType E₁) (Φ₂ : CMType E₂)
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Algebra Ω ℂ] :
    galoisAverageOverlap Ω (Φ₁.prod Φ₂) =
      galoisAverageOverlap Ω Φ₁ + galoisAverageOverlap Ω Φ₂ := by
  have h₁ : Finite (E₁ →+* ℂ) := (RingHom.equivRatAlgHom E₁ ℂ).finite_iff.mpr inferInstance
  have h₂ : Finite (E₂ →+* ℂ) := (RingHom.equivRatAlgHom E₂ ℂ).finite_iff.mpr inferInstance
  ext g
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective_of_isAlgClosed (Ω := ℂ) g
  simp only [AlgEquiv.restrictNormalHom_apply_eq_restrictNormal, Submodule.coe_add, Pi.add_apply,
    galoisAverageOverlap_restrictNormal, averageOverlap_prod]

end TauCeti.CMType

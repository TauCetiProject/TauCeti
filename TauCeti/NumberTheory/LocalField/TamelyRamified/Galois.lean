/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic
public import Mathlib.FieldTheory.KummerExtension
import TauCeti.NumberTheory.LocalField.Teichmuller

/-!
# Galois totally and tamely ramified extensions

A totally and tamely ramified extension of nonarchimedean local fields, with ramification index
`e`, is Galois exactly when the base field contains a primitive `e`-th root of unity, or
equivalently when `e` divides the size of its residue field minus one. In that case a radical
uniformizer identifies the Galois group with the `e`-th roots of unity in the base field by
`σ ↦ σ(α) / α`.

The radical presentation comes from `TamelyRamified.Basic`; the splitting-field and
automorphism constructions reuse Mathlib's `FieldTheory.KummerExtension`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField Polynomial
open scoped IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

private theorem isGalois_of_isTotallyRamified_of_isTamelyRamified_of_isPrimitiveRoot
    (h : IsTotallyRamified K L) (ht : IsTamelyRamified K L) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (ramificationIndex K L)) : IsGalois K L := by
  let := finite_of_valuativeExtension K L
  obtain ⟨π, α, _, _, hpow, hgen⟩ := h.exists_pow_eq_uniformizer_of_isTamelyRamified ht
  have he := (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 h
  rw [he] at hζ hpow
  have hroots : (primitiveRoots (Module.finrank K L) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots Module.finrank_pos).2 hζ⟩
  let := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hroots hpow hgen
  exact isGalois_of_isSplittingField_X_pow_sub_C hroots
    (irreducible_X_pow_sub_C_of_root_adjoin_eq_top hpow hgen) L

/-- A totally and tamely ramified extension is Galois exactly when its ramification index divides
the size of the base residue field minus one. -/
theorem IsTotallyRamified.isGalois_iff_ramificationIndex_dvd_card_residueField_sub_one
    (h : IsTotallyRamified K L) (ht : IsTamelyRamified K L) :
    IsGalois K L ↔ ramificationIndex K L ∣ Nat.card 𝓀[K] - 1 := by
  let := finite_of_valuativeExtension K L
  constructor
  · intro hG
    let := hG
    have hdvd := ht.ramificationIndex_dvd_card_residueField_sub_one
    rwa [natCard_residueField K L, h.inertiaDegree_eq_one, pow_one] at hdvd
  · intro hdvd
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_residueField_sub_one K
    have hroot := hζ.pow (Nat.sub_pos_of_lt Finite.one_lt_card)
      (Nat.div_mul_cancel hdvd).symm
    exact isGalois_of_isTotallyRamified_of_isTamelyRamified_of_isPrimitiveRoot h ht hroot

/-- A totally and tamely ramified extension with ramification index `e` is Galois exactly when
the base field contains a primitive `e`-th root of unity. -/
theorem IsTotallyRamified.isGalois_iff_exists_isPrimitiveRoot
    (h : IsTotallyRamified K L) (ht : IsTamelyRamified K L) :
    IsGalois K L ↔ ∃ ζ : K, IsPrimitiveRoot ζ (ramificationIndex K L) := by
  constructor
  · intro hG
    have hdvd := (h.isGalois_iff_ramificationIndex_dvd_card_residueField_sub_one ht).1 hG
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_residueField_sub_one K
    exact ⟨_, hζ.pow (Nat.sub_pos_of_lt Finite.one_lt_card) (Nat.div_mul_cancel hdvd).symm⟩
  · rintro ⟨ζ, hζ⟩
    exact isGalois_of_isTotallyRamified_of_isTamelyRamified_of_isPrimitiveRoot h ht hζ

/-- In a totally and tamely ramified Galois extension, a radical uniformizer identifies the
Galois group with the roots of unity in the base field by `σ ↦ σ(α) / α`. -/
theorem IsTotallyRamified.exists_pow_eq_uniformizer_and_autEquivRootsOfUnity
    [IsGalois K L] (h : IsTotallyRamified K L) (ht : IsTamelyRamified K L) :
    ∃ (π : Kˣ) (α : Lˣ), IsUniformizer K π ∧ IsUniformizer L α ∧
      (α : L) ^ ramificationIndex K L = algebraMap K L π ∧ K⟮(α : L)⟯ = ⊤ ∧
      ∃ Φ : (L ≃ₐ[K] L) ≃* rootsOfUnity (ramificationIndex K L) K,
        ∀ σ, algebraMap K L ((Φ σ : Kˣ) : K) = σ (α : L) / (α : L) := by
  let := finite_of_valuativeExtension K L
  obtain ⟨π, α, hπ, hα, hpow, hgen⟩ := h.exists_pow_eq_uniformizer_of_isTamelyRamified ht
  obtain ⟨ζ, hζ⟩ := (h.isGalois_iff_exists_isPrimitiveRoot ht).1 inferInstance
  have he := (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 h
  rw [he] at hζ hpow ⊢
  let : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  have hroots : (primitiveRoots (Module.finrank K L) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots Module.finrank_pos).2 hζ⟩
  let := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hroots hpow hgen
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hpow hgen
  refine ⟨π, α, hπ, hα, hpow, hgen, autEquivRootsOfUnity hroots hirr L, ?_⟩
  intro σ
  apply (eq_div_iff α.ne_zero).2
  simpa only [Subgroup.smul_def, Units.smul_def, Algebra.smul_def] using
    autEquivRootsOfUnity_smul hroots hirr L hpow σ

end TauCeti

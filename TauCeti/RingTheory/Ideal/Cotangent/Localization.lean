/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Cotangent spaces and localization at a maximal ideal

Let `p` be a maximal ideal of a commutative ring `R`, and let `Rₚ` be a localization of `R` at
`p`. The map from `R` to `Rₚ` identifies the cotangent space `p / p²` with the cotangent space
`pRₚ / (pRₚ)²` of the local ring `Rₚ`. This file constructs that identification and proves that
it is semilinear for the canonical equivalence between the two residue fields. So the two
cotangent spaces have the same dimension, and when `Rₚ` is Noetherian its regularity can be read
off from the dimension of `p / p²` over `R / p`.

This is the localization bridge used to compare the augmentation-ideal model of the tangent
space of an affine group with the Zariski tangent space of its spectrum at the identity.

## Main declarations

* `Ideal.cotangentLocalizationEquiv`: localization at a maximal ideal preserves the cotangent
  space.
* `Ideal.cotangentLocalizationEquiv_smul`: the equivalence is semilinear for the canonical
  residue-field equivalence.
* `Ideal.finrank_cotangent_eq_finrank_cotangentSpace`: the two cotangent spaces have the same
  dimension over their residue fields.
* `Ideal.isRegularLocalRing_iff_finrank_cotangent`: a Noetherian `Rₚ` is regular exactly when
  `p / p²` has dimension `dim Rₚ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

open IsLocalRing

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
variable (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]

private theorem le_comap_maximalIdeal : p ≤ (maximalIdeal Rₚ).comap (Algebra.ofId R Rₚ) :=
  (IsLocalization.AtPrime.under_maximalIdeal Rₚ p).ge

/-- The cotangent map `p / p² → pRₚ / (pRₚ)²` induced by localization is bijective. -/
private theorem mapCotangent_algebraMap_bijective :
    Function.Bijective (p.mapCotangent (maximalIdeal Rₚ) (Algebra.ofId R Rₚ)
      (le_comap_maximalIdeal p Rₚ)) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    obtain ⟨x, rfl⟩ := p.toCotangent_surjective a
    rw [mapCotangent_toCotangent, toCotangent_eq_zero] at ha
    rw [toCotangent_eq_zero, ← IsLocalization.AtPrime.under_maximalIdeal_pow p Rₚ 2]
    exact ha
  · intro a
    obtain ⟨⟨z, hz⟩, rfl⟩ := (maximalIdeal Rₚ).toCotangent_surjective a
    obtain ⟨y, hy⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ 2).surjective
      (Ideal.Quotient.mk _ z)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk, Ideal.Quotient.eq] at hy
    have hx : x ∈ p := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p x]
      simpa using add_mem (Ideal.pow_le_self two_ne_zero hy) hz
    exact ⟨p.toCotangent ⟨x, hx⟩, (toCotangent_eq _).2 hy⟩

/-- The canonical linear equivalence `p / p² ≃ pRₚ / (pRₚ)²` induced by localization. -/
noncomputable def cotangentLocalizationEquiv :
    p.Cotangent ≃ₗ[R] (maximalIdeal Rₚ).Cotangent :=
  .ofBijective _ (mapCotangent_algebraMap_bijective p Rₚ)

/-- On a class represented by `x ∈ p`, the cotangent localization equivalence is induced by the
ring localization map. -/
@[simp]
theorem cotangentLocalizationEquiv_toCotangent (x : p) :
    cotangentLocalizationEquiv p Rₚ (p.toCotangent x) =
      (maximalIdeal Rₚ).toCotangent
        ⟨algebraMap R Rₚ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p x).2 x.2⟩ :=
  (rfl)

/-- The cotangent localization equivalence is semilinear for the canonical equivalence between
the residue field `R / p` and the residue field of `Rₚ`. -/
@[simp]
theorem cotangentLocalizationEquiv_smul (r : R ⧸ p) (x : p.Cotangent) :
    cotangentLocalizationEquiv p Rₚ (r • x) =
      IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ r • cotangentLocalizationEquiv p Rₚ x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  simp [← Ideal.Quotient.algebraMap_eq,
    IsScalarTower.algebraMap_apply R Rₚ (Rₚ ⧸ maximalIdeal Rₚ)]

/-- Localization at a maximal ideal `p` preserves the dimension of the cotangent space: `p / p²`
over `R / p` has the dimension of the cotangent space of `Rₚ` over its residue field. -/
theorem finrank_cotangent_eq_finrank_cotangentSpace :
    Module.finrank (R ⧸ p) p.Cotangent =
      Module.finrank (IsLocalRing.ResidueField Rₚ) (CotangentSpace Rₚ) := by
  have h := lift_rank_eq_of_equiv_equiv (R' := IsLocalRing.ResidueField Rₚ)
    (M' := CotangentSpace Rₚ) (IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ)
    (cotangentLocalizationEquiv p Rₚ).toAddEquiv
    (IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ).bijective
    (cotangentLocalizationEquiv_smul p Rₚ)
  rw [Module.finrank, Module.finrank, ← Cardinal.toNat_lift, h, Cardinal.toNat_lift]

/-- A Noetherian localization `Rₚ` at a maximal ideal `p` is a regular local ring if and only if
`p / p²` has dimension `dim Rₚ` over `R / p`. -/
theorem isRegularLocalRing_iff_finrank_cotangent [IsNoetherianRing Rₚ] :
    IsRegularLocalRing Rₚ ↔
      (Module.finrank (R ⧸ p) p.Cotangent : WithBot ℕ∞) = ringKrullDim Rₚ := by
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace,
    finrank_cotangent_eq_finrank_cotangentSpace p Rₚ]

end Ideal

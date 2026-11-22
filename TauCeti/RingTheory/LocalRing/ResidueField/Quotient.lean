/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The quotient by a maximal ideal of a local ring

A local ring `R` has exactly one maximal ideal, so the quotient `R ⧸ 𝔪` by any maximal ideal `𝔪`
is the residue field `κ`. Likewise, any surjective `R₀`-algebra map `ψ : R →ₐ[R₀] L` onto a field
`L` has kernel `maximalIdeal R` and identifies `ResidueField R` with `L` as an `R₀`-algebra.

## Main declarations

* `TauCeti.isLocalHom_algebraMap_residueField`: `algebraMap R (ResidueField R)` is a local
  homomorphism.
* `TauCeti.quotientEquivResidueField`: `R ⧸ 𝔪 ≃ₗ[R] κ` for a maximal ideal `𝔪`,
  sending the class of `r` to `residue R r`.
* `TauCeti.residueFieldAlgEquivOfSurjective`: `ResidueField R ≃ₐ[R₀] L` induced by a surjective
  `R₀`-algebra map `ψ : R →ₐ[R₀] L` onto a field `L`.
* `TauCeti.finrank_residueField_eq_of_equiv_equiv`: a commuting square of ring equivalences
  between local ring extensions induces an equality of residue-field degrees.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The canonical algebra map `R →+* ResidueField R` of a local ring is a local homomorphism. -/
instance isLocalHom_algebraMap_residueField : IsLocalHom (algebraMap R (ResidueField R)) :=
  ResidueField.algebraMap_eq (R := R) ▸ inferInstance

/-- The quotient of a local ring by a maximal ideal is its residue field, as an `R`-linear
equivalence sending the class of `r` to `residue R r`. -/
def quotientEquivResidueField {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) :
    (R ⧸ 𝔪) ≃ₗ[R] ResidueField R :=
  -- `𝔪` is the maximal ideal, the kernel of `residue`.
  Submodule.quotEquivOfEq _ _ (by
      ext r
      simp [eq_maximalIdeal h𝔪, ResidueField.algebraMap_eq, residue_eq_zero_iff]) ≪≫ₗ
    (Algebra.linearMap R (ResidueField R)).quotKerEquivOfSurjective residue_surjective

/-- `quotientEquivResidueField` sends the class of `r` to its residue. -/
@[simp]
theorem quotientEquivResidueField_mk {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (r : R) :
    quotientEquivResidueField h𝔪 (Ideal.Quotient.mk 𝔪 r) = residue R r :=
  (rfl)

/-- A surjective `R₀`-algebra map `ψ : R →ₐ[R₀] L` from a local ring `R` onto a field `L` has
kernel `maximalIdeal R`, inducing an `R₀`-algebra isomorphism `ResidueField R ≃ₐ[R₀] L`. -/
def residueFieldAlgEquivOfSurjective {R₀ L : Type*} [CommRing R₀] [Algebra R₀ R] [Field L]
    [Algebra R₀ L] {ψ : R →ₐ[R₀] L} (hψ : Function.Surjective ψ) :
    ResidueField R ≃ₐ[R₀] L :=
  (Ideal.quotientEquivAlgOfEq R₀ (ker_eq_maximalIdeal ψ.toRingHom hψ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hψ)

/-- `residueFieldAlgEquivOfSurjective` sends `residue R r` to `ψ r`. -/
@[simp]
theorem residueFieldAlgEquivOfSurjective_residue {R₀ L : Type*} [CommRing R₀] [Algebra R₀ R]
    [Field L] [Algebra R₀ L] {ψ : R →ₐ[R₀] L} (hψ : Function.Surjective ψ) (r : R) :
    residueFieldAlgEquivOfSurjective hψ (residue R r) = ψ r := by
  have hker : maximalIdeal R = RingHom.ker ψ := (ker_eq_maximalIdeal ψ.toRingHom hψ).symm
  -- `ResidueField R` is the quotient by `maximalIdeal R` with quotient map `residue R`; rewriting
  -- with `residue_def` would alter the dependent type, so pass to the quotient form directly.
  change Ideal.quotientKerAlgEquivOfSurjective hψ
    (Ideal.quotientEquivAlgOfEq R₀ hker (Ideal.Quotient.mk _ r)) = ψ r
  rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The inverse of `residueFieldAlgEquivOfSurjective` sends `ψ r` to `residue R r`. -/
@[simp]
theorem residueFieldAlgEquivOfSurjective_symm_apply {R₀ L : Type*} [CommRing R₀] [Algebra R₀ R]
    [Field L] [Algebra R₀ L] {ψ : R →ₐ[R₀] L} (hψ : Function.Surjective ψ) (r : R) :
    (residueFieldAlgEquivOfSurjective hψ).symm (ψ r) = residue R r :=
  (residueFieldAlgEquivOfSurjective hψ).symm_apply_eq.mpr
    (residueFieldAlgEquivOfSurjective_residue hψ r).symm

/-- A commuting square of ring equivalences between local ring extensions induces an equality
of residue-field degrees. -/
theorem finrank_residueField_eq_of_equiv_equiv
    {R₀ S₀ R₁ S₁ : Type*} [CommRing R₀] [CommRing S₀] [CommRing R₁] [CommRing S₁]
    [IsLocalRing R₀] [IsLocalRing S₀] [IsLocalRing R₁] [IsLocalRing S₁]
    [Algebra R₀ S₀] [Algebra R₁ S₁]
    [IsLocalHom (algebraMap R₀ S₀)] [IsLocalHom (algebraMap R₁ S₁)]
    (i : R₀ ≃+* R₁) (j : S₀ ≃+* S₁)
    (hc : (algebraMap R₁ S₁).comp i.toRingHom = j.toRingHom.comp (algebraMap R₀ S₀)) :
    Module.finrank (ResidueField R₀) (ResidueField S₀) =
      Module.finrank (ResidueField R₁) (ResidueField S₁) := by
  refine Algebra.finrank_eq_of_equiv_equiv (ResidueField.mapEquiv i) (ResidueField.mapEquiv j) ?_
  have h₁ : algebraMap (ResidueField R₁) (ResidueField S₁) =
      ResidueField.map (algebraMap R₁ S₁) :=
    Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ ↦ rfl
  have h₀ : algebraMap (ResidueField R₀) (ResidueField S₀) =
      ResidueField.map (algebraMap R₀ S₀) :=
    Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ ↦ rfl
  have : IsLocalHom i.toRingHom := ⟨fun _ h ↦ by simpa using i.symm.toRingHom.isUnit_map h⟩
  have : IsLocalHom j.toRingHom := ⟨fun _ h ↦ by simpa using j.symm.toRingHom.isUnit_map h⟩
  rw [h₁, h₀]
  change (ResidueField.map (algebraMap R₁ S₁)).comp (ResidueField.map i.toRingHom) =
    (ResidueField.map j.toRingHom).comp (ResidueField.map (algebraMap R₀ S₀))
  rw [← ResidueField.map_comp, ← ResidueField.map_comp]
  exact Ideal.Quotient.ringHom_ext <| RingHom.ext fun x ↦ by
    change ResidueField.map ((algebraMap R₁ S₁).comp i.toRingHom) (residue R₀ x) =
      ResidueField.map (j.toRingHom.comp (algebraMap R₀ S₀)) (residue R₀ x)
    simp only [ResidueField.map_residue, RingHom.comp_apply, RingHom.congr_fun hc x]

end TauCeti

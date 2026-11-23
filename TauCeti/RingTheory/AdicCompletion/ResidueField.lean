/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Residue field of the adic completion of a Noetherian local ring

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and `𝔪`-adic completion `R̂`. The
canonical map `R → R̂` induces a bijection on residue fields
(`AdicCompletion.residueField_map_bijective`), giving an `R`-algebra isomorphism
`ResidueField R ≃ₐ[R] ResidueField R̂` (`TauCeti.AdicCompletion.residueFieldAlgEquiv`) via
`TauCeti.residueFieldAlgEquivOfSurjective`.

## Main declarations

* `TauCeti.AdicCompletion.algebraMap_residueField_surjective`: the canonical map
  `R →+* ResidueField R̂` is surjective.
* `TauCeti.AdicCompletion.residueFieldAlgEquiv`: the canonical `R`-algebra isomorphism
  `ResidueField R ≃ₐ[R] ResidueField R̂`.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
/-- The canonical ring homomorphism from `R` to the residue field of its maximal-ideal
completion is surjective. -/
theorem algebraMap_residueField_surjective :
    Function.Surjective
      (algebraMap R (ResidueField (_root_.AdicCompletion (maximalIdeal R) R))) := by
  have hmap : ⇑(ResidueField.map (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R))) ∘
      residue R =
      algebraMap R (ResidueField (_root_.AdicCompletion (maximalIdeal R) R)) := by
    ext r
    simp [IsScalarTower.algebraMap_apply R (_root_.AdicCompletion (maximalIdeal R) R)
      (ResidueField (_root_.AdicCompletion (maximalIdeal R) R)),
      ResidueField.algebraMap_eq]
  rw [← hmap]
  exact (_root_.AdicCompletion.residueField_map_bijective R).surjective.comp residue_surjective

variable (R) in
/-- The canonical `R`-algebra isomorphism between the residue field of a Noetherian local ring and
the residue field of its maximal-ideal completion, induced by `algebraMap`. -/
noncomputable def residueFieldAlgEquiv :
    ResidueField R ≃ₐ[R] ResidueField (_root_.AdicCompletion (maximalIdeal R) R) :=
  TauCeti.residueFieldAlgEquivOfSurjective (ψ := Algebra.ofId R _)
    (algebraMap_residueField_surjective R)

/-- `residueFieldAlgEquiv` sends `residue R r` to `algebraMap R (ResidueField R̂) r`. -/
@[simp]
theorem residueFieldAlgEquiv_residue (r : R) :
    residueFieldAlgEquiv R (residue R r) =
      algebraMap R (ResidueField (_root_.AdicCompletion (maximalIdeal R) R)) r :=
  TauCeti.residueFieldAlgEquivOfSurjective_residue (ψ := Algebra.ofId R _)
    (algebraMap_residueField_surjective R) r

/-- The inverse of `residueFieldAlgEquiv` sends `residue R̂ (algebraMap R R̂ r)` to
`residue R r`. -/
@[simp]
theorem residueFieldAlgEquiv_symm_residue (r : R) :
    (residueFieldAlgEquiv R).symm
        (residue (_root_.AdicCompletion (maximalIdeal R) R) (algebraMap R _ r)) =
      residue R r := by
  rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  exact TauCeti.residueFieldAlgEquivOfSurjective_symm_apply (ψ := Algebra.ofId R _)
    (algebraMap_residueField_surjective R) r

end TauCeti.AdicCompletion

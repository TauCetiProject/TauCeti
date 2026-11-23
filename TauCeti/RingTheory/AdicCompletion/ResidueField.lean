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

* `TauCeti.AdicCompletion.residueFieldAlgEquiv`: the canonical `R`-algebra isomorphism
  `ResidueField R ≃ₐ[R] ResidueField R̂`.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
/-- The canonical `R`-algebra isomorphism between the residue field of a Noetherian local ring and
the residue field of its maximal-ideal completion, induced by `algebraMap`. -/
noncomputable abbrev residueFieldAlgEquiv :
    ResidueField R ≃ₐ[R] ResidueField (_root_.AdicCompletion (maximalIdeal R) R) :=
  TauCeti.residueFieldAlgEquivOfSurjective
    (ψ := Algebra.ofId R (ResidueField (_root_.AdicCompletion (maximalIdeal R) R)))
    (by
      have hmap : ⇑(ResidueField.map (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R))) ∘
          residue R =
          Algebra.ofId R (ResidueField (_root_.AdicCompletion (maximalIdeal R) R)) := by
        ext r
        simp [IsScalarTower.algebraMap_apply R (_root_.AdicCompletion (maximalIdeal R) R)
          (ResidueField (_root_.AdicCompletion (maximalIdeal R) R)),
          ResidueField.algebraMap_eq]
      rw [← hmap]
      exact (_root_.AdicCompletion.residueField_map_bijective R).surjective.comp residue_surjective)

end TauCeti.AdicCompletion

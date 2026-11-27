/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Residue field of the adic completion of a local ring

Let `R` be a local ring with finitely generated maximal ideal `𝔪` and `𝔪`-adic completion
`R̂ = AdicCompletion 𝔪 R`. The canonical map `R → R̂` induces a bijection on residue fields
(`AdicCompletion.residueField_map_bijective_of_fg`), giving an `R`-algebra isomorphism
`ResidueField R ≃ₐ[R] ResidueField R̂` (`TauCeti.AdicCompletion.residueFieldAlgEquiv`) via
`IsLocalRing.ResidueField.mapAlgHom`.

## Main declarations

* `TauCeti.AdicCompletion.residueFieldAlgEquiv`: the canonical `R`-algebra isomorphism
  `ResidueField R ≃ₐ[R] ResidueField R̂`.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The canonical `R`-algebra isomorphism between the residue field of a local ring with finitely
generated maximal ideal and the residue field of its maximal-ideal completion, induced by
`algebraMap`. -/
noncomputable def residueFieldAlgEquiv (fg : (maximalIdeal R).FG) :
    letI := _root_.AdicCompletion.isLocalRing_of_fg fg
    ResidueField R ≃ₐ[R] ResidueField (_root_.AdicCompletion (maximalIdeal R) R) :=
  letI := _root_.AdicCompletion.isLocalRing_of_fg fg
  haveI : IsLocalHom (Algebra.ofId R (_root_.AdicCompletion (maximalIdeal R) R)) :=
    ⟨fun _ h ↦ (_root_.AdicCompletion.algebraMap_isLocalHom_of_fg fg).map_nonunit _ h⟩
  AlgEquiv.ofBijective
    (ResidueField.mapAlgHom (Algebra.ofId R (_root_.AdicCompletion (maximalIdeal R) R)))
    (_root_.AdicCompletion.residueField_map_bijective_of_fg fg)

/-- `residueFieldAlgEquiv` sends `residue R r` to
`residue R̂ (algebraMap R R̂ r)`. -/
@[simp]
theorem residueFieldAlgEquiv_residue (fg : (maximalIdeal R).FG) (r : R) :
    letI := _root_.AdicCompletion.isLocalRing_of_fg fg
    residueFieldAlgEquiv fg (residue R r) =
      residue (_root_.AdicCompletion (maximalIdeal R) R) (algebraMap R _ r) := by
  let := _root_.AdicCompletion.isLocalRing_of_fg fg
  have : IsLocalHom (Algebra.ofId R (_root_.AdicCompletion (maximalIdeal R) R)) :=
    ⟨fun _ h ↦ (_root_.AdicCompletion.algebraMap_isLocalHom_of_fg fg).map_nonunit _ h⟩
  rw [residueFieldAlgEquiv]
  exact ResidueField.mapAlgHom_residue (Algebra.ofId R (_root_.AdicCompletion (maximalIdeal R) R)) r

/-- The inverse of `residueFieldAlgEquiv` sends `residue R̂ (algebraMap R R̂ r)` to
`residue R r`. -/
@[simp]
theorem residueFieldAlgEquiv_symm_residue (fg : (maximalIdeal R).FG) (r : R) :
    letI := _root_.AdicCompletion.isLocalRing_of_fg fg
    (residueFieldAlgEquiv fg).symm
        (residue (_root_.AdicCompletion (maximalIdeal R) R) (algebraMap R _ r)) =
      residue R r :=
  (residueFieldAlgEquiv fg).symm_apply_eq.mpr (residueFieldAlgEquiv_residue fg r).symm

end TauCeti.AdicCompletion

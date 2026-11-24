/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.WordFiltration.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.PBW

/-!
# Isometries acting on the associated graded of a Clifford algebra

An isometry `φ : Q₁ →qᵢ Q₂` induces the algebra homomorphism `CliffordAlgebra.map φ`, which sends
a product of `k` generators to a product of `k` generators and so preserves the degree filtration.
This file builds the induced algebra homomorphism of associated gradeds and identifies it, through
the PBW equivalence `CliffordAlgebra.associatedGradedEquivExterior`, with the exterior-algebra map
`ExteriorAlgebra.map φ`: on the associated graded, the action of an isometry forgets the quadratic
form and becomes its action on the exterior algebra.

The comparison holds degree by degree, with `exteriorPower.map k φ` on the `k`-th graded piece. No
nondegeneracy or finiteness hypothesis is needed, only that `2` is invertible, as for the PBW
equivalence itself. The zero space and the zero form are included.

## Main definitions

* `CliffordAlgebra.mapAssociatedGraded`: the algebra homomorphism of Clifford associated gradeds
  induced by an isometry.

## Main results

* `CliffordAlgebra.gradedPieceEquivExteriorPower_mapGradedPiece`: on the `k`-th graded piece, the
  induced map is `exteriorPower.map k φ`.
* `CliffordAlgebra.associatedGradedEquivExterior_mapAssociatedGraded`: on the whole associated
  graded, the induced map is `ExteriorAlgebra.map φ`.
* `CliffordAlgebra.mapAssociatedGraded_eq`: the induced map is `ExteriorAlgebra.map φ` conjugated
  by the PBW equivalences.
* `CliffordAlgebra.mapAssociatedGraded_id` and `CliffordAlgebra.mapAssociatedGraded_comp`: the
  construction is functorial in the isometry.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Proposition I.1.2.
-/

public section

open TauCeti.Algebra TauCeti.Algebra.wordFiltration

namespace CliffordAlgebra

variable {R : Type*} {M₁ M₂ M₃ : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- The algebra homomorphism of Clifford associated gradeds induced by an isometry. -/
noncomputable def mapAssociatedGraded (φ : Q₁ →qᵢ Q₂) :
    AssociatedGraded (ι Q₁) →ₐ[R] AssociatedGraded (ι Q₂) :=
  wordFiltration.mapAssociatedGraded (ι Q₁) (ι Q₂) (map φ) (map_apply_ι_mem_filtration_one φ)

/-- On a homogeneous element, the induced map is the map of graded pieces induced by the Clifford
map. -/
@[simp]
theorem mapAssociatedGraded_of (φ : Q₁ →qᵢ Q₂) (k : ℕ) (x : GradedPiece (ι Q₁) k) :
    mapAssociatedGraded φ (DirectSum.of (GradedPiece (ι Q₁)) k x) =
      DirectSum.of (GradedPiece (ι Q₂)) k
        (mapGradedPiece (ι Q₁) (ι Q₂) (map φ) (map_apply_ι_mem_filtration_one φ) k x) :=
  wordFiltration.mapAssociatedGraded_of _ _ _ _ k x

/-- The identity isometry induces the identity on the associated graded. -/
@[simp]
theorem mapAssociatedGraded_id :
    mapAssociatedGraded (QuadraticMap.Isometry.id Q₁) = AlgHom.id R _ := by
  rw [mapAssociatedGraded]
  simp_rw [map_id]
  exact wordFiltration.mapAssociatedGraded_id (ι Q₁) _

/-- A composite of isometries induces the composite of the induced maps. -/
theorem mapAssociatedGraded_comp (φ₂ : Q₂ →qᵢ Q₃) (φ₁ : Q₁ →qᵢ Q₂) :
    mapAssociatedGraded (φ₂.comp φ₁) =
      (mapAssociatedGraded φ₂).comp (mapAssociatedGraded φ₁) := by
  rw [mapAssociatedGraded, mapAssociatedGraded, mapAssociatedGraded]
  simp_rw [← map_comp_map]
  exact wordFiltration.mapAssociatedGraded_comp (ι Q₁) (ι Q₂) (ι Q₃) _ _ _ _ _

variable [Invertible (2 : R)]

/-- **Isometries act on each graded piece through the exterior power.** Under the PBW
identification of the `k`-th graded piece with `⋀[R]^k`, the map induced by an isometry `φ` is
`exteriorPower.map k φ`. -/
@[simp]
theorem gradedPieceEquivExteriorPower_mapGradedPiece (φ : Q₁ →qᵢ Q₂) (k : ℕ)
    (x : GradedPiece (ι Q₁) k) :
    gradedPieceEquivExteriorPower Q₂ k
        (mapGradedPiece (ι Q₁) (ι Q₂) (map φ) (map_apply_ι_mem_filtration_one φ) k x) =
      exteriorPower.map k φ.toLinearMap (gradedPieceEquivExteriorPower Q₁ k x) := by
  have hmaps :
      (mapGradedPiece (ι Q₁) (ι Q₂) (map φ) (map_apply_ι_mem_filtration_one φ) k).comp
          (gradedPieceEquivExteriorPower Q₁ k).symm.toLinearMap =
        (gradedPieceEquivExteriorPower Q₂ k).symm.toLinearMap.comp
          (exteriorPower.map k φ.toLinearMap) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      gradedPieceEquivExteriorPower_symm_apply_ιMulti, exteriorPower.map_apply_ιMulti,
      mapGradedPiece_mk]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_apply_ι,
      QuadraticMap.Isometry.coe_toLinearMap]
  have h := LinearMap.congr_fun hmaps (gradedPieceEquivExteriorPower Q₁ k x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  rw [h, LinearEquiv.apply_symm_apply]

/-- **Isometries act on the associated graded through the exterior algebra.** Under the PBW
equivalence, the map of Clifford associated gradeds induced by an isometry `φ` is the
exterior-algebra map `ExteriorAlgebra.map φ`. -/
@[simp]
theorem associatedGradedEquivExterior_mapAssociatedGraded (φ : Q₁ →qᵢ Q₂)
    (x : AssociatedGraded (ι Q₁)) :
    associatedGradedEquivExterior Q₂ (mapAssociatedGraded φ x) =
      ExteriorAlgebra.map φ.toLinearMap (associatedGradedEquivExterior Q₁ x) := by
  have h : (associatedGradedEquivExterior Q₂).toAlgHom.comp (mapAssociatedGraded φ) =
      (ExteriorAlgebra.map φ.toLinearMap).comp (associatedGradedEquivExterior Q₁).toAlgHom := by
    apply DirectSum.algHom_ext
    intro k y
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      mapAssociatedGraded_of, associatedGradedEquivExterior_apply_of,
      gradedPieceEquivExteriorPower_mapGradedPiece, exteriorPower.coe_map]
  exact AlgHom.congr_fun h x

/-- The map induced by an isometry on Clifford associated gradeds is `ExteriorAlgebra.map φ`
conjugated by the PBW equivalences. -/
theorem mapAssociatedGraded_eq (φ : Q₁ →qᵢ Q₂) :
    mapAssociatedGraded φ =
      ((associatedGradedEquivExterior Q₂).symm.toAlgHom.comp
        (ExteriorAlgebra.map φ.toLinearMap)).comp (associatedGradedEquivExterior Q₁).toAlgHom := by
  refine AlgHom.ext fun x => (associatedGradedEquivExterior Q₂).injective ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
    associatedGradedEquivExterior_mapAssociatedGraded]

end CliffordAlgebra

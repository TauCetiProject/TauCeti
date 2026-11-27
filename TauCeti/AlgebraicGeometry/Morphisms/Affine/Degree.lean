/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import Mathlib.Tactic.Algebraize

/-!
# The rank of the coordinate rings of a dominant affine morphism

Let `f : X ⟶ Y` be a dominant affine morphism of integral schemes, and `f^* : K(Y) ⟶ K(X)` its
pullback of rational functions. Over a nonempty affine open `U` of `Y`, the coordinate ring
`Γ(X, f⁻¹ U)` has rank `[K(X) : f^* K(Y)]` over `Γ(Y, U)`
(`AlgebraicGeometry.Scheme.Hom.finrank_appLE_eq_finrank_fieldRange_functionFieldMap`). Both
coordinate rings are domains whose fraction fields are the function fields, `f^*` extends the map
of coordinate rings, and the rank of a torsion-free module over a domain is the dimension after
passing to fraction fields (`IsFractionRing.finrank_eq`). No finiteness or flatness is needed.

This computes the rank of a finite flat dominant morphism of integral schemes
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_fieldRange_functionFieldMap`) and the rank of
the semilocal rings in the projection formula for finite dominant morphisms
(`AlgebraicGeometry.Scheme.Hom.finsum_residueDegree_mul_toNat_ord_eq_finrank_mul_toNat_ord`).

As for the degree of a finite flat morphism, the degree is stated as the dimension of `K(X)` over
the subfield `f^* K(Y)`, avoiding an algebra structure on `K(X)` over `K(Y)`.
-/

public section

namespace AlgebraicGeometry

universe u

open CategoryTheory

variable {X Y : Scheme.{u}}

/-- **The rank of the coordinate rings of a dominant affine morphism.** For a dominant affine
morphism `f : X ⟶ Y` of integral schemes and a nonempty affine open `U` of `Y`, the ring
`Γ(X, f⁻¹ U)` has rank `[K(X) : f^* K(Y)]` over `Γ(Y, U)`, the algebra structure being given by
`f`. No finiteness or flatness is needed: the rank is that of the fraction fields. -/
theorem Scheme.Hom.finrank_appLE_eq_finrank_fieldRange_functionFieldMap (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsAffineHom f] [IsDominant f] {U : Y.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    letI := (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    Module.finrank Γ(Y, U) Γ(X, f ⁻¹ᵁ U) =
      Module.finrank f.functionFieldMap.hom.fieldRange X.functionField := by
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨y⟩ := ‹Nonempty U›
    obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open U.isOpen ⟨y.val, y.property⟩
    exact ⟨⟨x, hx⟩⟩
  set φ := f.appLE U (f ⁻¹ᵁ U) le_rfl
  -- The coordinate rings are domains with fraction fields `K(Y)` and `K(X)`, and `f^*` extends
  -- `φ`.
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have := functionField_isFractionRing_of_isAffineOpen X _ hV
  algebraize [φ.hom, f.functionFieldMap.hom]
  let : Algebra Γ(Y, U) X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp φ.hom).toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Y, U) Y.functionField X.functionField := .of_algebraMap_eq fun a ↦ by
    have := congr($(f.germToFunctionField_functionFieldMap U).hom a)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.app_eq_appLE] at this
    exact this.symm
  rw [← IsFractionRing.finrank_eq Γ(Y, U) Y.functionField Γ(X, f ⁻¹ᵁ U) X.functionField]
  exact Algebra.finrank_eq_of_equiv_equiv f.functionFieldMap.hom.rangeRestrictFieldEquiv
    (.refl _) (by ext; simp [Subfield.algebraMap_ofSubfield, RingHom.algebraMap_toAlgebra])

end AlgebraicGeometry

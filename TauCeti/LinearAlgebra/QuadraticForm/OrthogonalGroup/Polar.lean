/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Orthogonal groups and polar bilinear forms

This file gives the canonical group isomorphism between the orthogonal group of a quadratic form
and the isometry group of its polar bilinear form when multiplication by two is injective. It
records the underlying-linear-map equations in both directions and identifies the two determinant
homomorphisms.

The equivalence lets quadratic-space constructions use the bilinear isometry-group API without
changing their automorphisms. In particular, it is the field-level bridge to bilinear-first
integral lattices, where division by two need not be available.
-/

public section

namespace TauCeti.QuadraticMap

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The canonical group isomorphism between the orthogonal group of a quadratic form and the
isometry group of its polar bilinear form.

The regularity hypothesis on `2` is necessary: in characteristic two the polar form need not
determine the quadratic form. -/
noncomputable def orthogonalGroupEquivIsometryGroupPolarBilin
    (Q : QuadraticForm R M) (h2 : IsSMulRegular R (2 : R)) :
    orthogonalGroup Q ≃* BilinForm.isometryGroup Q.polarBilin :=
  MulEquiv.subgroupCongr (orthogonalGroup_eq_isometryGroup_polarBilin h2 Q)

/-- The quadratic-to-bilinear orthogonal-group equivalence does not change the underlying linear
automorphism. -/
@[simp]
theorem coe_orthogonalGroupEquivIsometryGroupPolarBilin_apply
    (Q : QuadraticForm R M) (h2 : IsSMulRegular R (2 : R)) (g : orthogonalGroup Q) :
    (orthogonalGroupEquivIsometryGroupPolarBilin Q h2 g : M ≃ₗ[R] M) = g := by
  simp [orthogonalGroupEquivIsometryGroupPolarBilin]

/-- The inverse quadratic-to-bilinear orthogonal-group equivalence does not change the underlying
linear automorphism. -/
@[simp]
theorem coe_orthogonalGroupEquivIsometryGroupPolarBilin_symm_apply
    (Q : QuadraticForm R M) (h2 : IsSMulRegular R (2 : R))
    (g : BilinForm.isometryGroup Q.polarBilin) :
    ((orthogonalGroupEquivIsometryGroupPolarBilin Q h2).symm g : M ≃ₗ[R] M) = g := by
  simp [orthogonalGroupEquivIsometryGroupPolarBilin]

end TauCeti.QuadraticMap

namespace QuadraticMap

open TauCeti.QuadraticMap

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- Passing from a quadratic form to its polar bilinear form preserves the determinant
homomorphism. -/
theorem isometryDet_comp_orthogonalGroupEquivIsometryGroupPolarBilin
    (Q : QuadraticForm R M) (h2 : IsSMulRegular R (2 : R)) :
    (LinearMap.BilinForm.isometryDet Q.polarBilin).comp
        (orthogonalGroupEquivIsometryGroupPolarBilin Q h2).toMonoidHom = orthogonalDet Q := by
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearMap.BilinForm.isometryDet_apply,
    coe_orthogonalGroupEquivIsometryGroupPolarBilin_apply, orthogonalDet_apply]

/-- The quadratic-to-bilinear equivalences for the full and determinant-one isometry groups
commute with their canonical inclusions. -/
@[simp]
theorem orthogonalGroupEquivIsometryGroupPolarBilin_specialOrthogonalToOrthogonal
    (Q : QuadraticForm R M) (h2 : IsSMulRegular R (2 : R))
    (g : TauCeti.QuadraticMap.specialOrthogonalGroup Q) :
    orthogonalGroupEquivIsometryGroupPolarBilin Q h2
        (specialOrthogonalToOrthogonal Q g) =
      LinearMap.BilinForm.specialIsometryToIsometry Q.polarBilin
        (TauCeti.QuadraticMap.specialOrthogonalGroupEquivSpecialIsometryGroupPolarBilin
          Q h2 g) := by
  apply Subtype.ext
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryGroupPolarBilin_apply,
    coe_specialOrthogonalToOrthogonal, LinearMap.BilinForm.coe_specialIsometryToIsometry,
    TauCeti.QuadraticMap.coe_specialOrthogonalGroupEquivSpecialIsometryGroupPolarBilin_apply]

end QuadraticMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.Algebra.MonoidAlgebra.Dual

/-!
# The Auslander--Reiten transpose over a finite group algebra

The symmetric Frobenius duality for a finite group algebra rewrites the transpose of a
presentation arrow using ordinary base-ring duals. Concretely, the cokernel of
`Hom_{R[G]}(f, R[G])` is the quotient of `Hom_R(P₁, R)` by contragredient precomposition with `f`.
This is the algebraic bridge between a transpose over `ℤ_p[G]` and the Pontryagin-dual
description of its `Ext¹` group.

## Main definitions

* `TauCeti.AuslanderReitenTranspose.groupAlgebraDualEquiv`: the transpose, expressed as a quotient
  of an ordinary base-ring dual.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323,
  Springer (2008), (5.4.11) and (5.6.9).
-/

public section

noncomputable section

namespace TauCeti.AuslanderReitenTranspose

variable {R G P₀ P₁ : Type*} [CommRing R] [Group G] [Finite G]
  [AddCommMonoid P₀] [Module (MonoidAlgebra R G) P₀] [Module R P₀]
  [IsScalarTower R (MonoidAlgebra R G) P₀]
  [AddCommMonoid P₁] [Module (MonoidAlgebra R G) P₁] [Module R P₁]
  [IsScalarTower R (MonoidAlgebra R G) P₁]

/-- Over a finite group algebra, the transpose of `f` is the cokernel of ordinary
base-ring-dual precomposition with its contragredient action. -/
noncomputable def groupAlgebraDualEquiv (f : P₁ →ₗ[MonoidAlgebra R G] P₀) :
    AuslanderReitenTranspose f ≃ₗ[(MonoidAlgebra R G)ᵐᵒᵖ]
      Module.Dual R P₁ ⧸ LinearMap.range (LinearMap.contragredientDualMap f) :=
  quotientEquiv f _ (MonoidAlgebra.dualLinearEquiv (G := G) (M := P₁))
    (LinearMap.map_range_lcomp_dualLinearEquiv f)

/-- `groupAlgebraDualEquiv` sends a group-algebra functional to the class of its
coefficient-at-one functional. -/
@[simp]
theorem groupAlgebraDualEquiv_mk (f : P₁ →ₗ[MonoidAlgebra R G] P₀)
    (φ : Module.Dual (MonoidAlgebra R G) P₁) :
    groupAlgebraDualEquiv f (mk f φ) =
      Submodule.Quotient.mk (MonoidAlgebra.dualLinearEquiv φ) :=
  quotientEquiv_mk f _ _ _ φ

/-- The inverse of `groupAlgebraDualEquiv` sends the class of a base-ring functional to the class
of the corresponding group-algebra functional. -/
@[simp]
theorem groupAlgebraDualEquiv_symm_mk (f : P₁ →ₗ[MonoidAlgebra R G] P₀)
    (ψ : Module.Dual R P₁) :
    (groupAlgebraDualEquiv f).symm (Submodule.Quotient.mk ψ) =
      mk f (MonoidAlgebra.dualLinearEquiv.symm ψ) :=
  quotientEquiv_symm_mk f _ _ _ ψ

end TauCeti.AuslanderReitenTranspose

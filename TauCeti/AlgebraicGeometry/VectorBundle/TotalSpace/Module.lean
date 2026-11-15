/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Module
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.Group

/-!
# Scalar multiplication on vector-bundle total spaces

The total space `𝕍(E) = Spec_X (Sym E^∨)` carries the scalar action of the affine line on a
linear spectrum. Under the section correspondence, this action is multiplication of sections
by regular functions on the test scheme. Together with `totalSpaceHomAddEquiv`, this identifies
both linear operations on points with those on sections, not just their underlying sets.
Bundle morphisms commute with the action.

The action and its unitality and associativity are inherited from
`modObjRelativeSpecSymmetricAlgebra`. Distributivity is inherited from
`lift_add_right_comp_relativeSpecSymmetricAlgebraSMul` and
`lift_add_left_comp_relativeSpecSymmetricAlgebraSMul`. Here `ModObj` denotes the action of the
multiplicative monoid of the affine line; it does not itself assert distributivity.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CommRingObj MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X)

/-- The affine line acts on the total space of a vector bundle by scalar multiplication. -/
instance modObjTotalSpaceScheme :
    ModObj (𝔸(PUnit.{u + 1}; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :=
  modObjRelativeSpecSymmetricAlgebra ((toQuasicoherent X).obj (dual E))

/-- The scalar action on a total space is the action on the linear spectrum of its dual. -/
@[simp]
theorem smul_totalSpaceScheme :
    γ[𝔸(PUnit.{u + 1}; X).asOver X,
        (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)] =
      relativeSpecSymmetricAlgebraSMul ((toQuasicoherent X).obj (dual E)) :=
  (rfl)

/-- Scalar multiplication on total-space points is multiplication of their sections by the
corresponding regular function on the test scheme. -/
@[simp]
theorem totalSpaceHomEquiv_lift_comp_smul {T : Over X}
    (a : T ⟶ 𝔸(PUnit.{u + 1}; X).asOver X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv E T (lift a t ≫
        relativeSpecSymmetricAlgebraSMul ((toQuasicoherent X).obj (dual E))) =
      totalSpaceHomEquiv E T t ≫ Scheme.Modules.globalSectionsSmul _
        (AffineSpace.homAsOverEquiv T a .unit) := by
  simp only [totalSpaceHomEquiv_apply]
  -- Rewriting inside the scheme-module wrappers cannot infer the relative-spectrum carrier;
  -- apply the functional formula as a term, then reassociate before using duality.
  refine (congrArg (fun φ ↦ Scheme.Modules.dualHomUnitEquiv _ (inv _ ≫ φ))
    (relativeSpecSymmetricAlgebraPullbackHomEquiv_lift_comp_smul
      ((toQuasicoherent X).obj (dual E)) a t)).trans ?_
  exact (congrArg (Scheme.Modules.dualHomUnitEquiv _) (Category.assoc _ _ _).symm).trans
    (Scheme.Modules.dualHomUnitEquiv_comp_globalSectionsSmul _ _ _)

variable {E} in
/-- A bundle morphism induces a morphism of total spaces commuting with scalar multiplication
by the affine line. -/
instance isModHom_totalSpaceScheme_map {F : FiniteLocallyFreeSheaf X} (a : E ⟶ F) :
    IsModHom (𝔸(PUnit.{u + 1}; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map a)) :=
  isModHom_relativeSpec_map ((toQuasicoherent X).map (dualFunctor.map a.op : dual F ⟶ dual E))

end

end TauCeti.AlgebraicGeometry

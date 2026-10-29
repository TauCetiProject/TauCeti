/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.LinearScheme
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Geometric vector bundles

A geometric vector bundle over a scheme `X` is a linear scheme over `X`, that is an affine scheme
`p : V ⟶ X` with a grading `p_* 𝒪_V ≅ ⨁ₙ Aₙ` freely generated in degree one, whose degree-one
component `A₁` is finite locally free. This is the definition of a vector bundle in the Stacks
Project ([Tag 062M](https://stacks.math.columbia.edu/tag/062M): `A₀ = 𝒪_X` and the maps
`Symⁿ A₁ ⟶ Aₙ` are isomorphisms), restricted to finite locally free `A₁`; no rank is fixed.
Geometric vector bundles form the full subcategory `GeometricVectorBundle X` of
`QuasicoherentLinearScheme X`, so, as in the Stacks Project, their morphisms are the morphisms of
schemes over `X` that preserve the gradings. Over an open set where the degree-one components of
source and target are free, such a morphism is given in linear coordinates by a matrix of
functions on `X`. Over a non-reduced base this is stronger than being linear on every fibre: over
`ℚ[ε]/(ε²)`, the automorphism `t ↦ t + εt²` of the affine line is the identity on the only fibre
but does not preserve the grading.

Hartshorne (Exercise II.5.18) instead defines a geometric vector bundle of rank `n` by local
trivialisations `p⁻¹(Uᵢ) ≅ 𝔸ⁿ_{Uᵢ}` whose transition automorphisms are linear. The geometric
vector bundles of constant rank `n` here are the same objects: locally, a trivialisation of `A₁`
identifies `Sym A₁` with a polynomial algebra over `𝒪_X`, and the graded automorphisms of a
polynomial algebra are exactly its linear changes of coordinates. This comparison with the chart
definition is not formalised.

Restricting the anti-equivalence `linearSpecEquiv X` between quasicoherent sheaves and linear
schemes to finite locally free sheaves gives an anti-equivalence
`linearSpecFiniteLocallyFreeEquiv X : (FiniteLocallyFreeSheaf X)ᵒᵖ ≌ GeometricVectorBundle X`.
Composing it with the duality anti-equivalence `E ↦ E^∨` of finite locally free sheaves gives the
equivalence

```text
totalSpaceEquiv X : FiniteLocallyFreeSheaf X ≌ GeometricVectorBundle X
```

whose functor is the geometric total space `totalSpace X`, sending a finite locally free sheaf
`E` to the linear scheme `𝕍(E) = Spec_X (Sym E^∨)`, and whose inverse sends a geometric vector
bundle to the dual of its degree-one component. Forgetting the grading, `totalSpace X` is the
total-space functor `totalSpaceScheme X` to affine schemes over `X` (`totalSpaceForgetIso X`),
whose points are the sections of `E` (`totalSpaceHomEquiv`).

## Notation

In this file, as for `totalSpaceScheme X`, `𝕍(E)` denotes the total space `Spec_X (Sym E^∨)` of a
finite locally free sheaf `E`, which is covariant in `E`. Following the Stacks Project
([Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)) and EGA II, the docstrings of
`linearSpec X` instead write `𝕍(F) = Spec_X (Sym F)`, which is contravariant in `F`. In that
notation the total space of `E` is `𝕍(E^∨)`, and `linearSpecFiniteLocallyFreeEquiv X` sends `E`
to `𝕍(E)`.

## Main declarations

* `TauCeti.AlgebraicGeometry.GeometricVectorBundle X`: linear schemes over `X` whose degree-one
  component is finite locally free;
* `TauCeti.AlgebraicGeometry.linearSpecFiniteLocallyFreeEquiv X`: the anti-equivalence
  `E ↦ Spec_X (Sym E)` between finite locally free sheaves and geometric vector bundles;
* `TauCeti.AlgebraicGeometry.totalSpace X`: the covariant total-space functor
  `E ↦ Spec_X (Sym E^∨)` to geometric vector bundles;
* `TauCeti.AlgebraicGeometry.totalSpaceEquiv X`: the equivalence
  `FiniteLocallyFreeSheaf X ≌ GeometricVectorBundle X` with functor `totalSpace X`;
* `TauCeti.AlgebraicGeometry.totalSpaceForgetIso X`: forgetting the grading of `totalSpace X`
  gives `totalSpaceScheme X`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1) (vector bundles);
  the definition used here is [Tag 062M](https://stacks.math.columbia.edu/tag/062M).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.18 (geometric vector bundles of rank `n`
  defined by linear transition maps, and their bijection with locally free sheaves of rank `n` on
  isomorphism classes; this chart definition is not the one used here).
-/

public section

open CategoryTheory Limits CategoricalPullback Opposite _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- A linear scheme over `X` is a geometric vector bundle when the degree-one component of its
grading is finite locally free. -/
def isGeometricVectorBundle : ObjectProperty (QuasicoherentLinearScheme X) :=
  (QuasicoherentSheaf.isFiniteLocallyFree X).op.inverseImage (QuasicoherentLinearScheme.degreeOne X)

variable {X} in
/-- A linear scheme is a geometric vector bundle exactly when the degree-one component of its
grading is finite locally free. -/
theorem isGeometricVectorBundle_iff (V : QuasicoherentLinearScheme X) :
    isGeometricVectorBundle X V ↔
      Scheme.Modules.isFiniteLocallyFree X
        ((QuasicoherentLinearScheme.degreeOne X).obj V).unop.obj :=
  Iff.rfl

/-- Being a geometric vector bundle is invariant under isomorphism of linear schemes. -/
instance : (isGeometricVectorBundle X).IsClosedUnderIsomorphisms :=
  inferInstanceAs ((QuasicoherentSheaf.isFiniteLocallyFree X).op.inverseImage
    (QuasicoherentLinearScheme.degreeOne X)).IsClosedUnderIsomorphisms

/-- The category of geometric vector bundles over `X`: linear schemes over `X` (the vector
bundles of the Stacks Project, [Tag 062M](https://stacks.math.columbia.edu/tag/062M)) whose
degree-one component is finite locally free. Morphisms are the morphisms of linear schemes, that
is the morphisms of schemes over `X` preserving the gradings. The comparison with Hartshorne's
definition by local trivialisations with linear transition maps is not formalised. -/
abbrev GeometricVectorBundle : Type (u + 1) :=
  (isGeometricVectorBundle X).FullSubcategory

variable {X} in
/-- The linear scheme `Spec_X (Sym F)` of a quasicoherent sheaf `F` is a geometric vector bundle
exactly when `F` is finite locally free, since its degree-one component recovers `F`. -/
theorem isGeometricVectorBundle_linearSpec_obj_iff (F : (QuasicoherentSheaf X)ᵒᵖ) :
    isGeometricVectorBundle X ((linearSpec X).obj F) ↔
      Scheme.Modules.isFiniteLocallyFree X F.unop.obj :=
  (QuasicoherentSheaf.isFiniteLocallyFree X).op.prop_iff_of_iso (degreeOneLinearSpecIso F)

/-- **Finite locally free sheaves are anti-equivalent to geometric vector bundles.** The
restriction of `linearSpecEquiv X` to finite locally free sheaves: the functor sends `E` to the
linear scheme `Spec_X (Sym E)` and the inverse reads off the degree-one component. The unit is
the identification `Sym¹ E ≅ E` and the counit is `linearSpecDegreeOneIso`. -/
-- Exposed so that the functor, inverse, unit and counit lemmas below typecheck by unfolding.
@[expose]
def linearSpecFiniteLocallyFreeEquiv :
    (FiniteLocallyFreeSheaf X)ᵒᵖ ≌ GeometricVectorBundle X where
  functor := (isGeometricVectorBundle X).lift
    ((FiniteLocallyFreeSheaf.toQuasicoherent X).op ⋙ linearSpec X)
    fun E ↦ (isGeometricVectorBundle_linearSpec_obj_iff _).2 E.unop.property
  inverse := ((Scheme.Modules.isFiniteLocallyFree X).lift
    (((isGeometricVectorBundle X).ι ⋙ QuasicoherentLinearScheme.degreeOne X).leftOp ⋙
      ObjectProperty.ι _)
    fun V ↦ (isGeometricVectorBundle_iff V.unop.obj).1 V.unop.property).rightOp
  unitIso := NatIso.ofComponents
    (fun E ↦ ((Scheme.Modules.isFiniteLocallyFree X).isoMk
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapIso
        ((linearSpecEquiv X).unitIso.app
          (op ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.unop))).unop)).op)
    fun f ↦ Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ (congrArg (fun g ↦ g.unop.hom)
      ((linearSpecEquiv X).unitIso.hom.naturality
        ((FiniteLocallyFreeSheaf.toQuasicoherent X).map f.unop).op)))
  counitIso := NatIso.ofComponents
    (fun V ↦ (isGeometricVectorBundle X).isoMk ((linearSpecEquiv X).counitIso.app V.obj))
    fun f ↦ ObjectProperty.hom_ext _ ((linearSpecEquiv X).counitIso.hom.naturality f.hom)
  functor_unitIso_comp E := by
    have h := (linearSpecEquiv X).functor_unitIso_comp
      (op ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.unop))
    exact ObjectProperty.hom_ext _ h

variable {X}

/-- The linear scheme underlying the geometric vector bundle of `E` under
`linearSpecFiniteLocallyFreeEquiv X` is `Spec_X (Sym E)`. -/
@[simp]
theorem linearSpecFiniteLocallyFreeEquiv_functor_obj_obj (E : (FiniteLocallyFreeSheaf X)ᵒᵖ) :
    ((linearSpecFiniteLocallyFreeEquiv X).functor.obj E).obj =
      (linearSpec X).obj (op ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.unop)) :=
  (rfl)

/-- On morphisms, the functor of `linearSpecFiniteLocallyFreeEquiv X` is `linearSpec X`. -/
@[simp]
theorem linearSpecFiniteLocallyFreeEquiv_functor_map_hom {E F : (FiniteLocallyFreeSheaf X)ᵒᵖ}
    (f : E ⟶ F) :
    ((linearSpecFiniteLocallyFreeEquiv X).functor.map f).hom =
      (linearSpec X).map ((FiniteLocallyFreeSheaf.toQuasicoherent X).map f.unop).op :=
  (rfl)

/-- The inverse of `linearSpecFiniteLocallyFreeEquiv X` sends a geometric vector bundle to its
degree-one component. -/
@[simp]
theorem linearSpecFiniteLocallyFreeEquiv_inverse_obj (V : GeometricVectorBundle X) :
    (linearSpecFiniteLocallyFreeEquiv X).inverse.obj V =
      op ⟨((QuasicoherentLinearScheme.degreeOne X).obj V.obj).unop.obj,
        (isGeometricVectorBundle_iff _).1 V.property⟩ :=
  (rfl)

/-- On morphisms, the inverse of `linearSpecFiniteLocallyFreeEquiv X` is the degree-one functor. -/
@[simp]
theorem linearSpecFiniteLocallyFreeEquiv_inverse_map_unop_hom {V W : GeometricVectorBundle X}
    (f : V ⟶ W) :
    ((linearSpecFiniteLocallyFreeEquiv X).inverse.map f).unop.hom =
      ((QuasicoherentLinearScheme.degreeOne X).map f.hom).unop.hom :=
  (rfl)

/-- The unit of `linearSpecFiniteLocallyFreeEquiv X` at `E` is the identification `Sym¹ E ≅ E` of
the degree-one component of `Spec_X (Sym E)` with `E`. -/
@[simp]
theorem linearSpecFiniteLocallyFreeEquiv_unit_app_unop_hom (E : (FiniteLocallyFreeSheaf X)ᵒᵖ) :
    ((linearSpecFiniteLocallyFreeEquiv X).unit.app E).unop.hom =
      ((gradedSymmetricAlgebraDegreeOneIso X).hom.app
        ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.unop)).hom := by
  have h := (linearSpecEquiv_unit_app (op ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj
    E.unop))).trans (degreeOneLinearSpecIso_inv _)
  exact congrArg (fun g ↦ g.unop.hom) h

/-- The counit of `linearSpecFiniteLocallyFreeEquiv X` at `V` is the isomorphism
`Spec_X (Sym A₁) ≅ V` of `linearSpecDegreeOneIso`. -/
@[simp]
theorem linearSpecFiniteLocallyFreeEquiv_counit_app_hom (V : GeometricVectorBundle X) :
    ((linearSpecFiniteLocallyFreeEquiv X).counit.app V).hom =
      (linearSpecDegreeOneIso V.obj).hom :=
  linearSpecEquiv_counit_app V.obj

variable (X)

/-- The geometric total space `𝕍(E) = Spec_X (Sym E^∨)` of a finite locally free sheaf `E`, as a
geometric vector bundle: the linear scheme of the dual `E^∨ = 𝓗om(E, 𝒪_X)`. It is covariant in
`E`. In the notation `𝕍(F) = Spec_X (Sym F)` of `linearSpec X`, it is `𝕍(E^∨)`. -/
-- Exposed, like `linearSpec`, so that its objects and morphisms are computed by unfolding.
@[expose]
def totalSpace : FiniteLocallyFreeSheaf X ⥤ GeometricVectorBundle X :=
  FiniteLocallyFreeSheaf.dualFunctor.rightOp ⋙ (linearSpecFiniteLocallyFreeEquiv X).functor

variable {X}

/-- The linear scheme underlying the total space of `E` is `Spec_X (Sym E^∨)`. -/
@[simp]
theorem totalSpace_obj_obj (E : FiniteLocallyFreeSheaf X) :
    ((totalSpace X).obj E).obj =
      (linearSpec X).obj
        (op ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj (FiniteLocallyFreeSheaf.dual E))) :=
  (rfl)

/-- A morphism `a : E ⟶ F` acts on total spaces through `linearSpec X` of its dual
`F^∨ ⟶ E^∨`. -/
@[simp]
theorem totalSpace_map_hom {E F : FiniteLocallyFreeSheaf X} (a : E ⟶ F) :
    ((totalSpace X).map a).hom =
      (linearSpec X).map ((FiniteLocallyFreeSheaf.toQuasicoherent X).map
        (FiniteLocallyFreeSheaf.dualFunctor.map a.op :
          FiniteLocallyFreeSheaf.dual F ⟶ FiniteLocallyFreeSheaf.dual E)).op :=
  (rfl)

variable (X)

/-- Forgetting the grading of the total space `totalSpace X` gives the total space
`totalSpaceScheme X` as an affine scheme over `X`. -/
def totalSpaceForgetIso :
    totalSpace X ⋙ (isGeometricVectorBundle X).ι ⋙ (isQuasicoherentLinearScheme X).ι ⋙
        π₁ (affineFunctions X) GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op ≅
      totalSpaceScheme X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- The comparison `totalSpaceForgetIso` is the identity on each object. -/
@[simp]
theorem totalSpaceForgetIso_hom_app (E : FiniteLocallyFreeSheaf X) :
    (totalSpaceForgetIso X).hom.app E = 𝟙 _ :=
  (rfl)

/-- The comparison `totalSpaceForgetIso` is the identity on each object. -/
@[simp]
theorem totalSpaceForgetIso_inv_app (E : FiniteLocallyFreeSheaf X) :
    (totalSpaceForgetIso X).inv.app E = 𝟙 _ :=
  (rfl)

/-- **Finite locally free sheaves are equivalent to geometric vector bundles.** The functor is the
geometric total space `totalSpace X`, sending `E` to `Spec_X (Sym E^∨)`, and the inverse sends a
geometric vector bundle to the dual of its degree-one component. It is the duality
anti-equivalence `E ↦ E^∨` followed by `linearSpecFiniteLocallyFreeEquiv X`. -/
-- Exposed so that the functor, unit and counit lemmas below typecheck by unfolding.
@[expose]
def totalSpaceEquiv : FiniteLocallyFreeSheaf X ≌ GeometricVectorBundle X :=
  FiniteLocallyFreeSheaf.dualEquiv.trans (linearSpecFiniteLocallyFreeEquiv X)

/-- The functor of `totalSpaceEquiv X` is the total space. -/
@[simp]
theorem totalSpaceEquiv_functor : (totalSpaceEquiv X).functor = totalSpace X :=
  (rfl)

/-- The inverse of `totalSpaceEquiv X` is the degree-one functor followed by dualization. -/
@[simp]
theorem totalSpaceEquiv_inverse :
    (totalSpaceEquiv X).inverse =
      (linearSpecFiniteLocallyFreeEquiv X).inverse ⋙ FiniteLocallyFreeSheaf.dualFunctor :=
  (rfl)

variable {X}

/-- The unit of `totalSpaceEquiv X` at `E` is the bidual isomorphism `E ≅ E^∨∨` followed by the
dual of the identification `Sym¹ E^∨ ≅ E^∨` of the degree-one component of `Spec_X (Sym E^∨)`. -/
@[simp]
theorem totalSpaceEquiv_unit_app (E : FiniteLocallyFreeSheaf X) :
    (totalSpaceEquiv X).unit.app E =
      (FiniteLocallyFreeSheaf.evalIso E).hom ≫
        FiniteLocallyFreeSheaf.dualFunctor.map (X := op (FiniteLocallyFreeSheaf.dual E))
          (Y := (linearSpecFiniteLocallyFreeEquiv X).inverse.obj ((totalSpace X).obj E))
          ((linearSpecFiniteLocallyFreeEquiv X).unit.app (op (FiniteLocallyFreeSheaf.dual E))) := by
  refine (Equivalence.trans_unit_app _ _ E).trans ?_
  rw [Equivalence.unit, FiniteLocallyFreeSheaf.dualEquiv_unitIso,
    FiniteLocallyFreeSheaf.evalNatIso_hom_app]
  -- The inverse of `dualEquiv` is `dualFunctor` and its functor sends `E` to `op (dual E)`, both
  -- by definition (`dualEquiv_inverse`, `dualEquiv_functor`).
  rfl

/-- The counit of `totalSpaceEquiv X` at `V`, with degree-one component `A₁`, is `linearSpec X` of
the bidual isomorphism `A₁ ≅ A₁^∨∨`, followed by the counit `Spec_X (Sym A₁) ≅ V` of
`linearSpecFiniteLocallyFreeEquiv X`. -/
@[simp]
theorem totalSpaceEquiv_counit_app (V : GeometricVectorBundle X) :
    (totalSpaceEquiv X).counit.app V =
      (linearSpecFiniteLocallyFreeEquiv X).functor.map
          (X := op (FiniteLocallyFreeSheaf.dual (FiniteLocallyFreeSheaf.dual
            ((linearSpecFiniteLocallyFreeEquiv X).inverse.obj V).unop)))
          (Y := (linearSpecFiniteLocallyFreeEquiv X).inverse.obj V)
          (FiniteLocallyFreeSheaf.evalIso
            ((linearSpecFiniteLocallyFreeEquiv X).inverse.obj V).unop).hom.op ≫
        (linearSpecFiniteLocallyFreeEquiv X).counit.app V := by
  refine (Equivalence.trans_counit_app _ _ V).trans ?_
  rw [Equivalence.counit, ← Iso.app_hom, FiniteLocallyFreeSheaf.dualEquiv_counitIso_app, Iso.op_hom]
  -- The inverse of `dualEquiv` is `dualFunctor`, by definition (`dualEquiv_inverse`).
  rfl

variable (X) in
/-- The total space is an equivalence, in particular fully faithful and essentially surjective. -/
instance totalSpace_isEquivalence : (totalSpace X).IsEquivalence :=
  (totalSpaceEquiv X).isEquivalence_functor

end

end TauCeti.AlgebraicGeometry

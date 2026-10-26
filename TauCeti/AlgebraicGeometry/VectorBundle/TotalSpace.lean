/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Bidual
public import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Pullback

/-!
# The geometric total space of a vector bundle

The geometric total space of a finite locally free sheaf `E` on a scheme `X` is the relative
spectrum `𝕍(E) = Spec_X (Sym E^∨)` of the symmetric algebra of its dual `E^∨ = 𝓗om(E, 𝒪_X)`.
Since dualization and relative `Spec` are both contravariant, this is a covariant functor
`totalSpaceScheme X` from finite locally free sheaves to affine schemes over `X`.

Its points are the sections of `E`: for a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ 𝕍(E)` over `X` correspond to global sections `𝒪_T ⟶ q^* E` of the pullback of `E`
(`totalSpaceHomEquiv`). This combines the universal property of `Spec_X (Sym F)`, whose points
are the linear functionals `q^* F ⟶ 𝒪_T`, with the base-change isomorphism
`q^* (E^∨) ≅ (q^* E)^∨` and the identification of linear functionals on `(q^* E)^∨` with sections
of `q^* E`, a section corresponding to evaluation at it. The correspondence is natural in the
vector bundle: a morphism `a : E ⟶ F` acts on points of the total spaces as `q^* a` acts on
sections (`totalSpaceHomEquiv_comp_map`).

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceScheme X`: the functor `E ↦ Spec_X (Sym E^∨)` from finite
  locally free sheaves on `X` to affine schemes over `X`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv E T`: morphisms `T ⟶ Spec_X (Sym E^∨)` over `X`
  are global sections of `q^* E`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_symm_apply`: the morphism of a section `s` is the
  one whose linear functional on `q^* (E^∨) ≅ (q^* E)^∨` is evaluation at `s`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_comp_map`: naturality in the vector bundle.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.18.
* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable (X : Scheme.{u})

-- Exposed so that points of `𝕍(E)` are visibly points of `Spec_X (Sym E^∨)`, to which the
-- universal property `relativeSpecSymmetricAlgebraPullbackHomEquiv` applies, and so that
-- `totalSpaceScheme_map` can be stated without transport along `totalSpaceScheme_obj`.
/-- The geometric total space `𝕍(E) = Spec_X (Sym E^∨)` of a finite locally free sheaf `E`, as a
covariant functor to affine schemes over `X`: the dual `E^∨ = 𝓗om(E, 𝒪_X)`, viewed as a
quasicoherent sheaf, followed by the relative spectrum of its symmetric algebra. -/
@[expose]
def totalSpaceScheme : FiniteLocallyFreeSheaf X ⥤ AffineSchemeOver X :=
  dualFunctor.rightOp ⋙ (toQuasicoherent X).op ⋙ (symmetricAlgebra X).op ⋙ relativeSpec X

variable {X}

/-- The total space of `E` is the relative spectrum of the symmetric algebra of its dual. -/
@[simp]
theorem totalSpaceScheme_obj (E : FiniteLocallyFreeSheaf X) :
    (totalSpaceScheme X).obj E =
      (relativeSpec X).obj (op ((symmetricAlgebra X).obj ((toQuasicoherent X).obj (dual E)))) :=
  (rfl)

/-- A morphism `a : E ⟶ F` acts on total spaces through the relative spectrum of the symmetric
algebra of its dual `F^∨ ⟶ E^∨`. -/
@[simp]
theorem totalSpaceScheme_map {E F : FiniteLocallyFreeSheaf X} (a : E ⟶ F) :
    (totalSpaceScheme X).map a =
      (relativeSpec X).map ((symmetricAlgebra X).map
        ((toQuasicoherent X).map (dualFunctor.map a.op : dual F ⟶ dual E))).op :=
  (rfl)

/-- **Points of the total space of a vector bundle are sections.** For a finite locally free
sheaf `E` on `X` and a scheme `q : T ⟶ X` over `X`, morphisms `T ⟶ Spec_X (Sym E^∨)` over `X`
correspond to global sections `𝒪_T ⟶ q^* E` of the pullback of `E`.

It is the linear-functional form `relativeSpecSymmetricAlgebraPullbackHomEquiv` of the universal
property of `Spec_X (Sym E^∨)`, followed by the base-change isomorphism
`q^* 𝓗om(E, 𝒪_X) ≅ 𝓗om(q^* E, 𝒪_T)` (the canonical comparison `pullbackIhomComparison`, invertible
for finite locally free `E`, and `Scheme.Modules.pullbackObjUnitIso`) and the identification
`Scheme.Modules.dualHomUnitEquiv` of linear functionals on `𝓗om(q^* E, 𝒪_T)` with sections of
`q^* E`. -/
def totalSpaceHomEquiv (E : FiniteLocallyFreeSheaf X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) ≃
      (𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj E.obj) :=
  (relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T).trans <|
    ((asIso ((pullbackIhomComparison E.obj T.hom).app (𝟙_ X.Modules) ≫
      (ihom ((Scheme.Modules.pullback T.hom).obj E.obj)).map
        (Scheme.Modules.pullbackObjUnitIso T.hom).hom)).homCongr (Iso.refl _)).trans
      (Scheme.Modules.dualHomUnitEquiv ((Scheme.Modules.pullback T.hom).obj E.obj))

/-- The section of a morphism `t : T ⟶ Spec_X (Sym E^∨)` over `X` is the section of the linear
functional `𝓗om(q^* E, 𝒪_T) ≅ q^* 𝓗om(E, 𝒪_X) ⟶ 𝒪_T` of `t`. -/
theorem totalSpaceHomEquiv_apply (E : FiniteLocallyFreeSheaf X) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv E T t =
      Scheme.Modules.dualHomUnitEquiv ((Scheme.Modules.pullback T.hom).obj E.obj)
        (inv ((pullbackIhomComparison E.obj T.hom).app (𝟙_ X.Modules) ≫
            (ihom ((Scheme.Modules.pullback T.hom).obj E.obj)).map
              (Scheme.Modules.pullbackObjUnitIso T.hom).hom) ≫
          relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T t) :=
  congrArg (fun φ ↦ Scheme.Modules.dualHomUnitEquiv _ (inv _ ≫ φ))
    (Category.comp_id _ : _ ≫ 𝟙 (𝟙_ T.left.Modules) = _)

/-- The morphism `T ⟶ Spec_X (Sym E^∨)` over `X` of a section `s` of `q^* E` is the one whose
linear functional `q^* 𝓗om(E, 𝒪_X) ≅ 𝓗om(q^* E, 𝒪_T) ⟶ 𝒪_T` is evaluation at `s`. -/
theorem totalSpaceHomEquiv_symm_apply (E : FiniteLocallyFreeSheaf X) (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj E.obj) :
    (totalSpaceHomEquiv E T).symm s =
      (relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T).symm
        ((pullbackIhomComparison E.obj T.hom).app (𝟙_ X.Modules) ≫
          (ihom ((Scheme.Modules.pullback T.hom).obj E.obj)).map
            (Scheme.Modules.pullbackObjUnitIso T.hom).hom ≫
          (λ_ _).inv ≫
            s ▷ (ihom ((Scheme.Modules.pullback T.hom).obj E.obj)).obj (𝟙_ T.left.Modules) ≫
            (ihom.ev ((Scheme.Modules.pullback T.hom).obj E.obj)).app (𝟙_ T.left.Modules)) := by
  refine congrArg (relativeSpecSymmetricAlgebraPullbackHomEquiv _ T).symm
    ((congrArg (_ ≫ ·) (Category.comp_id _ : _ ≫ 𝟙 (𝟙_ T.left.Modules) = _)).trans ?_)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (congrArg (_ ≫ ·) (Scheme.Modules.dualHomUnitEquiv_symm_apply _ s)))

/-- **Naturality of the section correspondence in the vector bundle.** Composing a point
`t : T ⟶ 𝕍(E)` with the map of total spaces induced by `a : E ⟶ F` corresponds to applying
`q^* a` to the section of `t`. -/
theorem totalSpaceHomEquiv_comp_map {E F : FiniteLocallyFreeSheaf X} (a : E ⟶ F) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv F T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map a)) =
      totalSpaceHomEquiv E T t ≫ (Scheme.Modules.pullback T.hom).map a.hom := by
  -- The universal property of `Spec_X (Sym F^∨)` turns the map of total spaces into
  -- precomposition with the pullback of the dual map `F^∨ ⟶ E^∨`.
  have key : relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual F)) T
        (t ≫ (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map a)) =
      (Scheme.Modules.pullback T.hom).map ((pre a.hom).app (𝟙_ X.Modules)) ≫
        relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T t :=
    relativeSpecSymmetricAlgebraPullbackHomEquiv_comp_relativeSpec_map
      (F' := (toQuasicoherent X).obj (dual F)) (F := (toQuasicoherent X).obj (dual E))
      ((toQuasicoherent X).map (dualFunctor.map a.op)) T t
  -- The base-change isomorphism of duals is natural, so the pulled-back dual map becomes the
  -- dual map of `q^* a`.
  have hdual : (Scheme.Modules.pullback T.hom).map ((pre a.hom).app (𝟙_ X.Modules)) ≫
        (pullbackIhomComparison E.obj T.hom).app (𝟙_ X.Modules) ≫
          (ihom ((Scheme.Modules.pullback T.hom).obj E.obj)).map
            (Scheme.Modules.pullbackObjUnitIso T.hom).hom =
      ((pullbackIhomComparison F.obj T.hom).app (𝟙_ X.Modules) ≫
          (ihom ((Scheme.Modules.pullback T.hom).obj F.obj)).map
            (Scheme.Modules.pullbackObjUnitIso T.hom).hom) ≫
        (pre ((Scheme.Modules.pullback T.hom).map a.hom)).app (𝟙_ T.left.Modules) :=
    ((reassoc_of% (pullback_map_pre_app_comp_pullbackIhomComparison_app T.hom a.hom
      (𝟙_ X.Modules))) _).trans ((congrArg (_ ≫ ·)
        ((pre ((Scheme.Modules.pullback T.hom).map a.hom)).naturality
          (Scheme.Modules.pullbackObjUnitIso T.hom).hom).symm).trans (Category.assoc _ _ _).symm)
  have hinv := (IsIso.inv_comp_eq _).2
    (((IsIso.eq_comp_inv _).2 hdual).trans (Category.assoc _ _ _))
  rw [totalSpaceHomEquiv_apply, totalSpaceHomEquiv_apply]
  -- `rw` cannot rewrite with `key` or reassociate here: the composites mix the `X.Modules` and
  -- underlying sheaf category instances, so the remaining steps are applied as terms.
  refine (congrArg (fun φ ↦ Scheme.Modules.dualHomUnitEquiv _ (_ ≫ φ)) key).trans
    ((congrArg (Scheme.Modules.dualHomUnitEquiv _) ?_).trans
    (Scheme.Modules.dualHomUnitEquiv_pre_comp
      (M := (Scheme.Modules.pullback T.hom).obj E.obj)
      (N := (Scheme.Modules.pullback T.hom).obj F.obj)
      (inv ((pullbackIhomComparison E.obj T.hom).app (𝟙_ X.Modules) ≫
          (ihom ((Scheme.Modules.pullback T.hom).obj E.obj)).map
            (Scheme.Modules.pullbackObjUnitIso T.hom).hom) ≫
        relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E)) T t)
      ((Scheme.Modules.pullback T.hom).map a.hom)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hinv).trans (Category.assoc _ _ _))

end

end TauCeti.AlgebraicGeometry

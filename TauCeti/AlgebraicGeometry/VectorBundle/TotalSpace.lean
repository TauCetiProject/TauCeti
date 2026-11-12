/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Bidual
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Pullback
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

The total space commutes with base change: for `f : Y ⟶ X`, the total space `𝕍(f^* E)` of the
pulled-back bundle is the fibre product `Y ×_X 𝕍(E)`, naturally in `E`
(`totalSpaceSchemeBaseChangeIso`). This combines `f^* (E^∨) ≅ (f^* E)^∨` with the base change
`Spec_Y (Sym (f^* F)) ≅ Y ×_X Spec_X (Sym F)` of the relative spectrum of a symmetric algebra.
On points this base change is pullback of sections: the projection `𝕍(f^* E) ⟶ 𝕍(E)`
(`totalSpacePullbackFst`) sends the point of a section `s` of `q^* f^* E`, for `q : T ⟶ Y`, to
the point of the section `(q ≫ f)^* E ≅ q^* f^* E` given by `s`
(`totalSpaceHomEquiv_map_comp_totalSpacePullbackFst`).

## Notation

In this file `𝕍(E)` denotes the total space `Spec_X (Sym E^∨)` of a finite locally free sheaf `E`,
which is covariant in `E` and whose sections are the sections of `E`. The references below use the
dual convention: Hartshorne (Exercise II.5.18(a)), the Stacks Project (Definition 27.6.1,
[Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)) and EGA II (1.7.8) define the vector bundle
of a sheaf `F` as `V(F) = Spec_X (Sym F)`, which is contravariant in `F` and whose sheaf of sections
is `F^∨` (Hartshorne, Exercise II.5.18(c); EGA II, 1.7.9). Following them, the docs of the relative
spectrum `Spec_X (Sym F)` and of `linearSpec X` in this library write `𝕍(F) = Spec_X (Sym F)`. In
that notation the total space of `E` is `𝕍(E^∨)`, whose sheaf of sections is `E^∨∨ ≅ E`. The
description of its points over an arbitrary scheme `q : T ⟶ X` (`totalSpaceHomEquiv`) is EGA II
(1.7.8) applied to `F = E^∨`: the points of `V(F)` over `T` are the linear maps `F ⟶ q_* 𝒪_T`.
Hartshorne's exercise describes only sections over open subsets of `X`.

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceScheme X`: the functor `E ↦ Spec_X (Sym E^∨)` from finite
  locally free sheaves on `X` to affine schemes over `X`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv E T`: morphisms `T ⟶ Spec_X (Sym E^∨)` over `X`
  are global sections of `q^* E`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_symm_apply`: the morphism of a section `s` is the
  one whose linear functional on `q^* (E^∨) ≅ (q^* E)^∨` is evaluation at `s`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_comp_map`: naturality in the vector bundle;
* `TauCeti.AlgebraicGeometry.totalSpaceSchemeBaseChangeIso`: the total space of `f^* E` is the
  base change of the total space of `E`, naturally in `E`.
* `TauCeti.AlgebraicGeometry.totalSpacePullbackFst`: the projection `𝕍(f^* E) ⟶ 𝕍(E)`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_map_comp_totalSpacePullbackFst`: the projection
  acts on sections by the composition isomorphism `(q ≫ f)^* E ≅ q^* f^* E`.

## References

These use the convention `V(F) = Spec_X (Sym F)`; see Notation.

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
quasicoherent sheaf, followed by the relative spectrum of its symmetric algebra. In the notation
`𝕍(F) = Spec_X (Sym F)` of the references and of `linearSpec X`, it is `𝕍(E^∨)`. -/
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


section BaseChange

variable {Y : Scheme.{u}} (f : Y ⟶ X)

/-- **Base change of the total space of a vector bundle.** For a morphism of schemes `f : Y ⟶ X`
and a finite locally free sheaf `E` on `X`, the total space `𝕍(f^* E)` of the pulled-back bundle
is the base change `Y ×_X 𝕍(E)` of the total space of `E`, as affine schemes over `Y` and
naturally in `E`. It combines the identification `f^* (E^∨) ≅ (f^* E)^∨` (`pullbackDualIso`) with
the base change of the relative spectrum of a symmetric algebra
(`relativeSpecSymmetricAlgebraBaseChangeIso`). -/
def totalSpaceSchemeBaseChangeIso :
    FiniteLocallyFreeSheaf.pullback f ⋙ totalSpaceScheme Y ≅
      totalSpaceScheme X ⋙ baseChangeAffineSchemeOver f :=
  Functor.isoWhiskerRight
      (NatIso.ofComponents (F := FiniteLocallyFreeSheaf.pullback f ⋙ dualFunctor.rightOp)
        (G := dualFunctor.rightOp ⋙ (FiniteLocallyFreeSheaf.pullback f).op)
        (fun E ↦ (pullbackDualIso f E).op)
        fun g ↦ Quiver.Hom.unop_inj (pullbackDualIso_naturality f g).symm)
      ((toQuasicoherent Y).op ⋙ (symmetricAlgebra Y).op ⋙ relativeSpec Y) ≪≫
    Functor.isoWhiskerLeft dualFunctor.rightOp
      (Functor.isoWhiskerRight
        ((NatIso.op (pullbackToQuasicoherentIso f)).symm :
          (FiniteLocallyFreeSheaf.pullback f).op ⋙ (toQuasicoherent Y).op ≅
            (toQuasicoherent X).op ⋙ (QuasicoherentSheaf.pullback f).op)
        ((symmetricAlgebra Y).op ⋙ relativeSpec Y)) ≪≫
    Functor.isoWhiskerLeft (dualFunctor.rightOp ⋙ (toQuasicoherent X).op)
      (relativeSpecSymmetricAlgebraBaseChangeIso f)

/-- The component of `totalSpaceSchemeBaseChangeIso` at `E` is relative Spec of the symmetric
algebra of the identification `f^* (E^∨) ≅ (f^* E)^∨` and of the identification of the two
pullbacks of `E^∨` as a quasicoherent sheaf, followed by the component of
`relativeSpecSymmetricAlgebraBaseChangeIso` at `E^∨`. -/
lemma totalSpaceSchemeBaseChangeIso_hom_app (E : FiniteLocallyFreeSheaf X) :
    (totalSpaceSchemeBaseChangeIso f).hom.app E =
      (relativeSpec Y).map
          ((symmetricAlgebra Y).map ((toQuasicoherent Y).map (pullbackDualIso f E).hom)).op ≫
        (relativeSpec Y).map
          ((symmetricAlgebra Y).map ((pullbackToQuasicoherentIso f).inv.app (dual E))).op ≫
          (relativeSpecSymmetricAlgebraBaseChangeIso f).hom.app
            (op ((toQuasicoherent X).obj (dual E))) :=
  (rfl)

variable (E : FiniteLocallyFreeSheaf X)

/-- The projection `𝕍(f^* E) ⟶ 𝕍(E)` from the total space of the pulled-back bundle, as a morphism
of schemes over `X`: relative Spec of the symmetric algebras of `f^* (E^∨) ≅ (f^* E)^∨`, followed
by the projection `Spec_Y (Sym (f^* E^∨)) ⟶ Spec_X (Sym E^∨)`. Under
`totalSpaceSchemeBaseChangeIso` it is the first projection of the fibre product `Y ×_X 𝕍(E)`
(`totalSpaceSchemeBaseChangeIso_hom_app_left_fst`). -/
def totalSpacePullbackFst :
    (Over.map f).obj ((MorphismProperty.Over.forget _ _ Y).obj
      ((totalSpaceScheme Y).obj ((FiniteLocallyFreeSheaf.pullback f).obj E))) ⟶
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E) :=
  (Over.map f).map ((MorphismProperty.Over.forget _ _ Y).map
      ((relativeSpec Y).map
          ((symmetricAlgebra Y).map ((toQuasicoherent Y).map (pullbackDualIso f E).hom)).op ≫
        (relativeSpec Y).map
          ((symmetricAlgebra Y).map ((pullbackToQuasicoherentIso f).inv.app (dual E))).op)) ≫
    relativeSpecSymmetricAlgebraPullbackFst f ((toQuasicoherent X).obj (dual E))

/-- The isomorphism `totalSpaceSchemeBaseChangeIso` followed by the first projection of the fibre
product `Y ×_X 𝕍(E)` is the projection `totalSpacePullbackFst`. -/
lemma totalSpaceSchemeBaseChangeIso_hom_app_left_fst :
    ((totalSpaceSchemeBaseChangeIso f).hom.app E).left ≫
        Limits.pullback.fst ((totalSpaceScheme X).obj E).hom f =
      (totalSpacePullbackFst f E).left := by
  rw [totalSpaceSchemeBaseChangeIso_hom_app, totalSpacePullbackFst]
  -- `MorphismProperty.Comma.comp_left` and `Over.comp_left` do not rewrite these composites:
  -- `@IsAffineHom` only has type `MorphismProperty Scheme` after unfolding. `change` states both
  -- sides as composites of underlying morphisms, which they are by definition of `.left` of a
  -- composite and of `Over.map_map_left`.
  change (((relativeSpec Y).map
          ((symmetricAlgebra Y).map ((toQuasicoherent Y).map (pullbackDualIso f E).hom)).op ≫
        (relativeSpec Y).map
          ((symmetricAlgebra Y).map ((pullbackToQuasicoherentIso f).inv.app (dual E))).op).left ≫
      ((relativeSpecSymmetricAlgebraBaseChangeIso f).hom.app
        (op ((toQuasicoherent X).obj (dual E)))).left) ≫
        Limits.pullback.fst ((totalSpaceScheme X).obj E).hom f =
    ((relativeSpec Y).map
          ((symmetricAlgebra Y).map ((toQuasicoherent Y).map (pullbackDualIso f E).hom)).op ≫
        (relativeSpec Y).map
          ((symmetricAlgebra Y).map ((pullbackToQuasicoherentIso f).inv.app (dual E))).op).left ≫
      (relativeSpecSymmetricAlgebraPullbackFst f ((toQuasicoherent X).obj (dual E))).left
  exact (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (relativeSpecSymmetricAlgebraBaseChangeIso_hom_app_left_fst f _))

/-- The linear functional on `(q ≫ f)^* E^∨` of the projection to `𝕍(E)` of a point `t` of
`𝕍(f^* E)` over `q : T ⟶ Y` is the base-change map `(q ≫ f)^* E^∨ ≅ q^* f^* E^∨ ⟶ q^* (f^* E)^∨`
followed by the linear functional of `t`. -/
private lemma relativeSpecSymmetricAlgebraPullbackHomEquiv_map_comp_totalSpacePullbackFst
    {T : Over Y} (t : T ⟶ (MorphismProperty.Over.forget _ _ Y).obj
      ((totalSpaceScheme Y).obj ((FiniteLocallyFreeSheaf.pullback f).obj E))) :
    relativeSpecSymmetricAlgebraPullbackHomEquiv ((toQuasicoherent X).obj (dual E))
      ((Over.map f).obj T) ((Over.map f).map t ≫ totalSpacePullbackFst f E) =
        (Scheme.Modules.pullbackComp T.hom f).inv.app ((ihom E.obj).obj (𝟙_ X.Modules)) ≫
          (Scheme.Modules.pullback T.hom).map ((pullbackIhomComparison E.obj f).app (𝟙_ X.Modules) ≫
            (ihom ((Scheme.Modules.pullback f).obj E.obj)).map
              (Scheme.Modules.pullbackObjUnitIso f).hom ≫
            eqToHom (congrArg (fun M : Y.Modules ↦ (ihom M).obj (𝟙_ Y.Modules))
              (FiniteLocallyFreeSheaf.pullback_obj_obj f E).symm)) ≫
          relativeSpecSymmetricAlgebraPullbackHomEquiv
            ((toQuasicoherent Y).obj (dual ((FiniteLocallyFreeSheaf.pullback f).obj E))) T t := by
  refine ((congrArg (relativeSpecSymmetricAlgebraPullbackHomEquiv _ _)
    ((Over.map f).map_comp_assoc t _ _).symm).trans
      (relativeSpecSymmetricAlgebraPullbackHomEquiv_map_comp_relativeSpecSymmetricAlgebraPullbackFst
        f _ _)).trans
        (congrArg (_ ≫ ·) ?_)
  -- Naturality of the linear functionals in the quasicoherent sheaf, for the two relative-Spec
  -- maps making up the first factor of `totalSpacePullbackFst`.
  refine (congrArg (_ ≫ ·) ((congrArg (relativeSpecSymmetricAlgebraPullbackHomEquiv _ T)
    ((congrArg (t ≫ ·) ((MorphismProperty.Over.forget _ _ Y).map_comp _ _)).trans
      (Category.assoc _ _ _).symm)).trans
    ((relativeSpecSymmetricAlgebraPullbackHomEquiv_comp_relativeSpec_map _ _ _).trans
      (congrArg (_ ≫ ·)
        (relativeSpecSymmetricAlgebraPullbackHomEquiv_comp_relativeSpec_map _ T t))))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm).trans
    (congrArg (· ≫ _) ?_)
  refine (congrArg (· ≫ _) ((Scheme.Modules.pullback T.hom).map_comp _ _).symm).trans
    (((Scheme.Modules.pullback T.hom).map_comp _ _).symm.trans (congrArg _ ?_))
  simp only [pullbackToQuasicoherentIso_inv_app_hom, toQuasicoherent_map_hom,
    pullbackDualIso_hom_hom]
  -- The leading transports cancel. The composites mix the `Y.Modules` and underlying sheaf
  -- category instances, which `simp` does not identify.
  erw [eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

-- The equation `M' = f^* M` is a hypothesis so that it can be eliminated: the sheaf underlying a
-- pulled-back finite locally free sheaf is equal, but not syntactically equal, to the pullback
-- of the underlying sheaf.
/-- `Scheme.Hom.dualHomUnitEquiv_inv_pullbackIhomComparison_app_unit_comp` for a sheaf `M'` equal
to `f^* M`: a functional on `(q ≫ f)^* M^∨` obtained from a functional `ψ` on `q^* M'^∨`
corresponds to the section of `q^* M'` of `ψ`, through `q^* f^* M ≅ (q ≫ f)^* M`. -/
private lemma dualHomUnitEquiv_inv_comp_eq_of_pullbackComp {T : Scheme.{u}} (q : T ⟶ Y)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsLocallyFree] [M.IsFiniteType]
    (M' : Y.Modules) [M'.IsQuasicoherent] [M'.IsLocallyFree] [M'.IsFiniteType]
    (h : M' = (Scheme.Modules.pullback f).obj M)
    [IsIso ((pullbackIhomComparison M (q ≫ f)).app (𝟙_ X.Modules) ≫
      (ihom ((Scheme.Modules.pullback (q ≫ f)).obj M)).map
        (Scheme.Modules.pullbackObjUnitIso (q ≫ f)).hom)]
    [IsIso ((pullbackIhomComparison M' q).app (𝟙_ Y.Modules) ≫
      (ihom ((Scheme.Modules.pullback q).obj M')).map (Scheme.Modules.pullbackObjUnitIso q).hom)]
    (ψ' : (Scheme.Modules.pullback (q ≫ f)).obj ((ihom M).obj (𝟙_ X.Modules)) ⟶ 𝟙_ T.Modules)
    (ψ : (Scheme.Modules.pullback q).obj ((ihom M').obj (𝟙_ Y.Modules)) ⟶ 𝟙_ T.Modules)
    (hψ : ψ' = (Scheme.Modules.pullbackComp q f).inv.app ((ihom M).obj (𝟙_ X.Modules)) ≫
      (Scheme.Modules.pullback q).map ((pullbackIhomComparison M f).app (𝟙_ X.Modules) ≫
        (ihom ((Scheme.Modules.pullback f).obj M)).map (Scheme.Modules.pullbackObjUnitIso f).hom ≫
        eqToHom (congrArg (fun N : Y.Modules ↦ (ihom N).obj (𝟙_ Y.Modules)) h.symm)) ≫ ψ) :
    Scheme.Modules.dualHomUnitEquiv ((Scheme.Modules.pullback (q ≫ f)).obj M)
        (inv ((pullbackIhomComparison M (q ≫ f)).app (𝟙_ X.Modules) ≫
            (ihom ((Scheme.Modules.pullback (q ≫ f)).obj M)).map
              (Scheme.Modules.pullbackObjUnitIso (q ≫ f)).hom) ≫ ψ') =
      Scheme.Modules.dualHomUnitEquiv ((Scheme.Modules.pullback q).obj M')
          (inv ((pullbackIhomComparison M' q).app (𝟙_ Y.Modules) ≫
            (ihom ((Scheme.Modules.pullback q).obj M')).map
              (Scheme.Modules.pullbackObjUnitIso q).hom) ≫ ψ) ≫
        eqToHom (congrArg (Scheme.Modules.pullback q).obj h) ≫
          (Scheme.Modules.pullbackComp q f).hom.app M := by
  subst hψ h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact Scheme.Hom.dualHomUnitEquiv_inv_pullbackIhomComparison_app_unit_comp q f M ψ

/-- **Base change of the total space on points.** For a scheme `q : T ⟶ Y` over `Y` and a point
`t : T ⟶ 𝕍(f^* E)` over `Y`, the section of `(q ≫ f)^* E` of the projection of `t` to `𝕍(E)` is
the section of `q^* f^* E` of `t`, through the composition isomorphism of pullback. -/
theorem totalSpaceHomEquiv_map_comp_totalSpacePullbackFst {T : Over Y}
    (t : T ⟶ (MorphismProperty.Over.forget _ _ Y).obj
      ((totalSpaceScheme Y).obj ((FiniteLocallyFreeSheaf.pullback f).obj E))) :
    totalSpaceHomEquiv E ((Over.map f).obj T) ((Over.map f).map t ≫ totalSpacePullbackFst f E) =
      totalSpaceHomEquiv ((FiniteLocallyFreeSheaf.pullback f).obj E) T t ≫
        eqToHom (congrArg (Scheme.Modules.pullback T.hom).obj
          (FiniteLocallyFreeSheaf.pullback_obj_obj f E)) ≫
          (Scheme.Modules.pullbackComp T.hom f).hom.app E.obj := by
  rw [totalSpaceHomEquiv_apply, totalSpaceHomEquiv_apply]
  exact dualHomUnitEquiv_inv_comp_eq_of_pullbackComp f T.hom E.obj _
    (FiniteLocallyFreeSheaf.pullback_obj_obj f E) _ _
    (relativeSpecSymmetricAlgebraPullbackHomEquiv_map_comp_totalSpacePullbackFst f E t)

/-- The projection to `𝕍(E)` of the point of `𝕍(f^* E)` of a section `s` of `q^* f^* E` is the
point of the section `(q ≫ f)^* E ≅ q^* f^* E` corresponding to `s`. -/
theorem map_totalSpaceHomEquiv_symm_comp_totalSpacePullbackFst {T : Over Y}
    (s : 𝟙_ T.left.Modules ⟶
      (Scheme.Modules.pullback T.hom).obj ((FiniteLocallyFreeSheaf.pullback f).obj E).obj) :
    (Over.map f).map ((totalSpaceHomEquiv ((FiniteLocallyFreeSheaf.pullback f).obj E) T).symm s) ≫
        totalSpacePullbackFst f E =
      (totalSpaceHomEquiv E ((Over.map f).obj T)).symm (s ≫
        eqToHom (congrArg (Scheme.Modules.pullback T.hom).obj
          (FiniteLocallyFreeSheaf.pullback_obj_obj f E)) ≫
          (Scheme.Modules.pullbackComp T.hom f).hom.app E.obj) :=
  (Equiv.eq_symm_apply _).2 ((totalSpaceHomEquiv_map_comp_totalSpacePullbackFst f E _).trans
    (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)))

end BaseChange

end

end TauCeti.AlgebraicGeometry

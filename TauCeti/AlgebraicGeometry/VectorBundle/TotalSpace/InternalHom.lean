/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Sections
public import TauCeti.CategoryTheory.Monoidal.Closed.Curry

/-!
# Points of the total spaces of internal-Hom and dual bundles

For finite locally free sheaves `E` and `F` on a scheme `X`, the internal Hom `𝓗om(E, F)` is
finite locally free, and its geometric total space `𝕍(𝓗om(E, F)) = Spec_X (Sym 𝓗om(E, F)^∨)`
is the vector bundle of homomorphisms from `E` to `F`. This file identifies its points: for a
scheme `q : T ⟶ X` over `X`, morphisms `T ⟶ 𝕍(𝓗om(E, F))` over `X` correspond to morphisms
`q^* E ⟶ q^* F` of `𝒪_T`-modules (`totalSpaceIhomHomEquiv`). The correspondence is natural in
both bundles: postcomposition with `b : F ⟶ F'` acts on points as `q^* b` acts on morphisms, and
precomposition with `a : E ⟶ E'` acts as `q^* a` (`totalSpaceIhomHomEquiv_comp_map_ihom_map`,
`totalSpaceIhomHomEquiv_comp_map_pre_app`). Over the identity of `X`, the sections of
`𝕍(𝓗om(E, F)) → X` are the morphisms `E ⟶ F` (`totalSpaceIhomSectionEquiv`).

Taking `F = 𝒪_X` gives the dual bundle: points `T ⟶ 𝕍(E^∨)` over `X` are linear functionals
`q^* E ⟶ 𝒪_T` (`totalSpaceDualHomEquiv`), and sections of `𝕍(E^∨) → X` are linear functionals
`E ⟶ 𝒪_X`.

The bijections combine the section-valued universal property `totalSpaceHomEquiv` of the total
space with the base change `q^* 𝓗om(E, F) ≅ 𝓗om(q^* E, q^* F)` for finite locally free `E`
(`FiniteLocallyFreeSheaf.pullbackIhomIso`) and Mathlib's identification
`MonoidalClosed.curryHomEquiv'` of global sections of an internal Hom with morphisms.

Here `𝕍(E)` means `Spec_X (Sym E^∨)`, covariantly in the sheaf of sections `E`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`. In the convention `V(F) = Spec_X (Sym F)` of the
references, `𝕍(𝓗om(E, F))` is `V(𝓗om(E, F)^∨)`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- **Points of the internal-Hom bundle are bundle maps.** For finite locally free sheaves `E`
and `F` on `X` and a scheme `q : T ⟶ X` over `X`, morphisms `T ⟶ 𝕍(𝓗om(E, F))` over `X`
correspond to morphisms `q^* E ⟶ q^* F` of `𝒪_T`-modules. -/
def totalSpaceIhomHomEquiv (E F : FiniteLocallyFreeSheaf X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj ((ihom E).obj F))) ≃
      ((Scheme.Modules.pullback T.hom).obj E.obj ⟶ (Scheme.Modules.pullback T.hom).obj F.obj) :=
  (totalSpaceHomEquiv ((ihom E).obj F) T).trans <|
    ((Iso.refl _).homCongr ((pullbackIhomIso E T.hom).app F.obj)).trans curryHomEquiv'.symm

/-- The morphism of a point `t : T ⟶ 𝕍(𝓗om(E, F))` is obtained from the section of
`q^* 𝓗om(E, F)` given by `t`: the base-change comparison carries it to a section of
`𝓗om(q^* E, q^* F)`, which is then uncurried. -/
theorem totalSpaceIhomHomEquiv_apply (E F : FiniteLocallyFreeSheaf X) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj ((ihom E).obj F))) :
    totalSpaceIhomHomEquiv E F T t =
      uncurry' (totalSpaceHomEquiv ((ihom E).obj F) T t ≫
        (pullbackIhomComparison E.obj T.hom).app F.obj) :=
  -- Unfolding the bijection leaves the identity of the conjugation by `Iso.refl`.
  congrArg uncurry' ((Category.id_comp _).trans
    (congrArg (_ ≫ ·) (NatTrans.congr_app (pullbackIhomIso_hom E T.hom) F.obj)))

/-- The point of `𝕍(𝓗om(E, F))` of a morphism `φ : q^* E ⟶ q^* F` is the point whose section of
`q^* 𝓗om(E, F) ≅ 𝓗om(q^* E, q^* F)` is the curried form of `φ`. -/
theorem totalSpaceIhomHomEquiv_symm_apply (E F : FiniteLocallyFreeSheaf X) (T : Over X)
    (φ : (Scheme.Modules.pullback T.hom).obj E.obj ⟶ (Scheme.Modules.pullback T.hom).obj F.obj) :
    (totalSpaceIhomHomEquiv E F T).symm φ =
      (totalSpaceHomEquiv ((ihom E).obj F) T).symm
        (curry' φ ≫ (pullbackIhomIso E T.hom).inv.app F.obj) := by
  rw [Equiv.symm_apply_eq, totalSpaceIhomHomEquiv_apply, Equiv.apply_symm_apply,
    ← pullbackIhomIso_hom]
  -- `rw` cannot cancel the isomorphism here: the composite mixes the `X.Modules` and functor
  -- composition forms of its objects, so the cancellation is applied as a term.
  exact (uncurry'_curry' φ).symm.trans (congrArg uncurry' ((Category.comp_id _).symm.trans
    ((congrArg (curry' φ ≫ ·) (Iso.inv_hom_id_app (pullbackIhomIso E T.hom) F.obj)).symm.trans
      (Category.assoc _ _ _).symm)))

/-- **Naturality in the target bundle.** Composing a point of `𝕍(𝓗om(E, F))` with the map of
total spaces induced by postcomposition with `b : F ⟶ F'` corresponds to postcomposing its
morphism `q^* E ⟶ q^* F` with `q^* b`. -/
theorem totalSpaceIhomHomEquiv_comp_map_ihom_map (E : FiniteLocallyFreeSheaf X)
    {F F' : FiniteLocallyFreeSheaf X} (b : F ⟶ F') (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj ((ihom E).obj F))) :
    totalSpaceIhomHomEquiv E F' T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map ((ihom E).map b))) =
      totalSpaceIhomHomEquiv E F T t ≫ (Scheme.Modules.pullback T.hom).map b.hom := by
  rw [totalSpaceIhomHomEquiv_apply, totalSpaceIhomHomEquiv_apply, totalSpaceHomEquiv_comp_map]
  -- Compare curried forms: postcomposition with `q^* b` becomes the internal-Hom map, which
  -- commutes with the base-change comparison.
  apply curry'_injective
  rw [curry'_uncurry', ← curry'_ihom_map, curry'_uncurry']
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((pullbackIhomComparison E.obj T.hom).naturality b.hom)).trans (Category.assoc _ _ _).symm)

/-- **Naturality in the source bundle.** Composing a point of `𝕍(𝓗om(E', F))` with the map of
total spaces induced by precomposition with `a : E ⟶ E'` corresponds to precomposing its
morphism `q^* E' ⟶ q^* F` with `q^* a`. -/
theorem totalSpaceIhomHomEquiv_comp_map_pre_app {E E' : FiniteLocallyFreeSheaf X} (a : E ⟶ E')
    (F : FiniteLocallyFreeSheaf X) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((totalSpaceScheme X).obj ((ihom E').obj F))) :
    totalSpaceIhomHomEquiv E F T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map ((pre a).app F))) =
      (Scheme.Modules.pullback T.hom).map a.hom ≫ totalSpaceIhomHomEquiv E' F T t := by
  rw [totalSpaceIhomHomEquiv_apply, totalSpaceIhomHomEquiv_apply, totalSpaceHomEquiv_comp_map,
    ObjectProperty.pre_app_hom]
  -- Compare curried forms: precomposition with `q^* a` becomes precomposition of internal Homs,
  -- which commutes with the base-change comparison.
  apply curry'_injective
  rw [curry'_uncurry', ← curry'_pre_app, curry'_uncurry']
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (pullback_map_pre_app_comp_pullbackIhomComparison_app T.hom a.hom F.obj)).trans
      (Category.assoc _ _ _).symm)

/-- **Sections of the internal-Hom bundle are bundle maps.** Sections of
`𝕍(𝓗om(E, F)) → X`, represented by morphisms from the identity of `X` in `Over X`, correspond to
morphisms `E ⟶ F` of finite locally free sheaves. -/
def totalSpaceIhomSectionEquiv (E F : FiniteLocallyFreeSheaf X) :
    (Over.mk (𝟙 X) ⟶
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj ((ihom E).obj F))) ≃
        (E ⟶ F) :=
  (totalSpaceSectionEquiv ((ihom E).obj F)).trans <|
    ((ObjectProperty.fullyFaithfulι (Scheme.Modules.isFiniteLocallyFree X)).homEquiv
      (X := 𝟙_ _) (Y := (ihom E).obj F)).symm.trans curryHomEquiv'.symm

/-- The bundle map of a section of `𝕍(𝓗om(E, F)) → X` is the uncurried global section
`𝒪_X ⟶ 𝓗om(E, F)` of the section. -/
theorem totalSpaceIhomSectionEquiv_apply_hom (E F : FiniteLocallyFreeSheaf X)
    (s : Over.mk (𝟙 X) ⟶
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj ((ihom E).obj F))) :
    (totalSpaceIhomSectionEquiv E F s).hom = uncurry' (totalSpaceSectionEquiv ((ihom E).obj F) s) :=
  (rfl)

/-- **Points of the dual bundle are linear functionals.** For a finite locally free sheaf `E`
on `X` and a scheme `q : T ⟶ X` over `X`, morphisms `T ⟶ 𝕍(E^∨)` over `X` correspond to linear
functionals `q^* E ⟶ 𝒪_T`. -/
def totalSpaceDualHomEquiv (E : FiniteLocallyFreeSheaf X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) ≃
      ((Scheme.Modules.pullback T.hom).obj E.obj ⟶ 𝟙_ T.left.Modules) :=
  -- `dual E` is the internal Hom from `E` into the unit by definition (`ihom_obj_unit_eq_dual`).
  (totalSpaceIhomHomEquiv E (𝟙_ _) T).trans
    ((Iso.refl _).homCongr (Scheme.Modules.pullbackObjUnitIso T.hom))

/-- The linear functional of a point `t : T ⟶ 𝕍(E^∨)` is its morphism `q^* E ⟶ q^* 𝒪_X`, read
through the identification `q^* 𝒪_X ≅ 𝒪_T`. -/
theorem totalSpaceDualHomEquiv_apply (E : FiniteLocallyFreeSheaf X) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E))) :
    totalSpaceDualHomEquiv E T t =
      totalSpaceIhomHomEquiv E (𝟙_ _) T t ≫ (Scheme.Modules.pullbackObjUnitIso T.hom).hom :=
  -- Unfolding the bijection leaves the identity of the conjugation by `Iso.refl`.
  Category.id_comp (totalSpaceIhomHomEquiv E (𝟙_ _) T t ≫
    (Scheme.Modules.pullbackObjUnitIso T.hom).hom)

/-- The point of `𝕍(E^∨)` of a linear functional `φ : q^* E ⟶ 𝒪_T` is the point of the
internal-Hom bundle of the morphism `q^* E ⟶ q^* 𝒪_X` obtained from `φ`. -/
theorem totalSpaceDualHomEquiv_symm_apply (E : FiniteLocallyFreeSheaf X) (T : Over X)
    (φ : (Scheme.Modules.pullback T.hom).obj E.obj ⟶ 𝟙_ T.left.Modules) :
    (totalSpaceDualHomEquiv E T).symm φ =
      (totalSpaceIhomHomEquiv E (𝟙_ _) T).symm
        (φ ≫ (Scheme.Modules.pullbackObjUnitIso T.hom).inv) :=
  congrArg (totalSpaceIhomHomEquiv E (𝟙_ _) T).symm
    (Category.id_comp (φ ≫ (Scheme.Modules.pullbackObjUnitIso T.hom).inv))

/-- **Naturality of the dual-bundle points.** Composing a point of `𝕍(E'^∨)` with the map of
total spaces induced by the dual `E'^∨ ⟶ E^∨` of `a : E ⟶ E'` corresponds to precomposing its
linear functional on `q^* E'` with `q^* a`. -/
theorem totalSpaceDualHomEquiv_comp_map {E E' : FiniteLocallyFreeSheaf X} (a : E ⟶ E')
    (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (dual E'))) :
    totalSpaceDualHomEquiv E T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map (dualFunctor.map a.op))) =
      (Scheme.Modules.pullback T.hom).map a.hom ≫ totalSpaceDualHomEquiv E' T t := by
  -- The dual of `a` is precomposition with `a` on internal Homs into `𝒪_X`.
  have h : dualFunctor.map a.op = (pre a).app (𝟙_ (FiniteLocallyFreeSheaf X)) :=
    ObjectProperty.hom_ext _ ((dualFunctor_map_hom a.op).trans
      (ObjectProperty.pre_app_hom a (𝟙_ (FiniteLocallyFreeSheaf X))).symm)
  rw [totalSpaceDualHomEquiv_apply, totalSpaceDualHomEquiv_apply, h]
  exact (congrArg (· ≫ _) (totalSpaceIhomHomEquiv_comp_map_pre_app a (𝟙_ _) T t)).trans
    (Category.assoc _ _ _)

end

end TauCeti.AlgebraicGeometry

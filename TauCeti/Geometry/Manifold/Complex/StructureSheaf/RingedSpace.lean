/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.AlgHom
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
import Mathlib.Tactic.TFAE
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Complex manifolds as locally `ℂ`-ringed spaces and the morphism equivalence

Any complex charted space `(X, I)` carries a sheafed space `sheafedSpace I X` and a locally ringed
space `locallyRingedSpace I X` with underlying carrier `X` and structure sheaf
`holomorphicStructureSheaf I X`. Every analytic map `f : X → Y` induces a morphism
`locallyRingedSpaceMap f hf : locallyRingedSpace I X ⟶ locallyRingedSpace J Y` by precomposition of
sections, functorially in `f`, commuting with restriction to open subsets
(`restrictLocallyRingedSpaceIso`), and — on finite-dimensional boundaryless complex manifolds —
canonically isomorphic to Mathlib's complex-smooth locally ringed space
`ChartedSpace.locallyRingedSpace I X` (`smoothLocallyRingedSpaceIso`).

Conversely, we characterize which morphisms between these locally ringed spaces come from analytic
maps:

* On arbitrary complex charted spaces `X` and `Y` (with no manifold, boundaryless, or
  finite-dimensionality hypotheses), `c_app_algebraMap_tfae` proves that for any morphism
  `φ : (locallyRingedSpace I X).toPresheafedSpace ⟶ (locallyRingedSpace J Y).toPresheafedSpace`
  the following four `ℂ`-linearity conditions are equivalent:
  1. `(φ.c.app (op U)).hom` preserves `algebraMap ℂ _ c` on every open `U : Opens Y`;
  2. `(φ.c.app (op ⊤)).hom` preserves `algebraMap ℂ _ c` on global sections;
  3. `(φ.stalkMap x).hom` preserves `algebraMap ℂ _ c` at every point `x : X`;
  4. `φ.stalkMap x ≫ evalHom I X x = evalHom J Y (φ.base x)` at every point `x : X`.
* Any presheafed-space morphism satisfying these equivalent conditions automatically induces local
  homomorphisms on all stalks (`isLocalHom_stalkMap_of_c_app_top_algebraMap`) and acts on sections
  by pointwise precomposition with `φ.base` (`c_app_apply_of_c_app_top_algebraMap`). The
  `ℂ`-linearity hypothesis is essential: composing section pullback with complex conjugation along
  an antiholomorphic map gives a `LocallyRingedSpace` morphism that fixes only real constants.
* When `Y` is modelled directly on `𝓘(ℂ, E')` for finite-dimensional `E'` (and `X` is an arbitrary
  complex charted space), pulling back centered linear coordinate sections expresses `φ.base` in
  every holomorphic chart `e ∈ maximalAtlas 𝓘(ℂ, E') ω Y`, basis `b`, and translation vector
  `z : E'` as `w ↦ e.symm (z + ∑ i, tᵢ w • b i)`
  (`OpenPartialHomeomorph.base_eq_symm_sum_of_c_app_top_algebraMap`). More generally, for any
  finite-dimensional boundaryless complex manifold `(Y, J)`, pulling back extended-chart coordinates
  shows independently of charts that `φ.base` is complex analytic
  (`contMDiff_base_of_c_app_top_algebraMap`) and that `locallyRingedSpaceMap φ.base _` recovers `φ`
  (`locallyRingedSpaceMap_base_toHom_of_c_app_top_algebraMap` and
  `locallyRingedSpaceMap_base_of_c_app_top_algebraMap`).
* `holomorphicMapLocalRingedEquivalence` packages this into a bijection between bundled analytic
  maps `C^ω⟮I, X; J, Y⟯` and `ℂ`-linear morphisms `locallyRingedSpace I X ⟶ locallyRingedSpace J Y`,
  compatible with identity, composition, open restriction, and the stalk-level germ equivalence
  `analyticMapGermEquivStalkAlgHom`.

The locally ringed space construction, functoriality of `locallyRingedSpaceMap`, and open-immersion
instance for open subsets adapt Heather Macbeth's smooth construction in
`Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean` to analytic regularity.

## References

* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Grundlehren der mathematischen
  Wissenschaften 265, Springer, 1984, Chapter 1, §1.
* O. Forster, *Lectures on Riemann Surfaces*, §§1 and 6.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Filter IsManifold Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section LocallyRingedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) (X : Type) [TopologicalSpace X] [ChartedSpace H X]

/-- A complex charted space equipped with its sheaf of holomorphic functions, as a sheafed space of
commutative rings. -/
abbrev sheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of X
  presheaf := (holomorphicStructureSheaf I X).presheaf
  IsSheaf := (holomorphicStructureSheaf I X).property

/-- A complex charted space equipped with its sheaf of holomorphic functions, as a locally ringed
space. No manifold, boundaryless, or Hausdorffness assumption is required. -/
abbrev locallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := sheafedSpace I X
  isLocalRing x := instIsLocalRingStalk I X x

variable {I X}

private theorem map_eqToHom_apply {U V : Opens X} (h : U = V)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : V) :
    toFun I X (op V) (((holomorphicStructureSheaf I X).obj.map (eqToHom h.symm).op).hom s) x =
      toFun I X (op U) s ⟨x.1, Eq.mpr congr(x.1 ∈ $h) x.2⟩ := by subst h; simp

private theorem toPresheafedSpace_hom_ext {W : PresheafedSpace CommRingCat}
    {α β : (locallyRingedSpace I X).toPresheafedSpace ⟶ W} (w : α.base = β.base)
    (h : ∀ (U : Opens W) (s : W.presheaf.obj (op U)) (x : ↥((Opens.map β.base).obj U)),
      toFun I X (op ((Opens.map α.base).obj U)) ((α.c.app (op U)).hom s)
        ⟨x.1, Eq.mpr congr(x.1 ∈ (Opens.map $w).obj U) x.2⟩ =
      toFun I X (op ((Opens.map β.base).obj U)) ((β.c.app (op U)).hom s) x) :
    α = β :=
  PresheafedSpace.ext_of_app w fun U ↦ CommRingCat.hom_ext <| RingHom.ext fun s ↦ ext fun x ↦ by
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact (map_eqToHom_apply congr((Opens.map $w).obj U) _ x).trans (h U s x)

private theorem locallyRingedSpace_hom_ext {W : LocallyRingedSpace}
    {α β : locallyRingedSpace I X ⟶ W} (w : α.base = β.base)
    (h : ∀ (U : Opens W) (s : W.presheaf.obj (op U)) (x : ↥((Opens.map β.base).obj U)),
      toFun I X (op ((Opens.map α.base).obj U)) ((α.c.app (op U)).hom s)
        ⟨x.1, Eq.mpr congr(x.1 ∈ (Opens.map $w).obj U) x.2⟩ =
      toFun I X (op ((Opens.map β.base).obj U)) ((β.c.app (op U)).hom s) x) :
    α = β :=
  LocallyRingedSpace.Hom.ext' (toPresheafedSpace_hom_ext w h)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℂ E' H'} {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] {H'' : Type*} [TopologicalSpace H'']
  {K : ModelWithCorners ℂ E'' H''} {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- A complex analytic map `f : X → Y` induces a morphism of holomorphic locally ringed spaces. -/
@[expose]
def locallyRingedSpaceMap (f : X → Y) (hf : ContMDiff I J ω f) :
    locallyRingedSpace I X ⟶ locallyRingedSpace J Y where
  toHom := { base := TopCat.ofHom ⟨f, hf.continuous⟩, c := (homOfContMDiff I X f hf).hom }
  prop x := ⟨fun s hs ↦ by
    obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf J Y).presheaf.exists_germ_eq s
    let φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
        (locallyRingedSpace J Y).toPresheafedSpace :=
      { base := TopCat.ofHom ⟨f, hf.continuous⟩, c := (homOfContMDiff I X f hf).hom }
    have h1 :
        (φ.stalkMap x).hom (((holomorphicStructureSheaf J Y).presheaf.germ U (f x) hx).hom g) =
          (((holomorphicStructureSheaf I X).presheaf.germ
            ((Opens.map φ.base).obj U) x hx).hom) (precomp I X f hf (op U) g) :=
      (PresheafedSpace.stalkMap_germ_apply φ U x hx g).trans <|
        congrArg _ (by rw [show φ.c.app (op U) = _ from homOfContMDiff_app I X f hf (op U)]; rfl)
    rw [isUnit_stalk_iff] at hs ⊢
    exact fun h0 ↦ hs <| (congrArg (eval I X x) h1).trans <| (eval_germ I X _ x hx _).trans <|
      (precomp_apply I X f hf (op U) g ⟨x, hx⟩).trans ((eval_germ J Y U (f x) hx g).symm.trans h0)⟩

/-- The underlying continuous map of `locallyRingedSpaceMap f hf` is `f`. -/
@[simp]
theorem locallyRingedSpaceMap_base (f : X → Y) (hf : ContMDiff I J ω f) :
    (locallyRingedSpaceMap f hf).base = TopCat.ofHom ⟨f, hf.continuous⟩ := (rfl)

/-- The sheaf part of `locallyRingedSpaceMap f hf` is `(homOfContMDiff I X f hf).hom`. -/
@[simp]
theorem locallyRingedSpaceMap_c (f : X → Y) (hf : ContMDiff I J ω f) :
    (locallyRingedSpaceMap f hf).c = (homOfContMDiff I X f hf).hom := (rfl)

/-- On sections over `U`, `locallyRingedSpaceMap f hf` acts by `precomp I X f hf U`. -/
theorem locallyRingedSpaceMap_c_app (f : X → Y) (hf : ContMDiff I J ω f) (U : (Opens Y)ᵒᵖ) :
    (locallyRingedSpaceMap f hf).c.app U = CommRingCat.ofHom (precomp I X f hf U) :=
  homOfContMDiff_app I X f hf U

-- Not `@[simp]`: `locallyRingedSpaceMap_c` and `homOfContMDiff_app` simplify `.c.app` on the LHS.
/-- On sections over `U`, `locallyRingedSpaceMap f hf` acts pointwise by precomposition with `f`. -/
theorem locallyRingedSpaceMap_c_app_apply (f : X → Y) (hf : ContMDiff I J ω f) (U : Opens Y)
    (s : (holomorphicStructureSheaf J Y).obj.obj (op U))
    (x : ↥((Opens.map (locallyRingedSpaceMap f hf).base).obj U)) :
    toFun I X (op ((Opens.map (locallyRingedSpaceMap f hf).base).obj U))
        (((locallyRingedSpaceMap f hf).c.app (op U)).hom s) x =
      toFun J Y (op U) s ⟨f x.1, x.2⟩ := by
  have hs : (((locallyRingedSpaceMap f hf).c.app (op U)).hom s :
      (holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj U))) =
      precomp I X f hf (op U) s := by rw [locallyRingedSpaceMap_c_app]; rfl
  exact (congrArg (fun t ↦ toFun I X _ t ⟨x.1, x.2⟩) hs).trans
    (precomp_apply I X f hf (op U) s ⟨x.1, x.2⟩)

/-- `locallyRingedSpaceMap f hf` preserves complex scalar sections on every open `U : Opens Y`. -/
theorem locallyRingedSpaceMap_c_app_algebraMap (f : X → Y) (hf : ContMDiff I J ω f)
    (U : Opens Y) (c : ℂ) :
    ((locallyRingedSpaceMap f hf).c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (locallyRingedSpaceMap f hf).base).obj U))) c :=
  ext fun x ↦ (locallyRingedSpaceMap_c_app_apply f hf U _ x).trans <|
    (algebraMap_apply (op U) c ⟨f x.1, x.2⟩).trans (algebraMap_apply _ c x).symm

/-- On stalks at `x`, `locallyRingedSpaceMap f hf` acts by `stalkPrecomp I X f hf x`. -/
@[simp]
theorem locallyRingedSpaceMap_stalkMap (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    ((locallyRingedSpaceMap f hf).stalkMap x).hom = stalkPrecomp I X f hf x := by
  ext s; obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf J Y).presheaf.exists_germ_eq s
  refine (PresheafedSpace.stalkMap_germ_apply (locallyRingedSpaceMap f hf).toHom U x hx g).trans ?_
  refine (congrArg (((holomorphicStructureSheaf I X).presheaf.germ
      ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj U) x hx).hom) ?_).trans
    (stalkPrecomp_germ I X f hf x U hx g).symm
  rw [locallyRingedSpaceMap_c_app]; rfl

/-- The stalk map of `locallyRingedSpaceMap f hf` at `x` commutes with `evalHom`. -/
@[reassoc (attr := simp)]
theorem locallyRingedSpaceMap_stalkMap_evalHom (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    (locallyRingedSpaceMap f hf).stalkMap x ≫ evalHom I X x = evalHom J Y (f x) :=
  CommRingCat.hom_ext <| RingHom.ext fun s ↦ by
    rw [CommRingCat.hom_comp, RingHom.comp_apply, locallyRingedSpaceMap_stalkMap]
    exact (evalHom_hom_apply x _).trans
      ((eval_stalkPrecomp I X f hf x s).trans (evalHom_hom_apply (f x) s).symm)

variable (I X) in
/-- `locallyRingedSpaceMap` sends the identity map on `X` to the identity morphism. -/
@[simp]
theorem locallyRingedSpaceMap_id :
    locallyRingedSpaceMap (I := I) (J := I) (id : X → X) contMDiff_id =
      𝟙 (locallyRingedSpace I X) :=
  locallyRingedSpace_hom_ext rfl fun U s x ↦
    (locallyRingedSpaceMap_c_app_apply (I := I) (J := I) (id : X → X) contMDiff_id
        U s ⟨x.1, x.2⟩).trans <| by
      simp only [LocallyRingedSpace.id_toHom, PresheafedSpace.id_c_app]
      exact (map_eqToHom_apply rfl s x).symm

/-- `locallyRingedSpaceMap` is covariantly functorial under composition of analytic maps. -/
theorem locallyRingedSpaceMap_comp {f : X → Y} (hf : ContMDiff I J ω f)
    {g : Y → Z} (hg : ContMDiff J K ω g) :
    locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg :=
  locallyRingedSpace_hom_ext rfl fun U s x ↦ by
    have hcomp : (((locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg).c.app (op U)).hom s :
        (holomorphicStructureSheaf I X).obj.obj
          (op ((Opens.map (locallyRingedSpaceMap f hf).base).obj
            ((Opens.map (locallyRingedSpaceMap g hg).base).obj U)))) =
        ((locallyRingedSpaceMap f hf).c.app
          (op ((Opens.map (locallyRingedSpaceMap g hg).base).obj U))).hom
          (((locallyRingedSpaceMap g hg).c.app (op U)).hom s) := rfl
    exact (locallyRingedSpaceMap_c_app_apply (g ∘ f) (hg.comp hf) U s ⟨x.1, x.2⟩).trans
      ((congrArg (fun t ↦ toFun I X _ t ⟨x.1, x.2⟩) hcomp).trans
        ((locallyRingedSpaceMap_c_app_apply f hf
            ((Opens.map (locallyRingedSpaceMap g hg).base).obj U) _ ⟨x.1, x.2⟩).trans
          (locallyRingedSpaceMap_c_app_apply g hg U s ⟨f x.1, x.2⟩))).symm

/-- Inclusion of an open subset induces an open immersion of holomorphic locally ringed spaces. -/
instance instIsOpenImmersionLocallyRingedSpaceMapSubtypeVal (U : Opens X) :
    LocallyRingedSpace.IsOpenImmersion
      (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val) where
  base_open := U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let a : TopCat.of U ⟶ TopCat.of X :=
      (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val).base
    have ha : IsOpenEmbedding a.hom := U.isOpenEmbedding'
    let V' : Opens U := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
    refine ⟨fun s₁ s₂ hs ↦ ext fun ⟨x, y, hy, hyx⟩ ↦ ?_, fun g ↦ ?_⟩
    · obtain rfl : y.1 = x := hyx
      have hyV' : y ∈ V' := ⟨y, hy, rfl⟩
      exact (locallyRingedSpaceMap_c_app_apply Subtype.val contMDiff_subtype_val
          (ha.isOpenMap.functor.obj V) s₁ ⟨y, hyV'⟩).symm.trans <|
        (congrArg (fun s ↦ toFun I U (op V') s ⟨y, hyV'⟩) hs).trans
          (locallyRingedSpaceMap_c_app_apply Subtype.val contMDiff_subtype_val
            (ha.isOpenMap.functor.obj V) s₂ ⟨y, hyV'⟩)
    · let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
        U.isOpenEmbedding'.homeomorphOfSubsetRange <| Set.image_subset_range _ V.1
      have hb : ContMDiff I I ω (b.symm : ha.isOpenMap.functor.obj V → V') := by
        refine (TauCeti.ContMDiff.subtypeVal_comp_iff V' _).mp ?_
        rw [← TauCeti.ContMDiff.subtypeVal_comp_iff U _]
        convert contMDiff_subtype_val using 1
        exact funext fun x ↦ congrArg Subtype.val (b.apply_symm_apply x)
      let gFun : V' → ℂ := toFun I U (op V') g
      refine ⟨ofContMDiff (gFun ∘ b.symm) ((contMDiff g).comp hb), ext fun x ↦ ?_⟩
      exact (locallyRingedSpaceMap_c_app_apply Subtype.val contMDiff_subtype_val
          (ha.isOpenMap.functor.obj V) _ x).trans <|
        (ofContMDiff_apply (gFun ∘ b.symm) _ ⟨x.1.1, x.2⟩).trans
          (congrArg gFun (b.symm_apply_apply x))

variable (I X) in
/-- Viewing a complex charted space as a holomorphic locally ringed space commutes with
restriction to open subsets. -/
def restrictLocallyRingedSpaceIso (U : Opens X) :
    (locallyRingedSpace I X).restrict (Opens.isOpenEmbedding (X := TopCat.of X) U) ≅
      locallyRingedSpace I U :=
  (LocallyRingedSpace.IsOpenImmersion.isoRestrict
    (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val)).symm

/-- The forward direction of `restrictLocallyRingedSpaceIso` is the identity on points. -/
@[simp]
theorem restrictLocallyRingedSpaceIso_hom_base (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).hom.base = 𝟙 (TopCat.of U) := (rfl)

/-- The inverse direction of `restrictLocallyRingedSpaceIso` is the identity on points. -/
@[simp]
theorem restrictLocallyRingedSpaceIso_inv_base (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).inv.base = 𝟙 (TopCat.of U) := (rfl)

/-- Composing `(restrictLocallyRingedSpaceIso I X U).hom` with the open-inclusion morphism gives
`(locallyRingedSpace I X).ofRestrict`. -/
@[reassoc (attr := simp)]
theorem restrictLocallyRingedSpaceIso_hom_comp_locallyRingedSpaceMap (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).hom ≫
      locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val =
      (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict _

/-- Composing `(restrictLocallyRingedSpaceIso I X U).inv` with `ofRestrict` gives
`locallyRingedSpaceMap Subtype.val contMDiff_subtype_val`. -/
@[reassoc (attr := simp)]
theorem restrictLocallyRingedSpaceIso_inv_comp_ofRestrict (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).inv ≫
      (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) =
      locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict _

end LocallyRingedSpace

section SmoothComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  (X : Type) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- On a finite-dimensional boundaryless complex manifold, the holomorphic locally ringed space is
canonically isomorphic over the identity on `X` to Mathlib's complex-smooth locally ringed space
`ChartedSpace.locallyRingedSpace I X`. -/
@[expose]
def smoothLocallyRingedSpaceIso :
    locallyRingedSpace I X ≅ ChartedSpace.locallyRingedSpace I X :=
  LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
    PresheafedSpace.isoOfComponents (Iso.refl (TopCat.of X))
      (eqToIso (TopCat.Presheaf.Pushforward.id_eq (holomorphicStructureSheaf I X).presheaf) ≪≫
        (sheafToPresheaf _ _).mapIso (smoothSheafIso I X))

/-- The forward direction of `smoothLocallyRingedSpaceIso` is the identity on points. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_hom_base :
    (smoothLocallyRingedSpaceIso I X).hom.base = 𝟙 (TopCat.of X) := (rfl)

/-- The inverse direction of `smoothLocallyRingedSpaceIso` is the identity on points. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_inv_base :
    (smoothLocallyRingedSpaceIso I X).inv.base = 𝟙 (TopCat.of X) := (rfl)

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).hom` preserves pointwise values. -/
theorem smoothLocallyRingedSpaceIso_hom_c_app_apply (U : Opens X)
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) (x : U) :
    toFun I X (op U) (((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s) x =
      (s : C^∞⟮I, U; 𝓘(ℂ), ℂ⟯) x := by
  have heq : ((eqToHom (TopCat.Presheaf.Pushforward.id_eq
      (holomorphicStructureSheaf I X).presheaf).symm).app (op U)) =
      𝟙 ((holomorphicStructureSheaf I X).presheaf.obj (op U)) :=
    (eqToHom_app _ (op U)).trans (eqToHom_refl _ _)
  -- Unfold `isoOfComponents` on `c.app (op U)` across `Pushforward.id_eq` before rewriting.
  have h1 : (((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s :
      (holomorphicStructureSheaf I X).obj.obj (op U)) =
      ((eqToHom (TopCat.Presheaf.Pushforward.id_eq
        (holomorphicStructureSheaf I X).presheaf).symm).app (op U)).hom
        (((smoothSheafIso I X).inv.hom.app (op U)).hom s) := rfl
  have h : (((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s :
      (holomorphicStructureSheaf I X).obj.obj (op U)) = (smoothSectionsEquiv I X U).symm s :=
    h1.trans <| (congrArg (fun k ↦ CommRingCat.Hom.hom k _) heq).trans
      (congrArg (fun k ↦ CommRingCat.Hom.hom k s) (smoothSheafIso_inv_app U))
  rw [h]; exact smoothSectionsEquiv_symm_apply U s x

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).inv` preserves pointwise values. -/
theorem smoothLocallyRingedSpaceIso_inv_c_app_apply (U : Opens X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : U) :
    DFunLike.coe (F := C^∞⟮I, U; 𝓘(ℂ), ℂ⟯)
        (((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)).hom s) x =
      toFun I X (op U) s x := by
  let t : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U) :=
    ((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)).hom s
  have hid := congrArg (fun k ↦ toFun I X (op U) (k.hom s) x) <| PresheafedSpace.congr_app
    (congrArg LocallyRingedSpace.Hom.toHom (smoothLocallyRingedSpaceIso I X).hom_inv_id) (op U)
  have hcomp : ((((smoothLocallyRingedSpaceIso I X).hom ≫
      (smoothLocallyRingedSpaceIso I X).inv).c.app (op U)).hom s :
      (holomorphicStructureSheaf I X).obj.obj (op U)) =
      ((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom t := rfl
  refine (smoothLocallyRingedSpaceIso_hom_c_app_apply I X U t x).symm.trans <|
    ((congrArg (fun u ↦ toFun I X (op U) u x) hcomp).symm.trans hid).trans ?_
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  refine (congrArg (fun k : (locallyRingedSpace I X).presheaf.obj (op U) ⟶ _ ↦ toFun I X (op U)
      (k.hom (((LocallyRingedSpace.Hom.toHom (𝟙 (locallyRingedSpace I X))).c.app (op U)).hom s)) x)
    ((congrArg (locallyRingedSpace I X).presheaf.map (eqToHom_refl _ _)).trans
      (CategoryTheory.Functor.map_id _ _))).trans ?_
  simp only [CommRingCat.hom_id, LocallyRingedSpace.id_toHom, PresheafedSpace.id_c_app]
  exact map_eqToHom_apply rfl s x

variable {I X} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'} [J.Boundaryless]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J 1 Y]

/-- `smoothLocallyRingedSpaceIso` intertwines `locallyRingedSpaceMap` with Mathlib's
`ChartedSpace.locallyRingedSpaceMap`. -/
@[reassoc]
theorem locallyRingedSpaceMap_comp_smoothLocallyRingedSpaceIso_hom
    (f : X → Y) (hf : ContMDiff I J ω f) :
    locallyRingedSpaceMap f hf ≫ (smoothLocallyRingedSpaceIso J Y).hom =
      (smoothLocallyRingedSpaceIso I X).hom ≫
        ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp)) :=
  locallyRingedSpace_hom_ext rfl fun U s x ↦ by
    have hlhs : (((locallyRingedSpaceMap f hf ≫
        (smoothLocallyRingedSpaceIso J Y).hom).c.app (op U)).hom s :
        (holomorphicStructureSheaf I X).obj.obj
          (op ((Opens.map (locallyRingedSpaceMap f hf).base).obj U))) =
        ((locallyRingedSpaceMap f hf).c.app (op U)).hom
          (((smoothLocallyRingedSpaceIso J Y).hom.c.app (op U)).hom s) := rfl
    have hrhs : ((((smoothLocallyRingedSpaceIso I X).hom ≫
        ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U)).hom s :
        (holomorphicStructureSheaf I X).obj.obj
          (op ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj U))) =
        ((smoothLocallyRingedSpaceIso I X).hom.c.app
          (op ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj U))).hom
          (((ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U)).hom s) := rfl
    exact (congrArg (fun t ↦ toFun I X _ t ⟨x.1, x.2⟩) hlhs).trans <|
      (locallyRingedSpaceMap_c_app_apply f hf U _ ⟨x.1, x.2⟩).trans <|
        (smoothLocallyRingedSpaceIso_hom_c_app_apply J Y U s ⟨f x.1, x.2⟩).trans
          ((congrArg (fun t ↦ toFun I X _ t x) hrhs).trans
            (smoothLocallyRingedSpaceIso_hom_c_app_apply I X _ _ x)).symm

end SmoothComparison

section CLinearity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℂ E' H'} {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

/-- Four equivalent formulations of `ℂ`-linearity for a presheafed-space morphism between
holomorphic ringed spaces: preserving constants on all opens, preserving constants on global
sections, preserving constants on all stalks, and commuting with evaluation on all stalks. Neither
locality on stalks nor any manifold hypothesis on `X` or `Y` is required. -/
theorem c_app_algebraMap_tfae
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace) :
    List.TFAE
      [∀ (U : Opens Y) (c : ℂ), (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj U))) c,
        ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c,
        ∀ (x : X) (c : ℂ), (φ.stalkMap x).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((holomorphicStructureSheaf I X).presheaf.stalk x) c,
        ∀ x : X, φ.stalkMap x ≫ evalHom I X x = evalHom J Y (φ.base x)] := by
  tfae_have 1 → 2 := fun h c ↦ h ⊤ c
  tfae_have 2 → 1 := fun h U c ↦ by
    have hnat := congrArg (fun k : (holomorphicStructureSheaf J Y).presheaf.obj (op ⊤) ⟶
        (holomorphicStructureSheaf I X).presheaf.obj (op ((Opens.map φ.base).obj U)) ↦
      k.hom (algebraMap ℂ _ c)) (φ.c.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      TopCat.Presheaf.pushforward_obj_map, presheaf_map_algebraMap] at hnat
    exact hnat.trans ((congrArg _ (h c)).trans (presheaf_map_algebraMap _ c))
  tfae_have 1 → 3 := fun h x c ↦ by
    have hxY : φ.base x ∈ (⊤ : Opens Y) := trivial; have hxX : x ∈ (Opens.map φ.base).obj ⊤ := hxY
    rw [← germ_algebraMap J Y ⊤ (φ.base x) hxY c, PresheafedSpace.stalkMap_germ_apply φ ⊤ x hxY,
      h ⊤ c, germ_algebraMap I X ((Opens.map φ.base).obj ⊤) x hxX c]
  tfae_have 3 → 4 := fun h x ↦ CommRingCat.hom_ext <| RingHom.ext fun s ↦ by
    let ψ : (holomorphicStructureSheaf J Y).presheaf.stalk (φ.base x) →ₐ[ℂ]
        (holomorphicStructureSheaf I X).presheaf.stalk x :=
      { __ := (φ.stalkMap x).hom, commutes' := h x }
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact (evalHom_hom_apply x (ψ s)).trans
      ((eval_algHom_apply ψ s).trans (evalHom_hom_apply (φ.base x) s).symm)
  tfae_have 4 → 2 := fun h c ↦ ext fun x ↦ by
    have hxY : φ.base x.1 ∈ (⊤ : Opens Y) := x.2
    have hev := congrArg (fun k ↦ k.hom
        (((holomorphicStructureSheaf J Y).presheaf.germ ⊤ (φ.base x.1) hxY).hom (algebraMap ℂ _ c)))
      (h x.1)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, evalHom_hom_apply, evalHom_hom_apply,
      PresheafedSpace.stalkMap_germ_apply φ ⊤ x.1 hxY] at hev
    exact (eval_germ I X _ x.1 x.2 _).symm.trans <| hev.trans <|
      (eval_germ J Y ⊤ (φ.base x.1) hxY _).trans <|
        (algebraMap_apply (op ⊤) c ⟨φ.base x.1, hxY⟩).trans
          (algebraMap_apply (op ((Opens.map φ.base).obj ⊤)) c x).symm
  tfae_finish

section TopAlgebraMap

variable
  (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶ (locallyRingedSpace J Y).toPresheafedSpace)
  (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
    algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c)
include hφ

/-- Bundle the stalk map of a `ℂ`-linear presheafed-space morphism at `x` as a `ℂ`-algebra
homomorphism `𝒪_{Y, φ.base x} →ₐ[ℂ] 𝒪_{X, x}`. -/
def stalkAlgHomOfCAppTopAlgebraMap (x : X) :
    (holomorphicStructureSheaf J Y).presheaf.stalk (φ.base x) →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk x where
  __ := (φ.stalkMap x).hom
  commutes' := ((c_app_algebraMap_tfae φ).out 2 3 rfl rfl).1 hφ x

/-- Coercing `stalkAlgHomOfCAppTopAlgebraMap φ hφ x` to a ring homomorphism recovers
`(φ.stalkMap x).hom`. -/
@[simp]
theorem coe_stalkAlgHomOfCAppTopAlgebraMap (x : X) :
    (stalkAlgHomOfCAppTopAlgebraMap φ hφ x :
      (holomorphicStructureSheaf J Y).presheaf.stalk (φ.base x) →+*
        (holomorphicStructureSheaf I X).presheaf.stalk x) = (φ.stalkMap x).hom := (rfl)

/-- `stalkAlgHomOfCAppTopAlgebraMap` acts on germs by `(φ.stalkMap x).hom`. -/
@[simp]
theorem stalkAlgHomOfCAppTopAlgebraMap_apply (x : X)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (φ.base x)) :
    stalkAlgHomOfCAppTopAlgebraMap φ hφ x s = (φ.stalkMap x).hom s := (rfl)

/-- Every presheafed-space morphism between holomorphic ringed spaces that preserves `ℂ`-constants
on global sections automatically induces local ring homomorphisms on all stalks. -/
theorem isLocalHom_stalkMap_of_c_app_top_algebraMap (x : X) : IsLocalHom (φ.stalkMap x).hom :=
  ⟨fun s hs ↦ isUnit_of_map_unit (stalkAlgHomOfCAppTopAlgebraMap φ hφ x) s hs⟩

/-- Promote a `ℂ`-linear morphism of presheafed spaces to a morphism of holomorphic locally ringed
spaces. -/
def locallyRingedSpaceHomOfPresheafedSpaceHom :
    locallyRingedSpace I X ⟶ locallyRingedSpace J Y where
  toHom := φ
  prop := isLocalHom_stalkMap_of_c_app_top_algebraMap φ hφ

/-- Forgetting stalk locality on `locallyRingedSpaceHomOfPresheafedSpaceHom φ hφ` recovers `φ`. -/
@[simp]
theorem locallyRingedSpaceHomOfPresheafedSpaceHom_toHom :
    (locallyRingedSpaceHomOfPresheafedSpaceHom φ hφ).toHom = φ := (rfl)

/-- **Section pullback formula.** Any `ℂ`-linear morphism of holomorphic presheafed spaces acts on
sections over every open `U : Opens Y` by pointwise precomposition with `φ.base`. -/
theorem c_app_apply_of_c_app_top_algebraMap (U : Opens Y)
    (g : (holomorphicStructureSheaf J Y).obj.obj (op U)) (x : ↥((Opens.map φ.base).obj U)) :
    toFun I X (op ((Opens.map φ.base).obj U)) ((φ.c.app (op U)).hom g) x =
      toFun J Y (op U) g ⟨φ.base x.1, x.2⟩ := by
  have hev := congrArg (fun k ↦ k.hom
      (((holomorphicStructureSheaf J Y).presheaf.germ U (φ.base x.1) x.2).hom g))
    (((c_app_algebraMap_tfae φ).out 2 4 rfl rfl).1 hφ x.1)
  rw [CommRingCat.hom_comp, RingHom.comp_apply, evalHom_hom_apply, evalHom_hom_apply,
    PresheafedSpace.stalkMap_germ_apply φ U x.1 x.2 g] at hev
  exact (eval_germ I X _ x.1 x.2 _).symm.trans (hev.trans (eval_germ J Y U (φ.base x.1) x.2 g))

end TopAlgebraMap

variable (I X) in
/-- The identity morphism on `(locallyRingedSpace I X).toPresheafedSpace` preserves complex scalar
sections. -/
theorem id_c_app_algebraMap (U : Opens X) (c : ℂ) :
    (((𝟙 (locallyRingedSpace I X).toPresheafedSpace :
        (locallyRingedSpace I X).toPresheafedSpace ⟶
          (locallyRingedSpace I X).toPresheafedSpace).c.app (op U)).hom (algebraMap ℂ _ c)) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (𝟙 (locallyRingedSpace I X).toPresheafedSpace :
          (locallyRingedSpace I X).toPresheafedSpace ⟶
            (locallyRingedSpace I X).toPresheafedSpace).base).obj U))) c := by
  rw [← LocallyRingedSpace.id_toHom (locallyRingedSpace I X), ← locallyRingedSpaceMap_id I X]
  exact locallyRingedSpaceMap_c_app_algebraMap id contMDiff_id U c

/-- Composition of `ℂ`-linear morphisms of holomorphic presheafed spaces preserves complex scalar
sections. -/
theorem comp_c_app_algebraMap {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
    {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]
    {φ : (locallyRingedSpace I X).toPresheafedSpace ⟶ (locallyRingedSpace J Y).toPresheafedSpace}
    (hφ : ∀ (U : Opens Y) (c : ℂ), (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj U))) c)
    {ψ : (locallyRingedSpace J Y).toPresheafedSpace ⟶ (locallyRingedSpace K Z).toPresheafedSpace}
    (hψ : ∀ (U : Opens Z) (c : ℂ), (ψ.c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf J Y).obj.obj (op ((Opens.map ψ.base).obj U))) c)
    (U : Opens Z) (c : ℂ) :
    ((φ ≫ ψ).c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (φ ≫ ψ).base).obj U))) c := by
  -- Unfold `(φ ≫ ψ).c.app (op U)` across `TopCat.Presheaf.pushforward` before rewriting.
  have hcomp : ((φ ≫ ψ).c.app (op U)).hom (algebraMap ℂ _ c) =
      (φ.c.app (op ((Opens.map ψ.base).obj U))).hom
        ((ψ.c.app (op U)).hom (algebraMap ℂ _ c)) := rfl
  exact hcomp.trans ((congrArg _ (hψ U c)).trans (hφ ((Opens.map ψ.base).obj U) c))

end CLinearity

section Equivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'} [J.Boundaryless]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J 1 Y]

section PresheafedRecovery

variable
  (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶ (locallyRingedSpace J Y).toPresheafedSpace)
  (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
    algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c)
include hφ

/-- **Holomorphic recovery of the base map.** For any finite-dimensional boundaryless complex
manifold `Y` and any complex charted space `X`, every `ℂ`-linear morphism of holomorphic
presheafed spaces `(X, 𝒪_X) ⟶ (Y, 𝒪_Y)` has complex-analytic underlying map
`ContMDiff I J ω φ.base`. No manifold, boundaryless, or Hausdorffness assumption on `X` is
needed. -/
theorem contMDiff_base_of_c_app_top_algebraMap : ContMDiff I J ω φ.base := by
  have : IsManifold J ω Y := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  intro x₀
  let y₀ : Y := φ.base x₀
  let U : Opens Y := ⟨(chartAt H' y₀).source, (chartAt H' y₀).open_source⟩
  have hy₀ : y₀ ∈ U := mem_chart_source H' y₀
  let V : Opens X := (Opens.map φ.base).obj U
  have hx₀ : x₀ ∈ V := hy₀
  rw [← contMDiffAt_subtype_iff (U := V) (x := ⟨x₀, hx₀⟩)]
  let b := Module.finBasis ℂ E'
  let s : Fin (Module.finrank ℂ E') → (holomorphicStructureSheaf J Y).obj.obj (op U) := fun i ↦
    ofContMDiff (fun z : U ↦ b.coord i (extChartAt J y₀ z.1)) fun z ↦
      ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff (n := ω)).contMDiff.contMDiffAt.comp z
        ((contMDiffAt_extChartAt' z.2).comp z contMDiff_subtype_val.contMDiffAt)
  let t : Fin (Module.finrank ℂ E') → (holomorphicStructureSheaf I X).obj.obj (op V) := fun i ↦
    (φ.c.app (op U)).hom (s i)
  let G : V → E' := fun w ↦ ∑ i, t i w • b i
  have hG_cm : ContMDiff I 𝓘(ℂ, E') ω G := fun w ↦ ContMDiffAt.sum fun i _ ↦
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b i)).contDiff
      (n := ω)).contMDiff.contMDiffAt.comp w (contMDiff (t i) w)
  have hG_eq (w : V) : G w = extChartAt J y₀ (φ.base w.1) := by
    have htw (i : Fin (Module.finrank ℂ E')) :
        t i w = b.coord i (extChartAt J y₀ (φ.base w.1)) :=
      (c_app_apply_of_c_app_top_algebraMap φ hφ U (s i) w).trans (ofContMDiff_apply _ _ _)
    simp_rw [G, htw]; exact b.sum_repr (extChartAt J y₀ (φ.base w.1))
  have hx₀_tgt : G ⟨x₀, hx₀⟩ ∈ (extChartAt J y₀).target := by
    rw [hG_eq]; exact (extChartAt J y₀).map_source (by rw [extChartAt_source]; exact hy₀)
  refine (((contMDiffOn_extChartAt_symm (n := ω) y₀).contMDiffAt
    (extChartAt_target_mem_nhds' hx₀_tgt)).comp (⟨x₀, hx₀⟩ : V)
      (hG_cm ⟨x₀, hx₀⟩)).congr_of_eventuallyEq (Eventually.of_forall fun w ↦ ?_)
  have hw_src : φ.base w.1 ∈ (extChartAt J y₀).source := by rw [extChartAt_source]; exact w.2
  rw [Function.comp_apply, hG_eq w, (extChartAt J y₀).left_inv hw_src]

/-- Every `ℂ`-linear morphism of holomorphic presheafed spaces into a finite-dimensional
boundaryless complex manifold `Y` is equal to `(locallyRingedSpaceMap φ.base _).toHom` on both
points and sections. -/
theorem locallyRingedSpaceMap_base_toHom_of_c_app_top_algebraMap :
    (locallyRingedSpaceMap (X := X) (Y := Y) φ.base
      (contMDiff_base_of_c_app_top_algebraMap φ hφ)).toHom = φ :=
  toPresheafedSpace_hom_ext rfl fun U g x ↦
    (locallyRingedSpaceMap_c_app_apply (X := X) (Y := Y) φ.base _ U g ⟨x.1, x.2⟩).trans
      (c_app_apply_of_c_app_top_algebraMap φ hφ U g x).symm

/-- At every point `x : X`, the `ℂ`-algebra stalk map of a `ℂ`-linear presheafed-space morphism
`φ : (locallyRingedSpace I X).toPresheafedSpace ⟶ (locallyRingedSpace J Y).toPresheafedSpace`
coincides with `stalkPullbackAt` along `φ.base`. -/
theorem stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAt (x : X) :
    stalkAlgHomOfCAppTopAlgebraMap φ hφ x =
      stalkPullbackAt (X := X) (Y := Y)
        (Eventually.of_forall fun _ ↦ (contMDiff_base_of_c_app_top_algebraMap φ hφ).contMDiffAt)
        rfl := by
  have hcm := contMDiff_base_of_c_app_top_algebraMap φ hφ
  have hstalk : φ.stalkMap x = (locallyRingedSpaceMap (X := X) (Y := Y) φ.base hcm).stalkMap x :=
    (PresheafedSpace.stalkMap.congr_hom φ
      (locallyRingedSpaceMap (X := X) (Y := Y) φ.base hcm).toHom
      (locallyRingedSpaceMap_base_toHom_of_c_app_top_algebraMap φ hφ).symm x).trans <|
      (congrArg (· ≫ (locallyRingedSpaceMap (X := X) (Y := Y) φ.base hcm).stalkMap x)
        (eqToHom_refl _ _)).trans (Category.id_comp _)
  rw [stalkPullbackAt_eq_stalkPrecompAlgHom (X := X) (Y := Y) φ.base hcm x]
  exact AlgHom.toRingHom_injective ((coe_stalkAlgHomOfCAppTopAlgebraMap φ hφ x).trans
    ((congrArg ConcreteCategory.hom hstalk).trans
      ((locallyRingedSpaceMap_stalkMap (X := X) (Y := Y) φ.base hcm x).trans
        (coe_stalkPrecompAlgHom I X φ.base hcm x).symm)))

/-- When `𝒪_{X, x}` is maximal-ideal separated (`IsHausdorff`), the local germ equivalence
`analyticMapGermEquivStalkAlgHom` applied to `stalkAlgHomOfCAppTopAlgebraMap φ hφ x` recovers the
germ of `φ.base` at `x`. -/
theorem analyticMapGermEquivStalkAlgHom_symm_stalkAlgHomOfCAppTopAlgebraMap (x : X)
    [IsHausdorff (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x)] :
    (analyticMapGermEquivStalkAlgHom (I := I) (J := J) x (φ.base x)).symm
        (stalkAlgHomOfCAppTopAlgebraMap φ hφ x) =
      AnalyticMapGerm.mk (X := X) (Y := Y) φ.base
        (Eventually.of_forall fun _ ↦ (contMDiff_base_of_c_app_top_algebraMap φ hφ).contMDiffAt)
        rfl := by
  rw [stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAt,
    analyticMapGermEquivStalkAlgHom_symm_stalkPullbackAt]

end PresheafedRecovery

/-- Every `ℂ`-linear morphism `φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y` into a
finite-dimensional boundaryless complex manifold `Y` is equal to `locallyRingedSpaceMap φ.base _`
on both points and sections. -/
theorem locallyRingedSpaceMap_base_of_c_app_top_algebraMap
    (φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c) :
    locallyRingedSpaceMap (X := X) (Y := Y) φ.base
      (contMDiff_base_of_c_app_top_algebraMap φ.toHom hφ) = φ :=
  LocallyRingedSpace.Hom.ext' (locallyRingedSpaceMap_base_toHom_of_c_app_top_algebraMap φ.toHom hφ)

/-- A morphism `φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y` into a finite-dimensional
boundaryless complex manifold `Y` is induced by a unique complex-analytic map `f : C^ω⟮I, X; J, Y⟯`
if and only if its section maps fix the complex constants. -/
theorem existsUnique_contMDiffMap_locallyRingedSpaceMap_eq_iff
    (φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y) :
    (∃! f : C^ω⟮I, X; J, Y⟯, locallyRingedSpaceMap f f.contMDiff = φ) ↔
      ∀ (U : Opens Y) (c : ℂ), (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
        algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj U))) c :=
  ⟨fun ⟨f, h, _⟩ U c ↦ h ▸ locallyRingedSpaceMap_c_app_algebraMap f f.contMDiff U c, fun hφ ↦
    ⟨⟨φ.base, contMDiff_base_of_c_app_top_algebraMap φ.toHom (hφ ⊤)⟩,
      locallyRingedSpaceMap_base_of_c_app_top_algebraMap φ (hφ ⊤), by
      rintro _ rfl; exact ContMDiffMap.ext fun _ ↦ rfl⟩⟩

variable (I X J Y) in
/-- **Equivalence between holomorphic maps and `ℂ`-linear morphisms of locally ringed spaces.**
For any complex charted space `(X, I)` and any finite-dimensional boundaryless complex manifold
`(Y, J)`, bundled complex-analytic maps `C^ω⟮I, X; J, Y⟯` correspond bijectively via
`locallyRingedSpaceMap` to `ℂ`-linear morphisms
`locallyRingedSpace I X ⟶ locallyRingedSpace J Y`. -/
def holomorphicMapLocalRingedEquivalence :
    C^ω⟮I, X; J, Y⟯ ≃
      {φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y //
        ∀ (U : Opens Y) (c : ℂ), (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ
            ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj U))) c} where
  toFun f := ⟨locallyRingedSpaceMap f f.contMDiff,
    locallyRingedSpaceMap_c_app_algebraMap f f.contMDiff⟩
  invFun φ := ⟨φ.1.base, contMDiff_base_of_c_app_top_algebraMap φ.1.toHom (φ.2 ⊤)⟩
  left_inv _ := ContMDiffMap.ext fun _ ↦ rfl
  right_inv φ := Subtype.ext (locallyRingedSpaceMap_base_of_c_app_top_algebraMap φ.1 (φ.2 ⊤))

/-- In the forward direction, `holomorphicMapLocalRingedEquivalence` sends `f` to
`locallyRingedSpaceMap f f.contMDiff`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_apply_val (f : C^ω⟮I, X; J, Y⟯) :
    (holomorphicMapLocalRingedEquivalence I X J Y f).1 =
      locallyRingedSpaceMap f f.contMDiff := (rfl)

/-- `holomorphicMapLocalRingedEquivalence` sends `ContMDiffMap.id` to the identity morphism. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_id [FiniteDimensional ℂ E] [I.Boundaryless]
    [IsManifold I 1 X] :
    holomorphicMapLocalRingedEquivalence I X I X ContMDiffMap.id =
      ⟨𝟙 (locallyRingedSpace I X), id_c_app_algebraMap I X⟩ :=
  Subtype.ext (locallyRingedSpaceMap_id I X)

/-- `holomorphicMapLocalRingedEquivalence.symm` sends the identity morphism to `ContMDiffMap.id`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_id [FiniteDimensional ℂ E] [I.Boundaryless]
    [IsManifold I 1 X] :
    (holomorphicMapLocalRingedEquivalence I X I X).symm
        ⟨𝟙 (locallyRingedSpace I X), id_c_app_algebraMap I X⟩ = ContMDiffMap.id :=
  ContMDiffMap.ext fun _ ↦ rfl

section SymmAndComp

variable
  (φ : {φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y //
    ∀ (U : Opens Y) (c : ℂ), (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj U))) c})

/-- Coercing `(holomorphicMapLocalRingedEquivalence I X J Y).symm φ` to a function gives
`φ.1.base`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_apply_coe :
    ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ : X → Y) = φ.1.base := (rfl)

/-- Evaluating `(holomorphicMapLocalRingedEquivalence I X J Y).symm φ` at `x` gives `φ.1.base x`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_apply (x : X) :
    (holomorphicMapLocalRingedEquivalence I X J Y).symm φ x = φ.1.base x := (rfl)

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] [FiniteDimensional ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''} [K.Boundaryless]
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold K 1 Z]

/-- `holomorphicMapLocalRingedEquivalence` sends composition of analytic maps to composition of
morphisms. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_comp (g : C^ω⟮J, Y; K, Z⟯) (f : C^ω⟮I, X; J, Y⟯) :
    holomorphicMapLocalRingedEquivalence I X K Z (g.comp f) =
      ⟨(holomorphicMapLocalRingedEquivalence I X J Y f).1 ≫
          (holomorphicMapLocalRingedEquivalence J Y K Z g).1,
        comp_c_app_algebraMap (φ := (holomorphicMapLocalRingedEquivalence I X J Y f).1.toHom)
          (ψ := (holomorphicMapLocalRingedEquivalence J Y K Z g).1.toHom)
          (holomorphicMapLocalRingedEquivalence I X J Y f).2
          (holomorphicMapLocalRingedEquivalence J Y K Z g).2⟩ :=
  Subtype.ext (locallyRingedSpaceMap_comp f.contMDiff g.contMDiff)

/-- `holomorphicMapLocalRingedEquivalence.symm` sends composition of morphisms to composition of
analytic maps. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_comp
    (ψ : {ψ : locallyRingedSpace J Y ⟶ locallyRingedSpace K Z //
      ∀ (U : Opens Z) (c : ℂ), (ψ.c.app (op U)).hom (algebraMap ℂ _ c) =
        algebraMap ℂ ((holomorphicStructureSheaf J Y).obj.obj (op ((Opens.map ψ.base).obj U))) c}) :
    (holomorphicMapLocalRingedEquivalence I X K Z).symm
        ⟨φ.1 ≫ ψ.1, comp_c_app_algebraMap (φ := φ.1.toHom) (ψ := ψ.1.toHom) φ.2 ψ.2⟩ =
      ((holomorphicMapLocalRingedEquivalence J Y K Z).symm ψ).comp
        ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ) :=
  ContMDiffMap.ext fun _ ↦ rfl

/-- Restricting a holomorphic map `f : C^ω⟮I, X; J, Y⟯` to an open subset `U : Opens X` corresponds
under `holomorphicMapLocalRingedEquivalence` to precomposing with the open immersion
`(restrictLocallyRingedSpaceIso I X U).inv ≫ (locallyRingedSpace I X).ofRestrict _`. -/
theorem holomorphicMapLocalRingedEquivalence_restrict_val (f : C^ω⟮I, X; J, Y⟯) (U : Opens X) :
    (holomorphicMapLocalRingedEquivalence I U J Y
      (f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^ω⟮I, U; I, X⟯))).1 =
      (restrictLocallyRingedSpaceIso I X U).inv ≫
        (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) ≫
        (holomorphicMapLocalRingedEquivalence I X J Y f).1 := by
  rw [restrictLocallyRingedSpaceIso_inv_comp_ofRestrict_assoc,
    holomorphicMapLocalRingedEquivalence_apply_val, holomorphicMapLocalRingedEquivalence_apply_val,
    ← locallyRingedSpaceMap_comp contMDiff_subtype_val f.contMDiff]; rfl

end SymmAndComp

end Equivalence

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y]
  (e : OpenPartialHomeomorph Y E') (he : e ∈ maximalAtlas 𝓘(ℂ, E') ω Y)

include he in
/-- **Chart-independent local coordinate recovery.** In *any* holomorphic chart `e`, *any* basis `b`
of `E'`, and *any* translation vector `z : E'`, the base map `φ.base` of a `ℂ`-linear morphism is
given on `φ.base ⁻¹' e.source` by `w ↦ e.symm (z + ∑ i, tᵢ w • b i)` where `tᵢ` is the pulled-back
linear coordinate section centered at `z`. -/
theorem base_eq_symm_sum_of_c_app_top_algebraMap {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ E')
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace 𝓘(ℂ, E') Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c)
    (z : E') (w : ↥((Opens.map φ.base).obj ⟨e.source, e.open_source⟩)) :
    φ.base w.1 = e.symm (z +
      ∑ i : ι, toFun I X (op ((Opens.map φ.base).obj ⟨e.source, e.open_source⟩))
        ((φ.c.app (op ⟨e.source, e.open_source⟩)).hom
          (e.holomorphicLinearCoordinateSection he
            (LinearMap.toContinuousLinearMap (b.coord i)) z)) w • b i) := by
  have hsum : ∑ i : ι, toFun I X (op ((Opens.map φ.base).obj ⟨e.source, e.open_source⟩))
      ((φ.c.app (op ⟨e.source, e.open_source⟩)).hom
        (e.holomorphicLinearCoordinateSection he
          (LinearMap.toContinuousLinearMap (b.coord i)) z)) w • b i = e (φ.base w.1) - z := by
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans (b.sum_repr (e (φ.base w.1) - z))
    rw [c_app_apply_of_c_app_top_algebraMap φ hφ ⟨e.source, e.open_source⟩ _ w]
    exact congrArg (· • b i) (e.holomorphicLinearCoordinateSection_apply he
      (LinearMap.toContinuousLinearMap (b.coord i)) z ⟨φ.base w.1, w.2⟩)
  rw [hsum, add_sub_cancel, e.left_inv w.2]

end OpenPartialHomeomorph

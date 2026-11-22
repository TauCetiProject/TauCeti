/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.AlgHom
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
import Mathlib.Tactic.TFAE
import TauCeti.Geometry.RingedSpace.LocallyRingedSpace
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
  by pointwise precomposition with `φ.base` (`c_app_apply_of_c_app_top_algebraMap`); consequently
  two `ℂ`-linear morphisms with the same base map are equal
  (`toPresheafedSpace_hom_ext_of_c_app_top_algebraMap`,
  `locallyRingedSpace_hom_ext_of_c_app_top_algebraMap`). Whenever `φ.base` is complex analytic
  (globally or near `x`), `φ` agrees with `locallyRingedSpaceMap`
  (`locallyRingedSpaceMap_base_toHom_of_c_app_top_algebraMap`,
  `locallyRingedSpaceMap_base_of_c_app_top_algebraMap`) and its `ℂ`-algebra stalk map agrees with
  `stalkPullbackAlgHom` (`stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAlgHom`). The
  `ℂ`-linearity hypothesis is essential: composing section pullback with complex conjugation along
  an antiholomorphic map gives a `LocallyRingedSpace` morphism that fixes only real constants.
* When `Y` is modelled directly on `𝓘(ℂ, E')` for finite-dimensional `E'` (and `X` is an arbitrary
  complex charted space), pulling back centered linear coordinate sections expresses `φ.base` in
  every holomorphic chart `e ∈ maximalAtlas 𝓘(ℂ, E') ω Y`, basis `b`, and translation vector
  `z : E'` as `w ↦ e.symm (z + ∑ i, tᵢ w • b i)`
  (`OpenPartialHomeomorph.base_eq_symm_sum_of_c_app_top_algebraMap`). More generally, for any
  finite-dimensional boundaryless complex manifold `(Y, J)`, pulling back extended-chart coordinates
  shows independently of charts that `φ.base` is complex analytic
  (`contMDiff_base_of_c_app_top_algebraMap`).
* `holomorphicMapLocalRingedEquivalence` packages this into a bijection between bundled analytic
  maps `C^ω⟮I, X; J, Y⟯` and `ℂ`-linear morphisms `LocallyRingedSpaceCLinearHom I X J Y`,
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
      toFun I X (op U) s ⟨x.val, Eq.mpr congr(x.val ∈ $h) x.property⟩ := by subst h; simp

/-- Two presheafed-space morphisms from `(locallyRingedSpace I X).toPresheafedSpace` to `W` are
equal if they agree on underlying continuous maps and pointwise on all pulled-back sections. -/
theorem toPresheafedSpace_hom_ext {W : PresheafedSpace CommRingCat}
    {α β : (locallyRingedSpace I X).toPresheafedSpace ⟶ W} (w : α.base = β.base)
    (h : ∀ (U : Opens W) (s : W.presheaf.obj (op U)) (x : ↥((Opens.map β.base).obj U)),
      toFun I X (op ((Opens.map α.base).obj U)) ((α.c.app (op U)).hom s)
        ⟨x.val, Eq.mpr congr(x.val ∈ (Opens.map $w).obj U) x.property⟩ =
      toFun I X (op ((Opens.map β.base).obj U)) ((β.c.app (op U)).hom s) x) :
    α = β :=
  PresheafedSpace.ext_of_app w fun U ↦ CommRingCat.hom_ext <| RingHom.ext fun s ↦ ext fun x ↦ by
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact (map_eqToHom_apply congr((Opens.map $w).obj U) _ x).trans (h U s x)

/-- Two locally ringed space morphisms from `locallyRingedSpace I X` to `W` are equal if they agree
on underlying continuous maps and pointwise on all pulled-back sections. -/
theorem locallyRingedSpace_hom_ext {W : LocallyRingedSpace}
    {α β : locallyRingedSpace I X ⟶ W} (w : α.base = β.base)
    (h : ∀ (U : Opens W) (s : W.presheaf.obj (op U)) (x : ↥((Opens.map β.base).obj U)),
      toFun I X (op ((Opens.map α.base).obj U)) ((α.c.app (op U)).hom s)
        ⟨x.val, Eq.mpr congr(x.val ∈ (Opens.map $w).obj U) x.property⟩ =
      toFun I X (op ((Opens.map β.base).obj U)) ((β.c.app (op U)).hom s) x) :
    α = β :=
  LocallyRingedSpace.Hom.ext' (toPresheafedSpace_hom_ext w h)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℂ E' H'} {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] {H'' : Type*} [TopologicalSpace H'']
  {K : ModelWithCorners ℂ E'' H''} {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]

private theorem stalkMap_mk_homOfContMDiff (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    (({ base := TopCat.ofHom ⟨f, hf.continuous⟩, c := (homOfContMDiff I X f hf).hom } :
        (locallyRingedSpace I X).toPresheafedSpace ⟶
          (locallyRingedSpace J Y).toPresheafedSpace).stalkMap x).hom =
      stalkPrecomp I X f hf x := by
  let φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace :=
    { base := TopCat.ofHom ⟨f, hf.continuous⟩, c := (homOfContMDiff I X f hf).hom }
  ext s; obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf J Y).presheaf.exists_germ_eq s
  refine (PresheafedSpace.stalkMap_germ_apply φ U x hx g).trans ?_
  refine (congrArg (((holomorphicStructureSheaf I X).presheaf.germ
      ((Opens.map φ.base).obj U) x hx).hom) ?_).trans
    (stalkPrecomp_germ I X f hf x U hx g).symm
  exact (congrArg (fun k ↦ k.hom g) (homOfContMDiff_app I X f hf (op U))).trans
    (CommRingCat.ofHom_apply (precomp I X f hf (op U)) g)

-- Exposed so `.base` reduces definitionally in the dependent types of the `.c` and `.stalkMap`
-- component lemmas below (`homOfContMDiff` remains unexposed).
/-- A complex analytic map `f : X → Y` induces a morphism of holomorphic locally ringed spaces. -/
@[expose]
def locallyRingedSpaceMap (f : X → Y) (hf : ContMDiff I J ω f) :
    locallyRingedSpace I X ⟶ locallyRingedSpace J Y where
  toHom := { base := TopCat.ofHom ⟨f, hf.continuous⟩, c := (homOfContMDiff I X f hf).hom }
  prop x := by
    rw [stalkMap_mk_homOfContMDiff f hf x, ← stalkPullback_eq_stalkPrecomp f hf x]
    exact isLocalHom_stalkPullback _

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
      toFun J Y (op U) s ⟨f x.val, x.property⟩ := by
  have hc : ((locallyRingedSpaceMap f hf).c.app (op U)).hom s = precomp I X f hf (op U) s :=
    (congrArg (fun k ↦ k.hom s) (locallyRingedSpaceMap_c_app f hf (op U))).trans
      (CommRingCat.ofHom_apply (precomp I X f hf (op U)) s)
  exact (congrArg (fun t ↦ toFun I X _ t x) hc).trans
    (precomp_apply I X f hf (op U) s ⟨x.val, x.property⟩)

/-- `locallyRingedSpaceMap f hf` preserves complex scalar sections on every open `U : Opens Y`. -/
theorem locallyRingedSpaceMap_c_app_algebraMap (f : X → Y) (hf : ContMDiff I J ω f)
    (U : Opens Y) (c : ℂ) :
    ((locallyRingedSpaceMap f hf).c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (locallyRingedSpaceMap f hf).base).obj U))) c :=
  (congrArg (fun k ↦ k.hom (algebraMap ℂ _ c)) (locallyRingedSpaceMap_c_app f hf (op U))).trans <|
    (CommRingCat.ofHom_apply (precomp I X f hf (op U)) _).trans
      (precomp_algebraMap f hf (op U) c)

/-- On stalks at `x`, `locallyRingedSpaceMap f hf` acts by `stalkPrecomp I X f hf x`. -/
@[simp]
theorem locallyRingedSpaceMap_stalkMap (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    ((locallyRingedSpaceMap f hf).stalkMap x).hom = stalkPrecomp I X f hf x :=
  stalkMap_mk_homOfContMDiff f hf x

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
  locallyRingedSpace_hom_ext (by ext; rfl) fun U s x ↦ by
    rw [locallyRingedSpaceMap_c_app_apply (I := I) (J := I) (id : X → X) contMDiff_id U s
      ⟨x.val, x.property⟩]
    have hid : ((𝟙 (locallyRingedSpace I X) : locallyRingedSpace I X ⟶
        locallyRingedSpace I X).c.app (op U)).hom s = s :=
      (congrArg (fun k ↦ k.hom s)
        ((PresheafedSpace.id_c_app (locallyRingedSpace I X).toPresheafedSpace (op U)).trans
          ((holomorphicStructureSheaf I X).presheaf.map_id (op U)))).trans
        (CommRingCat.id_apply _ s)
    exact (congrArg (fun t ↦ toFun I X (op U) t ⟨x.val, x.property⟩) hid).symm

/-- `locallyRingedSpaceMap` is covariantly functorial under composition of analytic maps. -/
theorem locallyRingedSpaceMap_comp {f : X → Y} (hf : ContMDiff I J ω f)
    {g : Y → Z} (hg : ContMDiff J K ω g) :
    locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg :=
  locallyRingedSpace_hom_ext (by ext; rfl) fun U s x ↦ by
    have h₁ := locallyRingedSpaceMap_c_app_apply (g ∘ f) (hg.comp hf) U s ⟨x.val, x.property⟩
    have h₂ := locallyRingedSpaceMap_c_app_apply f hf
      ((Opens.map (locallyRingedSpaceMap g hg).base).obj U)
      (((locallyRingedSpaceMap g hg).c.app (op U)).hom s) ⟨x.val, x.property⟩
    have h₃ := locallyRingedSpaceMap_c_app_apply g hg U s ⟨f x.val, x.property⟩
    exact h₁.trans <| h₃.symm.trans <| h₂.symm.trans <|
      congrArg (fun t ↦ toFun I X _ t x)
        (LocallyRingedSpace.comp_c_app_apply (locallyRingedSpaceMap f hf)
          (locallyRingedSpaceMap g hg) (op U) s).symm

/-- `locallyRingedSpaceMap` sends a composite bundled analytic map `g.comp f` to the composite
morphism, independently of the analyticity proof term. -/
@[simp]
theorem locallyRingedSpaceMap_contMDiffMap_comp (g : C^ω⟮J, Y; K, Z⟯) (f : C^ω⟮I, X; J, Y⟯)
    (hgf : ContMDiff I K ω (g.comp f)) :
    locallyRingedSpaceMap (g.comp f) hgf =
      locallyRingedSpaceMap f f.contMDiff ≫ locallyRingedSpaceMap g g.contMDiff :=
  locallyRingedSpaceMap_comp f.contMDiff g.contMDiff

/-- Inclusion of an open subset induces an open immersion of holomorphic locally ringed spaces. -/
instance instIsOpenImmersionLocallyRingedSpaceMapSubtypeVal (U : Opens X) :
    LocallyRingedSpace.IsOpenImmersion
      (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtypeVal) where
  base_open := U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let a : TopCat.of U ⟶ TopCat.of X :=
      (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtypeVal).base
    have ha : IsOpenEmbedding a.hom := U.isOpenEmbedding'
    let V' : Opens U := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
    refine ⟨fun s₁ s₂ hs ↦ ext fun ⟨x, y, hy, hyx⟩ ↦ ?_, fun g ↦ ?_⟩
    · obtain rfl : y.val = x := hyx
      have hyV' : y ∈ V' := ⟨y, hy, rfl⟩
      exact (locallyRingedSpaceMap_c_app_apply Subtype.val contMDiff_subtypeVal
          (ha.isOpenMap.functor.obj V) s₁ ⟨y, hyV'⟩).symm.trans <|
        (congrArg (fun s ↦ toFun I U (op V') s ⟨y, hyV'⟩) hs).trans
          (locallyRingedSpaceMap_c_app_apply Subtype.val contMDiff_subtypeVal
            (ha.isOpenMap.functor.obj V) s₂ ⟨y, hyV'⟩)
    · let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
        U.isOpenEmbedding'.homeomorphOfSubsetRange <| Set.image_subset_range _ V.carrier
      have hb : ContMDiff I I ω (b.symm : ha.isOpenMap.functor.obj V → V') := by
        refine (TauCeti.ContMDiff.subtypeVal_comp_iff V' _).mp ?_
        rw [← TauCeti.ContMDiff.subtypeVal_comp_iff U _]
        convert contMDiff_subtypeVal using 1
        exact funext fun x ↦ congrArg Subtype.val (b.apply_symm_apply x)
      let gFun : V' → ℂ := toFun I U (op V') g
      refine ⟨ofContMDiff (gFun ∘ b.symm) ((contMDiff g).comp hb), ext fun x ↦ ?_⟩
      exact (locallyRingedSpaceMap_c_app_apply Subtype.val contMDiff_subtypeVal
          (ha.isOpenMap.functor.obj V) _ x).trans <|
        (ofContMDiff_apply (gFun ∘ b.symm) _ ⟨x.val.val, x.property⟩).trans
          (congrArg gFun (b.symm_apply_apply x))

variable (I X) in
/-- Viewing a complex charted space as a holomorphic locally ringed space commutes with
restriction to open subsets. -/
def restrictLocallyRingedSpaceIso (U : Opens X) :
    (locallyRingedSpace I X).restrict (Opens.isOpenEmbedding (X := TopCat.of X) U) ≅
      locallyRingedSpace I U :=
  (LocallyRingedSpace.IsOpenImmersion.isoRestrict
    (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtypeVal)).symm

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
      locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtypeVal =
      (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict _

/-- Composing `(restrictLocallyRingedSpaceIso I X U).inv` with `ofRestrict` gives
`locallyRingedSpaceMap Subtype.val contMDiff_subtypeVal`. -/
@[reassoc (attr := simp)]
theorem restrictLocallyRingedSpaceIso_inv_comp_ofRestrict (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).inv ≫
      (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) =
      locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtypeVal :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict _

end LocallyRingedSpace

section SmoothComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  (X : Type) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

-- Exposed so `.hom.base` and `.inv.base` reduce definitionally in the dependent types of the
-- `.c.app` and `.stalkMap` comparison lemmas below (`smoothSheafIso` remains unexposed).
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

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).hom` is the inverse section equivalence
`(smoothSectionsEquiv I X U).symm`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_hom_c_app (U : Opens X) :
    (smoothLocallyRingedSpaceIso I X).hom.c.app (op U) =
      CommRingCat.ofHom (smoothSectionsEquiv I X U).symm.toRingHom := by
  have heq : (eqToHom (TopCat.Presheaf.Pushforward.id_eq
      (holomorphicStructureSheaf I X).presheaf).symm).app (op U) = 𝟙 _ :=
    (eqToHom_app _ _).trans (eqToHom_refl _ _)
  exact (congrArg ((smoothSheafIso I X).inv.hom.app (op U) ≫ ·) heq).trans <|
    (Category.comp_id _).trans (smoothSheafIso_inv_app U)

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).inv` is the section equivalence
`smoothSectionsEquiv I X U`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_inv_c_app (U : Opens X) :
    (smoothLocallyRingedSpaceIso I X).inv.c.app (op U) =
      CommRingCat.ofHom (smoothSectionsEquiv I X U).toRingHom := by
  let k : (holomorphicStructureSheaf I X).presheaf.obj (op U) ⟶
      (ChartedSpace.locallyRingedSpace I X).presheaf.obj (op U) :=
    (eqToHom (TopCat.Presheaf.Pushforward.id_eq
      (holomorphicStructureSheaf I X).presheaf)).app (op U) ≫
      (smoothSheafIso I X).hom.hom.app (op U)
  have h₁ : (holomorphicStructureSheaf I X).presheaf.map (eqToHom rfl : op U ⟶ op U) = 𝟙 _ :=
    (congrArg _ (eqToHom_refl _ _)).trans ((holomorphicStructureSheaf I X).presheaf.map_id (op U))
  have h₂ : (eqToHom (TopCat.Presheaf.Pushforward.id_eq
      (holomorphicStructureSheaf I X).presheaf)).app (op U) = 𝟙 _ :=
    (eqToHom_app _ _).trans (eqToHom_refl _ _)
  have h₃ : k = CommRingCat.ofHom (smoothSectionsEquiv I X U).toRingHom :=
    (congrArg (· ≫ (smoothSheafIso I X).hom.hom.app (op U)) h₂).trans <|
      (Category.id_comp _).trans (smoothSheafIso_hom_app U)
  exact (TopCat.Presheaf.toPushforwardOfIso_app (Iso.refl (TopCat.of X))
      (eqToIso (TopCat.Presheaf.Pushforward.id_eq (holomorphicStructureSheaf I X).presheaf) ≪≫
        (sheafToPresheaf _ _).mapIso (smoothSheafIso I X)).hom (op U)).trans <|
    (congrArg (· ≫ k) h₁).trans <| (Category.id_comp k).trans h₃

/-- On stalks at `x`, `(smoothLocallyRingedSpaceIso I X).hom` agrees with
`(smoothStalkIso I X x).inv`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_hom_stalkMap (x : X) :
    (smoothLocallyRingedSpaceIso I X).hom.stalkMap x = (smoothStalkIso I X x).inv := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  obtain ⟨U, hx, g, rfl⟩ := (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.exists_germ_eq s
  have h₁ := LocallyRingedSpace.stalkMap_germ_apply (smoothLocallyRingedSpaceIso I X).hom U x hx g
  have h₂ := congrArg (fun k ↦ k.hom g) (smoothLocallyRingedSpaceIso_hom_c_app I X U)
  exact h₁.trans <| (congrArg (((holomorphicStructureSheaf I X).presheaf.germ U x hx).hom)
    (h₂.trans (CommRingCat.ofHom_apply _ g))).trans (smoothStalkIso_inv_germ x U hx g).symm

/-- On stalks at `x`, `(smoothLocallyRingedSpaceIso I X).inv` agrees with
`(smoothStalkIso I X x).hom`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_inv_stalkMap (x : X) :
    (smoothLocallyRingedSpaceIso I X).inv.stalkMap x = (smoothStalkIso I X x).hom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf I X).presheaf.exists_germ_eq s
  have h₁ := LocallyRingedSpace.stalkMap_germ_apply (smoothLocallyRingedSpaceIso I X).inv U x hx g
  have h₂ := congrArg (fun k ↦ k.hom g) (smoothLocallyRingedSpaceIso_inv_c_app I X U)
  exact h₁.trans <| (congrArg (((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ U x hx).hom)
    (h₂.trans (CommRingCat.ofHom_apply _ g))).trans (smoothStalkIso_hom_germ x U hx g).symm

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).hom` preserves pointwise values. -/
theorem smoothLocallyRingedSpaceIso_hom_c_app_apply (U : Opens X)
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) (x : U) :
    toFun I X (op U) (((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s) x =
      (s : C^∞⟮I, U; 𝓘(ℂ), ℂ⟯) x := by
  have hc : ((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s =
      (smoothSectionsEquiv I X U).symm s :=
    (congrArg (fun k ↦ k.hom s) (smoothLocallyRingedSpaceIso_hom_c_app I X U)).trans
      (CommRingCat.ofHom_apply (smoothSectionsEquiv I X U).symm.toRingHom s)
  exact (congrArg (fun t ↦ toFun I X (op U) t x) hc).trans
    (smoothSectionsEquiv_symm_apply U s x)

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).inv` preserves pointwise values. -/
theorem smoothLocallyRingedSpaceIso_inv_c_app_apply (U : Opens X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : U) :
    DFunLike.coe (F := C^∞⟮I, U; 𝓘(ℂ), ℂ⟯)
        (((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)).hom s) x =
      toFun I X (op U) s x := by
  have hc : ((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)).hom s =
      smoothSectionsEquiv I X U s :=
    (congrArg (fun k ↦ k.hom s) (smoothLocallyRingedSpaceIso_inv_c_app I X U)).trans
      (CommRingCat.ofHom_apply (smoothSectionsEquiv I X U).toRingHom s)
  exact (congrArg (fun t : C^∞⟮I, U; 𝓘(ℂ), ℂ⟯ ↦ t x) hc).trans
    (smoothSectionsEquiv_apply U s x)

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
  locallyRingedSpace_hom_ext (by ext; rfl) fun U s x ↦ by
    have hL₁ := LocallyRingedSpace.comp_c_app_apply
      (locallyRingedSpaceMap f hf) (smoothLocallyRingedSpaceIso J Y).hom (op U) s
    have hL₂ := locallyRingedSpaceMap_c_app_apply f hf U
      (((smoothLocallyRingedSpaceIso J Y).hom.c.app (op U)).hom s) ⟨x.val, x.property⟩
    have hL₃ := smoothLocallyRingedSpaceIso_hom_c_app_apply J Y U s ⟨f x.val, x.property⟩
    have hR₁ := LocallyRingedSpace.comp_c_app_apply
      (smoothLocallyRingedSpaceIso I X).hom
      (ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))) (op U) s
    have hR₂ := smoothLocallyRingedSpaceIso_hom_c_app_apply I X
      ((Opens.map (ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).base).obj U)
      (((ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U)).hom s) x
    have hR₃ :
        (((ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U)).hom s).val x =
          s.val ⟨f x.val, x.property⟩ := by
      have hxU : f x.val ∈ U := x.property
      have hev := congrArg (fun k ↦ k.hom
        (((smoothSheafCommRing J 𝓘(ℂ) Y ℂ).presheaf.germ U (f x.val) hxU).hom s))
        (ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom f (hf.of_le (by simp)) x.val)
      have hgerm := LocallyRingedSpace.stalkMap_germ_apply
        (ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))) U x.val hxU s
      have hev' := (congrArg (smoothSheafCommRing.evalHom I 𝓘(ℂ) X ℂ x.val).hom hgerm).symm.trans <|
        (CommRingCat.comp_apply _ _ _).symm.trans hev
      exact (smoothSheafCommRing.evalHom_germ I 𝓘(ℂ) X ℂ _ x.val hxU _).symm.trans <|
        hev'.trans (smoothSheafCommRing.evalHom_germ J 𝓘(ℂ) Y ℂ U (f x.val) hxU s)
    exact (congrArg (fun t ↦ toFun I X _ t ⟨x.val, x.property⟩) hL₁).trans <|
      hL₂.trans <| hL₃.trans <| hR₃.symm.trans <| hR₂.symm.trans <|
        (congrArg (fun t ↦ toFun I X _ t x) hR₁).symm

end SmoothComparison

section CLinearity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℂ E' H'} {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

/-- If the stalk map of a presheafed-space morphism `φ` at `x.val` commutes with evaluation, then
`φ.c.app (op U)` acts at `x` by pointwise precomposition with `φ.base`. -/
theorem c_app_apply_of_stalkMap_evalHom
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (U : Opens Y) (g : (holomorphicStructureSheaf J Y).obj.obj (op U))
    (x : ↥((Opens.map φ.base).obj U))
    (h : φ.stalkMap x.val ≫ evalHom I X x.val = evalHom J Y (φ.base x.val)) :
    toFun I X (op ((Opens.map φ.base).obj U)) ((φ.c.app (op U)).hom g) x =
      toFun J Y (op U) g ⟨φ.base x.val, x.property⟩ := by
  have hev := congrArg (fun k ↦ k.hom
      (((holomorphicStructureSheaf J Y).presheaf.germ U (φ.base x.val) x.property).hom g)) h
  rw [CommRingCat.hom_comp, RingHom.comp_apply, evalHom_hom_apply, evalHom_hom_apply,
    PresheafedSpace.stalkMap_germ_apply φ U x.val x.property g] at hev
  exact (eval_germ I X _ x.val x.property _).symm.trans
    (hev.trans (eval_germ J Y U (φ.base x.val) x.property g))

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
  tfae_have 4 → 2 := fun h c ↦ ext fun x ↦
    (c_app_apply_of_stalkMap_evalHom φ ⊤ (algebraMap ℂ _ c) x (h x.val)).trans <|
      (algebraMap_apply (op ⊤) c ⟨φ.base x.val, x.property⟩).trans
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
theorem toRingHom_stalkAlgHomOfCAppTopAlgebraMap (x : X) :
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
      toFun J Y (op U) g ⟨φ.base x.val, x.property⟩ :=
  c_app_apply_of_stalkMap_evalHom φ U g x (((c_app_algebraMap_tfae φ).out 2 4 rfl rfl).1 hφ x.val)

/-- If the base map of a `ℂ`-linear presheafed-space morphism `φ` is complex analytic, then `φ`
equals `(locallyRingedSpaceMap φ.base hf).toHom` on both points and sections. -/
theorem locallyRingedSpaceMap_base_toHom_of_c_app_top_algebraMap
    (hf : ContMDiff I J ω φ.base) :
    (locallyRingedSpaceMap (X := X) (Y := Y) φ.base hf).toHom = φ :=
  toPresheafedSpace_hom_ext rfl fun U g x ↦
    (locallyRingedSpaceMap_c_app_apply (X := X) (Y := Y) φ.base hf U g ⟨x.val, x.property⟩).trans
      (c_app_apply_of_c_app_top_algebraMap φ hφ U g x).symm

/-- If the base map of a `ℂ`-linear presheafed-space morphism `φ` is complex analytic near `x : X`,
then its `ℂ`-algebra stalk map at `x` coincides with `stalkPullbackAlgHom hf`. -/
theorem stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAlgHom (x : X)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω φ.base w) :
    stalkAlgHomOfCAppTopAlgebraMap φ hφ x =
      stalkPullbackAlgHom (X := X) (Y := Y) hf := by
  ext s
  apply toFilterGerm_nhds_injective x
  obtain ⟨U, hxU, g, rfl⟩ := (holomorphicStructureSheaf J Y).presheaf.exists_germ_eq s
  let gExt : Y → ℂ := Function.extend Subtype.val (toFun J Y (op U) g) 0
  have hgExt (z : U) : toFun J Y (op U) g z = gExt z :=
    (Subtype.val_injective.extend_apply _ (0 : Y → ℂ) z).symm
  have hxX : x ∈ (Opens.map φ.base).obj U := hxU
  rw [stalkAlgHomOfCAppTopAlgebraMap_apply, stalkPullbackAlgHom_apply,
    PresheafedSpace.stalkMap_germ_apply φ U x hxU g, toFilterGerm_stalkPullback,
    toFilterGerm_germ le_rfl hxU g gExt hgExt, Germ.coe_compTendsto]
  exact toFilterGerm_germ le_rfl hxX ((φ.c.app (op U)).hom g) (gExt ∘ φ.base) fun w ↦
    (c_app_apply_of_c_app_top_algebraMap φ hφ U g w).trans (hgExt ⟨φ.base w.val, w.property⟩)

end TopAlgebraMap

/-- **Base-map extensionality for `ℂ`-linear presheafed-space morphisms.** Two morphisms of
holomorphic presheafed spaces whose global section maps fix the complex constants are equal if
their underlying continuous maps are equal. -/
theorem toPresheafedSpace_hom_ext_of_c_app_top_algebraMap
    {α β : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace}
    (w : α.base = β.base)
    (hα : ∀ c : ℂ, (α.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map α.base).obj ⊤))) c)
    (hβ : ∀ c : ℂ, (β.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map β.base).obj ⊤))) c) :
    α = β :=
  toPresheafedSpace_hom_ext w fun U g x ↦
    (c_app_apply_of_c_app_top_algebraMap α hα U g
      ⟨x.val, Eq.mpr congr(x.val ∈ (Opens.map $w).obj U) x.property⟩).trans <|
      (congrArg (fun z : U ↦ toFun J Y (op U) g z)
        (Subtype.ext (ConcreteCategory.congr_hom w x.val))).trans
        (c_app_apply_of_c_app_top_algebraMap β hβ U g x).symm

/-- **Base-map extensionality for `ℂ`-linear locally ringed-space morphisms.** Two morphisms of
holomorphic locally ringed spaces whose global section maps fix the complex constants are equal if
their underlying continuous maps are equal. -/
theorem locallyRingedSpace_hom_ext_of_c_app_top_algebraMap
    {α β : locallyRingedSpace I X ⟶ locallyRingedSpace J Y}
    (w : α.base = β.base)
    (hα : ∀ c : ℂ, (α.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map α.base).obj ⊤))) c)
    (hβ : ∀ c : ℂ, (β.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map β.base).obj ⊤))) c) :
    α = β :=
  LocallyRingedSpace.Hom.ext' (toPresheafedSpace_hom_ext_of_c_app_top_algebraMap w hα hβ)

/-- If the base map of a `ℂ`-linear morphism `φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y`
is complex analytic, then `φ` equals `locallyRingedSpaceMap φ.base hf` on both points and
sections. -/
theorem locallyRingedSpaceMap_base_of_c_app_top_algebraMap
    (φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c)
    (hf : ContMDiff I J ω φ.base) :
    locallyRingedSpaceMap (X := X) (Y := Y) φ.base hf = φ :=
  LocallyRingedSpace.Hom.ext'
    (locallyRingedSpaceMap_base_toHom_of_c_app_top_algebraMap φ.toHom hφ hf)

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
        (op ((Opens.map (φ ≫ ψ).base).obj U))) c :=
  (PresheafedSpace.comp_c_app_apply φ ψ (op U) (algebraMap ℂ _ c)).trans <|
    (congrArg _ (hψ U c)).trans (hφ ((Opens.map ψ.base).obj U) c)

/-- The type of `ℂ`-linear morphisms between holomorphic locally ringed spaces
`locallyRingedSpace I X` and `locallyRingedSpace J Y`, i.e., morphisms fixing the constant
sections `algebraMap ℂ _ c` on every open set. -/
abbrev LocallyRingedSpaceCLinearHom
    (I : ModelWithCorners ℂ E H) (X : Type) [TopologicalSpace X] [ChartedSpace H X]
    (J : ModelWithCorners ℂ E' H') (Y : Type) [TopologicalSpace Y] [ChartedSpace H' Y] : Type :=
  {φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y //
    ∀ (U : Opens Y) (c : ℂ), (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ
        ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj U))) c}

namespace LocallyRingedSpaceCLinearHom

/-- The identity `ℂ`-linear morphism on `locallyRingedSpace I X`. -/
def id (I : ModelWithCorners ℂ E H) (X : Type) [TopologicalSpace X] [ChartedSpace H X] :
    LocallyRingedSpaceCLinearHom I X I X :=
  ⟨𝟙 (locallyRingedSpace I X), id_c_app_algebraMap I X⟩

/-- The underlying locally ringed-space morphism of `LocallyRingedSpaceCLinearHom.id I X` is
`𝟙 (locallyRingedSpace I X)`. -/
@[simp]
theorem val_id (I : ModelWithCorners ℂ E H) (X : Type) [TopologicalSpace X] [ChartedSpace H X] :
    (LocallyRingedSpaceCLinearHom.id I X).val = 𝟙 (locallyRingedSpace I X) := (rfl)

/-- Composition of `ℂ`-linear morphisms `locallyRingedSpace I X ⟶ locallyRingedSpace J Y` and
`locallyRingedSpace J Y ⟶ locallyRingedSpace K Z`. -/
def comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] {H'' : Type*}
    [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace H'' Z]
    (ψ : LocallyRingedSpaceCLinearHom J Y K Z) (φ : LocallyRingedSpaceCLinearHom I X J Y) :
    LocallyRingedSpaceCLinearHom I X K Z :=
  ⟨φ.val ≫ ψ.val, comp_c_app_algebraMap (φ := φ.val.toHom) (ψ := ψ.val.toHom)
    φ.property ψ.property⟩

/-- The underlying locally ringed-space morphism of `ψ.comp φ` is `φ.val ≫ ψ.val`. -/
@[simp]
theorem val_comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] {H'' : Type*}
    [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace H'' Z]
    (ψ : LocallyRingedSpaceCLinearHom J Y K Z) (φ : LocallyRingedSpaceCLinearHom I X J Y) :
    (ψ.comp φ).val = φ.val ≫ ψ.val := (rfl)

/-- Left composition with `LocallyRingedSpaceCLinearHom.id` is the identity. -/
@[simp]
theorem id_comp (φ : LocallyRingedSpaceCLinearHom I X J Y) :
    (LocallyRingedSpaceCLinearHom.id J Y).comp φ = φ :=
  Subtype.ext (Category.comp_id φ.val)

/-- Right composition with `LocallyRingedSpaceCLinearHom.id` is the identity. -/
@[simp]
theorem comp_id (φ : LocallyRingedSpaceCLinearHom I X J Y) :
    φ.comp (LocallyRingedSpaceCLinearHom.id I X) = φ :=
  Subtype.ext (Category.id_comp φ.val)

/-- Composition of `ℂ`-linear morphisms of holomorphic locally ringed spaces is associative. -/
theorem comp_assoc {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] {H'' : Type*}
    [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace H'' Z]
    {E''' : Type*} [NormedAddCommGroup E'''] [NormedSpace ℂ E'''] {H''' : Type*}
    [TopologicalSpace H'''] {L : ModelWithCorners ℂ E''' H'''} {W : Type} [TopologicalSpace W]
    [ChartedSpace H''' W]
    (χ : LocallyRingedSpaceCLinearHom K Z L W) (ψ : LocallyRingedSpaceCLinearHom J Y K Z)
    (φ : LocallyRingedSpaceCLinearHom I X J Y) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  Subtype.ext (Category.assoc φ.val ψ.val χ.val).symm

end LocallyRingedSpaceCLinearHom

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
    ofContMDiff (fun z : U ↦ b.coord i (extChartAt J y₀ z.val)) fun z ↦
      ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff (n := ω)).contMDiff.contMDiffAt.comp z
        ((contMDiffAt_extChartAt' z.property).comp z contMDiff_subtypeVal.contMDiffAt)
  let t : Fin (Module.finrank ℂ E') → (holomorphicStructureSheaf I X).obj.obj (op V) := fun i ↦
    (φ.c.app (op U)).hom (s i)
  let G : V → E' := fun w ↦ ∑ i, t i w • b i
  have hG_cm : ContMDiff I 𝓘(ℂ, E') ω G := fun w ↦ ContMDiffAt.sum fun i _ ↦
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b i)).contDiff
      (n := ω)).contMDiff.contMDiffAt.comp w (contMDiff (t i) w)
  have hG_eq (w : V) : G w = extChartAt J y₀ (φ.base w.val) := by
    have htw (i : Fin (Module.finrank ℂ E')) :
        t i w = b.coord i (extChartAt J y₀ (φ.base w.val)) :=
      (c_app_apply_of_c_app_top_algebraMap φ hφ U (s i) w).trans (ofContMDiff_apply _ _ _)
    simp_rw [G, htw]; exact b.sum_repr (extChartAt J y₀ (φ.base w.val))
  have hx₀_tgt : G ⟨x₀, hx₀⟩ ∈ (extChartAt J y₀).target := by
    rw [hG_eq]; exact (extChartAt J y₀).map_source (by rw [extChartAt_source]; exact hy₀)
  refine (((contMDiffOn_extChartAt_symm (n := ω) y₀).contMDiffAt
    (extChartAt_target_mem_nhds' hx₀_tgt)).comp (⟨x₀, hx₀⟩ : V)
      (hG_cm ⟨x₀, hx₀⟩)).congr_of_eventuallyEq (Eventually.of_forall fun w ↦ ?_)
  have hw_src : φ.base w.val ∈ (extChartAt J y₀).source := by
    rw [extChartAt_source]; exact w.property
  rw [Function.comp_apply, hG_eq w, (extChartAt J y₀).left_inv hw_src]

/-- When `𝒪_{X, x}` is maximal-ideal separated (`IsHausdorff`), the inverse
`(analyticMapGermEquivStalkAlgHom x (φ.base x)).symm` applied to
`stalkAlgHomOfCAppTopAlgebraMap φ hφ x` recovers the germ of `φ.base` at `x`. -/
theorem analyticMapGermEquivStalkAlgHom_symm_stalkAlgHomOfCAppTopAlgebraMap (x : X)
    [IsHausdorff (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x)] :
    (analyticMapGermEquivStalkAlgHom (I := I) (J := J) x (φ.base x)).symm
        (stalkAlgHomOfCAppTopAlgebraMap φ hφ x) =
      AnalyticMapGerm.mk (X := X) (Y := Y) φ.base
        (Eventually.of_forall fun _ ↦ (contMDiff_base_of_c_app_top_algebraMap φ hφ).contMDiffAt)
        rfl := by
  rw [stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAlgHom φ hφ x
      (Eventually.of_forall fun _ ↦ (contMDiff_base_of_c_app_top_algebraMap φ hφ).contMDiffAt),
    analyticMapGermEquivStalkAlgHom_symm_stalkPullbackAlgHom]

end PresheafedRecovery

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
      locallyRingedSpaceMap_base_of_c_app_top_algebraMap φ (hφ ⊤)
        (contMDiff_base_of_c_app_top_algebraMap φ.toHom (hφ ⊤)), by
      rintro _ rfl; exact ContMDiffMap.ext fun _ ↦ rfl⟩⟩

variable (I X J Y) in
/-- **Equivalence between holomorphic maps and `ℂ`-linear morphisms of locally ringed spaces.**
For any complex charted space `(X, I)` and any finite-dimensional boundaryless complex manifold
`(Y, J)`, bundled complex-analytic maps `C^ω⟮I, X; J, Y⟯` correspond bijectively via
`locallyRingedSpaceMap` to `ℂ`-linear morphisms `LocallyRingedSpaceCLinearHom I X J Y`. -/
def holomorphicMapLocalRingedEquivalence :
    C^ω⟮I, X; J, Y⟯ ≃ LocallyRingedSpaceCLinearHom I X J Y where
  toFun f := ⟨locallyRingedSpaceMap f f.contMDiff,
    locallyRingedSpaceMap_c_app_algebraMap f f.contMDiff⟩
  invFun φ := ⟨φ.val.base, contMDiff_base_of_c_app_top_algebraMap φ.val.toHom (φ.property ⊤)⟩
  left_inv _ := ContMDiffMap.ext fun _ ↦ rfl
  right_inv φ := Subtype.ext <|
    locallyRingedSpaceMap_base_of_c_app_top_algebraMap φ.val (φ.property ⊤)
      (contMDiff_base_of_c_app_top_algebraMap φ.val.toHom (φ.property ⊤))

/-- In the forward direction, `holomorphicMapLocalRingedEquivalence` sends `f` to
`locallyRingedSpaceMap f f.contMDiff`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_apply_val (f : C^ω⟮I, X; J, Y⟯) :
    (holomorphicMapLocalRingedEquivalence I X J Y f).val =
      locallyRingedSpaceMap f f.contMDiff := (rfl)

/-- `holomorphicMapLocalRingedEquivalence` sends `ContMDiffMap.id` to
`LocallyRingedSpaceCLinearHom.id`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_id [FiniteDimensional ℂ E] [I.Boundaryless]
    [IsManifold I 1 X] :
    holomorphicMapLocalRingedEquivalence I X I X ContMDiffMap.id =
      LocallyRingedSpaceCLinearHom.id I X :=
  Subtype.ext (locallyRingedSpaceMap_id I X)

/-- `holomorphicMapLocalRingedEquivalence.symm` sends `LocallyRingedSpaceCLinearHom.id` to
`ContMDiffMap.id`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_id [FiniteDimensional ℂ E] [I.Boundaryless]
    [IsManifold I 1 X] :
    (holomorphicMapLocalRingedEquivalence I X I X).symm (LocallyRingedSpaceCLinearHom.id I X) =
      ContMDiffMap.id :=
  ContMDiffMap.ext fun _ ↦ rfl

section SymmAndComp

variable (φ : LocallyRingedSpaceCLinearHom I X J Y)

/-- Coercing `(holomorphicMapLocalRingedEquivalence I X J Y).symm φ` to a function gives
`φ.val.base`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_apply_coe :
    ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ : X → Y) = φ.val.base := (rfl)

/-- Evaluating `(holomorphicMapLocalRingedEquivalence I X J Y).symm φ` at `x` gives
`φ.val.base x`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_apply (x : X) :
    (holomorphicMapLocalRingedEquivalence I X J Y).symm φ x = φ.val.base x := (rfl)

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] [FiniteDimensional ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''} [K.Boundaryless]
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold K 1 Z]

/-- `holomorphicMapLocalRingedEquivalence` sends composition of analytic maps to composition of
`LocallyRingedSpaceCLinearHom`s. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_comp (g : C^ω⟮J, Y; K, Z⟯) (f : C^ω⟮I, X; J, Y⟯) :
    holomorphicMapLocalRingedEquivalence I X K Z (g.comp f) =
      (holomorphicMapLocalRingedEquivalence J Y K Z g).comp
        (holomorphicMapLocalRingedEquivalence I X J Y f) :=
  Subtype.ext (locallyRingedSpaceMap_comp f.contMDiff g.contMDiff)

/-- `holomorphicMapLocalRingedEquivalence.symm` sends composition of `LocallyRingedSpaceCLinearHom`s
to composition of analytic maps. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_comp
    (ψ : LocallyRingedSpaceCLinearHom J Y K Z) :
    (holomorphicMapLocalRingedEquivalence I X K Z).symm (ψ.comp φ) =
      ((holomorphicMapLocalRingedEquivalence J Y K Z).symm ψ).comp
        ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ) :=
  ContMDiffMap.ext fun _ ↦ rfl

/-- Restricting a holomorphic map `f : C^ω⟮I, X; J, Y⟯` to an open subset `U : Opens X` corresponds
under `holomorphicMapLocalRingedEquivalence` to precomposing with the open immersion
`(restrictLocallyRingedSpaceIso I X U).inv ≫ (locallyRingedSpace I X).ofRestrict _`. -/
theorem holomorphicMapLocalRingedEquivalence_restrict_val (f : C^ω⟮I, X; J, Y⟯) (U : Opens X) :
    (holomorphicMapLocalRingedEquivalence I U J Y
      (f.comp (⟨Subtype.val, contMDiff_subtypeVal⟩ : C^ω⟮I, U; I, X⟯))).val =
      (restrictLocallyRingedSpaceIso I X U).inv ≫
        (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) ≫
        (holomorphicMapLocalRingedEquivalence I X J Y f).val := by
  rw [restrictLocallyRingedSpaceIso_inv_comp_ofRestrict_assoc,
    holomorphicMapLocalRingedEquivalence_apply_val, holomorphicMapLocalRingedEquivalence_apply_val,
    ← locallyRingedSpaceMap_comp contMDiff_subtypeVal f.contMDiff]; rfl

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
    φ.base w.val = e.symm (z +
      ∑ i : ι, toFun I X (op ((Opens.map φ.base).obj ⟨e.source, e.open_source⟩))
        ((φ.c.app (op ⟨e.source, e.open_source⟩)).hom
          (e.holomorphicLinearCoordinateSection he
            (LinearMap.toContinuousLinearMap (b.coord i)) z)) w • b i) := by
  have hsum : ∑ i : ι, toFun I X (op ((Opens.map φ.base).obj ⟨e.source, e.open_source⟩))
      ((φ.c.app (op ⟨e.source, e.open_source⟩)).hom
        (e.holomorphicLinearCoordinateSection he
          (LinearMap.toContinuousLinearMap (b.coord i)) z)) w • b i = e (φ.base w.val) - z := by
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans (b.sum_repr (e (φ.base w.val) - z))
    rw [c_app_apply_of_c_app_top_algebraMap φ hφ ⟨e.source, e.open_source⟩ _ w]
    exact congrArg (· • b i) (e.holomorphicLinearCoordinateSection_apply he
      (LinearMap.toContinuousLinearMap (b.coord i)) z ⟨φ.base w.val, w.property⟩)
  rw [hsum, add_sub_cancel, e.left_inv w.property]

end OpenPartialHomeomorph

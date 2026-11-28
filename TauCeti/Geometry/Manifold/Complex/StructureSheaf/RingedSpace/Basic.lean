/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.RingedSpace.Defs
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Basic
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Complex manifolds as locally ringed spaces

Any complex charted space `(X, I)` carries a sheafed space `sheafedSpace I X` and a locally ringed
space `locallyRingedSpace I X` with underlying carrier `X` and structure sheaf
`holomorphicStructureSheaf I X` (defined in `StructureSheaf.RingedSpace.Defs`). On `X`,
`locallyRingedSpace I X` commutes with restriction to open subsets (`restrictLocallyRingedSpaceIso`)
and — on finite-dimensional boundaryless complex manifolds — is canonically isomorphic to Mathlib's
complex-smooth locally ringed space `ChartedSpace.locallyRingedSpace I X`
(`smoothLocallyRingedSpaceIso`). Every analytic map `f : X → Y` induces a morphism
`locallyRingedSpaceMap f hf : locallyRingedSpace I X ⟶ locallyRingedSpace J Y` by precomposition of
sections, functorially in `f` and compatibly with `smoothLocallyRingedSpaceIso`
(`locallyRingedSpaceMap_comp_smoothLocallyRingedSpaceIso_hom`).

For the characterization of which locally ringed-space morphisms come from analytic maps and the
resulting equivalence `holomorphicMapLocalRingedEquivalence`, see
`StructureSheaf.RingedSpace.Equiv`.

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
  rw [PresheafedSpace.stalkMap_germ_apply φ U x hx g]
  simp [φ, stalkPrecomp_germ I X f hf x U hx g]

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

private theorem locallyRingedSpaceMap_c_app_hom_apply (f : X → Y) (hf : ContMDiff I J ω f)
    (U : (Opens Y)ᵒᵖ) (s : (holomorphicStructureSheaf J Y).obj.obj U) :
    ((locallyRingedSpaceMap f hf).c.app U).hom s = precomp I X f hf U s :=
  (congrArg (fun k ↦ k.hom s) (locallyRingedSpaceMap_c_app f hf U)).trans
    (CommRingCat.ofHom_apply _ s)

-- Not `@[simp]`: `locallyRingedSpaceMap_c` and `homOfContMDiff_app` simplify `.c.app` on the LHS.
/-- On sections over `U`, `locallyRingedSpaceMap f hf` acts pointwise by precomposition with `f`. -/
theorem locallyRingedSpaceMap_c_app_apply (f : X → Y) (hf : ContMDiff I J ω f) (U : Opens Y)
    (s : (holomorphicStructureSheaf J Y).obj.obj (op U))
    (x : ↥((Opens.map (locallyRingedSpaceMap f hf).base).obj U)) :
    toFun I X (op ((Opens.map (locallyRingedSpaceMap f hf).base).obj U))
        (((locallyRingedSpaceMap f hf).c.app (op U)).hom s) x =
      toFun J Y (op U) s ⟨f x.val, x.property⟩ := by
  rw [locallyRingedSpaceMap_c_app_hom_apply]
  exact precomp_apply I X f hf (op U) s x

/-- `locallyRingedSpaceMap f hf` preserves complex scalar sections on every open `U : Opens Y`. -/
theorem locallyRingedSpaceMap_c_app_algebraMap (f : X → Y) (hf : ContMDiff I J ω f)
    (U : Opens Y) (c : ℂ) :
    ((locallyRingedSpaceMap f hf).c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (locallyRingedSpaceMap f hf).base).obj U))) c := by
  rw [locallyRingedSpaceMap_c_app_hom_apply]
  exact precomp_algebraMap f hf (op U) c

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
    rfl

/-- `locallyRingedSpaceMap` is covariantly functorial under composition of analytic maps. -/
theorem locallyRingedSpaceMap_comp {f : X → Y} (hf : ContMDiff I J ω f)
    {g : Y → Z} (hg : ContMDiff J K ω g) :
    locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg :=
  locallyRingedSpace_hom_ext (by ext; rfl) fun U s x ↦
    (locallyRingedSpaceMap_c_app_apply (g ∘ f) (hg.comp hf) U s ⟨x.val, x.property⟩).trans <|
      (locallyRingedSpaceMap_c_app_apply g hg U s ⟨f x.val, x.property⟩).symm.trans
        ((locallyRingedSpaceMap_c_app_apply f hf
          ((Opens.map (locallyRingedSpaceMap g hg).base).obj U) _ ⟨x.val, x.property⟩).symm.trans
          (congrArg (fun t ↦ toFun I X _ t x)
            (LocallyRingedSpace.comp_c_app_apply (locallyRingedSpaceMap f hf)
              (locallyRingedSpaceMap g hg) (op U) s).symm))

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

/-- The forward direction of `restrictLocallyRingedSpaceIso` is the identity on points. -/
@[simp]
theorem restrictLocallyRingedSpaceIso_hom_base (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).hom.base = 𝟙 (TopCat.of U) := by
  have h := congrArg (fun k : (locallyRingedSpace I X).restrict
      (Opens.isOpenEmbedding (X := TopCat.of X) U) ⟶ locallyRingedSpace I X ↦ k.base)
    (restrictLocallyRingedSpaceIso_hom_comp_locallyRingedSpaceMap (I := I) (X := X) U)
  exact TopCat.hom_ext <| ContinuousMap.ext fun x ↦
    Subtype.val_injective (ConcreteCategory.congr_hom h x)

/-- The inverse direction of `restrictLocallyRingedSpaceIso` is the identity on points. -/
@[simp]
theorem restrictLocallyRingedSpaceIso_inv_base (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).inv.base = 𝟙 (TopCat.of U) := by
  have h := congrArg (fun k : locallyRingedSpace I U ⟶ locallyRingedSpace I X ↦ k.base)
    (restrictLocallyRingedSpaceIso_inv_comp_ofRestrict (I := I) (X := X) U)
  ext x
  exact Subtype.val_injective (ConcreteCategory.congr_hom h x)

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

private theorem isoOfSheafIso_hom_c_app {T : TopCat} {P Q : TopCat.Sheaf CommRingCat T}
    (hP : ∀ x : T, IsLocalRing (P.presheaf.stalk x))
    (hQ : ∀ x : T, IsLocalRing (Q.presheaf.stalk x))
    (θ : P ≅ Q) (U : Opens T) :
    ((LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
      PresheafedSpace.isoOfComponents (Iso.refl T)
        (eqToIso (TopCat.Presheaf.Pushforward.id_eq P.presheaf) ≪≫
          (sheafToPresheaf _ _).mapIso θ) :
      (⟨⟨⟨T, P.presheaf⟩, P.property⟩, hP⟩ : LocallyRingedSpace) ≅
        (⟨⟨⟨T, Q.presheaf⟩, Q.property⟩, hQ⟩ : LocallyRingedSpace)).hom.c.app (op U)) =
      θ.inv.hom.app (op U) := by
  have heq : (eqToHom (TopCat.Presheaf.Pushforward.id_eq P.presheaf).symm).app (op U) = 𝟙 _ :=
    (eqToHom_app _ _).trans (eqToHom_refl _ _)
  exact (congrArg (θ.inv.hom.app (op U) ≫ ·) heq).trans (Category.comp_id _)

private theorem presheafedSpace_iso_hom_appLE_comp_inv_appLE {C : Type*} [Category C]
    {X Y : PresheafedSpace C} (e : X ≅ Y) (U : Opens Y) (V : Opens X)
    (hUV : V ≤ (Opens.map e.hom.base).obj U) (hVU : U ≤ (Opens.map e.inv.base).obj V) :
    e.hom.appLE U V hUV ≫ e.inv.appLE V U hVU = 𝟙 (Y.presheaf.obj (op U)) := by
  have h := PresheafedSpace.Hom.appLE_comp_appLE e.inv e.hom U V U hUV hVU
  rw [h, PresheafedSpace.Hom.congr_appLE e.inv_hom_id _ (by simp), PresheafedSpace.Hom.id_appLE]
  exact (congrArg Y.presheaf.map (Subsingleton.elim _ (𝟙 (op U)))).trans (Y.presheaf.map_id (op U))

private theorem locallyRingedSpace_iso_inv_appLE_eq {X Y : LocallyRingedSpace}
    (e : X ≅ Y) (U : Opens Y) (V : Opens X)
    (hUV : V ≤ (Opens.map e.hom.base).obj U) (hVU : U ≤ (Opens.map e.inv.base).obj V)
    {f : Y.presheaf.obj (op U) ⟶ X.presheaf.obj (op V)}
    {g : X.presheaf.obj (op V) ⟶ Y.presheaf.obj (op U)}
    (hf : e.hom.toHom.appLE U V hUV = f) (hg : g ≫ f = 𝟙 (X.presheaf.obj (op V))) :
    e.inv.toHom.appLE V U hVU = g := by
  let e' : X.toPresheafedSpace ≅ Y.toPresheafedSpace :=
    { hom := e.hom.toHom
      inv := e.inv.toHom
      hom_inv_id := (LocallyRingedSpace.comp_toHom _ _).symm.trans
        ((congrArg LocallyRingedSpace.Hom.toHom e.hom_inv_id).trans (LocallyRingedSpace.id_toHom _))
      inv_hom_id := (LocallyRingedSpace.comp_toHom _ _).symm.trans
        ((congrArg LocallyRingedSpace.Hom.toHom e.inv_hom_id).trans
          (LocallyRingedSpace.id_toHom _)) }
  have hcomp : f ≫ e.inv.toHom.appLE V U hVU = 𝟙 (Y.presheaf.obj (op U)) :=
    hf ▸ presheafedSpace_iso_hom_appLE_comp_inv_appLE e' U V hUV hVU
  calc
    e.inv.toHom.appLE V U hVU
        = 𝟙 (X.presheaf.obj (op V)) ≫ e.inv.toHom.appLE V U hVU := (Category.id_comp _).symm
    _   = (g ≫ f) ≫ e.inv.toHom.appLE V U hVU := by rw [hg]
    _   = g ≫ (f ≫ e.inv.toHom.appLE V U hVU) := Category.assoc _ _ _
    _   = g := by rw [hcomp, Category.comp_id]

private theorem isoOfSheafIso_inv_c_app {T : TopCat} {P Q : TopCat.Sheaf CommRingCat T}
    (hP : ∀ x : T, IsLocalRing (P.presheaf.stalk x))
    (hQ : ∀ x : T, IsLocalRing (Q.presheaf.stalk x))
    (θ : P ≅ Q) (U : Opens T) :
    ((LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
      PresheafedSpace.isoOfComponents (Iso.refl T)
        (eqToIso (TopCat.Presheaf.Pushforward.id_eq P.presheaf) ≪≫
          (sheafToPresheaf _ _).mapIso θ) :
      (⟨⟨⟨T, P.presheaf⟩, P.property⟩, hP⟩ : LocallyRingedSpace) ≅
        (⟨⟨⟨T, Q.presheaf⟩, Q.property⟩, hQ⟩ : LocallyRingedSpace)).inv.c.app (op U)) =
      θ.hom.hom.app (op U) := by
  let e : (⟨⟨⟨T, P.presheaf⟩, P.property⟩, hP⟩ : LocallyRingedSpace) ≅
      (⟨⟨⟨T, Q.presheaf⟩, Q.property⟩, hQ⟩ : LocallyRingedSpace) :=
    LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
      PresheafedSpace.isoOfComponents (Iso.refl T)
        (eqToIso (TopCat.Presheaf.Pushforward.id_eq P.presheaf) ≪≫
          (sheafToPresheaf _ _).mapIso θ)
  have hf : e.hom.toHom.appLE U U le_rfl = θ.inv.hom.app (op U) :=
    (PresheafedSpace.Hom.appLE_eq_app e.hom.toHom U).trans (isoOfSheafIso_hom_c_app hP hQ θ U)
  have hg : θ.hom.hom.app (op U) ≫ θ.inv.hom.app (op U) = 𝟙 _ :=
    congrArg (fun k ↦ k.hom.app (op U)) θ.hom_inv_id
  exact (PresheafedSpace.Hom.appLE_eq_app e.inv.toHom U).symm.trans
    (locallyRingedSpace_iso_inv_appLE_eq e U U le_rfl le_rfl hf hg)

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).hom` is the inverse section equivalence
`(smoothSectionsEquiv I X U).symm`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_hom_c_app (U : Opens X) :
    (smoothLocallyRingedSpaceIso I X).hom.c.app (op U) =
      CommRingCat.ofHom (smoothSectionsEquiv I X U).symm.toRingHom :=
  (isoOfSheafIso_hom_c_app _ _ (smoothSheafIso I X) U).trans (smoothSheafIso_inv_app U)

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).inv` is the section equivalence
`smoothSectionsEquiv I X U`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_inv_c_app (U : Opens X) :
    (smoothLocallyRingedSpaceIso I X).inv.c.app (op U) =
      CommRingCat.ofHom (smoothSectionsEquiv I X U).toRingHom :=
  (isoOfSheafIso_inv_c_app _ _ (smoothSheafIso I X) U).trans (smoothSheafIso_hom_app U)

private theorem smoothLocallyRingedSpaceIso_hom_c_app_hom_apply (U : Opens X)
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) :
    ((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s =
      (smoothSectionsEquiv I X U).symm s :=
  (congrArg (fun k ↦ k.hom s) (smoothLocallyRingedSpaceIso_hom_c_app I X U)).trans
    (CommRingCat.ofHom_apply _ s)

private theorem smoothLocallyRingedSpaceIso_inv_c_app_hom_apply (U : Opens X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) :
    ((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)).hom s =
      smoothSectionsEquiv I X U s :=
  (congrArg (fun k ↦ k.hom s) (smoothLocallyRingedSpaceIso_inv_c_app I X U)).trans
    (CommRingCat.ofHom_apply _ s)

/-- On stalks at `x`, `(smoothLocallyRingedSpaceIso I X).hom` agrees with
`(smoothStalkIso I X x).inv`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_hom_stalkMap (x : X) :
    (smoothLocallyRingedSpaceIso I X).hom.stalkMap x = (smoothStalkIso I X x).inv := by
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  obtain ⟨U, hx, g, rfl⟩ := (ChartedSpace.locallyRingedSpace I X).presheaf.exists_germ_eq s
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  have happ : ConcreteCategory.hom ((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)) g =
      (smoothSectionsEquiv I X U).symm g :=
    smoothLocallyRingedSpaceIso_hom_c_app_hom_apply I X U g
  rw [happ]
  exact (smoothStalkIso_inv_germ x U hx g).symm

/-- On stalks at `x`, `(smoothLocallyRingedSpaceIso I X).inv` agrees with
`(smoothStalkIso I X x).hom`. -/
@[simp]
theorem smoothLocallyRingedSpaceIso_inv_stalkMap (x : X) :
    (smoothLocallyRingedSpaceIso I X).inv.stalkMap x = (smoothStalkIso I X x).hom := by
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  obtain ⟨U, hx, g, rfl⟩ := (locallyRingedSpace I X).presheaf.exists_germ_eq s
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  have happ : ConcreteCategory.hom ((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)) g =
      smoothSectionsEquiv I X U g :=
    smoothLocallyRingedSpaceIso_inv_c_app_hom_apply I X U g
  rw [happ]
  exact (smoothStalkIso_hom_germ x U hx g).symm

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).hom` preserves pointwise values. -/
theorem smoothLocallyRingedSpaceIso_hom_c_app_apply (U : Opens X)
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) (x : U) :
    toFun I X (op U) (((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s) x =
      (s : C^∞⟮I, U; 𝓘(ℂ), ℂ⟯) x := by
  rw [smoothLocallyRingedSpaceIso_hom_c_app_hom_apply]
  exact smoothSectionsEquiv_symm_apply U s x

/-- On sections over `U`, `(smoothLocallyRingedSpaceIso I X).inv` preserves pointwise values. -/
theorem smoothLocallyRingedSpaceIso_inv_c_app_apply (U : Opens X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : U) :
    DFunLike.coe (F := C^∞⟮I, U; 𝓘(ℂ), ℂ⟯)
        (((smoothLocallyRingedSpaceIso I X).inv.c.app (op U)).hom s) x =
      toFun I X (op U) s x := by
  rw [smoothLocallyRingedSpaceIso_inv_c_app_hom_apply]
  exact smoothSectionsEquiv_apply U s x

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
    -- Re-bundle `U` as `V : Opens Y` so the holomorphic and smooth pointwise lemmas match.
    let V : Opens Y := ⟨U.carrier, U.isOpen⟩
    let sV : (smoothSheafCommRing J 𝓘(ℂ) Y ℂ).obj.obj (op V) := s
    have hL :
        (((locallyRingedSpaceMap f hf ≫
            (smoothLocallyRingedSpaceIso J Y).hom).c.app (op U)).hom s) =
          ((locallyRingedSpaceMap f hf).c.app (op V)).hom
            (((smoothLocallyRingedSpaceIso J Y).hom.c.app (op V)).hom sV) :=
      LocallyRingedSpace.comp_c_app_apply _ _ _ _
    have hR :
        ((((smoothLocallyRingedSpaceIso I X).hom ≫
          ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U)).hom s) =
          ((smoothLocallyRingedSpaceIso I X).hom.c.app
            (op ((Opens.map (ChartedSpace.locallyRingedSpaceMap f
              (hf.of_le (by simp))).base).obj U))).hom
            (((ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U)).hom s) :=
      LocallyRingedSpace.comp_c_app_apply _ _ _ _
    rw [hL, hR]
    have hL1 := locallyRingedSpaceMap_c_app_apply f hf V
      (((smoothLocallyRingedSpaceIso J Y).hom.c.app (op V)).hom sV) ⟨x.val, x.property⟩
    have hL2 := smoothLocallyRingedSpaceIso_hom_c_app_apply J Y V sV ⟨f x.val, x.property⟩
    have hR1 := smoothLocallyRingedSpaceIso_hom_c_app_apply I X
      ((Opens.map (ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).base).obj U)
      (((ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U)).hom s) x
    have hR2 := ChartedSpace.locallyRingedSpaceMap_c_app_apply f (hf.of_le (by simp)) sV x.property
    exact hL1.trans (hL2.trans (hR1.trans hR2).symm)

end SmoothComparison

end TauCeti.holomorphicStructureSheaf

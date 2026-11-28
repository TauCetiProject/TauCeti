/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.RingedSpace.Defs
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Basic
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Maps and open restrictions of holomorphic locally ringed spaces

Any complex charted space `(X, I)` carries a sheafed space `sheafedSpace I X` and a locally ringed
space `locallyRingedSpace I X` with underlying carrier `X` and structure sheaf
`holomorphicStructureSheaf I X` (defined in `StructureSheaf.RingedSpace.Defs`). On `X`,
`locallyRingedSpace I X` commutes with restriction to open subsets
(`restrictLocallyRingedSpaceIso`). Every analytic map `f : X → Y` induces a morphism
`locallyRingedSpaceMap f hf : locallyRingedSpace I X ⟶ locallyRingedSpace J Y` by precomposition of
sections, functorially in `f`.

For the comparison with Mathlib's complex-smooth locally ringed space
`ChartedSpace.locallyRingedSpace` on `C¹` finite-dimensional boundaryless complex manifolds, see
`StructureSheaf.RingedSpace.SmoothComparison`. For the characterization of which locally
ringed-space morphisms come from analytic maps and the resulting equivalence
`holomorphicMapLocalRingedEquivalence`, see `StructureSheaf.RingedSpace.Equiv`.

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
      𝟙 (locallyRingedSpace I X) := by
  have hbase :
      (locallyRingedSpaceMap (I := I) (J := I) (id : X → X) contMDiff_id).base =
        (𝟙 (locallyRingedSpace I X) : locallyRingedSpace I X ⟶ locallyRingedSpace I X).base := by
    rw [locallyRingedSpaceMap_base, LocallyRingedSpace.id_toHom, PresheafedSpace.id_base]
    exact TopCat.ofHom_id
  refine locallyRingedSpace_hom_ext hbase fun U s x ↦ ?_
  have hc : ((𝟙 (locallyRingedSpace I X) :
      locallyRingedSpace I X ⟶ locallyRingedSpace I X).c.app (op U)).hom s = s := by
    have hid := PresheafedSpace.id_c_app (locallyRingedSpace I X).toPresheafedSpace (op U)
    rw [(locallyRingedSpace I X).presheaf.map_id] at hid
    exact (congrArg (fun k ↦ k.hom s) hid).trans (CommRingCat.id_apply _ s)
  rw [locallyRingedSpaceMap_c_app_apply (I := I) (J := I) (id : X → X) contMDiff_id U s
    ⟨x.val, x.property⟩, hc]
  exact congrArg (toFun I X (op U) s) (Subtype.ext rfl)

/-- `locallyRingedSpaceMap` is covariantly functorial under composition of analytic maps. -/
theorem locallyRingedSpaceMap_comp {f : X → Y} (hf : ContMDiff I J ω f)
    {g : Y → Z} (hg : ContMDiff J K ω g) :
    locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg := by
  have hbase : (locallyRingedSpaceMap (g ∘ f) (hg.comp hf)).base =
      (locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg).base := by
    rw [LocallyRingedSpace.comp_base, locallyRingedSpaceMap_base,
      locallyRingedSpaceMap_base, locallyRingedSpaceMap_base]
    exact (TopCat.ofHom_comp ⟨f, hf.continuous⟩ ⟨g, hg.continuous⟩).symm
  refine locallyRingedSpace_hom_ext hbase fun U s x ↦ ?_
  exact (locallyRingedSpaceMap_c_app_apply (g ∘ f) (hg.comp hf) U s ⟨x.val, x.property⟩).trans <|
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

end TauCeti.holomorphicStructureSheaf

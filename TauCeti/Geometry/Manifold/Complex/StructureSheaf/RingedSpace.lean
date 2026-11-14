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
* When `Y` is a finite-dimensional boundaryless complex manifold (and `X` is an arbitrary complex
  charted space), pulling back local holomorphic chart coordinates expresses `φ.base` in every
  holomorphic chart `e` and basis `b` as `w ↦ e.symm (e (φ.base x) + ∑ i, tᵢ w • b i)`
  (`OpenPartialHomeomorph.base_eq_symm_sum_of_c_app_top_algebraMap`), showing independently of
  charts that `φ.base` is complex analytic (`contMDiff_base_of_c_app_top_algebraMap`) and that
  `locallyRingedSpaceMap φ.base _ = φ` (`eq_locallyRingedSpaceMap_of_c_app_top_algebraMap`).
* `holomorphicMapLocalRingedEquivalence` packages this into a bijection between bundled analytic
  maps `C^ω⟮I, X; J, Y⟯` and `ℂ`-linear morphisms `locallyRingedSpace I X ⟶ locallyRingedSpace J Y`,
  compatible with identity, composition, open restriction, and the stalk-level germ equivalence
  `analyticGermEquivStalkAlgHom`.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (X : Type) [TopologicalSpace X] [ChartedSpace H X]

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

/-- The `CommRingCat` evaluation morphism `evalHom` acts on germs by `eval`. -/
@[simp]
theorem evalHom_hom_apply (x : X) (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    (evalHom I X x).hom s = eval I X x s := by
  obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf I X).presheaf.exists_germ_eq s
  exact (evalHom_germ I X U x hx g).trans (eval_germ I X U x hx g).symm

private theorem map_eqToHom_apply {U V : Opens X} (h : U = V)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : V) :
    toFun I X (op V)
        (((holomorphicStructureSheaf I X).obj.map (eqToHom h.symm).op).hom s) x =
      toFun I X (op U) s ⟨x.1, h ▸ x.2⟩ := by
  subst h
  simp

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- The underlying morphism of presheafed spaces induced by a complex analytic map. -/
abbrev presheafedSpaceMap (f : X → Y) (hf : ContMDiff I J ω f) :
    (locallyRingedSpace I X).toPresheafedSpace ⟶ (locallyRingedSpace J Y).toPresheafedSpace where
  base := TopCat.ofHom ⟨f, hf.continuous⟩
  c := (homOfContMDiff I X f hf).hom

/-- Precomposition on sections along a complex analytic map preserves complex scalar sections. -/
@[simp]
theorem precomp_algebraMap (f : X → Y) (hf : ContMDiff I J ω f) (U : (Opens Y)ᵒᵖ) (c : ℂ) :
    precomp I X f hf U (algebraMap ℂ ((holomorphicStructureSheaf J Y).obj.obj U) c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).op.obj U)) c :=
  ext fun _ ↦ by simp

/-- On sections over `U`, `presheafedSpaceMap f hf` acts by `precomp I X f hf U`. -/
theorem presheafedSpaceMap_c_app (f : X → Y) (hf : ContMDiff I J ω f) (U : (Opens Y)ᵒᵖ) :
    (presheafedSpaceMap f hf).c.app U = CommRingCat.ofHom (precomp I X f hf U) :=
  homOfContMDiff_app I X f hf U

/-- On stalks at `x`, `presheafedSpaceMap f hf` acts by `stalkPrecomp I X f hf x`. -/
@[simp]
theorem presheafedSpaceMap_stalkMap (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    ((presheafedSpaceMap f hf).stalkMap x).hom = stalkPrecomp I X f hf x := by
  ext s
  obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf J Y).presheaf.exists_germ_eq s
  refine (PresheafedSpace.stalkMap_germ_apply (presheafedSpaceMap f hf) U x hx g).trans ?_
  refine (congrArg
    (((holomorphicStructureSheaf I X).presheaf.germ
      ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj U) x hx).hom) ?_).trans
    (stalkPrecomp_germ I X f hf x U hx g).symm
  rw [presheafedSpaceMap_c_app]
  rfl

/-- The stalk map of `presheafedSpaceMap f hf` at `x` reflects units. -/
theorem isLocalHom_presheafedSpaceMap_stalkMap
    (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    IsLocalHom ((presheafedSpaceMap f hf).stalkMap x).hom := by
  refine ⟨fun s hs ↦ isUnit_of_map_unit (stalkPrecompAlgHom I X f hf x) s ?_⟩
  simpa [presheafedSpaceMap_stalkMap] using hs

/-- A complex analytic map `f : X → Y` induces a morphism of holomorphic locally ringed spaces. -/
abbrev locallyRingedSpaceMap (f : X → Y) (hf : ContMDiff I J ω f) :
    locallyRingedSpace I X ⟶ locallyRingedSpace J Y where
  toHom := presheafedSpaceMap f hf
  prop := isLocalHom_presheafedSpaceMap_stalkMap f hf

/-- The underlying continuous map of `locallyRingedSpaceMap f hf` is `f`. -/
theorem locallyRingedSpaceMap_base (f : X → Y) (hf : ContMDiff I J ω f) :
    (locallyRingedSpaceMap f hf).base = TopCat.ofHom ⟨f, hf.continuous⟩ := (rfl)

/-- The sheaf part of `locallyRingedSpaceMap f hf` is `(homOfContMDiff I X f hf).hom`. -/
theorem locallyRingedSpaceMap_c (f : X → Y) (hf : ContMDiff I J ω f) :
    (locallyRingedSpaceMap f hf).c = (homOfContMDiff I X f hf).hom := (rfl)

/-- On sections over `U`, `locallyRingedSpaceMap f hf` acts by `precomp I X f hf U`. -/
theorem locallyRingedSpaceMap_c_app (f : X → Y) (hf : ContMDiff I J ω f) (U : (Opens Y)ᵒᵖ) :
    (locallyRingedSpaceMap f hf).c.app U = CommRingCat.ofHom (precomp I X f hf U) :=
  homOfContMDiff_app I X f hf U

/-- `locallyRingedSpaceMap f hf` preserves complex scalar sections on every open `U : Opens Y`. -/
theorem locallyRingedSpaceMap_c_app_algebraMap (f : X → Y) (hf : ContMDiff I J ω f)
    (U : Opens Y) (c : ℂ) :
    ((locallyRingedSpaceMap f hf).c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (locallyRingedSpaceMap f hf).base).obj U))) c := by
  apply ext
  intro x
  simp

/-- On stalks at `x`, `locallyRingedSpaceMap f hf` acts by `stalkPrecomp I X f hf x`. -/
@[simp]
theorem locallyRingedSpaceMap_stalkMap (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    ((locallyRingedSpaceMap f hf).stalkMap x).hom = stalkPrecomp I X f hf x :=
  presheafedSpaceMap_stalkMap f hf x

/-- The stalk map of `locallyRingedSpaceMap f hf` at `x` commutes with `evalHom`. -/
@[simp]
theorem locallyRingedSpaceMap_stalkMap_evalHom (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    (locallyRingedSpaceMap f hf).stalkMap x ≫ evalHom I X x = evalHom J Y (f x) := by
  apply CommRingCat.hom_ext
  ext s
  rw [CommRingCat.hom_comp, RingHom.comp_apply, locallyRingedSpaceMap_stalkMap]
  exact (evalHom_hom_apply x _).trans
    ((eval_stalkPrecomp I X f hf x s).trans (evalHom_hom_apply (f x) s).symm)

/-- Reassociated form of `locallyRingedSpaceMap_stalkMap_evalHom`. -/
@[simp]
theorem locallyRingedSpaceMap_stalkMap_evalHom_assoc (f : X → Y) (hf : ContMDiff I J ω f) (x : X)
    {R : CommRingCat} (h : CommRingCat.of ℂ ⟶ R) :
    (locallyRingedSpaceMap f hf).stalkMap x ≫ evalHom I X x ≫ h = evalHom J Y (f x) ≫ h := by
  rw [← Category.assoc, locallyRingedSpaceMap_stalkMap_evalHom]

variable (I X) in
/-- `locallyRingedSpaceMap` sends the identity map on `X` to the identity morphism. -/
theorem locallyRingedSpaceMap_id :
    locallyRingedSpaceMap (I := I) (J := I) (id : X → X) contMDiff_id =
      𝟙 (locallyRingedSpace I X) := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.ext_of_app rfl fun U ↦ ?_
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ext
  intro x
  simp only [CommRingCat.hom_comp, LocallyRingedSpace.id_toHom, PresheafedSpace.id_c_app]
  refine (map_eqToHom_apply rfl _ x).trans ?_
  rw [locallyRingedSpaceMap_c_app, CommRingCat.hom_ofHom]
  exact (precomp_apply I X id contMDiff_id (op U) s x).trans (map_eqToHom_apply rfl s x).symm

/-- `locallyRingedSpaceMap` is covariantly functorial under composition of analytic maps. -/
theorem locallyRingedSpaceMap_comp {f : X → Y} (hf : ContMDiff I J ω f)
    {g : Y → Z} (hg : ContMDiff J K ω g) :
    locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.ext_of_app rfl fun U ↦ ?_
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ext
  intro x
  simp only [CommRingCat.hom_comp, LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_c_app]
  refine (map_eqToHom_apply rfl _ x).trans ?_
  have hs1 : (((homOfContMDiff I X (g ∘ f) (hg.comp hf)).hom.app (op U)).hom s :
      (holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (TopCat.ofHom ⟨g ∘ f, (hg.comp hf).continuous⟩)).obj U))) =
      precomp I X (g ∘ f) (hg.comp hf) (op U) s := by
    rw [homOfContMDiff_app]
    rfl
  have hs2 : (((homOfContMDiff J Y g hg).hom.app (op U) ≫
      (homOfContMDiff I X f hf).hom.app
        (op ((Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U))).hom s :
      (holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj
          ((Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U)))) =
      precomp I X f hf (op ((Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U))
        (precomp J Y g hg (op U) s) := by
    -- Unfold `CommRingCat` composition across `TopCat.Presheaf.pushforward` before `rw`.
    have hcomp : (((homOfContMDiff J Y g hg).hom.app (op U) ≫
        (homOfContMDiff I X f hf).hom.app
          (op ((Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U))).hom s) =
        ((homOfContMDiff I X f hf).hom.app
          (op ((Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U))).hom
          (((homOfContMDiff J Y g hg).hom.app (op U)).hom s) := rfl
    rw [hcomp, homOfContMDiff_app, homOfContMDiff_app]
    rfl
  refine (congrArg (fun t ↦ toFun I X _ t ⟨x.1, x.2⟩) hs1).trans ?_
  refine (precomp_apply I X (g ∘ f) (hg.comp hf) (op U) s ⟨x.1, x.2⟩).trans ?_
  refine ((precomp_apply I X f hf
    (op ((Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U)) _ x).trans
    (precomp_apply J Y g hg (op U) s ⟨f x.1, x.2⟩)).symm.trans ?_
  exact (congrArg (fun t ↦ toFun I X _ t x) hs2).symm

/-- Inclusion of an open subset induces an open immersion of holomorphic locally ringed spaces. -/
instance instIsOpenImmersionLocallyRingedSpaceMapSubtypeVal (U : Opens X) :
    LocallyRingedSpace.IsOpenImmersion
      (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val) where
  base_open := U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let a : TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    have ha : IsOpenEmbedding a.hom := U.isOpenEmbedding'
    let V' : Opens U := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
    have hval (s : (holomorphicStructureSheaf I X).obj.obj (op (ha.isOpenMap.functor.obj V)))
        (z : V') :
        toFun I U (op V')
          (((locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X)
            contMDiff_subtype_val).c.app (op (ha.isOpenMap.functor.obj V))).hom s) z =
          toFun I X (op (ha.isOpenMap.functor.obj V)) s ⟨z.1.1, z.2⟩ := by
      have hsec : (((locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X)
          contMDiff_subtype_val).c.app (op (ha.isOpenMap.functor.obj V))).hom s :
          (holomorphicStructureSheaf I U).obj.obj (op V')) =
          precomp I U Subtype.val contMDiff_subtype_val (op (ha.isOpenMap.functor.obj V)) s := by
        rw [locallyRingedSpaceMap_c_app]
        rfl
      exact (congrArg (fun t ↦ toFun I U (op V') t z) hsec).trans
        (precomp_apply I U Subtype.val contMDiff_subtype_val
          (op (ha.isOpenMap.functor.obj V)) s z)
    refine ⟨fun s₁ s₂ hs ↦ ext fun ⟨x, y, hy, hyx⟩ ↦ ?_, fun g ↦ ?_⟩
    · obtain rfl : y.1 = x := hyx
      have hyV' : y ∈ V' := ⟨y, hy, rfl⟩
      exact (hval s₁ ⟨y, hyV'⟩).symm.trans <|
        (congrArg (fun s : (holomorphicStructureSheaf I U).obj.obj (op V') ↦
          toFun I U (op V') s ⟨y, hyV'⟩) hs).trans (hval s₂ ⟨y, hyV'⟩)
    · let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
        U.isOpenEmbedding'.homeomorphOfSubsetRange <| Set.image_subset_range _ V.1
      have hb : ContMDiff I I ω (b.symm : ha.isOpenMap.functor.obj V → V') := by
        refine (TauCeti.ContMDiff.subtypeVal_comp_iff V' _).mp ?_
        rw [← TauCeti.ContMDiff.subtypeVal_comp_iff U _]
        convert contMDiff_subtype_val using 1
        ext x
        exact congrArg Subtype.val (b.apply_symm_apply x)
      let gFun : V' → ℂ := toFun I U (op V') g
      have hgFun : ContMDiff I 𝓘(ℂ) ω gFun := contMDiff g
      refine ⟨ofContMDiff (gFun ∘ b.symm) (hgFun.comp hb), ext fun x ↦ ?_⟩
      exact (hval _ x).trans <|
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

/-- Composing `(restrictLocallyRingedSpaceIso I X U).hom` with the open-inclusion morphism gives
`(locallyRingedSpace I X).ofRestrict`. -/
@[simp]
theorem restrictLocallyRingedSpaceIso_hom_comp_locallyRingedSpaceMap (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).hom ≫
      locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val =
      (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict
    (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val)

/-- Composing `(restrictLocallyRingedSpaceIso I X U).inv` with `ofRestrict` gives
`locallyRingedSpaceMap Subtype.val contMDiff_subtype_val`. -/
@[simp]
theorem restrictLocallyRingedSpaceIso_inv_comp_ofRestrict (U : Opens X) :
    (restrictLocallyRingedSpaceIso I X U).inv ≫
      (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) =
      locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict
    (locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val)

/-- Reassociated form of `restrictLocallyRingedSpaceIso_inv_comp_ofRestrict`. -/
@[simp]
theorem restrictLocallyRingedSpaceIso_inv_comp_ofRestrict_assoc (U : Opens X)
    {W : LocallyRingedSpace} (h : locallyRingedSpace I X ⟶ W) :
    (restrictLocallyRingedSpaceIso I X U).inv ≫
      (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) ≫ h =
      locallyRingedSpaceMap (I := I) (J := I) (Subtype.val : U → X) contMDiff_subtype_val ≫ h := by
  rw [← Category.assoc, restrictLocallyRingedSpaceIso_inv_comp_ofRestrict]

end LocallyRingedSpace

section SmoothComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  (X : Type) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- On a finite-dimensional boundaryless complex manifold, the holomorphic locally ringed space is
canonically isomorphic over the identity on `X` to Mathlib's complex-smooth locally ringed space
`ChartedSpace.locallyRingedSpace I X`. -/
abbrev smoothLocallyRingedSpaceIso :
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
  have h : (((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s :
      (holomorphicStructureSheaf I X).obj.obj (op U)) =
      (smoothSectionsEquiv I X U).symm s := by
    -- Unfold `isoOfComponents` on `c.app (op U)` across `Pushforward.id_eq` before rewriting.
    have h1 : (((smoothLocallyRingedSpaceIso I X).hom.c.app (op U)).hom s :
        (holomorphicStructureSheaf I X).obj.obj (op U)) =
        ((eqToHom (TopCat.Presheaf.Pushforward.id_eq
          (holomorphicStructureSheaf I X).presheaf).symm).app (op U)).hom
          (((smoothSheafIso I X).inv.hom.app (op U)).hom s) := rfl
    exact h1.trans <|
      (congrArg
        (fun k : (holomorphicStructureSheaf I X).presheaf.obj (op U) ⟶
            (holomorphicStructureSheaf I X).presheaf.obj (op U) ↦
          k.hom (((smoothSheafIso I X).inv.hom.app (op U)).hom s))
        heq).trans <|
        congrArg
          (fun k : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U) ⟶
              (holomorphicStructureSheaf I X).obj.obj (op U) ↦ k.hom s)
          (smoothSheafIso_inv_app U)
  rw [h]
  exact smoothSectionsEquiv_symm_apply U s x

variable {I X}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'} [J.Boundaryless]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J 1 Y]

/-- `smoothLocallyRingedSpaceIso` intertwines `locallyRingedSpaceMap` with Mathlib's
`ChartedSpace.locallyRingedSpaceMap`. -/
theorem locallyRingedSpaceMap_comp_smoothLocallyRingedSpaceIso_hom
    (f : X → Y) (hf : ContMDiff I J ω f) :
    locallyRingedSpaceMap f hf ≫ (smoothLocallyRingedSpaceIso J Y).hom =
      (smoothLocallyRingedSpaceIso I X).hom ≫
        ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp)) := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.ext_of_app rfl fun U ↦ ?_
  let U' : Opens Y := U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  let s' : (smoothSheafCommRing J 𝓘(ℂ) Y ℂ).obj.obj (op U') := s
  apply ext
  intro x
  simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_c_app]
  refine (map_eqToHom_apply rfl _ x).trans ?_
  have hs : (((locallyRingedSpaceMap f hf).c.app (op U')).hom
      (((smoothLocallyRingedSpaceIso J Y).hom.c.app (op U')).hom s') :
      (holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj U'))) =
      precomp I X f hf (op U') (((smoothLocallyRingedSpaceIso J Y).hom.c.app (op U')).hom s') := by
    rw [locallyRingedSpaceMap_c_app]
    rfl
  refine (congrArg (fun t ↦ toFun I X _ t ⟨x.1, x.2⟩) hs).trans ?_
  refine (precomp_apply I X f hf (op U') _ ⟨x.1, x.2⟩).trans ?_
  exact (smoothLocallyRingedSpaceIso_hom_c_app_apply J Y U' s' ⟨f x.1, x.2⟩).trans
    (smoothLocallyRingedSpaceIso_hom_c_app_apply I X
      ((Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj U')
      (((ChartedSpace.locallyRingedSpaceMap f (hf.of_le (by simp))).c.app (op U')).hom s') x).symm

end SmoothComparison

section CLinearity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

/-- Restriction along open inclusions in `holomorphicStructureSheaf` preserves complex scalar
sections. -/
@[simp]
theorem presheaf_map_algebraMap {U V : Opens X} (h : U ⟶ V) (c : ℂ) :
    ((holomorphicStructureSheaf I X).presheaf.map h.op).hom
      (algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op V)) c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op U)) c :=
  ext fun _ ↦ by simp

/-- Four equivalent formulations of `ℂ`-linearity for a presheafed-space morphism between
holomorphic ringed spaces: preserving constants on all opens, preserving constants on global
sections, preserving constants on all stalks, and commuting with evaluation on all stalks. Neither
locality on stalks nor any manifold hypothesis on `X` or `Y` is required. -/
theorem c_app_algebraMap_tfae
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace) :
    List.TFAE
      [∀ (U : Opens Y) (c : ℂ),
          (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
            algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
              (op ((Opens.map φ.base).obj U))) c,
        ∀ c : ℂ,
          (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
            algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
              (op ((Opens.map φ.base).obj ⊤))) c,
        ∀ (x : X) (c : ℂ),
          (φ.stalkMap x).hom (algebraMap ℂ _ c) =
            algebraMap ℂ ((holomorphicStructureSheaf I X).presheaf.stalk x) c,
        ∀ x : X, φ.stalkMap x ≫ evalHom I X x = evalHom J Y (φ.base x)] := by
  tfae_have 1 → 2 := fun h c ↦ h ⊤ c
  tfae_have 2 → 1 := by
    intro h U c
    have hnat := congrArg
      (fun k : (holomorphicStructureSheaf J Y).presheaf.obj (op ⊤) ⟶
          (holomorphicStructureSheaf I X).presheaf.obj (op ((Opens.map φ.base).obj U)) ↦
        k.hom (algebraMap ℂ _ c))
      (φ.c.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      TopCat.Presheaf.pushforward_obj_map, presheaf_map_algebraMap] at hnat
    exact hnat.trans ((congrArg _ (h c)).trans (presheaf_map_algebraMap _ c))
  tfae_have 1 → 3 := by
    intro h x c
    have hxY : φ.base x ∈ (⊤ : Opens Y) := trivial
    have hxX : x ∈ (Opens.map φ.base).obj ⊤ := hxY
    rw [← germ_algebraMap J Y ⊤ (φ.base x) hxY c,
      PresheafedSpace.stalkMap_germ_apply φ ⊤ x hxY, h ⊤ c,
      germ_algebraMap I X ((Opens.map φ.base).obj ⊤) x hxX c]
  tfae_have 3 → 4 := by
    intro h x
    let ψ : (holomorphicStructureSheaf J Y).presheaf.stalk (φ.base x) →ₐ[ℂ]
        (holomorphicStructureSheaf I X).presheaf.stalk x :=
      { __ := (φ.stalkMap x).hom, commutes' := h x }
    apply CommRingCat.hom_ext
    ext s
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact (evalHom_hom_apply x (ψ s)).trans
      ((eval_algHom_apply ψ s).trans (evalHom_hom_apply (φ.base x) s).symm)
  tfae_have 4 → 2 := by
    intro h c
    apply ext
    intro x
    have hxY : φ.base x.1 ∈ (⊤ : Opens Y) := x.2
    have hev := congrArg (fun k ↦ k.hom
        (((holomorphicStructureSheaf J Y).presheaf.germ ⊤ (φ.base x.1) hxY).hom
          (algebraMap ℂ _ c)))
      (h x.1)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, evalHom_hom_apply, evalHom_hom_apply,
      PresheafedSpace.stalkMap_germ_apply φ ⊤ x.1 hxY] at hev
    refine (eval_germ I X _ x.1 x.2 _).symm.trans (hev.trans ?_)
    exact (eval_germ J Y ⊤ (φ.base x.1) hxY _).trans <|
      (algebraMap_apply (op ⊤) c ⟨φ.base x.1, hxY⟩).trans
        (algebraMap_apply (op ((Opens.map φ.base).obj ⊤)) c x).symm
  tfae_finish

/-- Bundle the stalk map of a `ℂ`-linear presheafed-space morphism at `x` as a `ℂ`-algebra
homomorphism `𝒪_{Y, φ.base x} →ₐ[ℂ] 𝒪_{X, x}`. -/
def stalkAlgHomOfCAppTopAlgebraMap
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c)
    (x : X) :
    (holomorphicStructureSheaf J Y).presheaf.stalk (φ.base x) →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk x where
  __ := (φ.stalkMap x).hom
  commutes' := ((c_app_algebraMap_tfae φ).out 2 3 rfl rfl).1 hφ x

/-- `stalkAlgHomOfCAppTopAlgebraMap` acts on germs by `(φ.stalkMap x).hom`. -/
@[simp]
theorem stalkAlgHomOfCAppTopAlgebraMap_apply
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c)
    (x : X) (s : (holomorphicStructureSheaf J Y).presheaf.stalk (φ.base x)) :
    stalkAlgHomOfCAppTopAlgebraMap φ hφ x s = (φ.stalkMap x).hom s := (rfl)

/-- Every presheafed-space morphism between holomorphic ringed spaces that preserves `ℂ`-constants
on global sections automatically induces local ring homomorphisms on all stalks. -/
theorem isLocalHom_stalkMap_of_c_app_top_algebraMap
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c)
    (x : X) :
    IsLocalHom (φ.stalkMap x).hom :=
  ⟨fun s hs ↦ isUnit_of_map_unit (stalkAlgHomOfCAppTopAlgebraMap φ hφ x) s hs⟩

/-- Promote a `ℂ`-linear morphism of presheafed spaces to a morphism of holomorphic locally ringed
spaces. -/
def locallyRingedSpaceHomOfPresheafedSpaceHom
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c) :
    locallyRingedSpace I X ⟶ locallyRingedSpace J Y where
  toHom := φ
  prop := isLocalHom_stalkMap_of_c_app_top_algebraMap φ hφ

/-- Forgetting stalk locality on `locallyRingedSpaceHomOfPresheafedSpaceHom φ hφ` recovers `φ`. -/
@[simp]
theorem locallyRingedSpaceHomOfPresheafedSpaceHom_toHom
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c) :
    (locallyRingedSpaceHomOfPresheafedSpaceHom φ hφ).toHom = φ := (rfl)

/-- **Section pullback formula.** Any `ℂ`-linear morphism of holomorphic presheafed spaces acts on
sections over every open `U : Opens Y` by pointwise precomposition with `φ.base`. -/
theorem c_app_apply_of_c_app_top_algebraMap
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c)
    (U : Opens Y) (g : (holomorphicStructureSheaf J Y).obj.obj (op U))
    (x : ↥((Opens.map φ.base).obj U)) :
    toFun I X (op ((Opens.map φ.base).obj U)) ((φ.c.app (op U)).hom g) x =
      toFun J Y (op U) g ⟨φ.base x.1, x.2⟩ := by
  have h4 := ((c_app_algebraMap_tfae φ).out 2 4 rfl rfl).1 hφ x.1
  have hev := congrArg (fun k ↦ k.hom
      (((holomorphicStructureSheaf J Y).presheaf.germ U (φ.base x.1) x.2).hom g)) h4
  rw [CommRingCat.hom_comp, RingHom.comp_apply, evalHom_hom_apply, evalHom_hom_apply,
    PresheafedSpace.stalkMap_germ_apply φ U x.1 x.2 g] at hev
  exact (eval_germ I X _ x.1 x.2 _).symm.trans <|
    hev.trans (eval_germ J Y U (φ.base x.1) x.2 g)

variable (I X) in
/-- The identity morphism on `locallyRingedSpace I X` preserves complex scalar sections. -/
theorem id_c_app_algebraMap (U : Opens X) (c : ℂ) :
    (((𝟙 (locallyRingedSpace I X) : locallyRingedSpace I X ⟶ locallyRingedSpace I X).c.app
        (op U)).hom (algebraMap ℂ _ c)) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map
          (𝟙 (locallyRingedSpace I X) :
            locallyRingedSpace I X ⟶ locallyRingedSpace I X).base).obj U))) c := by
  apply ext
  intro x
  -- Both sides evaluate definitionally to `c` across the identity pushforward.
  rfl

/-- Composition of `ℂ`-linear morphisms of holomorphic locally ringed spaces preserves complex
scalar sections. -/
theorem comp_c_app_algebraMap
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
    {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]
    {φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y}
    (hφ : ∀ (U : Opens Y) (c : ℂ),
      (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
        algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
          (op ((Opens.map φ.base).obj U))) c)
    {ψ : locallyRingedSpace J Y ⟶ locallyRingedSpace K Z}
    (hψ : ∀ (U : Opens Z) (c : ℂ),
      (ψ.c.app (op U)).hom (algebraMap ℂ _ c) =
        algebraMap ℂ ((holomorphicStructureSheaf J Y).obj.obj
          (op ((Opens.map ψ.base).obj U))) c)
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'} [J.Boundaryless]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J 1 Y]

/-- **Holomorphic recovery of the base map.** For any finite-dimensional boundaryless complex
manifold `Y` and any complex charted space `X`, every `ℂ`-linear morphism of holomorphic
presheafed spaces `(X, 𝒪_X) ⟶ (Y, 𝒪_Y)` has complex-analytic underlying map
`ContMDiff I J ω φ.base`. No manifold, boundaryless, or Hausdorffness assumption on `X` is
needed. -/
theorem contMDiff_base_of_c_app_top_algebraMap
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c) :
    ContMDiff I J ω φ.base := by
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
  have hG_cm : ContMDiff I 𝓘(ℂ, E') ω G := fun w ↦ by
    refine ContMDiffAt.sum fun i _ ↦ ?_
    have hbi := (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b i)).contDiff (n := ω)
    exact hbi.contMDiff.contMDiffAt.comp w (contMDiff (t i) w)
  have hG_eq (w : V) : G w = extChartAt J y₀ (φ.base w.1) := by
    have htw (i : Fin (Module.finrank ℂ E')) :
        t i w = b.coord i (extChartAt J y₀ (φ.base w.1)) :=
      (c_app_apply_of_c_app_top_algebraMap φ hφ U (s i) w).trans (ofContMDiff_apply _ _ _)
    simp_rw [G, htw]
    exact b.sum_repr (extChartAt J y₀ (φ.base w.1))
  have hx₀_tgt : G ⟨x₀, hx₀⟩ ∈ (extChartAt J y₀).target := by
    rw [hG_eq]
    exact (extChartAt J y₀).map_source (by rw [extChartAt_source]; exact hy₀)
  have hsymm : ContMDiffAt I J ω ((extChartAt J y₀).symm ∘ G) (⟨x₀, hx₀⟩ : V) :=
    ((contMDiffOn_extChartAt_symm (n := ω) y₀).contMDiffAt
      (extChartAt_target_mem_nhds' hx₀_tgt)).comp (⟨x₀, hx₀⟩ : V) (hG_cm ⟨x₀, hx₀⟩)
  refine hsymm.congr_of_eventuallyEq (Eventually.of_forall fun w ↦ ?_)
  have hw_src : φ.base w.1 ∈ (extChartAt J y₀).source := by
    rw [extChartAt_source]; exact w.2
  rw [Function.comp_apply, hG_eq w, (extChartAt J y₀).left_inv hw_src]

/-- Every `ℂ`-linear morphism `φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y` into a
finite-dimensional boundaryless complex manifold `Y` is equal to `locallyRingedSpaceMap φ.base _`
on both points and sections. -/
theorem eq_locallyRingedSpaceMap_of_c_app_top_algebraMap
    (φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c) :
    locallyRingedSpaceMap φ.base (contMDiff_base_of_c_app_top_algebraMap φ.toHom hφ) = φ := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.ext_of_app rfl fun U ↦ ?_
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro g
  apply ext
  intro x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  refine (map_eqToHom_apply rfl _ x).trans ?_
  rw [locallyRingedSpaceMap_c_app, CommRingCat.hom_ofHom]
  exact (precomp_apply I X φ.base _ (op U) g ⟨x.1, x.2⟩).trans
    (c_app_apply_of_c_app_top_algebraMap φ.toHom hφ U g x).symm

/-- At every point `x : X`, the `ℂ`-algebra stalk map of a `ℂ`-linear morphism
`φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y` coincides with `stalkPullbackAt` along
`φ.base`. -/
theorem stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAt
    (φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c)
    (x : X) :
    stalkAlgHomOfCAppTopAlgebraMap φ.toHom hφ x =
      stalkPullbackAt
        (Eventually.of_forall fun _ ↦
          (contMDiff_base_of_c_app_top_algebraMap φ.toHom hφ).contMDiffAt)
        rfl := by
  have hcm := contMDiff_base_of_c_app_top_algebraMap φ.toHom hφ
  rw [stalkPullbackAt_eq_stalkPrecompAlgHom φ.base hcm x]
  ext s
  obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf J Y).presheaf.exists_germ_eq s
  have hsec : ((φ.c.app (op U)).hom g :
      (holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj U))) =
      precomp I X φ.base hcm (op U) g :=
    ext fun w ↦ (c_app_apply_of_c_app_top_algebraMap φ.toHom hφ U g w).trans
      (precomp_apply I X φ.base hcm (op U) g w).symm
  rw [stalkAlgHomOfCAppTopAlgebraMap_apply, stalkPrecompAlgHom_apply]
  refine (PresheafedSpace.stalkMap_germ_apply φ.toHom U x hx g).trans ?_
  exact (congrArg
    (((holomorphicStructureSheaf I X).presheaf.germ ((Opens.map φ.base).obj U) x hx).hom)
    hsec).trans (stalkPrecomp_germ I X φ.base hcm x U hx g).symm

/-- When `𝒪_{X, x}` is maximal-ideal separated (`IsHausdorff`), the local germ equivalence
`analyticGermEquivStalkAlgHom` applied to `stalkAlgHomOfCAppTopAlgebraMap φ.toHom hφ x` recovers
the germ of `φ.base` at `x`. -/
theorem analyticGermEquivStalkAlgHom_symm_stalkAlgHom
    (φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c)
    (x : X)
    [IsHausdorff (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x)] :
    (analyticGermEquivStalkAlgHom (I := I) (J := J) x (φ.base x)).symm
        (stalkAlgHomOfCAppTopAlgebraMap φ.toHom hφ x) =
      AnalyticMapGerm.mk φ.base
        (Eventually.of_forall fun _ ↦
          (contMDiff_base_of_c_app_top_algebraMap φ.toHom hφ).contMDiffAt)
        rfl := by
  apply (analyticGermEquivStalkAlgHom (I := I) (J := J) x (φ.base x)).injective
  rw [Equiv.apply_symm_apply, analyticGermEquivStalkAlgHom_mk,
    stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAt]

/-- A morphism `φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y` into a finite-dimensional
boundaryless complex manifold `Y` is induced by a unique complex-analytic map `f : C^ω⟮I, X; J, Y⟯`
if and only if its section maps fix the complex constants. -/
theorem existsUnique_contMDiff_locallyRingedSpaceMap_eq_iff
    (φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y) :
    (∃! f : C^ω⟮I, X; J, Y⟯, locallyRingedSpaceMap f f.contMDiff = φ) ↔
      ∀ (U : Opens Y) (c : ℂ),
        (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
            (op ((Opens.map φ.base).obj U))) c := by
  constructor
  · rintro ⟨f, rfl, -⟩ U c
    exact locallyRingedSpaceMap_c_app_algebraMap f f.contMDiff U c
  · intro hφ
    refine ⟨⟨φ.base, contMDiff_base_of_c_app_top_algebraMap φ.toHom (hφ ⊤)⟩,
      eq_locallyRingedSpaceMap_of_c_app_top_algebraMap φ (hφ ⊤), ?_⟩
    rintro _ rfl
    ext x
    rfl

variable (I X J Y) in
/-- **Equivalence between holomorphic maps and `ℂ`-linear morphisms of locally ringed spaces.**
For any complex charted space `(X, I)` and any finite-dimensional boundaryless complex manifold
`(Y, J)`, bundled complex-analytic maps `C^ω⟮I, X; J, Y⟯` correspond bijectively via
`locallyRingedSpaceMap` to `ℂ`-linear morphisms
`locallyRingedSpace I X ⟶ locallyRingedSpace J Y`. -/
def holomorphicMapLocalRingedEquivalence :
    C^ω⟮I, X; J, Y⟯ ≃
      {φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y //
        ∀ (U : Opens Y) (c : ℂ),
          (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
            algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
              (op ((Opens.map φ.base).obj U))) c} where
  toFun f := ⟨locallyRingedSpaceMap f f.contMDiff,
    locallyRingedSpaceMap_c_app_algebraMap f f.contMDiff⟩
  invFun φ := ⟨φ.1.base, contMDiff_base_of_c_app_top_algebraMap φ.1.toHom (φ.2 ⊤)⟩
  left_inv _ := ContMDiffMap.ext fun _ ↦ rfl
  right_inv φ := Subtype.ext (eq_locallyRingedSpaceMap_of_c_app_top_algebraMap φ.1 (φ.2 ⊤))

/-- In the forward direction, `holomorphicMapLocalRingedEquivalence` sends `f` to
`locallyRingedSpaceMap f f.contMDiff`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_apply_val (f : C^ω⟮I, X; J, Y⟯) :
    (holomorphicMapLocalRingedEquivalence I X J Y f).1 =
      locallyRingedSpaceMap f f.contMDiff := (rfl)

/-- Coercing `(holomorphicMapLocalRingedEquivalence I X J Y).symm φ` to a function gives `φ.1.base`.
-/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_apply_coe
    (φ : {φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y //
      ∀ (U : Opens Y) (c : ℂ),
        (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
            (op ((Opens.map φ.base).obj U))) c}) :
    ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ : X → Y) = φ.1.base := (rfl)

/-- Evaluating `(holomorphicMapLocalRingedEquivalence I X J Y).symm φ` at `x` gives `φ.1.base x`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_apply
    (φ : {φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y //
      ∀ (U : Opens Y) (c : ℂ),
        (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
            (op ((Opens.map φ.base).obj U))) c})
    (x : X) :
    (holomorphicMapLocalRingedEquivalence I X J Y).symm φ x = φ.1.base x := (rfl)

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
        ⟨𝟙 (locallyRingedSpace I X), id_c_app_algebraMap I X⟩ =
      ContMDiffMap.id := by
  ext x
  rfl

section CompAndRestrict

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] [FiniteDimensional ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''} [K.Boundaryless]
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold K 1 Z]

/-- `holomorphicMapLocalRingedEquivalence` sends composition of analytic maps to composition of
morphisms. -/
theorem holomorphicMapLocalRingedEquivalence_comp
    (g : C^ω⟮J, Y; K, Z⟯) (f : C^ω⟮I, X; J, Y⟯) :
    (holomorphicMapLocalRingedEquivalence I X K Z (g.comp f)).1 =
      (holomorphicMapLocalRingedEquivalence I X J Y f).1 ≫
        (holomorphicMapLocalRingedEquivalence J Y K Z g).1 :=
  locallyRingedSpaceMap_comp f.contMDiff g.contMDiff

/-- `holomorphicMapLocalRingedEquivalence.symm` sends composition of morphisms to composition of
analytic maps. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_comp
    (φ : {φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y //
      ∀ (U : Opens Y) (c : ℂ),
        (φ.c.app (op U)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
            (op ((Opens.map φ.base).obj U))) c})
    (ψ : {ψ : locallyRingedSpace J Y ⟶ locallyRingedSpace K Z //
      ∀ (U : Opens Z) (c : ℂ),
        (ψ.c.app (op U)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((holomorphicStructureSheaf J Y).obj.obj
            (op ((Opens.map ψ.base).obj U))) c}) :
    (holomorphicMapLocalRingedEquivalence I X K Z).symm
        ⟨φ.1 ≫ ψ.1, comp_c_app_algebraMap φ.2 ψ.2⟩ =
      ((holomorphicMapLocalRingedEquivalence J Y K Z).symm ψ).comp
        ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ) := by
  ext x
  rfl

/-- Restricting a holomorphic map `f : C^ω⟮I, X; J, Y⟯` to an open subset `U : Opens X` corresponds
under `holomorphicMapLocalRingedEquivalence` to precomposing with the open immersion
`(restrictLocallyRingedSpaceIso I X U).inv ≫ (locallyRingedSpace I X).ofRestrict _`. -/
theorem holomorphicMapLocalRingedEquivalence_restrict (f : C^ω⟮I, X; J, Y⟯) (U : Opens X) :
    (holomorphicMapLocalRingedEquivalence I U J Y
      (f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^ω⟮I, U; I, X⟯))).1 =
      (restrictLocallyRingedSpaceIso I X U).inv ≫
        (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) ≫
        (holomorphicMapLocalRingedEquivalence I X J Y f).1 := by
  rw [restrictLocallyRingedSpaceIso_inv_comp_ofRestrict_assoc,
    holomorphicMapLocalRingedEquivalence_apply_val,
    holomorphicMapLocalRingedEquivalence_apply_val,
    ← locallyRingedSpaceMap_comp contMDiff_subtype_val f.contMDiff]
  rfl

end CompAndRestrict

end Equivalence

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y]
  (e : OpenPartialHomeomorph Y E') (he : e ∈ maximalAtlas 𝓘(ℂ, E') ω Y)

/-- Centered linear coordinate `z ↦ b.coord i (e z - e y)` on `e.source` as a holomorphic section
over `⟨e.source, e.open_source⟩`. -/
def holomorphicCoordinateSection {ι : Type*} (b : Module.Basis ι ℂ E') (y : Y) (i : ι) :
    (holomorphicStructureSheaf 𝓘(ℂ, E') Y).obj.obj (op ⟨e.source, e.open_source⟩) :=
  ofContMDiff (fun z : (⟨e.source, e.open_source⟩ : Opens Y) ↦
      b.coord i (e z.1 - e y)) <| by
    intro z
    have hlin := (LinearMap.toContinuousLinearMap (b.coord i)).contDiff (n := ω)
    have hez := ((contMDiffOn_of_mem_maximalAtlas he).contMDiffAt
      (e.open_source.mem_nhds z.2)).comp z contMDiff_subtype_val.contMDiffAt
    exact hlin.contMDiff.contMDiffAt.comp z (hez.sub contMDiffAt_const)

/-- Evaluating `e.holomorphicCoordinateSection he b y i` at `z ∈ e.source` gives
`b.coord i (e z - e y)`. -/
@[simp]
theorem holomorphicCoordinateSection_apply {ι : Type*} (b : Module.Basis ι ℂ E') (y : Y) (i : ι)
    (z : (⟨e.source, e.open_source⟩ : Opens Y)) :
    e.holomorphicCoordinateSection he b y i z = b.coord i (e z.1 - e y) :=
  ofContMDiff_apply _ _ z

include he in
/-- **Chart-independent local coordinate recovery.** In *any* holomorphic chart `e` around
`φ.base x` and *any* basis `b` of `E'`, the base map `φ.base` of a `ℂ`-linear morphism is given on
`φ.base ⁻¹' e.source` by `w ↦ e.symm (e (φ.base x) + ∑ i, tᵢ w • b i)` where `tᵢ` is the pulled-back
centered linear coordinate section. -/
theorem base_eq_symm_sum_of_c_app_top_algebraMap {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ E')
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace 𝓘(ℂ, E') Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj
        (op ((Opens.map φ.base).obj ⊤))) c)
    (x : X)
    (w : ↥((Opens.map φ.base).obj ⟨e.source, e.open_source⟩)) :
    φ.base w.1 = e.symm (e (φ.base x) +
      ∑ i : ι, toFun I X (op ((Opens.map φ.base).obj ⟨e.source, e.open_source⟩))
        ((φ.c.app (op ⟨e.source, e.open_source⟩)).hom
          (e.holomorphicCoordinateSection he b (φ.base x) i)) w • b i) := by
  have hsum : ∑ i : ι, toFun I X (op ((Opens.map φ.base).obj ⟨e.source, e.open_source⟩))
      ((φ.c.app (op ⟨e.source, e.open_source⟩)).hom
        (e.holomorphicCoordinateSection he b (φ.base x) i)) w • b i =
      e (φ.base w.1) - e (φ.base x) := by
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans (b.sum_repr (e (φ.base w.1) - e (φ.base x)))
    rw [c_app_apply_of_c_app_top_algebraMap φ hφ ⟨e.source, e.open_source⟩ _ w]
    exact congrArg (· • b i)
      (e.holomorphicCoordinateSection_apply he b (φ.base x) i ⟨φ.base w.1, w.2⟩)
  rw [hsum, add_sub_cancel, e.left_inv w.2]

end OpenPartialHomeomorph

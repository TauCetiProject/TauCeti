/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.AlgHom
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.RingedSpace.Basic
import Mathlib.Tactic.TFAE
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Equivalence between holomorphic maps and locally `ℂ`-ringed morphisms

This file characterizes which morphisms between the holomorphic locally ringed spaces
`locallyRingedSpace I X` and `locallyRingedSpace J Y` (constructed in
`StructureSheaf.RingedSpace.Defs`, with induced maps and comparisons in
`StructureSheaf.RingedSpace.Basic`) come from complex analytic maps:

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
  `locallyRingedSpace_hom_ext_of_c_app_top_algebraMap`). Whenever `φ.base` is globally complex
  analytic, `φ` agrees with `locallyRingedSpaceMap`
  (`locallyRingedSpaceMap_toHom_eq_of_c_app_top_algebraMap`,
  `locallyRingedSpaceMap_eq_of_c_app_top_algebraMap`), and whenever `φ.base` is complex analytic
  near `x`, its `ℂ`-algebra stalk map at `x` agrees with `stalkPullbackAlgHom`
  (`stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAlgHom`). The `ℂ`-linearity hypothesis is
  essential: composing section pullback with complex conjugation along an antiholomorphic map gives
  a `LocallyRingedSpace` morphism that fixes only real constants.
* For any complex charted space `Y` modelled over a finite-dimensional space `E'` via `(J, H')`
  (and any complex charted space `X`), pulling back extended-chart linear coordinate sections
  expresses `φ.base` in every holomorphic chart `e ∈ maximalAtlas J ω Y`, basis `b`, and
  translation vector `z : E'` as `w ↦ (e.extend J).symm (z + ∑ i, tᵢ w • b i)`
  (`OpenPartialHomeomorph.base_eq_symm_sum_of_c_app_top_algebraMap`). When `J` is boundaryless and
  `Y` is a complex manifold, applying this to `chartAt H' y₀` at `z := 0` shows independently of
  charts that `φ.base` is complex analytic (`contMDiff_base_of_c_app_top_algebraMap`).
* `holomorphicMapLocalRingedEquivalence` packages this into a bijection between bundled analytic
  maps `C^ω⟮I, X; J, Y⟯` and `ℂ`-linear morphisms `LocallyRingedSpaceCLinearHom I X J Y`,
  compatible with identity, composition, open restriction, and the stalk-level germ equivalence
  `analyticMapGermEquivStalkAlgHom`.

## References

* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Grundlehren der mathematischen
  Wissenschaften 265, Springer, 1984, Chapter 1, §1.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter V, §A
  (for the characterization of holomorphic maps as `ℂ`-linear morphisms of locally ringed spaces).
* O. Forster, *Lectures on Riemann Surfaces*, §§1 and 6.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Filter IsManifold Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

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

/-- **Section pullback formula.** Any `ℂ`-linear morphism of holomorphic presheafed spaces acts on
sections over every open `U : Opens Y` by pointwise precomposition with `φ.base`. -/
theorem c_app_apply_of_c_app_top_algebraMap (U : Opens Y)
    (g : (holomorphicStructureSheaf J Y).obj.obj (op U)) (x : ↥((Opens.map φ.base).obj U)) :
    toFun I X (op ((Opens.map φ.base).obj U)) ((φ.c.app (op U)).hom g) x =
      toFun J Y (op U) g ⟨φ.base x.val, x.property⟩ :=
  c_app_apply_of_stalkMap_evalHom φ U g x (((c_app_algebraMap_tfae φ).out 2 4 rfl rfl).1 hφ x.val)

/-- If the base map of a `ℂ`-linear presheafed-space morphism `φ` is complex analytic, then `φ`
equals `(locallyRingedSpaceMap φ.base hf).toHom` on both points and sections. -/
theorem locallyRingedSpaceMap_toHom_eq_of_c_app_top_algebraMap
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
theorem locallyRingedSpaceMap_eq_of_c_app_top_algebraMap
    (φ : locallyRingedSpace I X ⟶ locallyRingedSpace J Y)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c)
    (hf : ContMDiff I J ω φ.base) :
    locallyRingedSpaceMap (X := X) (Y := Y) φ.base hf = φ :=
  LocallyRingedSpace.Hom.ext'
    (locallyRingedSpaceMap_toHom_eq_of_c_app_top_algebraMap φ.toHom hφ hf)

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

/-- Two `ℂ`-linear morphisms of holomorphic locally ringed spaces are equal if their underlying
continuous maps are equal. -/
@[ext]
theorem ext {φ ψ : LocallyRingedSpaceCLinearHom I X J Y} (w : φ.val.base = ψ.val.base) :
    φ = ψ :=
  Subtype.ext <| locallyRingedSpace_hom_ext_of_c_app_top_algebraMap w (φ.property ⊤) (ψ.property ⊤)

-- Exposed so `.val.toHom` and `.val.base` reduce definitionally across module boundaries.
/-- Promote a presheafed-space morphism preserving `ℂ`-constants on global sections to a bundled
`ℂ`-linear morphism of holomorphic locally ringed spaces. -/
@[expose]
def ofPresheafedSpaceHom
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶ (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c) :
    LocallyRingedSpaceCLinearHom I X J Y :=
  ⟨⟨φ, isLocalHom_stalkMap_of_c_app_top_algebraMap φ hφ⟩,
    ((c_app_algebraMap_tfae φ).out 2 1 rfl rfl).1 hφ⟩

/-- Forgetting stalk locality on `(LocallyRingedSpaceCLinearHom.ofPresheafedSpaceHom φ hφ).val`
recovers `φ`. -/
@[simp]
theorem val_toHom_ofPresheafedSpaceHom
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶ (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c) :
    (ofPresheafedSpaceHom φ hφ).val.toHom = φ := (rfl)

-- Exposed so `.val.base` reduces definitionally in the dependent types of `stalkAlgHom` lemmas.
/-- The identity `ℂ`-linear morphism on `locallyRingedSpace I X`. -/
@[expose]
def id (I : ModelWithCorners ℂ E H) (X : Type) [TopologicalSpace X] [ChartedSpace H X] :
    LocallyRingedSpaceCLinearHom I X I X :=
  ⟨𝟙 (locallyRingedSpace I X), id_c_app_algebraMap I X⟩

/-- The underlying locally ringed-space morphism of `LocallyRingedSpaceCLinearHom.id I X` is
`𝟙 (locallyRingedSpace I X)`. -/
@[simp]
theorem val_id (I : ModelWithCorners ℂ E H) (X : Type) [TopologicalSpace X] [ChartedSpace H X] :
    (LocallyRingedSpaceCLinearHom.id I X).val = 𝟙 (locallyRingedSpace I X) := (rfl)

-- Exposed so `.val.base` reduces definitionally in the dependent types of `stalkAlgHom` lemmas.
/-- Composition of `ℂ`-linear morphisms `locallyRingedSpace I X ⟶ locallyRingedSpace J Y` and
`locallyRingedSpace J Y ⟶ locallyRingedSpace K Z`. -/
@[expose]
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

-- Exposed so `.val.base` reduces definitionally in the dependent types of `stalkAlgHom` lemmas.
/-- Bundle a complex analytic map `f : X → Y` as a `ℂ`-linear morphism of holomorphic locally
ringed spaces. No manifold, boundaryless, or finite-dimensionality hypotheses are required. -/
@[expose]
def ofContMDiff (f : X → Y) (hf : ContMDiff I J ω f) : LocallyRingedSpaceCLinearHom I X J Y :=
  ⟨locallyRingedSpaceMap f hf, locallyRingedSpaceMap_c_app_algebraMap f hf⟩

/-- The underlying locally ringed-space morphism of `ofContMDiff f hf` is
`locallyRingedSpaceMap f hf`. -/
@[simp]
theorem val_ofContMDiff (f : X → Y) (hf : ContMDiff I J ω f) :
    (ofContMDiff f hf).val = locallyRingedSpaceMap f hf := (rfl)

variable (I X) in
/-- `LocallyRingedSpaceCLinearHom.ofContMDiff` sends `id` to `LocallyRingedSpaceCLinearHom.id`. -/
@[simp]
theorem ofContMDiff_id :
    ofContMDiff (I := I) (J := I) (_root_.id : X → X) contMDiff_id =
      LocallyRingedSpaceCLinearHom.id I X :=
  Subtype.ext (locallyRingedSpaceMap_id I X)

/-- `LocallyRingedSpaceCLinearHom.ofContMDiff` is covariantly functorial under composition. -/
theorem ofContMDiff_comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
    {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]
    {f : X → Y} (hf : ContMDiff I J ω f) {g : Y → Z} (hg : ContMDiff J K ω g) :
    ofContMDiff (g ∘ f) (hg.comp hf) = (ofContMDiff g hg).comp (ofContMDiff f hf) :=
  Subtype.ext (locallyRingedSpaceMap_comp hf hg)

/-- `LocallyRingedSpaceCLinearHom.ofContMDiff` sends a composite bundled analytic map `g.comp f`
to the composite `ℂ`-linear morphism, independently of the analyticity proof term. -/
@[simp]
theorem ofContMDiff_contMDiffMap_comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
    {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]
    (g : C^ω⟮J, Y; K, Z⟯) (f : C^ω⟮I, X; J, Y⟯) (hgf : ContMDiff I K ω (g.comp f)) :
    ofContMDiff (g.comp f) hgf =
      (ofContMDiff g g.contMDiff).comp (ofContMDiff f f.contMDiff) :=
  ofContMDiff_comp f.contMDiff g.contMDiff

/-- The `ℂ`-algebra homomorphism induced on holomorphic stalks at `x : X` by a `ℂ`-linear morphism
`φ : LocallyRingedSpaceCLinearHom I X J Y`. -/
def stalkAlgHom (φ : LocallyRingedSpaceCLinearHom I X J Y) (x : X) :
    (holomorphicStructureSheaf J Y).presheaf.stalk (φ.val.base x) →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk x :=
  stalkAlgHomOfCAppTopAlgebraMap φ.val.toHom (φ.property ⊤) x

/-- Coercing `φ.stalkAlgHom x` to a ring homomorphism recovers `(φ.val.stalkMap x).hom`. -/
@[simp]
theorem toRingHom_stalkAlgHom (φ : LocallyRingedSpaceCLinearHom I X J Y) (x : X) :
    (φ.stalkAlgHom x :
      (holomorphicStructureSheaf J Y).presheaf.stalk (φ.val.base x) →+*
        (holomorphicStructureSheaf I X).presheaf.stalk x) = (φ.val.stalkMap x).hom := (rfl)

/-- `φ.stalkAlgHom x` acts on germs by `(φ.val.stalkMap x).hom`. -/
@[simp]
theorem stalkAlgHom_apply (φ : LocallyRingedSpaceCLinearHom I X J Y) (x : X)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (φ.val.base x)) :
    φ.stalkAlgHom x s = (φ.val.stalkMap x).hom s := (rfl)

/-- The `ℂ`-algebra stalk map of `LocallyRingedSpaceCLinearHom.id I X` is `AlgHom.id`. -/
@[simp]
theorem stalkAlgHom_id (x : X) :
    (LocallyRingedSpaceCLinearHom.id I X).stalkAlgHom x =
      AlgHom.id ℂ ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  AlgHom.ext fun s ↦ (stalkAlgHom_apply _ x s).trans <|
    (congrArg (fun k ↦ CommRingCat.Hom.hom k s)
      (LocallyRingedSpace.stalkMap_id (locallyRingedSpace I X) x)).trans
      (CommRingCat.id_apply _ s)

/-- The `ℂ`-algebra stalk map of a composite `ψ.comp φ` is the contravariant composite of the
`ℂ`-algebra stalk maps of `ψ` and `φ`. -/
@[simp]
theorem stalkAlgHom_comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
    {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]
    (ψ : LocallyRingedSpaceCLinearHom J Y K Z) (φ : LocallyRingedSpaceCLinearHom I X J Y)
    (x : X) :
    (ψ.comp φ).stalkAlgHom x =
      (φ.stalkAlgHom x).comp (ψ.stalkAlgHom (φ.val.base x)) :=
  AlgHom.ext fun s ↦ (stalkAlgHom_apply _ x s).trans <|
    (congrArg (fun k ↦ CommRingCat.Hom.hom k s)
      (LocallyRingedSpace.stalkMap_comp (f := φ.val) (g := ψ.val) x)).trans
      (CommRingCat.comp_apply _ _ s)

/-- The `ℂ`-algebra stalk map of `ofContMDiff f hf` at `x` is `stalkPullbackAlgHom`. -/
@[simp]
theorem stalkAlgHom_ofContMDiff (f : X → Y) (hf : ContMDiff I J ω f) (x : X) :
    (ofContMDiff f hf).stalkAlgHom x =
      stalkPullbackAlgHom (Eventually.of_forall fun _ ↦ hf.contMDiffAt) :=
  stalkAlgHomOfCAppTopAlgebraMap_eq_stalkPullbackAlgHom (locallyRingedSpaceMap f hf).toHom
    (locallyRingedSpaceMap_c_app_algebraMap f hf ⊤) x
    (Eventually.of_forall fun _ ↦ hf.contMDiffAt)

end LocallyRingedSpaceCLinearHom

end CLinearity

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]
  (e : OpenPartialHomeomorph Y H') (he : e ∈ maximalAtlas J ω Y)

include he in
/-- The `i`-th linear coordinate function of an extended holomorphic chart `e.extend J`, centered
at `z : E'`, as a holomorphic section on `⟨e.source, e.open_source⟩`. -/
def extendCoordSection {ι : Type*} (b : Module.Basis ι ℂ E') (z : E') (i : ι) :
    (holomorphicStructureSheaf J Y).obj.obj (op ⟨e.source, e.open_source⟩) :=
  ofContMDiff (fun y : (⟨e.source, e.open_source⟩ : Opens Y) ↦ b.coord i (e.extend J y.val - z))
    fun y ↦ ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff
      (n := ω)).contMDiff.contMDiffAt.comp y
      (((e.contMDiffAt_extend he y.property).comp y contMDiff_subtypeVal.contMDiffAt).sub
        contMDiffAt_const)

include he in
/-- Evaluating `e.extendCoordSection he b z i` at `y` gives `b.coord i (e.extend J y.val - z)`. -/
@[simp]
theorem extendCoordSection_apply {ι : Type*} (b : Module.Basis ι ℂ E') (z : E') (i : ι)
    (y : (⟨e.source, e.open_source⟩ : Opens Y)) :
    toFun J Y (op ⟨e.source, e.open_source⟩) (e.extendCoordSection he b z i) y =
      b.coord i (e.extend J y.val - z) :=
  ofContMDiff_apply _ _ y

private theorem extend_base_sub_eq_sum_of_c_app_top_algebraMap
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ E')
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c)
    (z : E') (w : ↥((Opens.map φ.base).obj ⟨e.source, e.open_source⟩)) :
    ∑ i : ι, toFun I X (op ((Opens.map φ.base).obj ⟨e.source, e.open_source⟩))
        ((φ.c.app (op ⟨e.source, e.open_source⟩)).hom (e.extendCoordSection he b z i))
        w • b i =
      e.extend J (φ.base w.val) - z := by
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans (b.sum_repr (e.extend J (φ.base w.val) - z))
  exact congrArg (· • b i)
    ((c_app_apply_of_c_app_top_algebraMap φ hφ ⟨e.source, e.open_source⟩ _ w).trans
      (e.extendCoordSection_apply he b z i ⟨φ.base w.val, w.property⟩))

include he in
/-- **Chart-independent local coordinate recovery.** In *any* holomorphic chart `e` for a model
`(J, H')`, *any* basis `b` of `E'`, and *any* translation vector `z : E'`, the base map `φ.base` of
a `ℂ`-linear morphism is given on `φ.base ⁻¹' e.source` by
`w ↦ (e.extend J).symm (z + ∑ i, tᵢ w • b i)` where `tᵢ` is the pulled-back extended-chart
linear coordinate section centered at `z`. -/
theorem base_eq_symm_sum_of_c_app_top_algebraMap
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ E')
    (φ : (locallyRingedSpace I X).toPresheafedSpace ⟶
      (locallyRingedSpace J Y).toPresheafedSpace)
    (hφ : ∀ c : ℂ, (φ.c.app (op ⊤)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map φ.base).obj ⊤))) c)
    (z : E') (w : ↥((Opens.map φ.base).obj ⟨e.source, e.open_source⟩)) :
    φ.base w.val = (e.extend J).symm (z +
      ∑ i : ι, toFun I X (op ((Opens.map φ.base).obj ⟨e.source, e.open_source⟩))
        ((φ.c.app (op ⟨e.source, e.open_source⟩)).hom (e.extendCoordSection he b z i))
        w • b i) := by
  rw [extend_base_sub_eq_sum_of_c_app_top_algebraMap e he b φ hφ z w, add_sub_cancel,
    (e.extend J).left_inv (by rw [e.extend_source]; exact w.property)]

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

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
  let e : OpenPartialHomeomorph Y H' := chartAt H' y₀
  have he : e ∈ maximalAtlas J ω Y := IsManifold.chart_mem_maximalAtlas y₀
  let U : Opens Y := ⟨e.source, e.open_source⟩
  have hy₀ : y₀ ∈ U := mem_chart_source H' y₀
  let V : Opens X := (Opens.map φ.base).obj U
  have hx₀ : x₀ ∈ V := hy₀
  rw [← contMDiffAt_subtype_iff (U := V) (x := ⟨x₀, hx₀⟩)]
  let b := Module.finBasis ℂ E'
  let t : Fin (Module.finrank ℂ E') → (holomorphicStructureSheaf I X).obj.obj (op V) := fun i ↦
    (φ.c.app (op U)).hom (e.extendCoordSection he b 0 i)
  let G : V → E' := fun w ↦ ∑ i, t i w • b i
  have hG_cm : ContMDiff I 𝓘(ℂ, E') ω G := fun w ↦ ContMDiffAt.sum fun i _ ↦
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b i)).contDiff
      (n := ω)).contMDiff.contMDiffAt.comp w (contMDiff (t i) w)
  have hGx₀ : G ⟨x₀, hx₀⟩ = extChartAt J y₀ y₀ := by
    dsimp [G, t, y₀, e, extChartAt]
    exact (e.extend_base_sub_eq_sum_of_c_app_top_algebraMap he b φ hφ 0 ⟨x₀, hx₀⟩).trans
      (sub_zero _)
  have hx₀_tgt : G ⟨x₀, hx₀⟩ ∈ (extChartAt J y₀).target := by
    rw [hGx₀]
    exact mem_extChartAt_target y₀
  refine (((contMDiffOn_extChartAt_symm (n := ω) y₀).contMDiffAt
    (extChartAt_target_mem_nhds' hx₀_tgt)).comp (⟨x₀, hx₀⟩ : V)
      (hG_cm ⟨x₀, hx₀⟩)).congr_of_eventuallyEq (Eventually.of_forall fun w ↦ ?_)
  exact (e.base_eq_symm_sum_of_c_app_top_algebraMap he b φ hφ 0 w).trans
    (congrArg (extChartAt J y₀).symm (zero_add (G w)))

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
      locallyRingedSpaceMap_eq_of_c_app_top_algebraMap φ (hφ ⊤)
        (contMDiff_base_of_c_app_top_algebraMap φ.toHom (hφ ⊤)), by
      rintro _ rfl; exact ContMDiffMap.ext fun _ ↦ rfl⟩⟩

-- Exposed so `(holomorphicMapLocalRingedEquivalence ... f).val.base` and `(.symm φ : X → Y)`
-- reduce definitionally in dependent stalk types.
variable (I X J Y) in
/-- **Equivalence between holomorphic maps and `ℂ`-linear morphisms of locally ringed spaces.**
For any complex charted space `(X, I)` and any finite-dimensional boundaryless complex manifold
`(Y, J)`, bundled complex-analytic maps `C^ω⟮I, X; J, Y⟯` correspond bijectively via
`locallyRingedSpaceMap` to `ℂ`-linear morphisms `LocallyRingedSpaceCLinearHom I X J Y`. -/
@[expose]
def holomorphicMapLocalRingedEquivalence :
    C^ω⟮I, X; J, Y⟯ ≃ LocallyRingedSpaceCLinearHom I X J Y where
  toFun f := LocallyRingedSpaceCLinearHom.ofContMDiff f f.contMDiff
  invFun φ := ⟨φ.val.base, contMDiff_base_of_c_app_top_algebraMap φ.val.toHom (φ.property ⊤)⟩
  left_inv _ := ContMDiffMap.ext fun _ ↦ rfl
  right_inv φ := Subtype.ext <|
    locallyRingedSpaceMap_eq_of_c_app_top_algebraMap φ.val (φ.property ⊤)
      (contMDiff_base_of_c_app_top_algebraMap φ.val.toHom (φ.property ⊤))

/-- In the forward direction, `holomorphicMapLocalRingedEquivalence` sends `f` to
`LocallyRingedSpaceCLinearHom.ofContMDiff f f.contMDiff`. -/
theorem holomorphicMapLocalRingedEquivalence_apply (f : C^ω⟮I, X; J, Y⟯) :
    holomorphicMapLocalRingedEquivalence I X J Y f =
      LocallyRingedSpaceCLinearHom.ofContMDiff f f.contMDiff := (rfl)

/-- In the forward direction, `holomorphicMapLocalRingedEquivalence` sends `⟨f, hf⟩` to
`LocallyRingedSpaceCLinearHom.ofContMDiff f hf`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_mk (f : X → Y) (hf : ContMDiff I J ω f) :
    holomorphicMapLocalRingedEquivalence I X J Y ⟨f, hf⟩ =
      LocallyRingedSpaceCLinearHom.ofContMDiff f hf := (rfl)

/-- In the forward direction, the underlying locally ringed-space morphism of
`holomorphicMapLocalRingedEquivalence` is `locallyRingedSpaceMap f f.contMDiff`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_apply_val (f : C^ω⟮I, X; J, Y⟯) :
    (holomorphicMapLocalRingedEquivalence I X J Y f).val =
      locallyRingedSpaceMap f f.contMDiff := (rfl)

/-- The `ℂ`-algebra stalk map of `holomorphicMapLocalRingedEquivalence I X J Y f` at `x` is
`stalkPullbackAlgHom`. -/
@[simp]
theorem stalkAlgHom_holomorphicMapLocalRingedEquivalence (f : C^ω⟮I, X; J, Y⟯) (x : X) :
    (holomorphicMapLocalRingedEquivalence I X J Y f).stalkAlgHom x =
      stalkPullbackAlgHom (Eventually.of_forall fun _ ↦ f.contMDiff.contMDiffAt) :=
  LocallyRingedSpaceCLinearHom.stalkAlgHom_ofContMDiff f f.contMDiff x

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

/-- `holomorphicMapLocalRingedEquivalence.symm` sends
`LocallyRingedSpaceCLinearHom.ofContMDiff f hf` to `⟨f, hf⟩`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_ofContMDiff (f : X → Y)
    (hf : ContMDiff I J ω f) :
    (holomorphicMapLocalRingedEquivalence I X J Y).symm
        (LocallyRingedSpaceCLinearHom.ofContMDiff f hf) = ⟨f, hf⟩ :=
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

/-- When `𝒪_{X, x}` is maximal-ideal separated (`IsHausdorff`), the inverse germ equivalence
`(analyticMapGermEquivStalkAlgHom x (φ.val.base x)).symm` applied to `φ.stalkAlgHom x` recovers
the germ at `x` of `(holomorphicMapLocalRingedEquivalence I X J Y).symm φ`. -/
theorem analyticMapGermEquivStalkAlgHom_symm_stalkAlgHom (x : X)
    [IsHausdorff (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x)] :
    (analyticMapGermEquivStalkAlgHom (I := I) (J := J) x (φ.val.base x)).symm
        (φ.stalkAlgHom x) =
      AnalyticMapGerm.mk (X := X) (Y := Y)
        ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ)
        (Eventually.of_forall fun _ ↦
          ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ).contMDiff.contMDiffAt)
        rfl :=
  analyticMapGermEquivStalkAlgHom_symm_stalkAlgHomOfCAppTopAlgebraMap
    φ.val.toHom (φ.property ⊤) x

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
under `holomorphicMapLocalRingedEquivalence` to precomposing in `LocallyRingedSpaceCLinearHom`
with `LocallyRingedSpaceCLinearHom.ofContMDiff Subtype.val contMDiff_subtypeVal`. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_restrict (f : C^ω⟮I, X; J, Y⟯) (U : Opens X) :
    holomorphicMapLocalRingedEquivalence I U J Y
        (f.comp (⟨Subtype.val, contMDiff_subtypeVal⟩ : C^ω⟮I, U; I, X⟯)) =
      (holomorphicMapLocalRingedEquivalence I X J Y f).comp
        (LocallyRingedSpaceCLinearHom.ofContMDiff Subtype.val contMDiff_subtypeVal) :=
  Subtype.ext (locallyRingedSpaceMap_comp contMDiff_subtypeVal f.contMDiff)

/-- Restricting a `ℂ`-linear morphism `φ : LocallyRingedSpaceCLinearHom I X J Y` to an open
subset `U : Opens X` corresponds under `(holomorphicMapLocalRingedEquivalence _ _ _ _).symm` to
restricting `(holomorphicMapLocalRingedEquivalence I X J Y).symm φ` to `U`. No manifold,
boundaryless, or finite-dimensionality hypotheses on `X` are required. -/
@[simp]
theorem holomorphicMapLocalRingedEquivalence_symm_restrict (U : Opens X) :
    (holomorphicMapLocalRingedEquivalence I U J Y).symm
        (φ.comp (LocallyRingedSpaceCLinearHom.ofContMDiff Subtype.val contMDiff_subtypeVal)) =
      ((holomorphicMapLocalRingedEquivalence I X J Y).symm φ).comp
        (⟨Subtype.val, contMDiff_subtypeVal⟩ : C^ω⟮I, U; I, X⟯) :=
  ContMDiffMap.ext fun _ ↦ rfl

/-- Restricting a holomorphic map `f : C^ω⟮I, X; J, Y⟯` to an open subset `U : Opens X` corresponds
on underlying locally ringed-space morphisms to precomposing with the open immersion
`(restrictLocallyRingedSpaceIso I X U).inv ≫ (locallyRingedSpace I X).ofRestrict _`. -/
theorem holomorphicMapLocalRingedEquivalence_restrict_val (f : C^ω⟮I, X; J, Y⟯) (U : Opens X) :
    (holomorphicMapLocalRingedEquivalence I U J Y
      (f.comp (⟨Subtype.val, contMDiff_subtypeVal⟩ : C^ω⟮I, U; I, X⟯))).val =
      (restrictLocallyRingedSpaceIso I X U).inv ≫
        (locallyRingedSpace I X).ofRestrict (Opens.isOpenEmbedding (X := TopCat.of X) U) ≫
        (holomorphicMapLocalRingedEquivalence I X J Y f).val := by
  rw [restrictLocallyRingedSpaceIso_inv_comp_ofRestrict_assoc,
    holomorphicMapLocalRingedEquivalence_restrict,
    LocallyRingedSpaceCLinearHom.val_comp, LocallyRingedSpaceCLinearHom.val_ofContMDiff]

end SymmAndComp

end Equivalence

end TauCeti.holomorphicStructureSheaf

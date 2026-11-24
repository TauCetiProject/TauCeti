/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.BaseChange
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.LocalScalars
import TauCeti.AlgebraicGeometry.Cohomology.Pullback.Comp
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange

/-!
# Flat base change for higher direct images

Consider a cartesian square of schemes

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

with `Y` affine, `f` quasi-compact and quasi-separated and `g` flat. This file proves that for
every quasi-coherent `𝒪_X`-module `M` and every `q`, the base change map
`TauCeti.AlgebraicGeometry.higherDirectImageBaseChange : g^* R^q f_* M ⟶ R^q f'_* g'^* M` is an
isomorphism (`TauCeti.AlgebraicGeometry.isIso_higherDirectImageBaseChange_app`). No hypothesis on
`Y'` is needed; the base `Y` is affine because the base change map is constructed over an affine
base.

A morphism of sheaves is an isomorphism once it is bijective on the sections over the members of a
basis of opens, so it suffices to show that the map is bijective on the sections over every affine
open `V` of `Y'`. Write `A = Γ(Y, ⊤)`, `B = Γ(Y', V)` and `W = f'⁻¹ V`, so
that `W ⟶ X` is the base change of `X` along `Spec B ⟶ Spec A`. On the source, the sections of
`g^* R^q f_* M` over `V` are `B ⊗_A H^q(X, M)` (`Scheme.Hom.isBaseChange_pullbackSectionsLE`).
On the target, the sections of `R^q f'_* g'^* M` over `V` are `H^q(W, g'^* M)`, which maps
injectively and `B`-linearly into the cohomology of the open subscheme `W` with coefficients in
the pullback of `M` (`Scheme.Opens.cohomologyOnPullbackι_injective` and
`Scheme.Hom.cohomologyOnPullbackι_higherDirectImageSectionsAddEquiv_symm_smul`). Composed with
this embedding, the base change map is pullback on cohomology along `W ⟶ X`
(`higherDirectImageBaseChange_app_app_pullbackSectionsLE_sectionsAddEquiv`
and `Scheme.Hom.cohomologyOnPullback_comp`), extended `B`-linearly, which is the flat base change
isomorphism `B ⊗_A H^q(X, M) ≅ H^q(W, M|_W)` of
`TauCeti.AlgebraicGeometry.bijective_cohomologyOnBaseChange`.

## Main declarations

* `TauCeti.AlgebraicGeometry.isIso_higherDirectImageBaseChange_app`: **flat base change**, the base
  change map `g^* R^q f_* M ⟶ R^q f'_* g'^* M` is an isomorphism for a cartesian square with
  affine `Y`, flat `g`, quasi-compact quasi-separated `f` and quasi-coherent `M`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3.
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules TensorProduct

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules Scheme.Hom

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Over an affine base `Y`, the preimage `f'⁻¹ V` of an affine open `V` of `Y'` is the base change
of `X` along `Spec Γ(Y', V) ⟶ Spec Γ(Y, ⊤)`. -/
private lemma isPullback_preimage_ι_comp (H : IsPullback g' f' f g) [IsAffine Y] {V : Y'.Opens}
    (hV : IsAffineOpen V) (hVg : V ≤ g ⁻¹ᵁ ⊤) :
    IsPullback ((f' ⁻¹ᵁ V).ι ≫ g') (f'.resLE V (f' ⁻¹ᵁ V) le_rfl ≫ hV.isoSpec.hom)
      (f ≫ Y.toSpecΓ) (Spec.map (g.appLE ⊤ V hVg)) := by
  have : IsIso V.toSpecΓ := inferInstanceAs (IsIso hV.isoSpec.hom)
  have hB : IsPullback (V.ι ≫ g) V.toSpecΓ Y.toSpecΓ (Spec.map (g.appLE ⊤ V hVg)) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [Category.assoc, Scheme.toSpecΓ_naturality,
      ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, ← Spec.map_comp]
    -- `g.appLE ⊤ V hVg` is by definition `g.appTop` followed by restriction to `V`.
    rfl
  have := ((isPullback_morphismRestrict f' V).flip.paste_horiz H).paste_vert hB
  rwa [← Scheme.Hom.resLE_eq_morphismRestrict] at this

/-- Through `f ≫ Y.toSpecΓ`, a function `r` on an affine `Y` acts on `X` as `f^* r`. -/
private lemma baseRingToGlobalSections_eq_appTop (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    letI : X.Over (Spec (.of Γ(Y, ⊤))) := ⟨f ≫ Y.toSpecΓ⟩
    baseRingToGlobalSections Γ(Y, ⊤) X r = f.appTop r := by
  rw [baseRingToGlobalSections_apply]
  -- The structure morphism of the local `Over` instance is `f ≫ Y.toSpecΓ` by definition.
  change (f ≫ Y.toSpecΓ).appTop ((Scheme.ΓSpecIso _).inv r) = _
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_apply]

/-- Through `f'⁻¹ V ⟶ V ≅ Spec Γ(Y', V)`, a function `a` on an affine open `V` acts on the open
subscheme `f'⁻¹ V` as `f'^* a`. -/
private lemma baseRingToGlobalSections_preimage (f' : X' ⟶ Y') {V : Y'.Opens}
    (hV : IsAffineOpen V) (a : Γ(Y', V)) :
    letI : (f' ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(Y', V))) :=
      ⟨f'.resLE V (f' ⁻¹ᵁ V) le_rfl ≫ hV.isoSpec.hom⟩
    baseRingToGlobalSections Γ(Y', V) (f' ⁻¹ᵁ V) a = (f' ⁻¹ᵁ V).topIso.inv (f'.app V a) := by
  have := congrArg (fun φ ↦ φ.hom a) (f'.ΓSpecIso_inv_comp_resLE_isoSpec_appLE hV _ le_rfl ⊤)
  rw [baseRingToGlobalSections_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  refine this.trans ?_
  rw [CommRingCat.comp_apply, Scheme.Hom.appLE_eq_app, Scheme.Opens.ι_appLE]
  -- Both sides restrict from `f'⁻¹ V` to the image of the top open of the subscheme `f'⁻¹ V`.
  rfl

/-- Over an affine base `Y`, the identification of the global sections of `R^q f_* M` with
`H^q(X, M)`, linear over `Γ(Y, ⊤)` acting on `X` through `f`. -/
private def sectionsTopLinearEquiv (f : X ⟶ Y) [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    letI : X.Over (Spec (.of Γ(Y, ⊤))) := ⟨f ≫ Y.toSpecΓ⟩
    Γ((f.higherDirectImage q).obj M, ⊤) ≃ₗ[Γ(Y, ⊤)] cohomologyOn M q (f ⁻¹ᵁ ⊤) :=
  letI : X.Over (Spec (.of Γ(Y, ⊤))) := ⟨f ≫ Y.toSpecΓ⟩
  ((f.higherDirectImageSectionsAddEquiv M q (isAffineOpen_top Y)).toLinearEquiv fun r c ↦ by
    rw [base_smul_cohomologyOn, baseRingToGlobalSections_eq_appTop,
      higherDirectImageSectionsAddEquiv_appTop_smul, show (⊤ : Y.Opens).leTop = 𝟙 _ from rfl,
      op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]).symm

/-- The sections of `R^q f'_* g'^* M` over an affine open `V` of `Y'`, read in the cohomology of the
open subscheme `f'⁻¹ V` with coefficients in the pullback of `M` along `f'⁻¹ V ⟶ X' ⟶ X`. -/
private def sectionsToCohomologyPreimage (g' : X' ⟶ X) (f' : X' ⟶ Y') [QuasiCompact f']
    [QuasiSeparated f'] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) {V : Y'.Opens}
    (hV : IsAffineOpen V) :
    Γ((f'.higherDirectImage q).obj ((pullback g').obj M), V) →+
      cohomologyOn ((pullback ((f' ⁻¹ᵁ V).ι ≫ g')).obj M) q ⊤ :=
  (cohomologyOnMap ((pullbackComp (f' ⁻¹ᵁ V).ι g').hom.app M) q ⊤).hom.comp
    (((f' ⁻¹ᵁ V).cohomologyOnPullbackι _ q).hom.comp
      (f'.higherDirectImageSectionsAddEquiv _ q hV).symm.toAddMonoidHom)

section SectionsToCohomologyPreimage

variable (g' : X' ⟶ X) (f' : X' ⟶ Y') [QuasiCompact f'] [QuasiSeparated f'] (M : X.Modules)
  [M.IsQuasicoherent] (q : ℕ) {V : Y'.Opens} (hV : IsAffineOpen V)

private lemma sectionsToCohomologyPreimage_apply
    (y : Γ((f'.higherDirectImage q).obj ((pullback g').obj M), V)) :
    sectionsToCohomologyPreimage g' f' M q hV y =
      cohomologyOnMap ((pullbackComp (f' ⁻¹ᵁ V).ι g').hom.app M) q ⊤
        ((f' ⁻¹ᵁ V).cohomologyOnPullbackι _ q
          ((f'.higherDirectImageSectionsAddEquiv _ q hV).symm y)) :=
  rfl

private lemma injective_sectionsToCohomologyPreimage :
    Function.Injective (sectionsToCohomologyPreimage g' f' M q hV) := by
  have hmap : Function.Injective
      (cohomologyOnMap ((pullbackComp (f' ⁻¹ᵁ V).ι g').hom.app M) q ⊤) := fun a b hab ↦ by
    simpa only [← ConcreteCategory.comp_apply, ← cohomologyOnMap_comp, Iso.hom_inv_id_app,
      cohomologyOnMap_id, ConcreteCategory.id_apply] using
      congrArg (cohomologyOnMap ((pullbackComp (f' ⁻¹ᵁ V).ι g').inv.app M) q ⊤) hab
  exact fun y₁ y₂ hy ↦ (f'.higherDirectImageSectionsAddEquiv _ q hV).symm.injective
    ((f' ⁻¹ᵁ V).cohomologyOnPullbackι_injective _ q (hmap hy))

/-- `sectionsToCohomologyPreimage` is linear over `Γ(Y', V)`, acting on the cohomology of `f'⁻¹ V`
through `f'⁻¹ V ⟶ V ≅ Spec Γ(Y', V)`. -/
private lemma sectionsToCohomologyPreimage_smul (a : Γ(Y', V))
    (y : Γ((f'.higherDirectImage q).obj ((pullback g').obj M), V)) :
    letI : (f' ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(Y', V))) :=
      ⟨f'.resLE V (f' ⁻¹ᵁ V) le_rfl ≫ hV.isoSpec.hom⟩
    sectionsToCohomologyPreimage g' f' M q hV (a • y) =
      a • sectionsToCohomologyPreimage g' f' M q hV y := by
  rw [sectionsToCohomologyPreimage_apply,
    cohomologyOnPullbackι_higherDirectImageSectionsAddEquiv_symm_smul,
    ← cohomologyOnMapLinear_apply, LinearMap.map_smul, cohomologyOnMapLinear_apply,
    ← baseRingToGlobalSections_preimage f' hV a]
  rfl

/-- On an affine open `V` of `Y'` and for a class `c ∈ H^q(X, M)`, `sectionsToCohomologyPreimage`
sends the image under the base change map of the pullback of the section defined by `c` to the
pullback of `c` along `f'⁻¹ V ⟶ X' ⟶ X`. -/
private lemma sectionsToCohomologyPreimage_higherDirectImageBaseChange_app_app
    (h : g' ≫ f = f' ≫ g) [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]
    (hVg : V ≤ g ⁻¹ᵁ ⊤) (c : cohomologyOn M q (f ⁻¹ᵁ ⊤)) :
    sectionsToCohomologyPreimage g' f' M q hV
        (((higherDirectImageBaseChange h q).app M).app V (g.pullbackSectionsLE _ ⊤ V hVg
          (f.higherDirectImageSectionsAddEquiv M q (isAffineOpen_top Y) c))) =
      ((f' ⁻¹ᵁ V).ι ≫ g').cohomologyOnPullback M q (f ⁻¹ᵁ ⊤) c := by
  rw [sectionsToCohomologyPreimage_apply,
    higherDirectImageBaseChange_app_app_pullbackSectionsLE_sectionsAddEquiv h q M
      (isAffineOpen_top Y) hV hVg, AddEquiv.symm_apply_apply,
    Scheme.Opens.cohomologyOnPullbackι_apply, cohomologyOnPullback_comp]
  have e := ConcreteCategory.congr_hom (cohomologyOnRes_comp_cohomologyOnPullback (f' ⁻¹ᵁ V).ι
    ((pullback g').obj M) q ((f'.preimage_mono hVg).trans (preimage_preimage_eq_of_comp_eq h ⊤).le))
    (g'.cohomologyOnPullback M q (f ⁻¹ᵁ ⊤) c)
  simp only [ConcreteCategory.comp_apply] at e ⊢
  rw [e, cohomologyOnRes_comp_apply]
  -- The remaining restriction is from `(f'⁻¹ V).ι⁻¹ g'⁻¹ f⁻¹ ⊤` to `⊤`, the same open.
  exact congrArg (ConcreteCategory.hom (cohomologyOnMap _ q ⊤))
    (ConcreteCategory.congr_hom (cohomologyOnRes_refl _ q ⊤) _)

end SectionsToCohomologyPreimage

section FlatBaseChange

variable (H : IsPullback g' f' f g) (q : ℕ) [IsAffine Y] [Flat g] [QuasiCompact f]
  [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent]

/-- On every affine open of `Y'`, the flat base change map is bijective on sections. -/
private theorem bijective_higherDirectImageBaseChange_app_app {V : Y'.Opens}
    (hV : IsAffineOpen V) :
    Function.Bijective (((higherDirectImageBaseChange H.w q).app M).app V) := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback H inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback H inferInstance
  have hY : IsAffineOpen (⊤ : Y.Opens) := isAffineOpen_top Y
  have hVg : V ≤ g ⁻¹ᵁ ⊤ := le_top.trans (Scheme.Hom.preimage_top g).ge
  let W := f' ⁻¹ᵁ V
  let N := (f.higherDirectImage q).obj M
  let φ := (higherDirectImageBaseChange H.w q).app M
  -- `W ⟶ X` is the base change of `X` along the flat `Spec Γ(Y', V) ⟶ Spec Γ(Y, ⊤)`.
  let : Algebra Γ(Y, ⊤) Γ(Y', V) := (g.appLE ⊤ V hVg).hom.toAlgebra
  have : Module.Flat Γ(Y, ⊤) Γ(Y', V) := HasRingHomProperty.appLE @Flat g ‹_› ⟨⊤, hY⟩ ⟨V, hV⟩ hVg
  let : X.Over (Spec (.of Γ(Y, ⊤))) := ⟨f ≫ Y.toSpecΓ⟩
  let : W.toScheme.Over (Spec (.of Γ(Y', V))) := ⟨f'.resLE V W le_rfl ≫ hV.isoSpec.hom⟩
  have H₀ : IsPullback (W.ι ≫ g') (W.toScheme ↘ Spec (.of Γ(Y', V))) (X ↘ Spec (.of Γ(Y, ⊤)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(Y', V)))) :=
    isPullback_preimage_ι_comp H hV hVg
  -- The source: sections of `g^* N` over `V` are `Γ(Y', V) ⊗ Γ(Y, N)`, and `Γ(Y, N) = H^q(X, M)`.
  let : Module Γ(Y, ⊤) Γ((pullback g).obj N, V) := Module.compHom _ (algebraMap Γ(Y, ⊤) Γ(Y', V))
  have : IsScalarTower Γ(Y, ⊤) Γ(Y', V) Γ((pullback g).obj N, V) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let ψ₀ : Γ(N, ⊤) →ₗ[Γ(Y, ⊤)] Γ((pullback g).obj N, V) :=
    { toFun := g.pullbackSectionsLE N ⊤ V hVg
      map_add' := map_add _
      map_smul' := (g.pullbackSectionsLE N ⊤ V hVg).map_smulₛₗ }
  have hψ₀ : IsBaseChange Γ(Y', V) ψ₀ :=
    g.isBaseChange_pullbackSectionsLE N hY hV hVg (fun _ ↦ rfl) ψ₀ (fun _ ↦ rfl)
  let φV : Γ((pullback g).obj N, V) →ₗ[Γ(Y', V)]
      Γ((f'.higherDirectImage q).obj ((pullback g').obj M), V) :=
    { toFun := φ.app V, map_add' := map_add _, map_smul' := φ.app_smul }
  let e := sectionsTopLinearEquiv f M q
  -- The target: sections of `R^q f'_* g'^* M` over `V` embed `Γ(Y', V)`-linearly into the
  -- cohomology of the open subscheme `W` with coefficients in the pullback of `M` along `W ⟶ X`.
  let κ := sectionsToCohomologyPreimage g' f' M q hV
  -- Read through these, the base change map is the flat base change map on cohomology.
  have hcomm (z) : κ (φV (hψ₀.equiv z)) = cohomologyOnBaseChange H₀ M q (f ⁻¹ᵁ ⊤)
      (LinearEquiv.baseChange Γ(Y, ⊤) Γ(Y', V) _ _ e z) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]
      -- the two sides add in `H^q` of `⊤` and of its preimage `(W.ι ≫ g')⁻¹ f⁻¹ ⊤`, the same open
      rfl
    | tmul a s =>
      rw [IsBaseChange.equiv_tmul, LinearMap.map_smul, sectionsToCohomologyPreimage_smul,
        LinearEquiv.baseChange_tmul, cohomologyOnBaseChange_tmul]
      refine congrArg (a • ·) (Eq.trans ?_
        (sectionsToCohomologyPreimage_higherDirectImageBaseChange_app_app g' f' M q hV H.w hVg
          (e s)))
      rw [show f.higherDirectImageSectionsAddEquiv M q hY (e s) = s from
        AddEquiv.apply_symm_apply _ s]
      -- `φV` and `ψ₀` are `φ.app V` and `g.pullbackSectionsLE` as linear maps
      rfl
  have hb : Function.Bijective (κ ∘ φV ∘ hψ₀.equiv) := by
    rw [show κ ∘ φV ∘ hψ₀.equiv = cohomologyOnBaseChange H₀ M q (f ⁻¹ᵁ ⊤) ∘
      LinearEquiv.baseChange Γ(Y, ⊤) Γ(Y', V) _ _ e from funext hcomm]
    exact (bijective_cohomologyOnBaseChange H₀ M (f.isCompact_preimage hY.isCompact)
      (f.isQuasiSeparated_preimage hY.isQuasiSeparated) q).comp (LinearEquiv.bijective _)
  have hL : Function.Bijective (φV ∘ hψ₀.equiv) :=
    ⟨hb.1.of_comp, fun y ↦ (hb.2 (κ y)).imp fun _ hz ↦
      injective_sectionsToCohomologyPreimage g' f' M q hV hz⟩
  exact (Function.Bijective.of_comp_iff φV hψ₀.equiv.bijective).mp hL

/-- **Flat base change for higher direct images.** Let `g' ≫ f = f' ≫ g` be a cartesian square of
schemes with `Y` affine, `g : Y' ⟶ Y` flat and `f : X ⟶ Y` quasi-compact and quasi-separated. For
every quasi-coherent `𝒪_X`-module `M` and every `q`, the base change map
`g^* R^q f_* M ⟶ R^q f'_* g'^* M` is an isomorphism. -/
theorem isIso_higherDirectImageBaseChange_app :
    IsIso ((higherDirectImageBaseChange H.w q).app M) :=
  Scheme.Modules.Hom.isIso_of_isBasis _ (B := fun V : Y'.affineOpens ↦ (V : Y'.Opens))
    (by rw [Subtype.range_coe]; exact Y'.isBasis_affineOpens) fun V ↦
      (ConcreteCategory.isIso_iff_bijective _).2
        (bijective_higherDirectImageBaseChange_app_app H q M V.property)

end FlatBaseChange

end TauCeti.AlgebraicGeometry

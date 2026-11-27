/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.BaseChange
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
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
isomorphism (`CategoryTheory.IsPullback.isIso_higherDirectImageBaseChange_app`). No hypothesis on
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
isomorphism `B ⊗_A H^q(X, M) ≅ H^q(W, p^* M)`, where `p : W ↪ X' ⟶ X`, of
`TauCeti.AlgebraicGeometry.bijective_cohomologyOnBaseChange`.

## Main declarations

* `CategoryTheory.IsPullback.isIso_higherDirectImageBaseChange_app`: **flat base change**, the base
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
      (cohomologyOnMap ((pullbackComp (f' ⁻¹ᵁ V).ι g').hom.app M) q ⊤) :=
    (ConcreteCategory.bijective_of_isIso
      ((cohomologyOnFunctor _ q ⊤).mapIso ((pullbackComp (f' ⁻¹ᵁ V).ι g').app M)).hom).injective
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
  rw [sectionsToCohomologyPreimage_apply, sectionsToCohomologyPreimage_apply,
    base_smul_cohomologyOn, baseRingToGlobalSections_preimage,
    cohomologyOnPullbackι_higherDirectImageSectionsAddEquiv_symm_smul,
    ← cohomologyOnMapLinear_apply, LinearMap.map_smul, cohomologyOnMapLinear_apply]

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
    H.isPullback_preimage_ι_comp hV hVg
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
  let e₀ : cohomologyOn M q (f ⁻¹ᵁ ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(N, ⊤) :=
    (f.higherDirectImageSectionsAddEquiv M q hY).toLinearEquiv fun r c ↦ by
      rw [base_smul_cohomologyOn, baseRingToGlobalSections_eq_appTop,
        higherDirectImageSectionsAddEquiv_appTop_smul, TopologicalSpace.Opens.leTop, homOfLE_refl,
        op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  let e := e₀.symm
  -- The local linear bundle retains the additive section map; use its own cancellation law.
  have he (s : Γ(N, ⊤)) : f.higherDirectImageSectionsAddEquiv M q hY (e s) = s :=
    e₀.apply_symm_apply s
  -- The target: sections of `R^q f'_* g'^* M` over `V` embed `Γ(Y', V)`-linearly into the
  -- cohomology of the open subscheme `W` with coefficients in the pullback of `M` along `W ⟶ X`.
  -- Both target opens are top; align the indexed module structures in the linearity laws.
  let κ : Γ((f'.higherDirectImage q).obj ((pullback g').obj M), V) →ₗ[Γ(Y', V)]
      cohomologyOn ((pullback (W.ι ≫ g')).obj M) q ((W.ι ≫ g') ⁻¹ᵁ (f ⁻¹ᵁ ⊤)) :=
    { toFun := sectionsToCohomologyPreimage g' f' M q hV
      map_add' := by
        intro x y
        convert! (sectionsToCohomologyPreimage g' f' M q hV).map_add x y using 1
      map_smul' := by
        intro a y
        convert! sectionsToCohomologyPreimage_smul g' f' M q hV a y using 1 }
  let : Module Γ(Y, ⊤)
      (cohomologyOn ((pullback (W.ι ≫ g')).obj M) q ((W.ι ≫ g') ⁻¹ᵁ (f ⁻¹ᵁ ⊤))) :=
    Module.compHom _ (algebraMap Γ(Y, ⊤) Γ(Y', V))
  have : IsScalarTower Γ(Y, ⊤) Γ(Y', V)
      (cohomologyOn ((pullback (W.ι ≫ g')).obj M) q ((W.ι ≫ g') ⁻¹ᵁ (f ⁻¹ᵁ ⊤))) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  -- Read through these, the base change map is the flat base change map on cohomology.
  have hcomm : κ.comp (φV.comp hψ₀.equiv.toLinearMap) =
      (cohomologyOnBaseChange H₀ M q (f ⁻¹ᵁ ⊤)).comp
        (LinearEquiv.baseChange Γ(Y, ⊤) Γ(Y', V) _ _ e).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a s
    -- Evaluate the bundled composites to use the pure-tensor computation rules.
    change κ (φV (hψ₀.equiv (a ⊗ₜ s))) =
      cohomologyOnBaseChange H₀ M q (f ⁻¹ᵁ ⊤)
        (LinearEquiv.baseChange Γ(Y, ⊤) Γ(Y', V) _ _ e (a ⊗ₜ s))
    rw [IsBaseChange.equiv_tmul, LinearMap.map_smul, LinearMap.map_smul,
      LinearEquiv.baseChange_tmul, cohomologyOnBaseChange_tmul]
    refine congrArg (a • ·) (Eq.trans ?_
      (sectionsToCohomologyPreimage_higherDirectImageBaseChange_app_app g' f' M q hV H.w hVg
        (e s)))
    rw [he]
    -- `κ`, `φV` and `ψ₀` bundle the section maps occurring in the comparison lemma.
    rfl
  have hcomp : κ ∘ φV ∘ hψ₀.equiv = cohomologyOnBaseChange H₀ M q (f ⁻¹ᵁ ⊤) ∘
      LinearEquiv.baseChange Γ(Y, ⊤) Γ(Y', V) _ _ e := funext (DFunLike.congr_fun hcomm)
  have hb : Function.Bijective (κ ∘ φV ∘ hψ₀.equiv) := by
    rw [hcomp]
    exact (bijective_cohomologyOnBaseChange H₀ M (f.isCompact_preimage hY.isCompact)
      (f.isQuasiSeparated_preimage hY.isQuasiSeparated) q).comp (LinearEquiv.bijective _)
  have hL : Function.Bijective (φV ∘ hψ₀.equiv) :=
    hb.of_comp_left (injective_sectionsToCohomologyPreimage g' f' M q hV)
  exact (Function.Bijective.of_comp_iff φV hψ₀.equiv.bijective).mp hL

/-- **Flat base change for higher direct images.** Let `g' ≫ f = f' ≫ g` be a cartesian square of
schemes with `Y` affine, `g : Y' ⟶ Y` flat and `f : X ⟶ Y` quasi-compact and quasi-separated. For
every quasi-coherent `𝒪_X`-module `M` and every `q`, the base change map
`g^* R^q f_* M ⟶ R^q f'_* g'^* M` is an isomorphism. -/
theorem _root_.CategoryTheory.IsPullback.isIso_higherDirectImageBaseChange_app :
    IsIso ((higherDirectImageBaseChange H.w q).app M) :=
  Scheme.Modules.Hom.isIso_of_isBasis _ (B := fun V : Y'.affineOpens ↦ (V : Y'.Opens))
    (by rw [Subtype.range_coe]; exact Y'.isBasis_affineOpens) fun V ↦
      (ConcreteCategory.isIso_iff_bijective _).2
        (bijective_higherDirectImageBaseChange_app_app H q M V.property)

end FlatBaseChange

end TauCeti.AlgebraicGeometry

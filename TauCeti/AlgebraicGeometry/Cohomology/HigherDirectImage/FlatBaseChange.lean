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

with `f` quasi-compact and quasi-separated and `g` flat. This file proves that for every
quasi-coherent `𝒪_X`-module `M` and every `q`, the base change map
`TauCeti.AlgebraicGeometry.higherDirectImageBaseChange : g^* R^q f_* M ⟶ R^q f'_* g'^* M` is an
isomorphism (`CategoryTheory.IsPullback.isIso_higherDirectImageBaseChange_app`). No hypothesis on
`Y` or `Y'` is needed.

A morphism of sheaves is an isomorphism once it is bijective on the sections over the members of a
basis of opens. The affine opens `V` of `Y'` whose image lies in an affine open `U` of `Y` form a
basis, so it suffices to show that the map is bijective on the sections over such a `V`. Write
`A = Γ(Y, U)`, `B = Γ(Y', V)`, and `X_U = f⁻¹ U` and `W = f'⁻¹ V` for the open subschemes, so that
`W ⟶ X_U`, the restriction of `g'`, is the base change of `X_U` along the flat
`Spec B ⟶ Spec A`. On the source, the sections of `g^* R^q f_* M` over `V` are
`B ⊗_A Γ(U, R^q f_* M)` (`Scheme.Hom.isBaseChange_pullbackSectionsLE`), and
`Γ(U, R^q f_* M) = H^q(f⁻¹ U, M) = H^q(X_U, M|_{X_U})`, `A`-linearly
(`Scheme.Hom.higherDirectImageSectionsAddEquiv`, `Scheme.Opens.cohomologyOnPullbackι` and
`Scheme.Hom.cohomologyOnPullbackι_higherDirectImageSectionsAddEquiv_symm_smul`). On the target,
the sections of `R^q f'_* g'^* M` over `V` are `H^q(W, g'^* M)`, which maps injectively and
`B`-linearly into the cohomology of the open subscheme `W` with coefficients in the restriction of
`g'^* M`. Composed with this embedding, the base change map is pullback on cohomology along
`W ⟶ X_U` (`higherDirectImageBaseChange_app_app_pullbackSectionsLE_sectionsAddEquiv` and
`Scheme.Hom.cohomologyOnPullback_cohomologyOnRes_cohomologyOnPullback_ι`), extended `B`-linearly,
which is the flat base change isomorphism `B ⊗_A H^q(X_U, M|_{X_U}) ≅ H^q(W, M|_W)` of
`TauCeti.AlgebraicGeometry.bijective_cohomologyOnBaseChange`.

## Main declarations

* `CategoryTheory.IsPullback.isIso_higherDirectImageBaseChange_app`: **flat base change**, the base
  change map `g^* R^q f_* M ⟶ R^q f'_* g'^* M` is an isomorphism for a cartesian square with
  flat `g`, quasi-compact quasi-separated `f` and quasi-coherent `M`.

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

section Transport

variable (g : X' ⟶ X) (M : X.Modules) (q : ℕ) {U : X.Opens} {U' : X'.Opens} (hle : U' ≤ g ⁻¹ᵁ U)

/-- The identification of the cohomology of the open subscheme `U'` with coefficients in
`(g.resLE U U' hle)^* (M|_U)` with that with coefficients in `(g^* M)|_{U'}`, along the
isomorphism of coefficients induced by `g.resLE U U' hle ≫ U.ι = U'.ι ≫ g`. -/
private def cohomologyResLETransport :
    cohomologyOn ((pullback (g.resLE U U' hle)).obj ((pullback U.ι).obj M)) q
        ((g.resLE U U' hle) ⁻¹ᵁ ⊤) →+
      cohomologyOn ((pullback U'.ι).obj ((pullback g).obj M)) q ⊤ :=
  (cohomologyOnRes _ q (g.resLE U U' hle).preimage_top.ge).hom.comp
    (cohomologyOnMap ((pullbackComp (g.resLE U U' hle) U.ι).hom.app M ≫
      (pullbackCongr (g.resLE_comp_ι hle)).hom.app M ≫ (pullbackComp U'.ι g).inv.app M) q
        ((g.resLE U U' hle) ⁻¹ᵁ ⊤)).hom

/-- `cohomologyResLETransport` is bijective: it is induced by an isomorphism of coefficients and
the restriction between the equal opens `(g.resLE U U' hle)⁻¹ ⊤ = ⊤`. -/
private lemma bijective_cohomologyResLETransport :
    Function.Bijective (cohomologyResLETransport g M q hle) := by
  have : IsIso (cohomologyOnRes ((pullback U'.ι).obj ((pullback g).obj M)) q
      (g.resLE U U' hle).preimage_top.ge) :=
    ⟨cohomologyOnRes _ q le_top, by rw [cohomologyOnRes_comp, cohomologyOnRes_refl],
      by rw [cohomologyOnRes_comp, cohomologyOnRes_refl]⟩
  rw [cohomologyResLETransport, AddMonoidHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).comp (ConcreteCategory.bijective_of_isIso
    ((cohomologyOnFunctor _ q _).mapIso ((pullbackComp (g.resLE U U' hle) U.ι).app M ≪≫
      (pullbackCongr (g.resLE_comp_ι hle)).app M ≪≫ ((pullbackComp U'.ι g).app M).symm)).hom)

/-- `cohomologyResLETransport` is linear over the base ring of `U'`. -/
private lemma cohomologyResLETransport_smul {R : Type u} [CommRing R]
    [U'.toScheme.Over (Spec (.of R))] (r : R)
    (z : cohomologyOn ((pullback (g.resLE U U' hle)).obj ((pullback U.ι).obj M)) q
      ((g.resLE U U' hle) ⁻¹ᵁ ⊤)) :
    cohomologyResLETransport g M q hle (r • z) = r • cohomologyResLETransport g M q hle z := by
  rw [base_smul_cohomologyOn, base_smul_cohomologyOn, cohomologyResLETransport,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    ← cohomologyOnMapLinear_apply, LinearMap.map_smul, cohomologyOnMapLinear_apply,
    ← cohomologyOnResLinear_apply, LinearMap.map_smul, cohomologyOnResLinear_apply]

/-- Pulling back a class on `U` along `g`, restricting to `U'` and passing to the open subscheme
`U'` is passing to the open subscheme `U`, pulling back along `g.resLE U U' hle` and transporting
the coefficients. -/
private lemma cohomologyOnPullbackι_cohomologyOnRes_cohomologyOnPullback
    (c : cohomologyOn M q U) :
    U'.cohomologyOnPullbackι _ q (cohomologyOnRes _ q hle (g.cohomologyOnPullback M q U c)) =
      cohomologyResLETransport g M q hle
        ((g.resLE U U' hle).cohomologyOnPullback _ q ⊤ (U.cohomologyOnPullbackι M q c)) := by
  have hsq := ConcreteCategory.congr_hom
    (g.cohomologyOnPullback_cohomologyOnRes_cohomologyOnPullback_ι M q U U' hle) c
  simp only [ConcreteCategory.comp_apply, ← Scheme.Opens.cohomologyOnPullbackι_apply] at hsq
  exact hsq

end Transport

section SectionsEquiv

variable (q : ℕ) {Z S : Scheme.{u}} (k : Z ⟶ S) [QuasiCompact k] [QuasiSeparated k] (N : Z.Modules)
  [N.IsQuasicoherent] {V : S.Opens} (hV : IsAffineOpen V)

/-- The sections of `R^q k_* N` over an affine open `V` of the base, read `Γ(S, V)`-linearly in the
cohomology of the open subscheme `k⁻¹ V` with coefficients in the restriction of `N`, on which
`Γ(S, V)` acts through `k⁻¹ V ⟶ V ≅ Spec Γ(S, V)`. -/
private def sectionsLinearEquivCohomologyPreimage :
    letI : (k ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(S, V))) :=
      ⟨k.resLE V (k ⁻¹ᵁ V) le_rfl ≫ hV.isoSpec.hom⟩
    Γ((k.higherDirectImage q).obj N, V) ≃ₗ[Γ(S, V)]
      cohomologyOn ((pullback (k ⁻¹ᵁ V).ι).obj N) q ⊤ :=
  letI : (k ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(S, V))) :=
    ⟨k.resLE V (k ⁻¹ᵁ V) le_rfl ≫ hV.isoSpec.hom⟩
  ((k.higherDirectImageSectionsAddEquiv N q hV).symm.trans
    (AddEquiv.ofBijective ((k ⁻¹ᵁ V).cohomologyOnPullbackι N q).hom
      ((k ⁻¹ᵁ V).cohomologyOnPullbackι_bijective N q))).toLinearEquiv fun a y ↦ by
    -- Unfold the composite of additive equivalences to its two component maps.
    change (k ⁻¹ᵁ V).cohomologyOnPullbackι N q _ = a • (k ⁻¹ᵁ V).cohomologyOnPullbackι N q _
    rw [base_smul_cohomologyOn, baseRingToGlobalSections_preimage]
    exact cohomologyOnPullbackι_higherDirectImageSectionsAddEquiv_symm_smul k N q hV a y

private lemma sectionsLinearEquivCohomologyPreimage_apply (c : cohomologyOn N q (k ⁻¹ᵁ V)) :
    sectionsLinearEquivCohomologyPreimage q k N hV (k.higherDirectImageSectionsAddEquiv N q hV c) =
      (k ⁻¹ᵁ V).cohomologyOnPullbackι N q c :=
  congrArg _ (AddEquiv.symm_apply_apply _ c)

end SectionsEquiv

section FlatBaseChange

variable (H : IsPullback g' f' f g) (q : ℕ) [Flat g] [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent]

omit [Flat g] in
/-- For affine opens `U` of `Y` and `V ≤ g⁻¹ U` of `Y'` and a class `c ∈ H^q(f⁻¹ U, M)`,
`sectionsLinearEquivCohomologyPreimage` sends the image under the base change map of the pullback
of the section defined by `c` to the pullback of `c` along `f'⁻¹ V ⟶ f⁻¹ U`, read in the
cohomology of the open subschemes. -/
private lemma sectionsLinearEquivCohomologyPreimage_higherDirectImageBaseChange_app_app
    (h : g' ≫ f = f' ≫ g) [QuasiCompact f'] [QuasiSeparated f'] {U : Y.Opens}
    (hU : IsAffineOpen U) {V : Y'.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
    (hle : f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ f ⁻¹ᵁ U) (c : cohomologyOn M q (f ⁻¹ᵁ U)) :
    sectionsLinearEquivCohomologyPreimage q f' _ hV (((higherDirectImageBaseChange h q).app M).app
        V (g.pullbackSectionsLE _ U V hVU (f.higherDirectImageSectionsAddEquiv M q hU c))) =
      cohomologyResLETransport g' M q hle ((g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hle).cohomologyOnPullback
        _ q ⊤ ((f ⁻¹ᵁ U).cohomologyOnPullbackι M q c)) := by
  rw [← cohomologyOnPullbackι_cohomologyOnRes_cohomologyOnPullback,
    higherDirectImageBaseChange_app_app_pullbackSectionsLE_sectionsAddEquiv h q M hU hV hVU]
  exact sectionsLinearEquivCohomologyPreimage_apply q f' _ hV _

/-- On every affine open `V` of `Y'` lying over an affine open `U` of `Y`, the flat base change map
is bijective on sections. -/
private theorem bijective_higherDirectImageBaseChange_app_app {U : Y.Opens} (hU : IsAffineOpen U)
    {V : Y'.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U) :
    Function.Bijective (((higherDirectImageBaseChange H.w q).app M).app V) := by
  -- Outline: identify the source with `Γ(Y', V) ⊗ H^q(f⁻¹ U, M)` and embed the target in the
  -- cohomology of `f'⁻¹ V`; the composite is the flat base change map of the open subscheme
  -- `f⁻¹ U` over `Spec Γ(Y, U)` (`hcomm`), which is bijective.
  have : QuasiCompact f' := MorphismProperty.of_isPullback H inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback H inferInstance
  have hle : f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ f ⁻¹ᵁ U :=
    (f'.preimage_mono hVU).trans (preimage_preimage_eq_of_comp_eq H.w U).le
  let N := (f.higherDirectImage q).obj M
  let φ := (higherDirectImageBaseChange H.w q).app M
  -- `f'⁻¹ V ⟶ f⁻¹ U` is the base change of `f⁻¹ U` along the flat `Spec Γ(Y', V) ⟶ Spec Γ(Y, U)`.
  let : Algebra Γ(Y, U) Γ(Y', V) := (g.appLE U V hVU).hom.toAlgebra
  have : Module.Flat Γ(Y, U) Γ(Y', V) := HasRingHomProperty.appLE @Flat g ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  let : (f ⁻¹ᵁ U).toScheme.Over (Spec (.of Γ(Y, U))) :=
    ⟨f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ hU.isoSpec.hom⟩
  let : (f' ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(Y', V))) :=
    ⟨f'.resLE V (f' ⁻¹ᵁ V) le_rfl ≫ hV.isoSpec.hom⟩
  have H₀ : IsPullback (g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hle)
      ((f' ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(Y', V))) ((f ⁻¹ᵁ U).toScheme ↘ Spec (.of Γ(Y, U)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) Γ(Y', V)))) :=
    H.isPullback_resLE_preimage hU hV hVU hle
  have : CompactSpace (f ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.1 (f.isCompact_preimage hU.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ U) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ U).isOpen).1
      (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  -- The source: sections of `g^* N` over `V` are `Γ(Y', V) ⊗ Γ(U, N)`.
  let : Module Γ(Y, U) Γ((pullback g).obj N, V) := Module.compHom _ (algebraMap Γ(Y, U) Γ(Y', V))
  have : IsScalarTower Γ(Y, U) Γ(Y', V) Γ((pullback g).obj N, V) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let ψ₀ : Γ(N, U) →ₗ[Γ(Y, U)] Γ((pullback g).obj N, V) :=
    { toFun := g.pullbackSectionsLE N U V hVU
      map_add' := map_add _
      map_smul' := (g.pullbackSectionsLE N U V hVU).map_smulₛₗ }
  have hψ₀ : IsBaseChange Γ(Y', V) ψ₀ :=
    g.isBaseChange_pullbackSectionsLE N hU hV hVU (fun _ ↦ rfl) ψ₀ (fun _ ↦ rfl)
  let φV : Γ((pullback g).obj N, V) →ₗ[Γ(Y', V)]
      Γ((f'.higherDirectImage q).obj ((pullback g').obj M), V) :=
    { toFun := φ.app V, map_add' := map_add _, map_smul' := φ.app_smul }
  -- Sections of higher direct images over `U` and `V` are cohomology of the open subschemes.
  let e := sectionsLinearEquivCohomologyPreimage q f M hU
  let κ := sectionsLinearEquivCohomologyPreimage q f' ((pullback g').obj M) hV
  -- Through `e` and `κ`, the base change map is the flat base change map on the cohomology of
  -- `f⁻¹ U`, up to the bijective `Γ(Y', V)`-linear transport of coefficients.
  have hcomm (z : Γ(Y', V) ⊗[Γ(Y, U)] Γ(N, U)) :
      κ (φV (hψ₀.equiv z)) =
        cohomologyResLETransport g' M q hle (cohomologyOnBaseChange H₀ _ q ⊤
          (LinearEquiv.baseChange Γ(Y, U) Γ(Y', V) _ _ e z)) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul a s =>
      obtain ⟨c, rfl⟩ := (f.higherDirectImageSectionsAddEquiv M q hU).surjective s
      rw [IsBaseChange.equiv_tmul, LinearMap.map_smul, LinearEquiv.map_smul,
        LinearEquiv.baseChange_tmul, cohomologyOnBaseChange_tmul, cohomologyResLETransport_smul,
        sectionsLinearEquivCohomologyPreimage_apply]
      exact congrArg (a • ·)
        (sectionsLinearEquivCohomologyPreimage_higherDirectImageBaseChange_app_app q M H.w hU hV hVU
          hle c)
  have hb : Function.Bijective (κ ∘ φV ∘ hψ₀.equiv) := by
    rw [show κ ∘ φV ∘ hψ₀.equiv =
      cohomologyResLETransport g' M q hle ∘ cohomologyOnBaseChange H₀ _ q ⊤ ∘
        LinearEquiv.baseChange Γ(Y, U) Γ(Y', V) _ _ e from funext hcomm]
    exact (bijective_cohomologyResLETransport g' M q hle).comp
      ((bijective_cohomologyOnBaseChange H₀ _ isCompact_univ isQuasiSeparated_univ q).comp
        (LinearEquiv.bijective _))
  exact (Function.Bijective.of_comp_iff φV hψ₀.equiv.bijective).mp
    (hb.of_comp_left κ.injective)

/-- **Flat base change for higher direct images.** Let `g' ≫ f = f' ≫ g` be a cartesian square of
schemes with `g : Y' ⟶ Y` flat and `f : X ⟶ Y` quasi-compact and quasi-separated. For every
quasi-coherent `𝒪_X`-module `M` and every `q`, the base change map
`g^* R^q f_* M ⟶ R^q f'_* g'^* M` is an isomorphism. -/
theorem _root_.CategoryTheory.IsPullback.isIso_higherDirectImageBaseChange_app :
    IsIso ((higherDirectImageBaseChange H.w q).app M) :=
  Scheme.Modules.Hom.isIso_of_isBasis _ g.isBasis_range_affineOpens_le_preimage fun V ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_higherDirectImageBaseChange_app_app H q M
      V.val.2.property V.val.1.property V.property)

end FlatBaseChange

end TauCeti.AlgebraicGeometry

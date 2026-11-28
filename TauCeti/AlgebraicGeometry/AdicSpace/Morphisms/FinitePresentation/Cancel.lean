/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Chart

import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel

/-!
# Cancellation and open restriction for morphisms locally of finite presentation

This file proves right-cancellation (`LocallyOfFinitePresentation.of_comp`, Huber 1996,
Proposition 1.6.7(iii); Stacks Project, Tag 02FV) and open restriction
(`LocallyOfFinitePresentation.restrict`) for morphisms of adic spaces locally of finite
presentation.

Unlike `LocallyOfFiniteType.of_comp` (which requires no hypothesis on `g`), cancelling
`LocallyOfFinitePresentation` from `f ≫ g` requires `g : Y ⟶ Z` to be locally of finite type:
that hypothesis allows target charts on `Z` to be refined over `Y` via Huber-pair morphisms
topologically of finite type, which simultaneously ascends `IsHuberStandard` from `Z` to `Y` and
supplies the ring-homomorphism finite-type condition needed for discrete right-cancellation
(`TauCeti.Huber.IsTopologicallyFiniteType.finitePresentation_of_comp`). Similarly, open restriction
along a commuting square `g ≫ iV = iU ≫ f` assumes open immersions on both the source (`iU`) and
the target (`iV`), using `LocallyOfFiniteType.of_isOpenImmersion iV` to cancel `iV`.

## Main results

* `TauCeti.AdicSpace.LocallyOfFinitePresentation.of_comp`: if `f ≫ g` is locally of finite
  presentation and `g` is locally of finite type, then `f` is locally of finite presentation.
* `TauCeti.AdicSpace.LocallyOfFinitePresentation.restrict`: if `g ≫ iV = iU ≫ f` with `iU` and
  `iV` open immersions and `f` locally of finite presentation, then `g` is locally of finite
  presentation.
* `TauCeti.AdicSpace.locallyOfFinitePresentation_iff_of_iSup_eq_top_source`: open-cover descent on
  the source for `LocallyOfFinitePresentation`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), Proposition 1.6.7(iii).
* [The Stacks Project, Tag 02FV][stacks-project].
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum CompleteAffinoidOpen

universe u

variable {X Y Z : AdicSpace.{u}}

/-- **Right-cancellation of `LocallyOfFinitePresentation` along `LocallyOfFiniteType`**
(Huber 1996, Proposition 1.6.7(iii); Stacks Project, Tag 02FV): if `f ≫ g` is locally of finite
presentation and `g : Y ⟶ Z` is locally of finite type, then `f : X ⟶ Y` is locally of finite
presentation. -/
theorem LocallyOfFinitePresentation.of_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f := (locallyOfFinitePresentation_iff f).mpr fun x ↦ by
  obtain ⟨CZ, CX₀, _, χ, hχ, hχ_fp, c₀₀, hc₀₀, hsq_fg⟩ := hfg.exists_openImmersion_chart x
  have ha₀ : CZ.hom.base ((CZ.pairComap CX₀ χ).base c₀₀) = g.hom.base (f.hom.base x) :=
    CZ.pairComap_comp_hom_base_comp CX₀ χ (f := f.hom) (g := g.hom) hsq_fg hc₀₀
  obtain ⟨TA, sA, hTA, -, CY, ψ, hψ, b₀, hb₀, hsq_g⟩ :=
    hg.exists_openImmersion_over_rationalLocalization CZ (f.hom.base x) ha₀
  let ψ₀ := ψ.comp (CZ.rationalLocalizationHom TA sA hTA)
  have hψ₀_tft := hψ.comp (CZ.isTopologicallyFiniteType_rationalLocalizationHom TA sA hTA)
  have : IsHuberStandard CY.Ring :=
    .of_isTopologicallyFiniteType hψ₀_tft.isTopologicallyFiniteType_toRingHom
  have hsq_g₀ : CZ.pairComap CY ψ₀ ≫ CZ.hom = CY.hom ≫ g.hom :=
    (CZ.pairComap_comp_rationalLocalizationHom_comp_hom CY ψ).trans hsq_g
  obtain ⟨TC, sC, hTC, φ, c₁, hc₁, hsq_f, hφψ₀⟩ :=
    exists_rationalLocalization_lift_sq CZ CY CX₀ ψ₀ χ hb₀ hc₀₀ hsq_g₀ hsq_fg
  obtain ⟨hφ_tft, hφ_fp⟩ :=
    isTopologicallyFiniteType_and_finitePresentation_of_comp_rationalLocalization
      hψ₀_tft hχ hχ_fp hφψ₀
  exact locallyOfFinitePresentationAt_of_openImmersion_sq CY
    (CX₀.rationalLocalization TC sC hTC) φ hφ_tft hφ_fp hc₁ hsq_f

/-- **Restriction of `LocallyOfFinitePresentation` along open immersions**: given a commuting
square `g ≫ iV = iU ≫ f` of adic spaces with `iU` and `iV` open immersions and `f` locally of
finite presentation, the restricted morphism `g : U ⟶ V` is locally of finite presentation. -/
theorem LocallyOfFinitePresentation.restrict {U V : AdicSpace.{u}} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} {g : U ⟶ V} [PreAdicSpace.IsOpenImmersion iU.hom]
    [PreAdicSpace.IsOpenImmersion iV.hom] (hcomm : g ≫ iV = iU ≫ f)
    (hf : LocallyOfFinitePresentation f) : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp
    (hcomm ▸ (LocallyOfFinitePresentation.of_isOpenImmersion iU
      ((IsLocallyHuberStandard.of_locallyOfFinitePresentation hf).of_isOpenImmersion iU)).comp hf)
    (LocallyOfFiniteType.of_isOpenImmersion iV)

/-- **Open-cover descent on the source for `LocallyOfFinitePresentation`**: a morphism
`f : X ⟶ Y` of adic spaces is locally of finite presentation if and only if its restriction
`X.ofRestrict (U i) ≫ f` to each member of an open cover `U` of `X` is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_iff_of_iSup_eq_top_source {f : X ⟶ Y} {ι : Type*}
    (U : ι → Opens X.obj) (hU : iSup U = ⊤) :
    LocallyOfFinitePresentation f ↔ ∀ i, LocallyOfFinitePresentation (X.ofRestrict (U i) ≫ f) := by
  refine ⟨fun hf i ↦ hf.restrict (iU := X.ofRestrict (U i)) (iV := 𝟙 Y) (Category.comp_id _),
    fun h ↦ (locallyOfFinitePresentation_iff_forall_exists_openImmersion_chart f).mpr fun x ↦ ?_⟩
  obtain ⟨i, hx⟩ := Opens.mem_iSup.mp (hU.ge (Opens.mem_top x))
  let xᵢ : (X.restrict (U i)).obj := ⟨x, hx⟩
  obtain ⟨CY, CX, _, φ, hφ, hfp, b₀, hb₀, hsq⟩ := (h i).exists_openImmersion_chart xᵢ
  refine ⟨CY, CX.compOpenImmersion (X.ofRestrict (U i)).hom, inferInstance, φ, hφ, hfp, b₀, ?_, ?_⟩
  · rw [compOpenImmersion_hom_base, hb₀, AdicSpace.ofRestrict_base_apply]
  · rw [pairComap_compOpenImmersion_right_eq_comp_iff]
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using hsq

end TauCeti.AdicSpace

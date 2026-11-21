/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Basic

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
  have ha₀ : CZ.hom.base ((CZ.pairComap CX₀ χ).base c₀₀) = g.hom.base (f.hom.base x) := by
    simpa [hc₀₀] using congrArg (fun m ↦ m.base c₀₀) hsq_fg
  obtain ⟨TA, sA, hTA, -, CY, ψ, hψ, b₀, hb₀, hsq_g⟩ :=
    hg.exists_openImmersion_over_rationalLocalization CZ (f.hom.base x) ha₀
  let CZ₁ := CZ.rationalLocalization TA sA hTA
  let ψ₀ := ψ.comp (CZ.rationalLocalizationHom TA sA hTA)
  have hψ₀_tft := hψ.comp (CZ.isTopologicallyFiniteType_rationalLocalizationHom TA sA hTA)
  have : IsHuberStandard CY.Ring :=
    .of_isTopologicallyFiniteType hψ₀_tft.isTopologicallyFiniteType_toRingHom
  have hsq_g₀ : CZ.pairComap CY ψ₀ ≫ CZ.hom = CY.hom ≫ g.hom := by
    rw [CZ.pairComap_comp CZ₁ CY _ ψ, Category.assoc]
    have h := hsq_g
    rw [ofRationalLocalization_hom] at h
    exact h
  obtain ⟨TC, sC, hTC, φ, c₁, hc₁, hsq_f, hφψ₀⟩ :=
    exists_rationalLocalization_lift_sq (f := f.hom) (g := g.hom) CZ CY CX₀ ψ₀ χ hb₀ hc₀₀
      hsq_g₀ hsq_fg
  have hφ_tft : φ.IsTopologicallyFiniteType :=
    .of_comp (hφψ₀ ▸ (CX₀.isTopologicallyFiniteType_rationalLocalizationHom TC sC hTC).comp hχ)
  refine locallyOfFinitePresentationAt_of_openImmersion_sq CY
    (CX₀.rationalLocalization TC sC hTC) φ hφ_tft (fun _ ↦ ?_) hc₁ hsq_f
  exact hψ₀_tft.isTopologicallyFiniteType_toRingHom.finitePresentation_of_comp
    hφ_tft.isTopologicallyFiniteType_toRingHom fun hDiscA ↦ by
      have : DiscreteTopology CX₀.Ring := hχ.isTopologicallyFiniteType_toRingHom.discreteTopology
      rw [← Pair.Hom.toRingHom_comp, hφψ₀, Pair.Hom.toRingHom_comp]
      exact (CX₀.finitePresentation_rationalLocalizationHom TC sC hTC).comp (hχ_fp hDiscA)

/-- **Restriction of `LocallyOfFinitePresentation` along open immersions**: given a commuting
square `g ≫ iV = iU ≫ f` of adic spaces with `iU` and `iV` open immersions and `f` locally of
finite presentation, the restricted morphism `g : U ⟶ V` is locally of finite presentation. -/
theorem LocallyOfFinitePresentation.restrict {U V : AdicSpace.{u}} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} {g : U ⟶ V} [PreAdicSpace.IsOpenImmersion iU.hom]
    [PreAdicSpace.IsOpenImmersion iV.hom] (hcomm : g ≫ iV = iU ≫ f)
    (hf : LocallyOfFinitePresentation f) : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp
    (hcomm ▸ (LocallyOfFinitePresentation.of_isOpenImmersion iU
      hf.isLocallyHuberStandard_source).comp hf)
    (LocallyOfFiniteType.of_isOpenImmersion iV)

end TauCeti.AdicSpace

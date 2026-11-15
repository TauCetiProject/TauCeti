/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Basic

import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType

/-!
# Cancellation and open restriction for morphisms locally of finite presentation

Proves right-cancellation (`LocallyOfFinitePresentation.of_comp`, Huber 1996,
Proposition 1.6.7(iii); Stacks 02FV) and open restriction (`LocallyOfFinitePresentation.restrict`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), Proposition 1.6.7(iii).
* [The Stacks Project, *Morphisms, Lemma 02FV (29.21.11)*][stacks-project].
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum CompleteAffinoidOpen

universe u

variable {X Y Z : AdicSpace.{u}}

/-- **Right-cancellation of `LocallyOfFinitePresentation` along `LocallyOfFiniteType`**
(Huber 1996, Proposition 1.6.7(iii); Stacks 02FV). -/
theorem LocallyOfFinitePresentation.of_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f := (locallyOfFinitePresentation_iff f).mpr fun x ↦ by
  obtain ⟨CZ, CX₀, _, χ, hχ, hχ_fp, c₀₀, hc₀₀, hsq_fg⟩ := hfg.exists_openImmersion_chart x
  have ha₀ : CZ.hom.base ((CZ.pairComap CX₀ χ).base c₀₀) = g.hom.base (f.hom.base x) := by
    simpa [hc₀₀] using congrArg (fun m ↦ m.base c₀₀) hsq_fg
  obtain ⟨TA, sA, hTA, -, CY, ψ, hψ, b₀, hb₀, hsq_g⟩ :=
    hg.exists_openImmersion_over_rationalLocalization CZ.pod CZ.le_plus CZ.isSheaf CZ.hom
      (f.hom.base x) ha₀
  let CZ₁ := CZ.rationalShrink TA sA hTA
  let ψ₀ := ψ.comp (CZ.toRationalShrinkHom TA sA hTA)
  have hψ₀_tft := hψ.comp (isTopologicallyFiniteType_toRationalLocalizationHom CZ.pod CZ.le_plus
    CZ.isSheaf CZ.hom TA sA hTA)
  have : IsHuberStandard CY.Ring :=
    .of_isTopologicallyFiniteType hψ₀_tft.isTopologicallyFiniteType_toRingHom
  have hsq_g₀ : CZ.pairComap CY ψ₀ ≫ CZ.hom = CY.hom ≫ g.hom := by
    rw [pairComap, presentationLimitPreAdicSpacePairComap_comp CZ.pod CZ₁.pod CY.pod CZ.le_plus
      CZ₁.le_plus CY.le_plus CZ₁.isSheaf CY.isSheaf, Category.assoc]
    have h := hsq_g; rw [ofRationalLocalization_hom] at h; exact h
  obtain ⟨TC, sC, hTC, φ, hφ_tft, c₁, hc₁, hsq_f, hφψ₀⟩ :=
    exists_rational_shrink_lift_sq (f_hom := f.hom) (g_hom := g.hom) CZ CY CX₀.pod CX₀.le_plus
      CX₀.isSheaf CX₀.hom ψ₀ χ hχ hb₀ hc₀₀ hsq_g₀ hsq_fg
  exact exists_locallyOfFinitePresentation_chart_of_openImmersion_sq CY
    (CX₀.rationalShrink TC sC hTC) φ hφ_tft
    (finitePresentation_of_comp_eq_toRationalShrinkHom_comp CZ CY CX₀ hTC hψ₀_tft hχ hχ_fp hφ_tft
      hφψ₀)
    hc₁ hsq_f

/-- **Restriction of `LocallyOfFinitePresentation` along open immersions**. -/
theorem LocallyOfFinitePresentation.restrict {U V : AdicSpace.{u}} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} {g : U ⟶ V} [PreAdicSpace.IsOpenImmersion iU.hom]
    [PreAdicSpace.IsOpenImmersion iV.hom] (hcomm : g ≫ iV = iU ≫ f)
    (hf : LocallyOfFinitePresentation f) : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp
    (hcomm ▸ (LocallyOfFinitePresentation.of_isOpenImmersion iU
      hf.isLocallyHuberStandard_source).comp hf)
    (LocallyOfFiniteType.of_isOpenImmersion iV)

end TauCeti.AdicSpace

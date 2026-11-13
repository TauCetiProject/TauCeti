/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.GlobalSections
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.OpenUnitDisc.Adic

/-!
# Tests for global sections of morphisms into affinoids

These clients use the global-sections criterion for arbitrary adic sources and for the
non-affinoid open unit disc. They also check the pointwise germ square and preservation of
integral sections after precomposition, without unfolding the constructions.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open Huber

variable {A : Type} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
  (P : PairOfDefinition A) (Aplus : Subring A)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)

/-- Global sections detect equality for every adic source, not just affinoid sources. -/
example (X : AdicSpace)
    (f g : X.obj ⟶ presentationLimitPreAdicSpace P Aplus hAplus hP)
    (h : presentationLimitAppTop P Aplus hAplus hP f =
      presentationLimitAppTop P Aplus hAplus hP g) : f = g :=
  presentationLimitAppTop_injective P Aplus hAplus hP X.property.isSheafy h

/-- The germ square remains valid after precomposition by any pre-adic morphism. -/
example {X Y : PreAdicSpace} (h : Y ⟶ X)
    (f : X ⟶ presentationLimitPreAdicSpace P Aplus hAplus hP) (y : Y) :
    (Y.toRingPresheafedSpace.presheaf.germ ⊤ y (Opens.mem_top y)).hom.comp
        (presentationLimitAppTop P Aplus hAplus hP (h ≫ f)) =
      ((h ≫ f).stalkMap y).hom.comp (presentationLimitGlobalGerm P Aplus ((h ≫ f).base y)) :=
  presentationLimitAppTop_comp_germ P Aplus hAplus hP (h ≫ f) y

/-- The coefficient pullback after precomposition is continuous and preserves integrality. -/
example {X Y : PreAdicSpace} (h : Y ⟶ X)
    (f : X ⟶ presentationLimitPreAdicSpace P Aplus hAplus hP) {a : A} (ha : a ∈ Aplus) :
    Continuous (presentationLimitAppTop P Aplus hAplus hP (h ≫ f)) ∧
      presentationLimitAppTop P Aplus hAplus hP (h ≫ f) a ∈ Y.plusSubring ⊤ :=
  ⟨continuous_presentationLimitAppTop P Aplus hAplus hP (h ≫ f),
    presentationLimitAppTop_mem_plus P Aplus hAplus hP (h ≫ f) ha⟩

/-- Non-affinoid-source test: maps from the open unit disc into an affinoid are determined by
coefficient pullback even though the source is not quasi-compact. -/
example {K : Type} [NormedField K] [NonarchimedeanRing K] [IsUltrametricDist K]
    [CompleteSpace K] [IsTateRing K] (c : K) (Q : PairOfDefinition K) (hc : IsPseudoUniformizer c)
    (f g : openUnitDiscPreAdicSpace c Q hc ⟶ presentationLimitPreAdicSpace P Aplus hAplus hP)
    (h : presentationLimitAppTop P Aplus hAplus hP f =
      presentationLimitAppTop P Aplus hAplus hP g) :
    f = g ∧ ¬ PreAdicSpace.isAffinoid (openUnitDiscPreAdicSpace c Q hc) :=
  ⟨presentationLimitAppTop_injective P Aplus hAplus hP
      (isAdic_openUnitDiscPreAdicSpace c Q hc).isSheafy h,
    not_isAffinoid_openUnitDiscPreAdicSpace c Q hc⟩

end TauCeti.ValuationSpectrum

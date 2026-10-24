/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral

/-!
# Measurable reindexing of projection-valued measures

A measurable map `f : X → Y` transports a projection-valued measure on `X` to one on `Y`:
the projection of a measurable set `B` is the original projection of its preimage under `f`.
The diagonal scalar measures are the corresponding pushforward measures.

Identity and composition of measurable maps are respected by this construction. Integration
against the transported measure is the change of variables `∫ f d(P.map κ) = ∫ (f ∘ κ) dP` for
bounded Borel symbols `f` (`integral_map`); this is how a spectral integral over one parameter
space is rewritten as one over another, for instance from a compact spectrum to the real line.

The underlying projection-valued measure and its diagonal-measure representation come from
`TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic`, adapted from the Kitware DKPS
formalization and the Spectra formalization; see that module for source references.
-/

public section

open MeasureTheory
open scoped CStarAlgebra

namespace TauCeti.ProjValMeasure

variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]
variable {Z : Type*} [MeasurableSpace Z]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Push a projection-valued measure forward along a measurable map. -/
noncomputable def map (P : ProjValMeasure X H) (f : X → Y) (hf : Measurable f) :
    ProjValMeasure Y H where
  proj B hB := P.proj (f ⁻¹' B) (hf hB)
  diag ξ := Measure.map f (P.diag ξ)
  diag_finite _ := inferInstance
  inner_proj B hB ξ := by
    simpa only [Measure.map_apply hf hB] using
      P.inner_proj (f ⁻¹' B) (hf hB) ξ
  proj_univ := by
    simpa only [Set.preimage_univ] using P.proj_univ
  proj_inter B C hB hC := by
    simpa only [Set.preimage_inter] using
      P.proj_inter (f ⁻¹' B) (f ⁻¹' C) (hf hB) (hf hC)

/-- Evaluating the transported PVM on a measurable set is evaluating its preimage. -/
@[simp]
theorem map_proj (P : ProjValMeasure X H) (f : X → Y) (hf : Measurable f)
    (B : Set Y) (hB : MeasurableSet B) :
    (P.map f hf).proj B hB = P.proj (f ⁻¹' B) (hf hB) :=
  (rfl)

/-- Diagonal scalar measures are pushed forward by the same measurable map. -/
@[simp]
theorem map_diag (P : ProjValMeasure X H) (f : X → Y) (hf : Measurable f) (ξ : H) :
    (P.map f hf).diag ξ = Measure.map f (P.diag ξ) :=
  (rfl)

/-- Transport along the identity measurable map leaves the PVM unchanged. -/
@[simp]
theorem map_id (P : ProjValMeasure X H) :
    P.map (id : X → X) measurable_id = P := by
  apply ProjValMeasure.ext
  intro B hB
  simp only [map_proj, Set.preimage_id]

/-- Transport along two measurable maps equals transport along their composition. -/
@[simp]
theorem map_map (P : ProjValMeasure X H) (f : X → Y) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g) :
    (P.map f hf).map g hg = P.map (g ∘ f) (hg.comp hf) := by
  apply ProjValMeasure.ext
  intro B hB
  simp only [map_proj, Set.preimage_comp]

/-- **Change of variables** for the integral against a projection-valued measure: integrating a
bounded Borel symbol `f` on `Y` against the transported measure `P.map κ hκ` is integrating its
pullback `f ∘ κ` against `P`. -/
theorem integral_map (P : ProjValMeasure X H) (κ : X → Y) (hκ : Measurable κ)
    (f : BoundedBorelFunction Y) :
    (P.map κ hκ).integral f = P.integral (BoundedBorelFunction.compStarAlgHom' κ hκ f) := by
  -- Both sides are continuous in `f`, so it suffices to compare them on simple symbols, which
  -- are sums of multiples of indicators of measurable sets.
  refine (congrFun ((P.map κ hκ).eq_integral_of_continuous
    (P.continuous_integral.comp (map_continuous _)) fun s => ?_) f).symm
  rw [Function.comp_apply]
  induction s using SimpleFunc.induction with
  | @const c B hB =>
    simp [BoundedBorelFunction.ofSimpleFunc_piecewise_const_zero,
      BoundedBorelFunction.compStarAlgHom'_indicator]
  | add _ hs₁ hs₂ => simp only [map_add, hs₁, hs₂]

end TauCeti.ProjValMeasure

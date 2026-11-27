/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MemLpLoc
import Mathlib.MeasureTheory.Group.Measure

/-!
# Translation and affine invariance of local `Lᵖ` classes

Right-translation invariance (`TauCeti.MemLpLoc.comp_add_right`,
`TauCeti.memLpLoc_comp_add_right_iff`), combined with linear invariance under arbitrary additive
Haar measures (`ContinuousLinearEquiv.memLpLoc_comp_right_iff` in
`TauCeti.MeasureTheory.Function.MemLpLoc`), shows that continuous linear equivalences
(`TauCeti.MemLpLoc.comp_continuousLinearEquiv`) and real-affine equivalences
(`TauCeti.MemLpLoc.comp_continuousLinearEquiv_add`) preserve local `Lᵖ` classes between arbitrary
Borel additive Haar measures.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

section Translation

/-- Right translation preserves and reflects local `Lᵖ` membership. -/
@[simp]
theorem memLpLoc_comp_add_right_iff {G F : Type*}
    [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddRightInvariant]
    [NormedAddCommGroup F] {p : ENNReal} {V : Set G} {u : G → F} (b : G) :
    MemLpLoc p ((· + b) ⁻¹' V) (fun x => u (x + b)) μ ↔ MemLpLoc p V u μ := by
  simpa [Function.comp_def, (measurePreserving_add_right μ b).map_eq] using
    (Homeomorph.addRight b).memLpLoc_comp_iff (μ := μ) (p := p) (U := V) (f := u)

/-- Right translation preserves local `Lᵖ` membership under any right-invariant Borel measure. -/
theorem MemLpLoc.comp_add_right {G F : Type*}
    [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddRightInvariant]
    [NormedAddCommGroup F] {p : ENNReal} {U V : Set G} {u : G → F}
    (hu : MemLpLoc p V u μ) (b : G) (hmaps : MapsTo (· + b) U V) :
    MemLpLoc p U (fun x => u (x + b)) μ :=
  ((memLpLoc_comp_add_right_iff b).2 hu).mono_set hmaps.subset_preimage

end Translation

section LinearAndAffineLp

variable {E E₁ F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedAddCommGroup F]

/-- Precomposition with a continuous linear equivalence onto a finite-dimensional real normed space
preserves local `Lᵖ` membership between arbitrary Borel additive Haar measures. -/
theorem MemLpLoc.comp_continuousLinearEquiv {μ : Measure E} [μ.IsAddHaarMeasure]
    {ν : Measure E₁} [ν.IsAddHaarMeasure] {p : ENNReal} {U : Set E} {V : Set E₁}
    {u : E₁ → F} (hu : MemLpLoc p V u ν) (e : E ≃L[ℝ] E₁) (hmaps : MapsTo e U V) :
    MemLpLoc p U (u ∘ e) μ :=
  ((e.memLpLoc_comp_right_iff μ ν).2 hu).mono_set hmaps.subset_preimage

/-- Real-affine changes of variables onto a finite-dimensional real normed space preserve local `Lᵖ`
membership between arbitrary Borel additive Haar measures. -/
theorem MemLpLoc.comp_continuousLinearEquiv_add {μ : Measure E} [μ.IsAddHaarMeasure]
    {ν : Measure E₁} [ν.IsAddHaarMeasure] {p : ENNReal} {U : Set E} {V : Set E₁}
    {u : E₁ → F} (hu : MemLpLoc p V u ν) (A : E ≃L[ℝ] E₁) (b : E₁)
    (hmaps : MapsTo (fun x => A x + b) U V) :
    MemLpLoc p U (fun x => u (A x + b)) μ :=
  (hu.comp_add_right b (mapsTo_preimage (· + b) V)).comp_continuousLinearEquiv A hmaps

end LinearAndAffineLp

end TauCeti

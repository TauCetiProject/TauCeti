/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Function.MemLpLoc
import Mathlib.MeasureTheory.Group.Measure

/-!
# Measure scaling, translation, and affine invariance of local `Lᵖ` classes

Scaling the ambient measure by a positive finite scalar preserves and reflects `Lᵖ` membership on
compact sets (`TauCeti.memLpLoc_smul_measure_iff`). Two additive Haar measures on a locally compact
group are proportional on every compact set, so they define the same local `Lᵖ` classes
(`TauCeti.memLpLoc_iff_of_isAddHaarMeasure`). Combined with right-translation invariance
(`TauCeti.MemLpLoc.comp_add_right`, `TauCeti.memLpLoc_comp_add_right_iff`), this shows that
continuous linear equivalences (`ContinuousLinearEquiv.memLpLoc_comp_right_iff`,
`TauCeti.MemLpLoc.comp_continuousLinearEquiv`) and real-affine equivalences
(`TauCeti.MemLpLoc.comp_continuousLinearEquiv_add`) preserve local `Lᵖ` classes between arbitrary
Borel additive Haar measures.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

section SmulMeasure

/-- Scaling the ambient measure by a positive finite constant preserves and reflects local `Lᵖ`
membership. -/
theorem memLpLoc_smul_measure_iff {X F : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    {p : ENNReal} {U : Set X} {f : X → F} :
    MemLpLoc p U f (c • μ) ↔ MemLpLoc p U f μ :=
  ⟨fun h => h.of_measure_le_smul (ENNReal.inv_ne_top.2 hc0)
      (by rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul]),
    fun h => h.of_measure_le_smul hc le_rfl⟩

end SmulMeasure

section Haar

variable {G F : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup F] {p : ℝ≥0∞} {U : Set G} {f : G → F}

/-- **Independence of the Haar measure.** Two additive Haar measures on a locally compact group
are proportional on every compact set, so they define the same local `Lᵖ` classes. -/
theorem memLpLoc_iff_of_isAddHaarMeasure (μ ν : Measure G) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] : MemLpLoc p U f μ ↔ MemLpLoc p U f ν := by
  have key : ∀ (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure],
      MemLpLoc p U f μ → MemLpLoc p U f ν := fun μ ν _ _ h =>
    memLpLoc_iff.2 fun K hKU hK =>
      ((memLpLoc_iff.1 h) K hKU hK).of_measure_le_smul ENNReal.coe_ne_top <|
        le_of_eq <| Measure.ext fun s hs => by
          rw [smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs]
          exact Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν μ
            (hK.closure_of_subset Set.inter_subset_right)
  exact ⟨key μ ν, key ν μ⟩

end Haar

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

/-- **Linear changes of variables.** A continuous linear equivalence `e : E ≃L[ℝ] E₁` onto a
finite-dimensional real normed space carries the local `Lᵖ` class of `U` in `E₁` to that of
`e ⁻¹' U` in `E`, for any additive Haar measures on the two spaces. -/
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_right_iff (e : E ≃L[ℝ] E₁) (μ : Measure E)
    [μ.IsAddHaarMeasure] (ν : Measure E₁) [ν.IsAddHaarMeasure] {p : ℝ≥0∞} {U : Set E₁}
    {f : E₁ → F} : MemLpLoc p (e ⁻¹' U) (f ∘ e) μ ↔ MemLpLoc p U f ν := by
  rw [← memLpLoc_iff_of_isAddHaarMeasure (μ.map e) ν]
  exact e.toHomeomorph.memLpLoc_comp_iff

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

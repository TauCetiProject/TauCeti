/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.MeasureTheory.Function.Lp.AeMem
public import TauCeti.MeasureTheory.Function.Lp.LinearIsometry

/-!
# Bochner spaces with values in a submodule

For a target submodule `S`, `Submodule.lp` is the submodule of ambient `Lᵖ` classes whose
values belong to `S` almost everywhere. `Submodule.lpEquiv` identifies it linearly and
isometrically with `Lp S p μ`. Neither this identification nor its representative formulas
requires `S` to be closed. When `S` is closed, so is `S.lp p μ`; when `S` is complete,
its Bochner subspace is complete.

This allows integration and approximation in a closed target subspace to use its native
Bochner space, while retaining the ambient representatives and norm.

The construction uses `LinearIsometry.compLpₗᵢ` for the subtype inclusion and Mathlib's
`LinearIsometry.equivRange`. The subspace interpretation of Bochner spaces is as in
Hytönen, van Neerven, Veraar and Weis, *Analysis in Banach Spaces*, Volume I, §1.2.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Submodule

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (S : Submodule 𝕜 E) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)

/-- The ambient `Lᵖ` classes with values almost everywhere in a target submodule. -/
def lp : Submodule 𝕜 (Lp E p μ) :=
  (S.subtypeₗᵢ.compLpₗᵢ p μ).toLinearMap.range

variable {p μ}

/-- Membership in the target submodule of `Lᵖ` is exactly a.e. membership of the values. -/
@[simp]
theorem mem_lp_iff (f : Lp E p μ) :
    f ∈ S.lp p μ ↔ ∀ᵐ x ∂μ, f x ∈ S := by
  classical
  constructor
  · rintro ⟨g, rfl⟩
    filter_upwards [S.subtypeₗᵢ.coeFn_compLpₗᵢ g] with x hx
    simpa only [LinearIsometry.coe_toLinearMap, hx, coe_subtypeₗᵢ, subtype_apply] using
      (g x).property
  · intro hf
    let g : α → S := fun x ↦ if hx : f x ∈ S then ⟨f x, hx⟩ else 0
    have hg : (fun x ↦ (g x : E)) =ᵐ[μ] f := by
      filter_upwards [hf] with x hx
      simp [g, hx]
    have hgm : AEStronglyMeasurable g μ :=
      (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).1
        ((Lp.aestronglyMeasurable f).congr hg.symm)
    have hgp : MemLp g p μ := (Lp.memLp f).congr_norm hgm (by
      filter_upwards [hg] with x hx
      exact congrArg norm hx.symm)
    refine ⟨hgp.toLp g, Lp.ext ?_⟩
    filter_upwards [S.subtypeₗᵢ.coeFn_compLpₗᵢ (hgp.toLp g), hgp.coeFn_toLp, hg]
      with x hx₁ hx₂ hx₃
    exact hx₁.trans ((congrArg Subtype.val hx₂).trans hx₃)

/-- Closed target submodules give closed submodules of the ambient Bochner space. -/
theorem isClosed_lp (hS : IsClosed (S : Set E)) :
    IsClosed (S.lp p μ : Set (Lp E p μ)) := by
  convert Lp.isClosed_setOf_ae_mem (p := p) (μ := μ) hS using 1
  ext f
  exact S.mem_lp_iff f

variable (p μ)

/-- The native Bochner space of a target submodule is isometric to the ambient classes
whose values belong to that submodule almost everywhere. -/
def lpEquiv : Lp S p μ ≃ₗᵢ[𝕜] S.lp p μ :=
  (S.subtypeₗᵢ.compLpₗᵢ p μ).equivRange

variable {p μ}

/-- The ambient class of `lpEquiv` is postcomposition with the subtype inclusion. -/
@[simp]
theorem coe_lpEquiv_apply (f : Lp S p μ) :
    (S.lpEquiv p μ f : Lp E p μ) = S.subtypeₗᵢ.compLpₗᵢ p μ f :=
  (rfl)

/-- Representatives of `lpEquiv` agree a.e. with inclusion of the subspace-valued
representative. -/
theorem coeFn_lpEquiv (f : Lp S p μ) :
    ((S.lpEquiv p μ f : Lp E p μ) : α → E) =ᵐ[μ] fun x ↦ (f x : E) := by
  rw [coe_lpEquiv_apply]
  exact S.subtypeₗᵢ.coeFn_compLpₗᵢ f

/-- The inverse identification lifts the ambient representative almost everywhere. -/
theorem coeFn_lpEquiv_symm (f : S.lp p μ) :
    (fun x ↦ ((S.lpEquiv p μ).symm f x : E)) =ᵐ[μ] (f : Lp E p μ) := by
  have h := S.coeFn_lpEquiv ((S.lpEquiv p μ).symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- A complete target subspace gives a complete subspace of ambient `Lᵖ`. -/
instance completeSpace_lp [CompleteSpace S] : CompleteSpace (S.lp p μ) :=
  (S.lpEquiv p μ).symm.toIsometryEquiv.completeSpace

end Submodule

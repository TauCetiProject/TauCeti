/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The manifold structure on an open ball

An open ball in a pseudometric charted space inherits the open-subset atlas and any manifold
structure. In particular a complex disc, written with its usual subtype rather than as a bundled
open set, is a complex manifold.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {H M : Type*} [TopologicalSpace H] [PseudoMetricSpace M] [ChartedSpace H M]

/-- An open ball has the atlas induced from its ambient charted space. -/
noncomputable instance instChartedSpaceBall (c : M) (r : ℝ) : ChartedSpace H (Metric.ball c r) :=
  inferInstanceAs (ChartedSpace H
    (⟨Metric.ball c r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens M))

/-- The charted-space structure on a ball is the one on the corresponding bundled open set. -/
theorem instChartedSpaceBall_eq (c : M) (r : ℝ) :
    instChartedSpaceBall (H := H) c r =
      TopologicalSpace.Opens.instChartedSpace ⟨Metric.ball c r, Metric.isOpen_ball⟩ := (rfl)

/-- The atlas of an open ball consists of the restrictions of its ambient charts. -/
theorem atlas_ball (c : M) (r : ℝ) :
    atlas H (Metric.ball c r) = ⋃ x : Metric.ball c r,
      {(chartAt H (x : M)).subtypeRestr
        (s := ⟨Metric.ball c r, Metric.isOpen_ball⟩) ⟨x⟩} := (rfl)

/-- The induced atlas makes an open ball in a manifold a manifold with the same model. -/
instance instIsManifoldBall {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n M]
    (c : M) (r : ℝ) : IsManifold I n (Metric.ball c r) :=
  inferInstanceAs (IsManifold I n
    (⟨Metric.ball c r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens M))

/-- The chart of an open ball is the restriction of its ambient chart. -/
theorem chartAt_ball {c : M} {r : ℝ} (x : Metric.ball c r) :
    chartAt H x = (chartAt H (x : M)).subtypeRestr
      (s := ⟨Metric.ball c r, Metric.isOpen_ball⟩) ⟨x⟩ := (rfl)

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} {c : M} {r : ℝ}

/-- The inclusion of an open ball into its ambient manifold is `C^n`. -/
theorem contMDiff_subtypeVal_ball :
    ContMDiff I I n (Subtype.val : Metric.ball c r → M) :=
  contMDiff_subtype_val (U := ⟨Metric.ball c r, Metric.isOpen_ball⟩)

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N]
  [ChartedSpace H' N] (f : N → Metric.ball c r)

/-- Restricting the source to an open ball preserves `C^n` regularity at its points. -/
theorem contMDiffAt_ball_iff {g : M → N} {x : Metric.ball c r} :
    ContMDiffAt I I' n (fun x : Metric.ball c r ↦ g x) x ↔ ContMDiffAt I I' n g x :=
  contMDiffAt_subtype_iff (U := ⟨Metric.ball c r, Metric.isOpen_ball⟩)

/-- A map into an open ball is `C^n` within a set at a point iff its ambient map is. -/
@[simp] theorem contMDiffWithinAt_subtypeVal_ball_comp_iff (s : Set N) (x : N) :
    ContMDiffWithinAt I' I n (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I' I n f s x :=
  ContMDiffWithinAt.subtypeVal_comp_iff ⟨Metric.ball c r, Metric.isOpen_ball⟩ f s x

/-- A map into an open ball is `C^n` at a point iff its ambient map is. -/
@[simp] theorem contMDiffAt_subtypeVal_ball_comp_iff (x : N) :
    ContMDiffAt I' I n (Subtype.val ∘ f) x ↔ ContMDiffAt I' I n f x :=
  ContMDiffAt.subtypeVal_comp_iff ⟨Metric.ball c r, Metric.isOpen_ball⟩ f x

/-- A map into an open ball is `C^n` on a set iff its ambient map is. -/
@[simp] theorem contMDiffOn_subtypeVal_ball_comp_iff (s : Set N) :
    ContMDiffOn I' I n (Subtype.val ∘ f) s ↔ ContMDiffOn I' I n f s :=
  ContMDiffOn.subtypeVal_comp_iff ⟨Metric.ball c r, Metric.isOpen_ball⟩ f s

/-- A map into an open ball is `C^n` iff its ambient map is. -/
@[simp] theorem contMDiff_subtypeVal_ball_comp_iff :
    ContMDiff I' I n (Subtype.val ∘ f) ↔ ContMDiff I' I n f :=
  ContMDiff.subtypeVal_comp_iff ⟨Metric.ball c r, Metric.isOpen_ball⟩ f

end TauCeti

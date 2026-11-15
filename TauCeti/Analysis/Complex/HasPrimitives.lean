/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.HasPrimitives

import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.LocalPotentials.Complex

/-!
# Primitives of holomorphic and conservative functions on simply connected domains

Mathlib's `DifferentiableOn.isExactOn_ball` and `Complex.IsConservativeOn.isExactOn_ball` give
every holomorphic (or continuous rectangle-conservative) function on a disc with values in a
complete complex normed space a primitive there. This file records both the local convex-gluing
consequence on discs and the global extension to simply connected open sets via local potentials
and homotopy-invariant continuous path integration:

* `DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter` -- a primitive of a holomorphic integrand
  on `ball c r ∩ U`, for convex `U`, is the restriction of a primitive on `ball c r`.
* `DifferentiableOn.isExactOn_of_isSimplyConnected`,
  `DifferentiableOn.isExactOn_of_simplyConnected`, and
  `DifferentiableOn.isExactOn_of_forall_connectedComponentIn` -- a holomorphic function on a simply
  connected open subset of `ℂ` (or an open subset whose connected components are simply connected)
  admits a global primitive.
* `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected`,
  `Complex.IsConservativeOn.isExactOn_of_simplyConnected`, and
  `Complex.IsConservativeOn.isExactOn_of_forall_connectedComponentIn` -- Morera's theorem on simply
  connected open subsets of `ℂ` (and unions of simply connected open components).
-/

public section

open Complex Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A holomorphic integrand `g` on a disc has a primitive on the disc agreeing with any given
primitive `f` of `g` on the intersection of the disc with a convex set `U`. -/
theorem DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter {f g : ℂ → E} {c : ℂ} {r : ℝ}
    {U : Set ℂ} (hg : DifferentiableOn ℂ g (ball c r)) (hU : Convex ℝ U)
    (hf : ∀ z ∈ ball c r ∩ U, HasDerivWithinAt f (g z) (ball c r ∩ U) z) :
    ∃ G : ℂ → E, (∀ z ∈ ball c r, HasDerivAt G (g z) z) ∧ EqOn G f (ball c r ∩ U) := by
  obtain ⟨P, hP⟩ := hg.isExactOn_ball
  rcases (ball c r ∩ U).eq_empty_or_nonempty with hV | ⟨z₀, hz₀⟩
  · exact ⟨P, hP, by simp [hV]⟩
  refine ⟨fun z ↦ P z + (f z₀ - P z₀), fun z hz ↦ (hP z hz).add_const _, fun z hz ↦ ?_⟩
  have hderiv (w) (hw : w ∈ ball c r ∩ U) :
      HasDerivWithinAt (f - P) 0 (ball c r ∩ U) w := by
    simpa using (hf w hw).sub (hP w hw.1).hasDerivWithinAt
  have := ((convex_ball c r).inter hU).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ ↦ norm_zero.le) hz₀ hz
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, Pi.sub_apply, Pi.sub_apply] at this
  simp [← this]

/-- On an open subset `U ⊆ ℂ` whose connected components in `U` are simply connected, every
holomorphic function `f : ℂ → E` into a complete complex normed space has a global primitive. -/
theorem DifferentiableOn.isExactOn_of_forall_connectedComponentIn {U : Set ℂ} {f : ℂ → E}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hsc : ∀ z ∈ U, IsSimplyConnected (connectedComponentIn U z)) :
    IsExactOn f U := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨g, -, hg⟩ :=
    (hf.hasLocalPotentials hU).exists_hasFDerivAt_of_forall_connectedComponentIn hsc
  exact ⟨g, fun z hz ↦ TauCeti.hasDerivAt_iff_hasFDerivAt_restrictScalars.mpr (hg z hz)⟩

/-- Every holomorphic function `f : ℂ → E` on a simply connected open set `U ⊆ ℂ` with values in a
complete complex normed space admits a global primitive on `U`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected {U : Set ℂ} {f : ℂ → E}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hU_sc : IsSimplyConnected U) :
    IsExactOn f U := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨g, -, hg⟩ := (hf.hasLocalPotentials hU).exists_hasFDerivAt_of_isSimplyConnected hU_sc
  exact ⟨g, fun z hz ↦ TauCeti.hasDerivAt_iff_hasFDerivAt_restrictScalars.mpr (hg z hz)⟩

/-- Typeclass-hypothesis version of `DifferentiableOn.isExactOn_of_isSimplyConnected`: a holomorphic
function on an open set `U ⊆ ℂ` with `[SimplyConnectedSpace U]` has a global primitive on `U`. -/
theorem DifferentiableOn.isExactOn_of_simplyConnected {U : Set ℂ} [SimplyConnectedSpace U]
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    IsExactOn f U :=
  hf.isExactOn_of_isSimplyConnected hU ‹SimplyConnectedSpace U›

/-- **Morera's theorem on unions of simply connected components**: a continuous function on an open
set `U ⊆ ℂ` whose integrals around rectangles in `U` vanish has a global primitive whenever every
connected component of `U` is simply connected. -/
theorem Complex.IsConservativeOn.isExactOn_of_forall_connectedComponentIn {U : Set ℂ} {f : ℂ → E}
    (hf : IsConservativeOn f U) (hU : IsOpen U) (hf_cont : ContinuousOn f U)
    (hsc : ∀ z ∈ U, IsSimplyConnected (connectedComponentIn U z)) :
    IsExactOn f U :=
  ((isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
    ⟨hf, hf_cont⟩).isExactOn_of_forall_connectedComponentIn hU hsc

/-- **Morera's theorem on simply connected open domains**: a continuous function `f : ℂ → E` on a
simply connected open set `U ⊆ ℂ` whose integrals around rectangles in `U` vanish admits a global
primitive on `U`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected {U : Set ℂ} {f : ℂ → E}
    (hf : IsConservativeOn f U) (hU : IsOpen U) (hf_cont : ContinuousOn f U)
    (hU_sc : IsSimplyConnected U) :
    IsExactOn f U :=
  ((isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
    ⟨hf, hf_cont⟩).isExactOn_of_isSimplyConnected hU hU_sc

/-- Typeclass-hypothesis version of `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected`. -/
theorem Complex.IsConservativeOn.isExactOn_of_simplyConnected {U : Set ℂ} [SimplyConnectedSpace U]
    {f : ℂ → E} (hf : IsConservativeOn f U) (hU : IsOpen U) (hf_cont : ContinuousOn f U) :
    IsExactOn f U :=
  hf.isExactOn_of_isSimplyConnected hU hf_cont ‹SimplyConnectedSpace U›

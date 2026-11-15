/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import TauCeti.Analysis.Calculus.LocalPotentials.SimplyConnected
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Extending primitives on discs and holomorphic primitives on simply connected domains

Mathlib's `DifferentiableOn.isExactOn_ball` gives every holomorphic function on a disc with values
in a complete complex normed space `E` a primitive there. This file first records the gluing
consequence on convex parts of a disc, and then links `DifferentiableOn ℂ f U` to real local
potentials via the `ℂ`-linear covector field `z ↦ (v ↦ v • f z)`:

* on any open set `U ⊆ ℂ`, `z ↦ (toSpanSingleton ℂ (f z)).restrictScalars ℝ` has local `C¹`
  potentials if and only if `f` is holomorphic on `U`;
* consequently, by `TauCeti.HasLocalPotentials.exists_hasFDerivAt_of_isSimplyConnected`, every
  holomorphic function on a simply connected open subset of `ℂ` (or on an open subset whose
  connected components are all simply connected) admits a global complex primitive.

## Main results

* `DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter`: a primitive of a holomorphic integrand
  on `ball c r ∩ U`, for convex `U`, is the restriction of a primitive on `ball c r`.
* `DifferentiableOn.hasLocalPotentials` and `TauCeti.hasLocalPotentials_toSpanSingleton_iff`:
  characterization of holomorphicity on open sets in terms of local potentials of the associated
  `ℂ`-linear covector field.
* `DifferentiableOn.isExactOn_of_isSimplyConnected`,
  `DifferentiableOn.isExactOn_of_simplyConnectedSpace`, and
  `DifferentiableOn.isExactOn_of_forall_isSimplyConnected_connectedComponentIn`: global complex
  primitives on simply connected open domains and open domains with simply connected components.
-/

public section

open Complex Metric Set
open scoped ContDiff

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

/-- For a holomorphic function `f : ℂ → E` on an open set `U`, the `ℂ`-linear covector field
`z ↦ (v ↦ v • f z)` viewed over `ℝ` has local `C¹` potentials on `U`. -/
theorem DifferentiableOn.hasLocalPotentials {f : ℂ → E} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    TauCeti.HasLocalPotentials U
      fun z ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ := by
  rw [TauCeti.hasLocalPotentials_iff]
  intro z hz
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨g, hdg⟩ := (hf.mono hsub).isExactOn_ball
  have hg_diff : DifferentiableOn ℂ g (ball z r) :=
    fun w hw ↦ (hdg w hw).differentiableAt.differentiableWithinAt
  exact ⟨r, hr, hsub, g, (hg_diff.contDiffOn isOpen_ball).restrict_scalars ℝ,
    fun w hw ↦ (hdg w hw).hasFDerivAt.restrictScalars ℝ⟩

namespace TauCeti

/-- Conversely, if the `ℂ`-linear covector field `z ↦ (v ↦ v • f z)` has local `C¹` potentials on
`U`, then `f` is holomorphic on `U`. -/
theorem HasLocalPotentials.differentiableOn_of_toSpanSingleton {f : ℂ → E} {U : Set ℂ}
    (hφ : HasLocalPotentials U
      fun z ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ) :
    DifferentiableOn ℂ f U := by
  intro z hz
  obtain ⟨r, hr, -, g, -, hdg⟩ := hasLocalPotentials_iff.mp hφ z hz
  have hex : Complex.IsExactOn f (ball z r) :=
    ⟨g, fun w hw ↦ hasDerivAt_iff_hasFDerivAt.mpr (hasFDerivAt_of_restrictScalars ℝ (hdg w hw) rfl)⟩
  exact ((hex.differentiableOn isOpen_ball z (mem_ball_self hr)).differentiableAt
    (ball_mem_nhds z hr)).differentiableWithinAt

/-- The `ℂ`-linear covector field `z ↦ (v ↦ v • f z)` has local `C¹` potentials on `U` if and only
if `U` is open and `f` is holomorphic on `U`. -/
theorem hasLocalPotentials_toSpanSingleton_iff {f : ℂ → E} {U : Set ℂ} :
    HasLocalPotentials U
        (fun z ↦ (ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ) ↔
      IsOpen U ∧ DifferentiableOn ℂ f U :=
  ⟨fun h ↦ ⟨h.isOpen, h.differentiableOn_of_toSpanSingleton⟩,
    fun ⟨hU, hf⟩ ↦ hf.hasLocalPotentials hU⟩

end TauCeti

/-- A holomorphic function `f : ℂ → E` on an open set `U` whose connected components are all simply
connected has a global complex primitive on `U`. -/
theorem DifferentiableOn.isExactOn_of_forall_isSimplyConnected_connectedComponentIn {f : ℂ → E}
    {U : Set ℂ} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hsc : ∀ z ∈ U, IsSimplyConnected (connectedComponentIn U z)) :
    Complex.IsExactOn f U := by
  obtain ⟨g, -, -, hdg⟩ := (hf.hasLocalPotentials hU)
    |>.exists_hasFDerivAt_of_forall_isSimplyConnected_connectedComponentIn hsc
  exact ⟨g, fun z hz ↦
    hasDerivAt_iff_hasFDerivAt.mpr (hasFDerivAt_of_restrictScalars ℝ (hdg z hz) rfl)⟩

/-- A holomorphic function `f : ℂ → E` on a simply connected open subset `U ⊆ ℂ` has a global
complex primitive on `U`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected {f : ℂ → E} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hsc : IsSimplyConnected U) :
    Complex.IsExactOn f U := by
  obtain ⟨g, -, hdg⟩ := (hf.hasLocalPotentials hU).exists_hasFDerivAt_of_isSimplyConnected hsc
  exact ⟨g, fun z hz ↦
    hasDerivAt_iff_hasFDerivAt.mpr (hasFDerivAt_of_restrictScalars ℝ (hdg z hz) rfl)⟩

/-- Subtype-typeclass form of `DifferentiableOn.isExactOn_of_isSimplyConnected`. -/
theorem DifferentiableOn.isExactOn_of_simplyConnectedSpace {f : ℂ → E} {U : Set ℂ}
    [SimplyConnectedSpace U] (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    Complex.IsExactOn f U :=
  hf.isExactOn_of_isSimplyConnected hU ‹_›

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.LocalPotentials.SimplyConnected
import TauCeti.Analysis.Complex.LocalPotentials

/-!
# Primitives of holomorphic and conservative functions on discs and simply connected domains

Mathlib's `Complex.IsConservativeOn.isExactOn_ball` and `DifferentiableOn.isExactOn_ball` give
every continuous conservative — in particular, every holomorphic — function on a disc with values
in a complete complex normed space a complex primitive there. This file records both the
convex-overlap disc extension and the global passage from discs to simply connected open sets via
`TauCeti.exists_hasFDerivAt_of_simplyConnected`:

* on a disc, a primitive on `ball c r ∩ U` for convex `U` extends to a primitive on `ball c r`;
* on any simply connected open set `U ⊆ ℂ` (or any open set whose connected components are simply
  connected), every continuous conservative function — and hence every holomorphic function — with
  values in a complete complex normed space admits a global complex primitive (`Complex.IsExactOn`).

## Main results

* `DifferentiableOn.exists_hasDerivAt_eqOn_ball_inter`: a primitive of a holomorphic integrand on
  `ball c r ∩ U`, for convex `U`, is the restriction of a primitive on `ball c r`.
* `Complex.IsConservativeOn.isExactOn_of_simplyConnected` and
  `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn`: Morera's theorem
  on simply connected open domains and open domains with simply connected components.
* `DifferentiableOn.isExactOn_of_simplyConnected` and
  `DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn`: holomorphic functions on
  simply connected open domains (and open domains with simply connected components) have complex
  primitives.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §4.2, Corollary 2.
-/

public section

open Complex Metric Set ContinuousLinearMap

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

/-- **Morera's theorem on a simply connected open domain.** A continuous function `f : ℂ → E`
with values in a complete complex normed space whose rectangle integrals vanish on a simply
connected open set `U ⊆ ℂ` has a complex primitive on `U`. -/
theorem Complex.IsConservativeOn.isExactOn_of_simplyConnected {f : ℂ → E} {U : Set ℂ}
    (hf : Complex.IsConservativeOn f U) (hU : IsOpen U) [SimplyConnectedSpace U]
    (hcont : ContinuousOn f U) : Complex.IsExactOn f U := by
  have hφ := TauCeti.hasLocalPotentials_toSpanSingleton_of_isConservativeOn hU hcont hf
  obtain ⟨g, -, hg⟩ := TauCeti.exists_hasFDerivAt_of_simplyConnected hφ
  exact ⟨g, fun z hz ↦ by simpa using (hasFDerivAt_of_restrictScalars ℝ (hg z hz) rfl).hasDerivAt⟩

/-- **Morera's theorem on open sets with simply connected components.** If `U ⊆ ℂ` is open, every
connected component of `U` is simply connected, and `f : ℂ → E` is continuous and conservative on
`U`, then `f` has a complex primitive on `U`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn
    {f : ℂ → E} {U : Set ℂ} (hf : Complex.IsConservativeOn f U) (hU : IsOpen U)
    (hc : ∀ z ∈ U, IsSimplyConnected (connectedComponentIn U z)) (hcont : ContinuousOn f U) :
    Complex.IsExactOn f U := by
  have hφ := TauCeti.hasLocalPotentials_toSpanSingleton_of_isConservativeOn hU hcont hf
  obtain ⟨g, -, hg, -⟩ := hφ.exists_hasFDerivAt_of_isSimplyConnected_connectedComponentIn hc
  exact ⟨g, fun z hz ↦ by simpa using (hasFDerivAt_of_restrictScalars ℝ (hg z hz) rfl).hasDerivAt⟩

/-- **Holomorphic functions on simply connected open domains have primitives.** If `U ⊆ ℂ` is a
simply connected open set and `f : ℂ → E` is holomorphic on `U` with values in a complete complex
normed space, then `f` admits a complex primitive on `U`. -/
theorem DifferentiableOn.isExactOn_of_simplyConnected {f : ℂ → E} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) [SimplyConnectedSpace U] :
    Complex.IsExactOn f U :=
  hf.isConservativeOn.isExactOn_of_simplyConnected hU hf.continuousOn

/-- If `U ⊆ ℂ` is open and every connected component of `U` is simply connected, then every
holomorphic function `f : ℂ → E` on `U` with values in a complete complex normed space has a
complex primitive on `U`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn
    {f : ℂ → E} {U : Set ℂ} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hc : ∀ z ∈ U, IsSimplyConnected (connectedComponentIn U z)) :
    Complex.IsExactOn f U :=
  hf.isConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn hU hc hf.continuousOn

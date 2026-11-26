/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.SchwartzSpace.Subsingleton

/-!
# Bessel-potential norms on a zero-dimensional space

On a zero-dimensional space `E`, a complex-valued Schwartz function `u` is `u 0` times the
constant function `1`. Hence every complex-homogeneous map out of `𝓢(E, ℂ)` is bounded between
any two Bessel-potential norms
(`SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_le_of_subsingleton`), an instance of
`SchwartzMap.exists_norm_le_of_subsingleton` for the injective inclusion of `𝓢(E, ℂ)` into
`H^{s,p}`. This settles the zero-dimensional case of mapping estimates whose proofs in positive
dimension go through symbol estimates.
-/

public section

noncomputable section

open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace SchwartzMap

/-- **Dimension zero.** On a zero-dimensional space `E`, every complex-homogeneous map `T` from
complex-valued Schwartz functions to Schwartz functions is bounded from `H^{s,p}` to `H^{r,q}`:
there is a constant `C` with `‖T u‖_{H^{r,q}} ≤ C ‖u‖_{H^{s,p}}` for every `u`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_le_of_subsingleton [Subsingleton E]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {T : 𝓢(E, ℂ) → 𝓢(E, F)}
    (hT : ∀ (c : ℂ) u, T (c • u) = c • T u) (s r : ℝ) :
    ∃ C, ∀ u, ‖toBesselPotentialSpaceCLM r q (T u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖ := by
  simpa using exists_norm_le_of_subsingleton (toBesselPotentialSpaceCLM_injective s p)
    (T := fun u ↦ toBesselPotentialSpaceCLM r q (T u)) fun c u ↦ by simp [hT]

end SchwartzMap

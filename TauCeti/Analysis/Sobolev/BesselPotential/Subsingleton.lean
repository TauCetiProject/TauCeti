/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Bessel-potential norms on a zero-dimensional space

On a zero-dimensional space `E`, a complex-valued Schwartz function `u` is `u 0` times the
constant function `1`. Hence every complex-homogeneous map out of `𝓢(E, ℂ)` is bounded between
any two Bessel-potential norms
(`SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_le_of_subsingleton`). This settles the
zero-dimensional case of mapping estimates whose proofs in positive dimension go through symbol
estimates.
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
  -- Every `u` is `u 0 • u₁` for the constant Schwartz function `u₁ = 1`.
  let u₁ : 𝓢(E, ℂ) := HasCompactSupport.toSchwartzMap (f := fun _ ↦ (1 : ℂ))
    Set.subsingleton_of_subsingleton.isCompact contDiff_const
  have hu₁ (x : E) : u₁ x = 1 := (rfl)
  have hu (u : 𝓢(E, ℂ)) : u = u 0 • u₁ := by
    ext x
    simp [hu₁, Subsingleton.elim x 0]
  have h₁ : ‖toBesselPotentialSpaceCLM s p u₁‖ ≠ 0 := by
    rw [norm_ne_zero_iff, ← map_zero (toBesselPotentialSpaceCLM s p)]
    refine (toBesselPotentialSpaceCLM_injective s p).ne fun h ↦ ?_
    simpa [hu₁] using congr($h 0)
  refine ⟨‖toBesselPotentialSpaceCLM r q (T u₁)‖ / ‖toBesselPotentialSpaceCLM s p u₁‖,
    fun u ↦ ?_⟩
  rw [hu u, hT, map_smul, map_smul, norm_smul, norm_smul]
  exact le_of_eq (by field_simp)

end SchwartzMap

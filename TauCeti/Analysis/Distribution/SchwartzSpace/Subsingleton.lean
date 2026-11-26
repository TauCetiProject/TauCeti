/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz functions on a zero-dimensional space

On a zero-dimensional space `E`, a complex-valued Schwartz function `u` is `u 0` times the
constant function `1`. Hence every complex-homogeneous map `T` out of `𝓢(E, ℂ)` is bounded by
every norm `‖L u‖` coming from an injective linear map `L`
(`SchwartzMap.exists_norm_le_of_subsingleton`), for instance between any two Bessel-potential or
Besov norms. This settles the zero-dimensional case of mapping estimates whose proofs in positive
dimension go through symbol estimates.
-/

public section

noncomputable section

open scoped SchwartzMap

variable {E X Y G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℂ X] [SeminormedAddCommGroup Y] [NormedSpace ℂ Y]
  [FunLike G 𝓢(E, ℂ) X] [LinearMapClass G ℂ 𝓢(E, ℂ) X]

namespace SchwartzMap

/-- **Dimension zero.** On a zero-dimensional space `E`, every complex-homogeneous map `T` from
complex-valued Schwartz functions to a seminormed space is bounded by the norm `‖L u‖` for every
injective linear map `L` into a normed space: there is a constant `C` with `‖T u‖ ≤ C ‖L u‖` for
every `u`. -/
theorem exists_norm_le_of_subsingleton [Subsingleton E] {L : G} (hL : Function.Injective L)
    {T : 𝓢(E, ℂ) → Y} (hT : ∀ (c : ℂ) u, T (c • u) = c • T u) :
    ∃ C, ∀ u, ‖T u‖ ≤ C * ‖L u‖ := by
  -- Every `u` is `u 0 • u₁` for the constant Schwartz function `u₁ = 1`.
  let u₁ : 𝓢(E, ℂ) := HasCompactSupport.toSchwartzMap (f := fun _ ↦ (1 : ℂ))
    Set.subsingleton_of_subsingleton.isCompact contDiff_const
  -- `HasCompactSupport.toSchwartzMap` is the Schwartz map with underlying function `f` by
  -- definition, and Mathlib has no evaluation lemma for it.
  have hu₁ (x : E) : u₁ x = 1 := (rfl)
  have hu (u : 𝓢(E, ℂ)) : u = u 0 • u₁ := by
    ext x
    simp [hu₁, Subsingleton.elim x 0]
  have h₁ : ‖L u₁‖ ≠ 0 := by
    rw [norm_ne_zero_iff, ← map_zero L]
    refine hL.ne fun h ↦ ?_
    simpa [hu₁] using congr($h 0)
  refine ⟨‖T u₁‖ / ‖L u₁‖, fun u ↦ ?_⟩
  rw [hu u, hT, map_smul, norm_smul, norm_smul]
  exact le_of_eq (by field_simp)

end SchwartzMap

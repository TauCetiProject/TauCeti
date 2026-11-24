/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth self-maps of a punctured space

Near a nonzero point `ξ₀` of a real normed space, the identity extends to a smooth self-map of
the whole space that never takes the value `0`
(`TauCeti.exists_contDiff_ne_zero_eventuallyEq_id`). Precomposing with it turns a function that is
smooth away from `0` into a smooth function on the whole space with the same germ at `ξ₀`, without
assuming that the space carries smooth bump functions.

The map is `ξ ↦ ξ₀ + s(ξ) • (ξ - ξ₀)`, where `s` is a smooth transition from `0` to `1` in the
value of a norming functional of `ξ₀` (`exists_dual_vector`, `Real.smoothTransition`).
-/

public section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A smooth self-map of the punctured space.** Near a nonzero point `ξ₀`, the identity agrees
with a smooth self-map of the whole space that never vanishes. -/
theorem exists_contDiff_ne_zero_eventuallyEq_id {ξ₀ : E} (hξ₀ : ξ₀ ≠ 0) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ ξ, g ξ ≠ 0) ∧ g =ᶠ[𝓝 ξ₀] id := by
  -- For a functional `ℓ` with `ℓ ξ₀ = ‖ξ₀‖` and a smooth transition `s ξ` from `0` where
  -- `ℓ ξ ≤ ‖ξ₀‖ / 4` to `1` where `ℓ ξ ≥ ‖ξ₀‖ / 2`, take `g ξ = ξ₀ + s ξ • (ξ - ξ₀)`.
  have hn : 0 < ‖ξ₀‖ := norm_pos_iff.2 hξ₀
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ ξ₀ hn.ne'
  set t : E → ℝ := fun ξ ↦ 4 * (ℓ ξ / ‖ξ₀‖) - 1 with ht
  set g : E → E := fun ξ ↦ ξ₀ + Real.smoothTransition (t ξ) • (ξ - ξ₀) with hg
  refine ⟨g, contDiff_const.add <|
    (Real.smoothTransition.contDiff.comp (by fun_prop)).smul (contDiff_id.sub contDiff_const),
    fun ξ h ↦ ?_, ?_⟩
  · have hs0 := Real.smoothTransition.nonneg (t ξ)
    have hs1 := Real.smoothTransition.le_one (t ξ)
    have h0 : ‖ξ₀‖ + Real.smoothTransition (t ξ) * (ℓ ξ - ‖ξ₀‖) = 0 := by
      simpa [hg, hℓ] using congrArg ℓ h
    by_cases hξ : ℓ ξ ≤ ‖ξ₀‖ / 4
    · rw [Real.smoothTransition.zero_of_nonpos (by rw [ht]; field_simp; linarith)] at h0
      linarith
    · nlinarith [mul_le_mul_of_nonneg_left (min_le_left ‖ξ₀‖ (ℓ ξ)) (sub_nonneg.2 hs1),
        mul_le_mul_of_nonneg_left (min_le_right ‖ξ₀‖ (ℓ ξ)) hs0, lt_min hn (by linarith : 0 < ℓ ξ)]
  -- Near `ξ₀` the transition variable exceeds `1`, where the transition equals `1`.
  have h3 : 1 < t ξ₀ := by norm_num [ht, hℓ, hn.ne']
  have htc : Continuous t := by rw [ht]; fun_prop
  filter_upwards [htc.continuousAt.eventually (lt_mem_nhds h3)] with ξ hξ
  simp [hg, Real.smoothTransition.one_of_one_le hξ.le]

end TauCeti

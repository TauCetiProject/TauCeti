/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Differentiating a curve pushed through an operator family

Mathlib's `HasDerivWithinAt.clm_apply` differentiates `y ↦ T y (u y)` when the operator family
`T` is differentiable in operator norm. Families of evolution operators, such as the propagators
of the wave or heat equations, are usually only strongly differentiable, and only on a dense
domain. This file proves the product rule under the weaker hypotheses that are actually
available: `T` is locally bounded in operator norm, `y ↦ T y v` is continuous at `x` for the
derivative `v = u'` of the curve, and `y ↦ T y (u x)` is differentiable at `x` for the one point
`u x` of the curve. Then `y ↦ T y (u y)` has derivative `d + T x u'`, where `d` is the derivative
of `y ↦ T y (u x)`.

## Main results

* `HasDerivWithinAt.clm_apply_of_tendsto`: the product rule for a locally bounded, strongly
  continuous operator family.
-/

public section

open Filter Asymptotics
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T : 𝕜 → E →L[𝕜] F} {u : 𝕜 → E} {u' : E} {d : F} {s : Set 𝕜} {x : 𝕜} {M : ℝ}

/-- **The product rule for strongly continuous operator families.** If `T` is bounded in operator
norm near `x`, `y ↦ T y u'` is continuous at `x`, `u` has derivative `u'` and `y ↦ T y (u x)` has
derivative `d` at `x`, then `y ↦ T y (u y)` has derivative `d + T x u'` at `x`. -/
theorem HasDerivWithinAt.clm_apply_of_tendsto (hT : HasDerivWithinAt (fun y ↦ T y (u x)) d s x)
    (hu : HasDerivWithinAt u u' s x) (hTu' : Tendsto (fun y ↦ T y u') (𝓝[s] x) (𝓝 (T x u')))
    (hM : ∀ᶠ y in 𝓝[s] x, ‖T y‖ ≤ M) :
    HasDerivWithinAt (fun y ↦ T y (u y)) (d + T x u') s x := by
  rw [hasDerivWithinAt_iff_isLittleO] at hT hu ⊢
  -- `T y` applied to the remainder of `u` is small, since `T y` is bounded near `x`.
  have h₁ : (fun y ↦ T y (u y - u x - (y - x) • u')) =o[𝓝[s] x] fun y ↦ y - x :=
    (IsBigO.of_bound M (hM.mono fun y hy ↦ ((T y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hy (norm_nonneg _)))).trans_isLittleO hu
  -- The strong continuity of `T` at `u'` makes `(y - x) • (T y u' - T x u')` small.
  have h₂ : (fun y ↦ (y - x) • (T y u' - T x u')) =o[𝓝[s] x] fun y ↦ y - x := by
    have := (isBigO_refl (fun y ↦ y - x) (𝓝[s] x)).smul_isLittleO
      ((isLittleO_one_iff 𝕜).2 (tendsto_sub_nhds_zero_iff.2 hTu'))
    simpa using this
  refine ((h₁.add h₂).add hT).congr_left fun y ↦ ?_
  simp only [map_sub, map_smul, smul_sub, smul_add]
  abel

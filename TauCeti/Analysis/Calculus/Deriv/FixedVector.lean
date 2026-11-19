/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Fixed vectors of a differentiable family of operators near the identity

Let `A : 𝕜 → E →L[𝕜] E` be a family of operators on a normed space with `A t₀ = 1` and
derivative `L` at `t₀`, so that `A t = 1 + (t - t₀) L + o(t - t₀)`. If `L` is antilipschitz, then
for `t ≠ t₀` close to `t₀` the operator `A t` fixes no nonzero vector
(`HasDerivAt.eventually_eq_zero_of_apply_eq_self_of_antilipschitzWith`): `1` is not an eigenvalue
of `A t`. On a finite-dimensional space over a complete field, an injective `L` is antilipschitz
(`HasDerivAt.eventually_eq_zero_of_apply_eq_self`).

For instance, if `L` is injective then `exp (t L)` fixes no nonzero vector for small `t ≠ 0`. The
statement needs only the first-order expansion, so it applies to the differential of the time-`t`
map of a flow at a rest point, whose derivative in `t` at `t = 0` is the linearization of the vector
field. This is how rest points with invertible linearization become nondegenerate fixed points of
the short-time maps of the flow.

If moreover `A` is a one-parameter group, `A (s + t) = A s ∘ A t` with `A 0 = 1`, then its
generator `L` kills exactly the vectors fixed by every `A t`
(`HasDerivAt.apply_eq_zero_iff_forall_apply_eq_self`).
-/

public section

open Filter Topology
open scoped NNReal

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **No fixed vectors near the identity.** Let `A : 𝕜 → E →L[𝕜] E` have derivative `L` at `t₀`,
with `A t₀ = 1`. If `L` is antilipschitz, then for every `t ≠ t₀` close to `t₀` the only vector
fixed by `A t` is `0`. -/
theorem HasDerivAt.eventually_eq_zero_of_apply_eq_self_of_antilipschitzWith
    {A : 𝕜 → E →L[𝕜] E} {L : E →L[𝕜] E} {t₀ : 𝕜} {K : ℝ≥0} (hL : HasDerivAt A L t₀)
    (hA : A t₀ = ContinuousLinearMap.id 𝕜 E) (hK : AntilipschitzWith K L) :
    ∀ᶠ t in 𝓝[≠] t₀, ∀ w, A t w = w → w = 0 := by
  have hKpos : (0 : ℝ) < K + 1 := by positivity
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hL
  filter_upwards [nhdsWithin_le_nhds (hL (c := 1 / (2 * (K + 1))) (by positivity)),
    self_mem_nhdsWithin] with t ht htne w hw
  have hτ : 0 < ‖t - t₀‖ := norm_pos_iff.2 (sub_ne_zero.2 htne)
  -- On a fixed vector the remainder of the first-order expansion is `-(t - t₀) • L w`, which the
  -- expansion makes small compared with `‖t - t₀‖ ‖w‖`, while `L` keeps it large.
  have hrem : (A t - A t₀ - (t - t₀) • L) w = -((t - t₀) • L w) := by
    simp [hw, hA]
  have hbound : ‖t - t₀‖ * ‖L w‖ ≤ 1 / (2 * (K + 1)) * ‖t - t₀‖ * ‖w‖ := by
    have h := (A t - A t₀ - (t - t₀) • L).le_of_opNorm_le ht w
    rwa [hrem, norm_neg, norm_smul] at h
  have hw' : ‖w‖ ≤ (K + 1) * ‖L w‖ := by
    have h : ‖w‖ ≤ K * ‖L w‖ := by simpa using hK.le_mul_dist w 0
    nlinarith [norm_nonneg (L w)]
  have hLw : ‖L w‖ ≤ ‖L w‖ / 2 := by
    have h1 : 1 / (2 * (K + 1)) * ‖t - t₀‖ * ‖w‖ ≤ ‖t - t₀‖ * (‖L w‖ / 2) := by
      calc 1 / (2 * (K + 1)) * ‖t - t₀‖ * ‖w‖
          ≤ 1 / (2 * (K + 1)) * ‖t - t₀‖ * ((K + 1) * ‖L w‖) := by gcongr
        _ = ‖t - t₀‖ * (‖L w‖ / 2) := by field_simp
    exact le_of_mul_le_mul_left (hbound.trans h1) hτ
  have hLw0 : L w = 0 := norm_le_zero_iff.1 (by linarith [norm_nonneg (L w)])
  exact hK.injective (by rw [hLw0, map_zero])

/-- **No fixed vectors near the identity, finite-dimensional case.** Let `A : 𝕜 → E →L[𝕜] E` have
derivative `L` at `t₀`, with `A t₀ = 1`, on a finite-dimensional space over a complete field. If `L`
is injective, then for every `t ≠ t₀` close to `t₀` the only vector fixed by `A t` is `0`. -/
theorem HasDerivAt.eventually_eq_zero_of_apply_eq_self [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {A : 𝕜 → E →L[𝕜] E} {L : E →L[𝕜] E} {t₀ : 𝕜} (hL : HasDerivAt A L t₀)
    (hA : A t₀ = ContinuousLinearMap.id 𝕜 E) (hinj : Function.Injective L) :
    ∀ᶠ t in 𝓝[≠] t₀, ∀ w, A t w = w → w = 0 := by
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz (L : E →ₗ[𝕜] E)).1 hinj
  exact hL.eventually_eq_zero_of_apply_eq_self_of_antilipschitzWith hA hK

section OneParameterGroup

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Fixed vectors of a one-parameter group of operators.** Let `D : 𝕜 → F →L[𝕜] F` satisfy
`D 0 = 1` and `D (s + t) = D s ∘ D t`, with derivative `L` at `0`. Then a vector is killed by the
generator `L` exactly when it is fixed by every `D t`. -/
theorem HasDerivAt.apply_eq_zero_iff_forall_apply_eq_self {D : 𝕜 → F →L[𝕜] F} {L : F →L[𝕜] F}
    (hL : HasDerivAt D L 0) (hD0 : D 0 = ContinuousLinearMap.id 𝕜 F)
    (hadd : ∀ s t, D (s + t) = (D s).comp (D t)) (v : F) :
    L v = 0 ↔ ∀ t, D t v = v := by
  have hDv : HasDerivAt (fun t ↦ D t v) (L v) 0 := by
    simpa using hL.clm_apply (hasDerivAt_const (0 : 𝕜) v)
  constructor
  · -- If `L v = 0`, then `t ↦ D t v` has derivative `D t (L v) = 0` at every `t`, because
    -- `D u = D t ∘ D (u - t)`; so it is the constant `D 0 v = v`.
    intro hv
    have hderiv (t : 𝕜) : HasDerivAt (fun u ↦ D u v) 0 t := by
      have hg := (D t).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hDv
      rw [hv, map_zero, ← sub_self t] at hg
      refine (hg.comp_sub_const t t).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun u ↦ ?_)
      simp [← ContinuousLinearMap.comp_apply, ← hadd]
    intro t
    simpa [hD0] using is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
      (fun u ↦ (hderiv u).deriv) t 0
  · -- If every `D t` fixes `v`, then `t ↦ D t v` is constant, so its derivative `L v` vanishes.
    intro hv
    exact hDv.unique ((hasDerivAt_const (0 : 𝕜) v).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hv))

end OneParameterGroup

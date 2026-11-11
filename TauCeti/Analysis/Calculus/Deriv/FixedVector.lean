/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Fixed vectors of a differentiable family of operators near the identity

Let `A : ℝ → E →L[ℝ] E` be a family of operators on a finite-dimensional real normed space with
`A t₀ = 1` and derivative `L` at `t₀`, so that `A t = 1 + (t - t₀) L + o(t - t₀)`. If `L` is
injective, then for `t ≠ t₀` close to `t₀` the operator `A t` fixes no nonzero vector
(`HasDerivAt.eventually_eq_zero_of_apply_eq_self`): `1` is not an eigenvalue of `A t`.

For `A t = exp (t L)` this recovers the fact that the fixed vectors of `exp (t L)` are the kernel
of `L` for small `t`. The statement needs only the first-order expansion, so it applies to the
differential of the time-`t` map of a flow at a rest point, whose derivative in `t` at `t = 0` is
the linearization of the vector field. This is how rest points with invertible linearization
become nondegenerate fixed points of the short-time maps of the flow.
-/

public section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **No fixed vectors near the identity.** Let `A : ℝ → E →L[ℝ] E` have derivative `L` at `t₀`,
with `A t₀ = 1`, on a finite-dimensional space. If `L` is injective, then for every `t ≠ t₀` close
to `t₀` the only vector fixed by `A t` is `0`. -/
theorem HasDerivAt.eventually_eq_zero_of_apply_eq_self {A : ℝ → E →L[ℝ] E} {L : E →L[ℝ] E}
    {t₀ : ℝ} (hL : HasDerivAt A L t₀) (hA : A t₀ = ContinuousLinearMap.id ℝ E)
    (hinj : Function.Injective L) :
    ∀ᶠ t in 𝓝[≠] t₀, ∀ w, A t w = w → w = 0 := by
  obtain ⟨K, hK, hKL⟩ := (LinearMap.injective_iff_antilipschitz (L : E →ₗ[ℝ] E)).1 hinj
  have hKpos : (0 : ℝ) < K := hK
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hL
  filter_upwards [nhdsWithin_le_nhds (hL (c := 1 / (2 * K)) (by positivity)),
    self_mem_nhdsWithin] with t ht htne w hw
  have hτ : 0 < |t - t₀| := abs_pos.2 (sub_ne_zero.2 htne)
  -- On a fixed vector the remainder of the first-order expansion is `-(t - t₀) • L w`, which the
  -- expansion makes small compared with `|t - t₀| ‖w‖`, while `L` keeps it large.
  have hrem : (A t - A t₀ - (t - t₀) • L) w = -((t - t₀) • L w) := by
    simp [hw, hA]
  have hbound : |t - t₀| * ‖L w‖ ≤ 1 / (2 * K) * |t - t₀| * ‖w‖ := by
    have h := (A t - A t₀ - (t - t₀) • L).le_of_opNorm_le ht w
    rwa [hrem, norm_neg, norm_smul, Real.norm_eq_abs] at h
  have hw' : ‖w‖ ≤ K * ‖L w‖ := by
    simpa using hKL.le_mul_dist w 0
  have hLw : ‖L w‖ ≤ ‖L w‖ / 2 := by
    have h1 : 1 / (2 * K) * |t - t₀| * ‖w‖ ≤ |t - t₀| * (‖L w‖ / 2) := by
      calc 1 / (2 * K) * |t - t₀| * ‖w‖ ≤ 1 / (2 * K) * |t - t₀| * (K * ‖L w‖) := by gcongr
        _ = |t - t₀| * (‖L w‖ / 2) := by field_simp
    exact le_of_mul_le_mul_left (hbound.trans h1) hτ
  have hLw0 : L w = 0 := norm_le_zero_iff.1 (by linarith [norm_nonneg (L w)])
  exact hinj (by rw [hLw0, map_zero])

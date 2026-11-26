/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# Positive tangent cones, normals and nearest points

In a real inner product space, a vector `n` is an outward normal of a set `s` at `y` when
`⟪n, k - y⟫ ≤ 0` for every `k ∈ s`. Such a normal pairs nonpositively with every positive tangent
vector of `s` at `y`, since `y` is then a local maximum of `⟪n, ·⟫` on `s`.

The same first-variation argument applied to the squared distance shows that the residual `M - x`
from a local nearest point `x` of `s` to `M` is orthogonal to every two-sided tangent vector of `s`
at `x`. Dually, a retraction onto `s` that is constant along short segments normal to a subspace of
tangent vectors has derivative the orthogonal projection onto that subspace.

## Main results

* `TauCeti.real_inner_le_zero_of_mem_posTangentConeAt`: an outward normal of a set pairs
  nonpositively with its positive tangent vectors.
* `TauCeti.real_inner_sub_eq_zero_of_isLocalMinOn_dist`: first variation of the distance to a set.
* `TauCeti.fderiv_eq_starProjection_of_eventually_add_smul`: the derivative of a retraction that is
  constant along normal segments is an orthogonal projection.
-/

public section

open Filter Set
open scoped RealInnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace TauCeti

/-- An outward normal `n` of a set `s` at `y`, in the sense that `⟪n, k - y⟫ ≤ 0` for every
`k ∈ s`, pairs nonpositively with every positive tangent vector of `s` at `y`. -/
theorem real_inner_le_zero_of_mem_posTangentConeAt {s : Set E} {y n w : E}
    (hn : ∀ k ∈ s, ⟪n, k - y⟫ ≤ 0) (hw : w ∈ posTangentConeAt s y) : ⟪n, w⟫ ≤ 0 := by
  have hmax : IsLocalMaxOn (innerSL ℝ n) s y :=
    eventually_nhdsWithin_of_forall fun k hk ↦ by
      simpa [innerSL_apply_apply, inner_sub_right] using hn k hk
  simpa using hmax.hasFDerivWithinAt_nonpos (innerSL ℝ n).hasFDerivWithinAt hw

/-- **First variation of the distance to a set.** If `x` is, locally in `s`, a nearest point of `s`
to `M`, the residual `M - x` is orthogonal to every vector `w` such that `w` and `-w` are positive
tangent vectors of `s` at `x`. -/
theorem real_inner_sub_eq_zero_of_isLocalMinOn_dist {s : Set E} {x M w : E}
    (h : IsLocalMinOn (dist M) s x) (hw : w ∈ posTangentConeAt s x)
    (hw' : -w ∈ posTangentConeAt s x) : ⟪M - x, w⟫ = 0 := by
  -- The squared distance `y ↦ ‖y - M‖²` also has a local minimum at `x` on `s`.
  have hmin2 : IsLocalMinOn (fun y : E ↦ ‖y - M‖ ^ 2) s x :=
    Filter.Eventually.mono h fun y (hy : dist M x ≤ dist M y) ↦ by
      simp only [← dist_eq_norm, dist_comm _ M]
      exact pow_le_pow_left₀ dist_nonneg hy 2
  have h0 := hmin2.hasFDerivWithinAt_eq_zero
    ((hasFDerivAt_id x).sub_const M).norm_sq.hasFDerivWithinAt hw hw'
  simp only [smul_apply, id_eq, nsmul_eq_mul, Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or] at h0
  rw [← neg_sub, inner_neg_left, neg_eq_zero]
  exact h0

/-- **The derivative of a retraction that is constant along normal segments.** Let `K` be a
subspace of tangent vectors of `s` at `x ∈ s`. If `r` is differentiable at `x`, fixes every point
of `s`, and satisfies `r (x + t • v) = x` for every `v` orthogonal to `K` and every small `t`, then
its derivative at `x` is the orthogonal projection onto `K`. -/
theorem fderiv_eq_starProjection_of_eventually_add_smul {s : Set E} {r : E → E} {x : E}
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (hK : (K : Set E) ⊆ tangentConeAt ℝ s x)
    (hr : DifferentiableAt ℝ r x) (hrs : EqOn r id s) (hx : x ∈ s)
    (hnormal : ∀ v ∈ Kᗮ, ∀ᶠ t in 𝓝 (0 : ℝ), r (x + t • v) = x) :
    fderiv ℝ r x = K.starProjection := by
  refine ContinuousLinearMap.ext fun V ↦ ?_
  -- Split `V` into its tangential and normal parts; `r` is constant along the normal one.
  have h0 : fderiv ℝ r x (V - K.starProjection V) = 0 :=
    (hr.hasFDerivAt.hasLineDerivAt _).unique ((hasDerivAt_const (0 : ℝ) (r x)).congr_of_eventuallyEq
      (by filter_upwards [hnormal _ (K.sub_starProjection_mem_orthogonal V)] with t ht
          using ht.trans (hrs hx).symm))
  rwa [map_sub, sub_eq_zero, fderiv_apply_eq_self_of_mem_tangentConeAt hr hrs hx
    (hK (K.starProjection_apply_mem V))] at h0

end TauCeti

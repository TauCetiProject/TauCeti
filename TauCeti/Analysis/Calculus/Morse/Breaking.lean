/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.Convergence
public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Dynamics.Flow.Breaking
-- Private: used only to compare the gradient with the differential.
import TauCeti.Analysis.Calculus.Gradient
-- Private: used for index drop and discreteness of trajectory slices.
import TauCeti.Analysis.Calculus.Morse.TrajectorySpace

/-!
# Negative gradient trajectories break at nondegenerate critical points

A negative gradient trajectory trapped, in forward time, in a closed ball containing no critical
point other than its centre `x` converges to `x`; the same holds in backward time. So the radius of
such a ball isolates `x` in the sense of `TauCeti.Dynamics.Flow.Breaking`, and every sufficiently
small radius about a nondegenerate critical point does.

Feeding this into `Flow.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet` gives the
elementary step of the compactness theorem for spaces of Morse trajectories. If trajectories
converging to a critical point `q` accumulate on a trajectory converging instead to a nondegenerate
critical point `x ≠ q`, then they also accumulate on a nonconstant trajectory leaving `x`: the limit
is a trajectory broken at `x`. In terms of sets, the closure of the stable set `W^s(q)` meets the
unstable set `W^u(x)` on every small sphere about `x`. The time-reversed statement holds for
unstable sets.

## Main declarations

* `Flow.IsNegativeGradient.mem_stableSet_of_forall_mem_closedBall` and
  `Flow.IsNegativeGradient.mem_unstableSet_of_forall_mem_closedBall`: a trajectory trapped in a
  closed ball whose only critical point is its centre converges to the centre.
* `TauCeti.IsNondegenerateCriticalPoint.eventually_forall_mem_stableSet_of_forall_mem_closedBall`
  and its unstable counterpart: every small radius about a nondegenerate critical point isolates
  it.
* `TauCeti.IsNondegenerateCriticalPoint.eventually_exists_mem_closure_stableSet_inter_unstableSet`
  and its time reversal
  `TauCeti.IsNondegenerateCriticalPoint.eventually_exists_mem_closure_unstableSet_inter_stableSet`:
  limits of trajectories break at a nondegenerate critical point.
* `TauCeti.IsNondegenerateCriticalPoint.morseIndex_lt_of_mem_closure_stableSet_inter_stableSet`
  and its time reversal: iterating breaks through convergent Morse--Smale trajectories strictly
  lowers the Morse index.
* `TauCeti.IsNondegenerateCriticalPoint.isClosed_unstableSet_inter_stableSet_inter_level` and
  `finite_unstableSet_inter_stableSet_inter_level`: an index-one trajectory slice is closed, and
  is finite when it is contained in a compact set.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories).
-/

public section

open Filter Metric Set Topology
open scoped Gradient NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {x : E} {r : ℝ}

namespace Flow

/-- **A trajectory trapped near an isolated critical point converges to it.** If `f` is
differentiable with continuous gradient on `closedBall x r`, and `x` is the only critical point of
`f` in that ball, then a negative gradient trajectory staying in the ball at all nonnegative times
converges to `x`. -/
theorem IsNegativeGradient.mem_stableSet_of_forall_mem_closedBall (hφ : IsNegativeGradient φ f)
    (hdiff : ∀ y ∈ closedBall x r, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) (closedBall x r)) (hcrit : ∀ y ∈ closedBall x r, ∇ f y = 0 → y = x)
    {w : E} (hw : ∀ t, 0 ≤ t → φ t w ∈ closedBall x r) : w ∈ stableSet φ x := by
  obtain ⟨p, hp, hp0, hlim⟩ := TauCeti.IsIntegralCurveOn.exists_tendsto_atTop
    ((hφ.isIntegralCurve w).isIntegralCurveOn _) (isCompact_closedBall x r) hw hdiff hgrad
    ((finite_singleton x).subset fun y hy ↦ hcrit y hy.1 hy.2)
  exact mem_stableSet.2 (hcrit p hp hp0 ▸ hlim)

/-- **A trajectory trapped near an isolated critical point converges to it in backward time.** The
backward-time counterpart of `Flow.IsNegativeGradient.mem_stableSet_of_forall_mem_closedBall`. -/
theorem IsNegativeGradient.mem_unstableSet_of_forall_mem_closedBall (hφ : IsNegativeGradient φ f)
    (hdiff : ∀ y ∈ closedBall x r, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) (closedBall x r)) (hcrit : ∀ y ∈ closedBall x r, ∇ f y = 0 → y = x)
    {w : E} (hw : ∀ t, t ≤ 0 → φ t w ∈ closedBall x r) : w ∈ unstableSet φ x := by
  obtain ⟨p, hp, hp0, hlim⟩ := TauCeti.IsIntegralCurveOn.exists_tendsto_atBot
    ((hφ.isIntegralCurve w).isIntegralCurveOn _) (isCompact_closedBall x r) hw hdiff hgrad
    ((finite_singleton x).subset fun y hy ↦ hcrit y hy.1 hy.2)
  exact mem_unstableSet.2 (hcrit p hp hp0 ▸ hlim)

end Flow

namespace TauCeti

namespace IsNondegenerateCriticalPoint

/-- Every small closed ball about a nondegenerate critical point carries the regularity used by the
convergence theorem and contains no other critical point. -/
private theorem eventually_closedBall (h : IsNondegenerateCriticalPoint f x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), (∀ y ∈ closedBall x r, DifferentiableAt ℝ f y) ∧
      ContinuousOn (∇ f) (closedBall x r) ∧ ∀ y ∈ closedBall x r, ∇ f y = 0 → y = x := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((h.contDiffAt.eventually (by simp)).and
      (eventually_nhdsWithin_iff.1 h.eventually_fderiv_ne_zero))
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  have hsub (y : E) (hy : y ∈ closedBall x r) : y ∈ ball x ε :=
    mem_ball.2 ((mem_closedBall.1 hy).trans_lt hr.2)
  have hgradfun : (∇ f : E → E) = fun y ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y) := by
    funext y
    exact (InnerProductSpace.toDual ℝ E).eq_symm_apply.2 toDual_gradient
  refine ⟨fun y hy ↦ (hball y (hsub y hy)).1.differentiableAt (by simp), fun y hy ↦ ?_,
    fun y hy hy0 ↦ by_contra fun hyx ↦ (hball y (hsub y hy)).2 hyx ?_⟩
  · rw [hgradfun]
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.comp
      ((hball y (hsub y hy)).1.continuousAt_fderiv two_ne_zero)).continuousWithinAt
  · rw [← norm_eq_zero, ← norm_gradient_eq_norm_fderiv, hy0, norm_zero]

/-- **Small balls isolate a nondegenerate critical point in forward time.** For every sufficiently
small `r > 0`, a negative gradient trajectory staying in `closedBall x r` at all nonnegative times
converges to the nondegenerate critical point `x`. -/
theorem eventually_forall_mem_stableSet_of_forall_mem_closedBall
    (h : IsNondegenerateCriticalPoint f x) (hφ : Flow.IsNegativeGradient φ f) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ w, (∀ t, 0 ≤ t → φ t w ∈ closedBall x r) → w ∈ Flow.stableSet φ x := by
  filter_upwards [h.eventually_closedBall] with r ⟨hdiff, hgrad, hcrit⟩ w hw
  exact hφ.mem_stableSet_of_forall_mem_closedBall hdiff hgrad hcrit hw

/-- **Small balls isolate a nondegenerate critical point in backward time.** For every
sufficiently small `r > 0`, a negative gradient trajectory staying in `closedBall x r` at all
nonpositive times converges to the nondegenerate critical point `x` in backward time. -/
theorem eventually_forall_mem_unstableSet_of_forall_mem_closedBall
    (h : IsNondegenerateCriticalPoint f x) (hφ : Flow.IsNegativeGradient φ f) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ w, (∀ t, t ≤ 0 → φ t w ∈ closedBall x r) → w ∈ Flow.unstableSet φ x := by
  filter_upwards [h.eventually_closedBall] with r ⟨hdiff, hgrad, hcrit⟩ w hw
  exact hφ.mem_unstableSet_of_forall_mem_closedBall hdiff hgrad hcrit hw

/-- **Limits of trajectories break at a nondegenerate critical point.** Let `x` be a nondegenerate
critical point and `q ≠ x`. If a point `y` of the stable set of `x` is a limit of points of the
stable set of `q`, then for every sufficiently small `r > 0` some point at distance `r` from `x`
lies both in the unstable set of `x` and in the closure of the stable set of `q`. -/
theorem eventually_exists_mem_closure_stableSet_inter_unstableSet
    (h : IsNondegenerateCriticalPoint f x) (hφ : Flow.IsNegativeGradient φ f) {q : E}
    (hqx : q ≠ x) {y : E} (hy : y ∈ closure (Flow.stableSet φ q) ∩ Flow.stableSet φ x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∃ z ∈ closure (Flow.stableSet φ q) ∩ Flow.unstableSet φ x, dist z x = r := by
  filter_upwards [self_mem_nhdsWithin,
    h.eventually_forall_mem_stableSet_of_forall_mem_closedBall hφ,
    h.eventually_forall_mem_unstableSet_of_forall_mem_closedBall hφ] with r hr hfwd hbwd
  exact Flow.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet (mem_Ioi.1 hr)
    hfwd hbwd (Flow.isInvariant_stableSet φ q) (Flow.disjoint_stableSet hqx) hy

/-- **Limits of trajectories break at a nondegenerate critical point, in backward time.** Let `x` be
a nondegenerate critical point and `p ≠ x`. If a point `y` of the unstable set of `x` is a limit of
points of the unstable set of `p`, then for every sufficiently small `r > 0` some point at distance
`r` from `x` lies both in the stable set of `x` and in the closure of the unstable set of `p`. -/
theorem eventually_exists_mem_closure_unstableSet_inter_stableSet
    (h : IsNondegenerateCriticalPoint f x) (hφ : Flow.IsNegativeGradient φ f) {p : E}
    (hpx : p ≠ x) {y : E} (hy : y ∈ closure (Flow.unstableSet φ p) ∩ Flow.unstableSet φ x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∃ z ∈ closure (Flow.unstableSet φ p) ∩ Flow.stableSet φ x, dist z x = r := by
  filter_upwards [self_mem_nhdsWithin,
    h.eventually_forall_mem_stableSet_of_forall_mem_closedBall hφ,
    h.eventually_forall_mem_unstableSet_of_forall_mem_closedBall hφ] with r hr hfwd hbwd
  exact Flow.exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet (mem_Ioi.1 hr)
    hfwd hbwd (Flow.isInvariant_unstableSet φ p) (Flow.disjoint_unstableSet hpx) hy

end IsNondegenerateCriticalPoint

/-! ### Morse-index control along broken limits -/

variable {K : ℝ≥0}

/-- Find the next critical point after a break in a forward limit. The positive-distance
condition furnished by the breaking theorem and the absence of nonconstant homoclinic gradient
trajectories ensure that it differs from the point where the break occurred. -/
private theorem exists_nextCriticalPoint_of_mem_closure_stableSet_inter_stableSet
    (hx : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {q y : E} (hqx : q ≠ x)
    (hy : y ∈ closure (Flow.stableSet (negativeGradientFlow f hf) q) ∩
      Flow.stableSet (negativeGradientFlow f hf) x)
    (hconv : ∀ {z}, z ∈ closure (Flow.stableSet (negativeGradientFlow f hf) q) →
      ∃ a, IsNondegenerateCriticalPoint f a ∧
        z ∈ Flow.stableSet (negativeGradientFlow f hf) a) :
    ∃ a z, IsNondegenerateCriticalPoint f a ∧ a ≠ x ∧
      z ∈ closure (Flow.stableSet (negativeGradientFlow f hf) q) ∩
        Flow.unstableSet (negativeGradientFlow f hf) x ∧
      z ∈ Flow.stableSet (negativeGradientFlow f hf) a := by
  let _ : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot_of_exists_gt ⟨1, zero_lt_one⟩
  have hbreak := hx.eventually_exists_mem_closure_stableSet_inter_unstableSet
    (isNegativeGradient_negativeGradientFlow f hf) hqx hy
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, z, hz, hzr⟩ := (hpos.and hbreak).exists
  obtain ⟨a, ha, hza⟩ := hconv hz.1
  refine ⟨a, z, ha, ?_, hz, hza⟩
  intro hax
  subst a
  have hzx : z = x := Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
    (isNegativeGradient_negativeGradientFlow f hf)
      (fun t ↦ (hfs.differentiable (by norm_num)).differentiableAt)
      hfs.continuous.continuousAt ⟨hz.2, hza⟩
  rw [hzx, dist_self] at hzr
  exact (ne_of_gt hr) hzr.symm

/-- Find the preceding critical point after a break in a backward limit. This is the time-reversed
counterpart of `exists_nextCriticalPoint_of_mem_closure_stableSet_inter_stableSet`. -/
private theorem exists_prevCriticalPoint_of_mem_closure_unstableSet_inter_unstableSet
    (hx : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {p y : E} (hpx : p ≠ x)
    (hy : y ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p) ∩
      Flow.unstableSet (negativeGradientFlow f hf) x)
    (hconv : ∀ {z}, z ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p) →
      ∃ a, IsNondegenerateCriticalPoint f a ∧
        z ∈ Flow.unstableSet (negativeGradientFlow f hf) a) :
    ∃ a z, IsNondegenerateCriticalPoint f a ∧ a ≠ x ∧
      z ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p) ∩
        Flow.stableSet (negativeGradientFlow f hf) x ∧
      z ∈ Flow.unstableSet (negativeGradientFlow f hf) a := by
  let _ : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot_of_exists_gt ⟨1, zero_lt_one⟩
  have hbreak := hx.eventually_exists_mem_closure_unstableSet_inter_stableSet
    (isNegativeGradient_negativeGradientFlow f hf) hpx hy
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, z, hz, hzr⟩ := (hpos.and hbreak).exists
  obtain ⟨a, ha, hza⟩ := hconv hz.1
  refine ⟨a, z, ha, ?_, hz, hza⟩
  intro hax
  subst a
  have hzx : z = x := Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
    (isNegativeGradient_negativeGradientFlow f hf)
      (fun t ↦ (hfs.differentiable (by norm_num)).differentiableAt)
      hfs.continuous.continuousAt ⟨hza, hz.2⟩
  rw [hzx, dist_self] at hzr
  exact (ne_of_gt hr) hzr.symm

namespace IsNondegenerateCriticalPoint

/-- **Morse index drops along a broken forward limit.** Suppose every point in the closure of
`Wˢ(q)` converges forward to a nondegenerate critical point, and all connecting stable and
unstable manifolds meet transversally. If that closure meets `Wˢ(x)` for `x ≠ q`, then the
Morse index of `q` is strictly smaller than that of `x`. -/
theorem morseIndex_lt_of_mem_closure_stableSet_inter_stableSet
    (hx : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hqx : q ≠ x)
    (hy : (closure (Flow.stableSet (negativeGradientFlow f hf) q) ∩
      Flow.stableSet (negativeGradientFlow f hf) x).Nonempty)
    (hconv : ∀ {z}, z ∈ closure (Flow.stableSet (negativeGradientFlow f hf) q) →
      ∃ a, IsNondegenerateCriticalPoint f a ∧
        z ∈ Flow.stableSet (negativeGradientFlow f hf) a)
    (htr : ∀ {a b z}, IsNondegenerateCriticalPoint f a →
      IsNondegenerateCriticalPoint f b →
      z ∈ Flow.unstableSet (negativeGradientFlow f hf) a →
      z ∈ Flow.stableSet (negativeGradientFlow f hf) b →
      Submodule.span ℝ (tangentConeAt ℝ
          (Flow.unstableSet (negativeGradientFlow f hf) a) z) ⊔
        Submodule.span ℝ (tangentConeAt ℝ
          (Flow.stableSet (negativeGradientFlow f hf) b) z) = ⊤) :
    morseIndex f q < morseIndex f x := by
  -- Iterate the one-break theorem. At every new limiting critical point, Morse--Smale
  -- transversality strictly lowers the index, so strong induction on the index forces the chain
  -- to terminate at `q`.
  have H : ∀ n x, morseIndex f x = n → IsNondegenerateCriticalPoint f x → q ≠ x →
      (closure (Flow.stableSet (negativeGradientFlow f hf) q) ∩
        Flow.stableSet (negativeGradientFlow f hf) x).Nonempty →
      morseIndex f q < morseIndex f x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hxn hx hqx hy
        obtain ⟨y, hy⟩ := hy
        obtain ⟨a, z, ha, hax, hzq, hza⟩ :=
          exists_nextCriticalPoint_of_mem_closure_stableSet_inter_stableSet
            hx hfs hf hqx hy hconv
        have hxa : morseIndex f a < morseIndex f x :=
          hx.morseIndex_lt_of_mem_unstableSet_inter_stableSet ha hfs hf hax.symm
            hzq.2 hza (htr hx ha hzq.2 hza)
        by_cases haq : a = q
        · simpa only [haq] using hxa
        · exact (ih (morseIndex f a) (hxn ▸ hxa) a rfl ha (fun h ↦ haq h.symm)
            ⟨z, hzq.1, hza⟩).trans hxa
  exact H (morseIndex f x) x rfl hx hqx hy

/-- **Morse index drops along a broken backward limit.** Suppose every point in the closure of
`Wᵘ(p)` converges backward to a nondegenerate critical point, and all connecting stable and
unstable manifolds meet transversally. If that closure meets `Wᵘ(x)` for `x ≠ p`, then the
Morse index of `x` is strictly smaller than that of `p`. This is the backward counterpart of
`morseIndex_lt_of_mem_closure_stableSet_inter_stableSet`. -/
theorem morseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet
    (hx : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hpx : p ≠ x)
    (hy : (closure (Flow.unstableSet (negativeGradientFlow f hf) p) ∩
      Flow.unstableSet (negativeGradientFlow f hf) x).Nonempty)
    (hconv : ∀ {z}, z ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p) →
      ∃ a, IsNondegenerateCriticalPoint f a ∧
        z ∈ Flow.unstableSet (negativeGradientFlow f hf) a)
    (htr : ∀ {a b z}, IsNondegenerateCriticalPoint f a →
      IsNondegenerateCriticalPoint f b →
      z ∈ Flow.unstableSet (negativeGradientFlow f hf) a →
      z ∈ Flow.stableSet (negativeGradientFlow f hf) b →
      Submodule.span ℝ (tangentConeAt ℝ
          (Flow.unstableSet (negativeGradientFlow f hf) a) z) ⊔
        Submodule.span ℝ (tangentConeAt ℝ
          (Flow.stableSet (negativeGradientFlow f hf) b) z) = ⊤) :
    morseIndex f x < morseIndex f p := by
  -- Induct on the codimension of the unstable manifold, which decreases at every preceding
  -- critical point.
  let d := Module.finrank ℝ E
  have H : ∀ n x, d - morseIndex f x = n → IsNondegenerateCriticalPoint f x → p ≠ x →
      (closure (Flow.unstableSet (negativeGradientFlow f hf) p) ∩
        Flow.unstableSet (negativeGradientFlow f hf) x).Nonempty →
      morseIndex f x < morseIndex f p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hxn hx hpx hy
        obtain ⟨y, hy⟩ := hy
        obtain ⟨a, z, ha, hax, hzp, hza⟩ :=
          exists_prevCriticalPoint_of_mem_closure_unstableSet_inter_unstableSet
            hx hfs hf hpx hy hconv
        have hxa : morseIndex f x < morseIndex f a :=
          ha.morseIndex_lt_of_mem_unstableSet_inter_stableSet hx hfs hf hax
            hza hzp.2 (htr ha hx hza hzp.2)
        have hcodim : d - morseIndex f a < d - morseIndex f x := by
          have hxa' := morseIndex_le_finrank (f := f) (x := a)
          omega
        by_cases hap : a = p
        · simpa only [hap] using hxa
        · exact hxa.trans (ih (d - morseIndex f a) (hxn ▸ hcodim) a rfl ha
            (fun h ↦ hap h.symm)
            ⟨z, hzp.1, hza⟩)
  exact H (d - morseIndex f x) x rfl hx hpx hy

/-- **An index-one Morse trajectory slice is closed.** Assume that points in the closures of the
relevant stable and unstable manifolds converge to nondegenerate critical points, and that all
such manifolds meet transversally. If the Morse indices of `p` and `q` differ by one, then their
connecting set, cut at any value strictly between `f q` and `f p`, is closed. -/
theorem isClosed_unstableSet_inter_stableSet_inter_level
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hind : morseIndex f p = morseIndex f q + 1) {c : ℝ} (hc : f q < c ∧ c < f p)
    (hconvS : ∀ {z}, z ∈ closure (Flow.stableSet (negativeGradientFlow f hf) q) →
      ∃ b, IsNondegenerateCriticalPoint f b ∧
        z ∈ Flow.stableSet (negativeGradientFlow f hf) b)
    (hconvU : ∀ {z}, z ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p) →
      ∃ a, IsNondegenerateCriticalPoint f a ∧
        z ∈ Flow.unstableSet (negativeGradientFlow f hf) a)
    (htr : ∀ {a b z}, IsNondegenerateCriticalPoint f a →
      IsNondegenerateCriticalPoint f b →
      z ∈ Flow.unstableSet (negativeGradientFlow f hf) a →
      z ∈ Flow.stableSet (negativeGradientFlow f hf) b →
      Submodule.span ℝ (tangentConeAt ℝ
          (Flow.unstableSet (negativeGradientFlow f hf) a) z) ⊔
        Submodule.span ℝ (tangentConeAt ℝ
          (Flow.stableSet (negativeGradientFlow f hf) b) z) = ⊤) :
    IsClosed (Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∩ {z | f z = c}) := by
  -- A limit point has backward and forward critical limits `a` and `b`. The two preceding
  -- index-control theorems and the trajectory from `a` to `b` fit their indices between two
  -- consecutive integers. Any extra break would force a strict intermediate index; the only
  -- remaining degenerate possibilities put the limit point at `p` or `q`, away from the level.
  apply isClosed_of_closure_subset
  intro y hy
  have hyU : y ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p) :=
    closure_mono (fun _ hz ↦ hz.1.1) hy
  have hyS : y ∈ closure (Flow.stableSet (negativeGradientFlow f hf) q) :=
    closure_mono (fun _ hz ↦ hz.1.2) hy
  have hyc : f y = c :=
    (isClosed_eq hfs.continuous continuous_const).closure_subset
      (closure_mono (fun _ hz ↦ hz.2) hy)
  obtain ⟨a, ha, hya⟩ := hconvU hyU
  obtain ⟨b, hb, hyb⟩ := hconvS hyS
  have hba : morseIndex f b ≤ morseIndex f a := by
    by_cases hab : a = b
    · subst a
      exact le_rfl
    · exact (ha.morseIndex_lt_of_mem_unstableSet_inter_stableSet hb hfs hf hab hya hyb
        (htr ha hb hya hyb)).le
  have hbq : b = q := by
    by_contra hbq
    have hqb := hb.morseIndex_lt_of_mem_closure_stableSet_inter_stableSet hfs hf
      (fun h ↦ hbq h.symm) ⟨y, hyS, hyb⟩ hconvS htr
    have hap : a = p := by
      by_contra hap
      have hap' := ha.morseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hfs hf
        (fun h ↦ hap h.symm) ⟨y, hyU, hya⟩ hconvU htr
      omega
    subst a
    have hab : p = b := by
      by_contra hab
      have hba' := hp.morseIndex_lt_of_mem_unstableSet_inter_stableSet hb hfs hf hab hya hyb
        (htr hp hb hya hyb)
      omega
    subst b
    have hyp : y = p := Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
      (isNegativeGradient_negativeGradientFlow f hf)
        (fun t ↦ (hfs.differentiable (by norm_num)).differentiableAt)
        hfs.continuous.continuousAt ⟨hya, hyb⟩
    rw [hyp] at hyc
    linarith
  subst b
  have hap : a = p := by
    by_contra hap
    have hap' := ha.morseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hfs hf
      (fun h ↦ hap h.symm) ⟨y, hyU, hya⟩ hconvU htr
    by_cases hab : a = q
    · subst a
      have hyq : y = q := Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
        (isNegativeGradient_negativeGradientFlow f hf)
          (fun t ↦ (hfs.differentiable (by norm_num)).differentiableAt)
          hfs.continuous.continuousAt ⟨hya, hyb⟩
      rw [hyq] at hyc
      linarith
    · have hba' := ha.morseIndex_lt_of_mem_unstableSet_inter_stableSet hq hfs hf hab hya hyb
        (htr ha hq hya hyb)
      omega
  subst a
  exact ⟨⟨hya, hyb⟩, hyc⟩

/-- **A compact index-one Morse trajectory slice is finite.** Under the hypotheses of
`isClosed_unstableSet_inter_stableSet_inter_level`, if the slice is contained in a compact set
then it is finite. This is the finiteness needed to define the coefficient of the Morse
differential. -/
theorem finite_unstableSet_inter_stableSet_inter_level
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hind : morseIndex f p = morseIndex f q + 1) {c : ℝ} (hc : f q < c ∧ c < f p)
    (hconvS : ∀ {z}, z ∈ closure (Flow.stableSet (negativeGradientFlow f hf) q) →
      ∃ b, IsNondegenerateCriticalPoint f b ∧
        z ∈ Flow.stableSet (negativeGradientFlow f hf) b)
    (hconvU : ∀ {z}, z ∈ closure (Flow.unstableSet (negativeGradientFlow f hf) p) →
      ∃ a, IsNondegenerateCriticalPoint f a ∧
        z ∈ Flow.unstableSet (negativeGradientFlow f hf) a)
    (htr : ∀ {a b z}, IsNondegenerateCriticalPoint f a →
      IsNondegenerateCriticalPoint f b →
      z ∈ Flow.unstableSet (negativeGradientFlow f hf) a →
      z ∈ Flow.stableSet (negativeGradientFlow f hf) b →
      Submodule.span ℝ (tangentConeAt ℝ
          (Flow.unstableSet (negativeGradientFlow f hf) a) z) ⊔
        Submodule.span ℝ (tangentConeAt ℝ
          (Flow.stableSet (negativeGradientFlow f hf) b) z) = ⊤)
    {C : Set E} (hC : IsCompact C)
    (hsub : Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∩ {z | f z = c} ⊆ C) :
    (Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∩ {z | f z = c}).Finite := by
  -- The slice is a closed subset of a compact set, and Morse--Smale transversality together with
  -- the index difference makes it discrete.
  apply (hC.of_isClosed_subset
    (hp.isClosed_unstableSet_inter_stableSet_inter_level hq hfs hf hind hc hconvS hconvU htr)
    hsub).finite
  exact hp.isDiscrete_unstableSet_inter_stableSet_level hq hfs hf hind
    (fun y hy ↦ htr hp hq hy.1.1 hy.1.2)

end IsNondegenerateCriticalPoint

end TauCeti

end

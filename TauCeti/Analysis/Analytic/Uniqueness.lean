/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.RCLike.Basic

-- Proof-only: `HasFiniteFPowerSeriesOnBall.changeOrigin`, the identity principle
-- `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, and its analytic inputs.
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Restrictions to lines and iterated derivatives of analytic functions

A continuous homogeneous polynomial `v ↦ m (v, …, v)` over a nontrivially normed field that
vanishes on a neighbourhood of a single point vanishes everywhere
(`ContinuousMultilinearMap.apply_diag_eq_zero_of_eventuallyEq`).

Over an `RCLike` field, a function analytic at `p` vanishes on a neighbourhood of `p` exactly when
its restriction `t ↦ f (p + t • v)` to every line through `p` vanishes on a neighbourhood of `0`.
The nontrivial direction is the identity principle along each line: on a ball around `p` where `f`
is analytic, the restriction to the line through `p` and a point `y` of the ball is analytic on a
disc containing `0` and `1`, so it vanishes at `1`, that is at `y`.

Over a characteristic-zero normed field and into a complete codomain,
`HasFPowerSeriesOnBall.hasSum_iteratedFDeriv` expresses a germ analytic at `p` on a ball around `p`
through the diagonal values of its iterated Fréchet derivatives at `p`. Consequently `f` vanishes
near `p` if and only if `iteratedFDeriv 𝕜 n f p = 0` for every `n : ℕ`, and Mathlib's identity
principle extends this pointwise jet condition along any preconnected set on which `f` is analytic
on neighbourhoods.

The identity principle also shows that an analytic function on a preconnected set which does not
vanish identically does not vanish on a dense subset: otherwise it would vanish on an open set.
Combined with continuity, the nonvanishing set of an entire function such as a polynomial in the
entries of a matrix is open and dense, which is how genericity statements for finitely many
polynomial conditions are proved.

The name follows Mathlib's `Mathlib.Analysis.Analytic.Uniqueness`, where the identity principle
lives. The linear general-position corollary (generalized to finite families over any nontrivially
normed field) lives in `TauCeti.Analysis.Analytic.SingularDirection`.

## Main declarations

* `ContinuousMultilinearMap.apply_diag_eq_zero_of_eventuallyEq`: a continuous homogeneous
  polynomial vanishing near a point vanishes identically.
* `AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul`: an analytic function
  vanishes near `p` exactly when all its restrictions to lines through `p` vanish near `0`.
* `AnalyticAt.eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero`,
  `AnalyticAt.eventuallyEq_iff_forall_iteratedFDeriv_eq`: over a characteristic-zero field and into
  a complete space, an analytic germ is determined by its iterated Fréchet derivatives at a single
  point.
* `AnalyticOnNhd.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq`: the corresponding identity
  principles on preconnected sets.
* `AnalyticOnNhd.subset_closure_setOf_ne_zero`: on a preconnected set, an analytic function not
  vanishing at some point does not vanish on a dense subset.
* `AnalyticOnNhd.dense_setOf_ne_zero`: the same for a function analytic on the whole space.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
-/

public section

open Filter Metric Topology

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If the homogeneous polynomial `v ↦ m (v, …, v)` associated to a continuous multilinear map
vanishes near a point `v₀`, then it vanishes on the whole space. -/
theorem ContinuousMultilinearMap.apply_diag_eq_zero_of_eventuallyEq {n : ℕ}
    (m : E [×n]→L[𝕜] F) {v₀ : E} (h : (fun v ↦ m fun _ ↦ v) =ᶠ[𝓝 v₀] 0) (v : E) :
    (m fun _ ↦ v) = 0 := by
  let q : FormalMultilinearSeries 𝕜 E F := fun k ↦ if hk : k = n then hk ▸ m else 0
  have hq₀ : HasFiniteFPowerSeriesOnBall (fun y ↦ m fun _ ↦ y) q 0 (n + 1) ⊤ := by
    refine .mk' (fun k hk ↦ dite_eq_right (by omega)) ENNReal.zero_lt_top fun y _ ↦ ?_
    rw [Finset.sum_eq_single_of_mem n (Finset.self_mem_range_succ n)
      fun k _ hkn ↦ by simp [q, hkn]]
    simp [q]
  have hq : HasFPowerSeriesOnBall (fun y ↦ m fun _ ↦ y) (q.changeOrigin v₀) v₀ ⊤ := by
    simpa using (hq₀.changeOrigin (y := v₀) ENNReal.coe_lt_top).toHasFPowerSeriesOnBall
  have hzero : HasFPowerSeriesAt 0 (q.changeOrigin v₀) v₀ := hq.hasFPowerSeriesAt.congr h
  have hsum : HasSum (fun k ↦ q.changeOrigin v₀ k fun _ ↦ v - v₀) 0 := by
    convert hasSum_zero (α := F) using 1
    ext k
    exact hzero.apply_eq_zero k (v - v₀)
  exact (hq.hasSum_sub (Metric.mem_eball.2 (edist_lt_top v v₀))).unique hsum

end NontriviallyNormedField

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The nontrivial direction of
`AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul` for a complete
codomain, where `f` is analytic on a ball around `p`. -/
private theorem AnalyticAt.eventuallyEq_zero_of_forall_eventuallyEq_zero_comp_add_smul
    [CompleteSpace F] {f : E → F} {p : E} (hf : AnalyticAt 𝕜 f p)
    (h : ∀ v : E, (fun t : 𝕜 ↦ f (p + t • v)) =ᶠ[𝓝 0] 0) : f =ᶠ[𝓝 p] 0 := by
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  filter_upwards [ball_mem_nhds p hr] with y hy
  set v := y - p
  rcases eq_or_ne v 0 with hv | hv
  · -- On the trivial direction the restriction is the constant `f p = f y`.
    simpa [sub_eq_zero.1 hv] using (h 0).self_of_nhds
  -- On the line through `p` and `y`, the restriction is analytic on a disc containing `0` and `1`.
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hmem : ∀ t ∈ ball (0 : 𝕜) (r / ‖v‖), p + t • v ∈ ball p r := fun t ht ↦ by
    rw [mem_ball_zero_iff, lt_div_iff₀ hv'] at ht
    simpa [dist_eq_norm, norm_smul] using ht
  have hline (t : 𝕜) : AnalyticAt 𝕜 (fun t : 𝕜 ↦ p + t • v) t := by fun_prop
  have han : AnalyticOnNhd 𝕜 (fun t : 𝕜 ↦ f (p + t • v)) (ball (0 : 𝕜) (r / ‖v‖)) :=
    fun t ht ↦ AnalyticAt.comp (g := f) (hfr _ (hmem t ht)) (hline t)
  have h1 : (1 : 𝕜) ∈ ball (0 : 𝕜) (r / ‖v‖) := by
    rw [mem_ball_zero_iff, norm_one, one_lt_div hv']
    simpa [v, dist_eq_norm] using hy
  simpa [v] using han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : 𝕜) _).isPreconnected (mem_ball_self (div_pos hr hv')) (h v) h1

/-- **An analytic function is determined near a point by its restrictions to lines.** A function
analytic at `p` vanishes on a neighbourhood of `p` exactly when, for every direction `v`, the
restriction `t ↦ f (p + t • v)` vanishes on a neighbourhood of `0`. -/
theorem AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul {f : E → F}
    {p : E} (hf : AnalyticAt 𝕜 f p) :
    f =ᶠ[𝓝 p] 0 ↔ ∀ v : E, (fun t : 𝕜 ↦ f (p + t • v)) =ᶠ[𝓝 0] 0 := by
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · have hline : Tendsto (fun t : 𝕜 ↦ p + t • v) (𝓝 0) (𝓝 p) := by
      have : Continuous fun t : 𝕜 ↦ p + t • v := by fun_prop
      simpa using this.tendsto (0 : 𝕜)
    exact hline.eventually h
  -- Pass to the completion of `F`, as in Mathlib's identity principle.
  let e : F →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have he : (e ∘ f) =ᶠ[𝓝 p] 0 :=
    ((e.analyticAt _).comp hf).eventuallyEq_zero_of_forall_eventuallyEq_zero_comp_add_smul
      fun v ↦ (h v).mono fun t ht ↦ by simp [ht]
  exact he.mono fun y hy ↦ UniformSpace.Completion.coe_injective F (by simpa [e] using hy)

end RCLike

section IteratedFDeriv

variable {𝕜' E' F' : Type*} [NontriviallyNormedField 𝕜'] [CharZero 𝕜']
  [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜' F'] [CompleteSpace F']

/-- Over a characteristic-zero field and into a complete normed space, an analytic germ vanishes
near `p` if and only if all of its iterated Fréchet derivatives at `p` vanish. -/
theorem AnalyticAt.eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero
    {f : E' → F'} {p : E'} (hf : AnalyticAt 𝕜' f p) :
    f =ᶠ[𝓝 p] 0 ↔ ∀ n : ℕ, iteratedFDeriv 𝕜' n f p = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · simpa [iteratedFDeriv_zero] using (h.iteratedFDeriv 𝕜' n).eq_of_nhds
  · obtain ⟨P, r, hP⟩ := hf
    filter_upwards [Metric.eball_mem_nhds p hP.r_pos] with y hy
    have hy' : y - p ∈ Metric.eball 0 r := by
      simpa [eDist_eq_eNorm_sub] using hy
    have hsum := hP.hasSum_iteratedFDeriv hy'
    simp only [h, zero_apply, smul_zero, add_sub_cancel] at hsum
    exact hsum.unique hasSum_zero

/-- Over a characteristic-zero field and into a complete normed space, two germs analytic at `p`
agree near `p` if and only if all of their iterated Fréchet derivatives at `p` agree. -/
theorem AnalyticAt.eventuallyEq_iff_forall_iteratedFDeriv_eq
    {f g : E' → F'} {p : E'} (hf : AnalyticAt 𝕜' f p) (hg : AnalyticAt 𝕜' g p) :
    f =ᶠ[𝓝 p] g ↔ ∀ n : ℕ, iteratedFDeriv 𝕜' n f p = iteratedFDeriv 𝕜' n g p := by
  rw [Filter.eventuallyEq_iff_sub,
    (hf.sub hg).eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero]
  refine forall_congr' fun n ↦ ?_
  rw [iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt, sub_eq_zero]

/-- **Identity principle via iterated derivatives.** If a function into a complete normed space is
analytic on neighbourhoods along a preconnected set `U` over a characteristic-zero field and all of
its iterated Fréchet derivatives vanish at one point `z₀ ∈ U`, then it vanishes on `U`. -/
theorem AnalyticOnNhd.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero
    {f : E' → F'} {U : Set E'} (hf : AnalyticOnNhd 𝕜' f U) (hU : IsPreconnected U)
    {z₀ : E'} (h₀ : z₀ ∈ U) (hfz₀ : ∀ n : ℕ, iteratedFDeriv 𝕜' n f z₀ = 0) :
    Set.EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero.2 hfz₀)

/-- **Identity principle via iterated derivatives.** Two functions into a complete normed space
that are analytic on neighbourhoods along a preconnected set `U` over a characteristic-zero field
and have equal iterated Fréchet derivatives at one point `z₀ ∈ U` agree on `U`. -/
theorem AnalyticOnNhd.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    {f g : E' → F'} {U : Set E'} (hf : AnalyticOnNhd 𝕜' f U) (hg : AnalyticOnNhd 𝕜' g U)
    (hU : IsPreconnected U) {z₀ : E'} (h₀ : z₀ ∈ U)
    (hfg : ∀ n : ℕ, iteratedFDeriv 𝕜' n f z₀ = iteratedFDeriv 𝕜' n g z₀) :
    Set.EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hU h₀
    (((hf z₀ h₀).eventuallyEq_iff_forall_iteratedFDeriv_eq (hg z₀ h₀)).2 hfg)

end IteratedFDeriv

section NonvanishingSet

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The nonvanishing set of an analytic function is dense.** If `f` is analytic on a
preconnected set `U` and does not vanish at some point of `U`, then every point of `U` is a limit
of points where `f` does not vanish. Otherwise `f` would vanish on a neighbourhood of a point of
`U`, hence on all of `U` by the identity principle. -/
theorem AnalyticOnNhd.subset_closure_setOf_ne_zero {f : E → F} {U : Set E}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U) {z₀ : E} (hz₀U : z₀ ∈ U)
    (hz₀ : f z₀ ≠ 0) : U ⊆ closure {x | f x ≠ 0} := by
  intro x hx
  by_contra hcl
  have hzero : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with y hy
    by_contra hfy
    exact hy (subset_closure hfy)
  exact hz₀ (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hx hzero hz₀U)

/-- **The nonvanishing set of an entire function is dense.** A function analytic on a preconnected
space that does not vanish at some point does not vanish on a dense set. Preconnectedness holds for
real and complex normed spaces; over a totally disconnected field such as `ℚ_[p]` the indicator
function of a ball is analytic, and the statement fails. -/
theorem AnalyticOnNhd.dense_setOf_ne_zero [PreconnectedSpace E] {f : E → F}
    (hf : AnalyticOnNhd 𝕜 f Set.univ) {z₀ : E} (hz₀ : f z₀ ≠ 0) : Dense {x | f x ≠ 0} := fun x ↦
  hf.subset_closure_setOf_ne_zero isPreconnected_univ (Set.mem_univ z₀) hz₀ (Set.mem_univ x)

end NonvanishingSet

end

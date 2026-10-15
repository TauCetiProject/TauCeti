/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
public import TauCeti.Analysis.Convex.FunctionTopology
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Extrema
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak continuity of the Monge–Ampère measure

Let `Ω` be an open subset of a finite-dimensional real inner product space `E`, and let
`F k → u` locally uniformly on `Ω` along a filter `l`, where the `F k` are eventually convex on
`Ω`. Then the limit `u` is convex on `Ω`, and the Aleksandrov Monge–Ampère measures
`MA_{F k}` (of `F k` extended by `⊤` off `Ω`) converge to `MA_u` in the weak sense:

* for a compact `K ⊆ Ω`, `limsup MA_{F k}(K) ≤ MA_u(K)`;
* for an open `U ⊆ Ω`, `MA_u(U) ≤ liminf MA_{F k}(U)`;
* consequently, `MA_{F k}(s) → MA_u(s)` for every bounded `s` with closure inside `Ω` and
  `MA_u(frontier s) = 0`.

The measures are taken with respect to any measure `μ` absolutely continuous with respect to an
additive Haar measure (outer regular for the bounds on compact sets), so the weighted measures
`∫_{∂u(s)} g` are covered as well. This stability of Aleksandrov solutions under locally uniform
convergence is the limiting step when the Dirichlet problem for the Monge–Ampère equation is
solved by approximation.

The bound on compact sets follows from the upper semicontinuity of subgradient images
(`TauCeti.eventually_biUnion_subset_of_tendstoLocallyUniformlyOn`): every open neighbourhood `V`
of `∂u(K)` eventually contains `∂F_k(K)`. Outer regularity of `μ` then bounds
`limsup μ(∂F_k(K))` by `μ(∂u(K))`.

For the bound on open sets, first let `U` be bounded with closure inside `Ω`. Almost every
`y ∈ ∂u(U)` is a subgradient of `u` at a single point `x₀ ∈ U`
(`TauCeti.measure_setOf_exists_ne_mem_subdifferential_eq_zero`). For such `y` the convex
function `u - ⟪·, y⟫` exceeds its value at `x₀` by some `η > 0` on a small sphere about `x₀`.
Once `|F k - u| < η / 2` on the closure of `U`, the function `F k - ⟪·, y⟫` attains its minimum
over the closed ball inside the ball, so `y ∈ ∂F_k(U)`. Sorting such `y` by `η` gives an
increasing sequence of sets, each eventually contained in `∂F_k(U)`. A general open `U ⊆ Ω` is
the increasing union of bounded open sets with closure inside `U`.

The convergence on continuity sets then follows from both bounds by Mathlib's
`MeasureTheory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le`.

## Main statements

* `TauCeti.limsup_mongeAmpereMeasure_le` — the bound on compact sets;
* `TauCeti.mongeAmpereMeasure_le_liminf` — the bound on open sets;
* `TauCeti.tendsto_mongeAmpereMeasure` — convergence on relatively compact continuity sets.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.2.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, §2.1.
-/

public section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric

open scoped Topology ENNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Set E} {l : Filter ι} {F : ι → E → ℝ} {u : E → ℝ}

/-- Let `g` be convex on an open set `Ω ⊇ U`, and let the closed ball of radius `r > 0` about `x₀`
lie in `U`. If `u - ⟪·, y⟫` exceeds its value at `x₀` by at least `η` on the sphere of radius `r`
about `x₀`, and `|g - u| < η / 2` on the ball, then `y` is a subgradient of `g` relative to `Ω` at
some point of `U`. -/
private theorem mem_biUnion_of_forall_sphere {g : E → ℝ} (hΩ : IsOpen Ω) (hg : ConvexOn ℝ Ω g)
    {U : Set E} (hUΩ : U ⊆ Ω) {x₀ y : E} {r η : ℝ} (hr : 0 < r) (hball : closedBall x₀ r ⊆ U)
    (hη : ∀ z ∈ sphere x₀ r, η ≤ u z - u x₀ - inner ℝ (z - x₀) y)
    (hgu : ∀ z ∈ closedBall x₀ r, |g z - u z| < η / 2) :
    y ∈ ⋃ x ∈ U ∩ Ω, {y | ∀ x' ∈ Ω, g x + inner ℝ (x' - x) y ≤ g x'} := by
  -- `g - ⟪·, y⟫` attains its minimum over the closed ball at a point of the open ball, since on
  -- the sphere it exceeds its value at the centre.
  set h : E → ℝ := fun z => g z - inner ℝ z y
  have hcont : ContinuousOn h (closedBall x₀ r) :=
    ((hg.continuousOn hΩ).mono (hball.trans hUΩ)).sub
      (continuous_id.inner continuous_const).continuousOn
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall x₀ r).exists_isMinOn_mem_subset hcont
    (mem_closedBall_self hr.le) (s := ball x₀ r) fun z' hz' => by
      have hz's : z' ∈ sphere x₀ r := by
        rw [← closedBall_sdiff_ball]
        exact hz'
      have h₁ := hη z' hz's
      have h₂ := (abs_lt.1 (hgu z' hz'.1)).1
      have h₃ := (abs_lt.1 (hgu x₀ (mem_closedBall_self hr.le))).2
      simp only [h, inner_sub_left] at h₁ ⊢
      linarith
  have hzΩ : z ∈ Ω := hUΩ (hball (ball_subset_closedBall hz))
  -- A local minimum of the convex function `g - ⟪·, y⟫` on `Ω` is a global one.
  have hconv : ConvexOn ℝ Ω h := hg.sub ((innerₗ E).flip y |>.concaveOn hg.1)
  have hloc := hmin.isLocalMin (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  have hglob := IsMinOn.of_isLocalMinOn_of_convexOn hzΩ (hloc.isLocalMinOn Ω) hconv
  refine mem_biUnion ⟨hball (ball_subset_closedBall hz), hzΩ⟩ fun x' hx' => ?_
  have := isMinOn_iff.1 hglob x' hx'
  simp only [h, inner_sub_left] at this ⊢
  linarith

/-- Let `u` be continuous on an open set `Ω`, let `U ⊆ Ω` be open, and let `y` be a subgradient
of `u` relative to `Ω` at `x₀ ∈ U` which is a subgradient of `u` (extended by `⊤` off `Ω`) at no
other point. Then `u - ⟪·, y⟫` exceeds its value at `x₀` by some `η > 0` on a sphere about `x₀`
whose closed ball lies in `U`. -/
private theorem exists_forall_sphere [DecidablePred (· ∈ Ω)] (hu : ContinuousOn u Ω)
    {U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Ω) {x₀ y : E} (hx₀ : x₀ ∈ U)
    (hy : ∀ x' ∈ Ω, u x₀ + inner ℝ (x' - x₀) y ≤ u x')
    (huniq : ∀ x, y ∈ subdifferential (innerₗ E)
      (fun x => if x ∈ Ω then (u x : EReal) else ⊤) x → x = x₀) :
    ∃ r > 0, ∃ η > 0, closedBall x₀ r ⊆ U ∧
      ∀ z ∈ sphere x₀ r, η ≤ u z - u x₀ - inner ℝ (z - x₀) y := by
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx₀)
  -- On the sphere, `u - ⟪·, y⟫` is strictly above its value at `x₀`: equality at `z` would make
  -- `y` a subgradient at `z ≠ x₀`.
  have hpos : ∀ z ∈ sphere x₀ r, 0 < u z - u x₀ - inner ℝ (z - x₀) y := fun z hz => by
    have hzΩ : z ∈ Ω := hUΩ (hball (sphere_subset_closedBall hz))
    refine lt_of_le_of_ne (by linarith [hy z hzΩ]) fun heq => ?_
    have hzx : z ≠ x₀ := ne_of_mem_sphere hz hr.ne'
    refine hzx (huniq z ((mem_subdifferential_ite_iff (innerₗ E) hzΩ).2 fun x' hx' => ?_))
    have := hy x' hx'
    simp only [innerₗ_apply_apply]
    rw [show x' - x₀ = (x' - z) + (z - x₀) by abel, inner_add_left] at this
    linarith
  rcases (sphere x₀ r).eq_empty_or_nonempty with he | hne
  · exact ⟨r, hr, 1, one_pos, hball, by simp [he]⟩
  have hcont : ContinuousOn (fun z => u z - u x₀ - inner ℝ (z - x₀) y) (sphere x₀ r) :=
    ((hu.mono ((sphere_subset_closedBall.trans hball).trans hUΩ)).sub continuousOn_const).sub
      ((continuous_id.sub continuous_const).inner continuous_const).continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere x₀ r).exists_isMinOn hne hcont
  exact ⟨r, hr, _, hpos z₀ hz₀, hball, fun z hz => isMinOn_iff.1 hmin z hz⟩

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) {ν : Measure E}
  [ν.IsAddHaarMeasure] [DecidablePred (· ∈ Ω)]

/-- **Upper semicontinuity of the Monge–Ampère measure on compact sets.** Let `F k → u` locally
uniformly on an open set `Ω`, where the `F k` are eventually convex on `Ω`. For every compact
`K ⊆ Ω`, `limsup MA_{F k}(K) ≤ MA_u(K)`, for the Monge–Ampère measures of `F k` and `u` (extended
by `⊤` off `Ω`) with respect to an outer regular measure `μ` absolutely continuous with respect
to an additive Haar measure. -/
theorem limsup_mongeAmpereMeasure_le [μ.OuterRegular] (hμ : μ ≪ ν) (hΩ : IsOpen Ω)
    (hF : ∀ᶠ k in l, ConvexOn ℝ Ω (F k)) (hFu : TendstoLocallyUniformlyOn F u l Ω)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    limsup (fun k => mongeAmpereMeasure μ (fun x => if x ∈ Ω then (F k x : EReal) else ⊤) K) l ≤
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) K := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have hu : ConvexOn ℝ Ω u := convexOn_of_tendsto hF fun x hx => hFu.tendsto_at hx
  rw [mongeAmpereMeasure_ite_apply μ hΩ hu hμ hK.measurableSet, inter_eq_left.2 hKΩ,
    Set.measure_eq_iInf_isOpen]
  refine le_iInf₂ fun V hKV => le_iInf fun hV => limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hF, eventually_biUnion_subset_of_tendstoLocallyUniformlyOn hΩ
    (hu.continuousOn hΩ) hFu hK hKΩ hV hKV] with k hk hkV
  rw [mongeAmpereMeasure_ite_apply μ hΩ hk hμ hK.measurableSet, inter_eq_left.2 hKΩ]
  exact measure_mono hkV

/-- The lower bound `MA_u(U) ≤ liminf MA_{F k}(U)` for a bounded open `U` whose closure lies in
`Ω`. -/
private theorem mongeAmpereMeasure_le_liminf_of_isBounded (hμ : μ ≪ ν) (hΩ : IsOpen Ω)
    (hF : ∀ᶠ k in l, ConvexOn ℝ Ω (F k)) (hFu : TendstoLocallyUniformlyOn F u l Ω)
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUΩ : closure U ⊆ Ω) :
    mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) U ≤
      liminf (fun k => mongeAmpereMeasure μ (fun x => if x ∈ Ω then (F k x : EReal) else ⊤) U)
        l := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have hu : ConvexOn ℝ Ω u := convexOn_of_tendsto hF fun x hx => hFu.tendsto_at hx
  have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
  rw [mongeAmpereMeasure_ite_apply μ hΩ hu hμ hU.measurableSet]
  -- `A n` is the set of slopes `y` for which `u - ⟪·, y⟫` exceeds its value at the centre of a
  -- closed ball in `U` by at least `1 / (n + 1)` on the boundary sphere.
  set A : ℕ → Set E := fun n => {y | ∃ x₀ r, 0 < r ∧ closedBall x₀ r ⊆ U ∧
    ∀ z ∈ sphere x₀ r, 1 / ((n : ℝ) + 1) ≤ u z - u x₀ - inner ℝ (z - x₀) y}
  have hAmono : Monotone A := fun n m hnm y ⟨x₀, r, hr, hball, hη⟩ =>
    ⟨x₀, r, hr, hball, fun z hz => (Nat.one_div_le_one_div hnm).trans (hη z hz)⟩
  -- Each `A n` is eventually contained in the subgradient image of `U` under `F k`.
  have hA : ∀ n, μ (A n) ≤ liminf (fun k =>
      mongeAmpereMeasure μ (fun x => if x ∈ Ω then (F k x : EReal) else ⊤) U) l := fun n => by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    have hη : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    filter_upwards [hF, hFu.eventually_forall_abs_sub_lt hUb.isCompact_closure hUΩ
      (half_pos hη)] with k hk hk'
    rw [mongeAmpereMeasure_ite_apply μ hΩ hk hμ hU.measurableSet]
    exact measure_mono fun y ⟨x₀, r, hr, hball, hyη⟩ =>
      mem_biUnion_of_forall_sphere hΩ hk hUΩ' hr hball hyη fun z hz =>
        hk' z (subset_closure (hball hz))
  -- Up to the null set of slopes that are subgradients at two distinct points, every subgradient
  -- of `u` at a point of `U` lies in some `A n`.
  set N := {y | ∃ x₁ x₂, x₁ ≠ x₂ ∧
    y ∈ subdifferential (innerₗ E) (fun x => if x ∈ Ω then (u x : EReal) else ⊤) x₁ ∧
    y ∈ subdifferential (innerₗ E) (fun x => if x ∈ Ω then (u x : EReal) else ⊤) x₂}
  have hN : μ N = 0 := hμ (measure_setOf_exists_ne_mem_subdifferential_eq_zero ν _)
  have hSA : (⋃ x ∈ U ∩ Ω, {y | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x'}) \ N ⊆
      ⋃ n, A n := by
    rintro y ⟨hy, hyN⟩
    obtain ⟨x₀, ⟨hx₀U, hx₀Ω⟩, hy⟩ := mem_iUnion₂.1 hy
    have hy₀ : y ∈ subdifferential (innerₗ E) (fun x => if x ∈ Ω then (u x : EReal) else ⊤) x₀ :=
      (mem_subdifferential_ite_iff (innerₗ E) hx₀Ω).2 fun x' hx' => by
        simpa only [innerₗ_apply_apply] using hy x' hx'
    obtain ⟨r, hr, η, hη, hball, hsph⟩ := exists_forall_sphere (hu.continuousOn hΩ) hU hUΩ'
      hx₀U hy fun x hx => by_contra fun hne => hyN ⟨x, x₀, hne, hx, hy₀⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
    exact mem_iUnion.2 ⟨n, x₀, r, hr, hball, fun z hz => hn.le.trans (hsph z hz)⟩
  calc μ (⋃ x ∈ U ∩ Ω, {y | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x'})
      = μ ((⋃ x ∈ U ∩ Ω, {y | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x'}) \ N) :=
        (measure_sdiff_null hN).symm
    _ ≤ μ (⋃ n, A n) := measure_mono hSA
    _ = ⨆ n, μ (A n) := hAmono.measure_iUnion
    _ ≤ _ := iSup_le hA

/-- **Lower semicontinuity of the Monge–Ampère measure on open sets.** Let `F k → u` locally
uniformly on an open set `Ω`, where the `F k` are eventually convex on `Ω`. For every open
`U ⊆ Ω`, `MA_u(U) ≤ liminf MA_{F k}(U)`, for the Monge–Ampère measures of `F k` and `u` (extended
by `⊤` off `Ω`) with respect to any measure `μ` absolutely continuous with respect to an additive
Haar measure. -/
theorem mongeAmpereMeasure_le_liminf (hμ : μ ≪ ν) (hΩ : IsOpen Ω)
    (hF : ∀ᶠ k in l, ConvexOn ℝ Ω (F k)) (hFu : TendstoLocallyUniformlyOn F u l Ω)
    {U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Ω) :
    mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) U ≤
      liminf (fun k => mongeAmpereMeasure μ (fun x => if x ∈ Ω then (F k x : EReal) else ⊤) U)
        l := by
  -- Exhaust `U` by the bounded open sets `V n` of points of norm `< n` at distance
  -- `> 1 / (n + 1)` from the complement of `U`; their closures lie in `U`.
  set V : ℕ → Set E := fun n => ball 0 n ∩ (fun x => infEDist x Uᶜ) ⁻¹' Ioi ((n : ℝ≥0∞) + 1)⁻¹
  have hVmono : Monotone V := fun n m hnm => inter_subset_inter
    (ball_subset_ball (by exact_mod_cast hnm)) fun x hx => by
      refine lt_of_le_of_lt ?_ (show ((n : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ from hx)
      gcongr
  have hVU : ∀ n, closure (V n) ⊆ U := fun n x hx => by
    by_contra hxU
    have := closure_lt_subset_le continuous_const continuous_infEDist
      (closure_mono inter_subset_right hx)
    rw [mem_ofPred_eq, infEDist_zero_of_mem hxU] at this
    simp at this
  have hUV : ⋃ n, V n = U := by
    refine Subset.antisymm (iUnion_subset fun n => subset_closure.trans (hVU n)) fun x hx => ?_
    have hd : infEDist x Uᶜ ≠ 0 := by
      rw [← pos_iff_ne_zero, infEDist_pos_iff_notMem_closure, hU.isClosed_compl.closure_eq]
      exact not_not.2 hx
    obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hd
    obtain ⟨M, hM⟩ := exists_nat_gt ‖x‖
    refine mem_iUnion.2 ⟨max N M, mem_ball_zero_iff.2 (hM.trans_le ?_), lt_of_le_of_lt ?_ hN⟩
    · exact_mod_cast le_max_right N M
    · gcongr
      exact_mod_cast (le_max_left N M).trans (Nat.le_succ _)
  calc mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) U
      = ⨆ n, mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) (V n) := by
        rw [← hVmono.measure_iUnion, hUV]
    _ ≤ _ := iSup_le fun n => (mongeAmpereMeasure_le_liminf_of_isBounded μ hμ hΩ hF hFu
        ((isOpen_ball).inter (isOpen_Ioi.preimage continuous_infEDist))
        (isBounded_ball.subset inter_subset_left) ((hVU n).trans hUΩ)).trans
      (liminf_le_liminf (Eventually.of_forall fun k =>
        measure_mono (subset_closure.trans (hVU n))))

/-- **Weak continuity of the Monge–Ampère measure.** Let `F k → u` locally uniformly on an open set
`Ω`, where the `F k` are eventually convex on `Ω`. For every bounded set `s` whose closure lies in
`Ω` and whose frontier is `MA_u`-null, `MA_{F k}(s) → MA_u(s)`, for the Monge–Ampère measures of
`F k` and `u` (extended by `⊤` off `Ω`) with respect to an outer regular measure `μ` absolutely
continuous with respect to an additive Haar measure. -/
theorem tendsto_mongeAmpereMeasure [μ.OuterRegular] (hμ : μ ≪ ν) (hΩ : IsOpen Ω)
    (hF : ∀ᶠ k in l, ConvexOn ℝ Ω (F k)) (hFu : TendstoLocallyUniformlyOn F u l Ω)
    {s : Set E} (hsb : Bornology.IsBounded s) (hsΩ : closure s ⊆ Ω)
    (hfr : mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) (frontier s) = 0) :
    Tendsto (fun k => mongeAmpereMeasure μ (fun x => if x ∈ Ω then (F k x : EReal) else ⊤) s) l
      (𝓝 (mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) s)) :=
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure hfr
    (mongeAmpereMeasure_le_liminf μ hμ hΩ hF hFu isOpen_interior
      (interior_subset.trans (subset_closure.trans hsΩ)))
    (limsup_mongeAmpereMeasure_le μ hμ hΩ hF hFu hsb.isCompact_closure hsΩ)

end TauCeti

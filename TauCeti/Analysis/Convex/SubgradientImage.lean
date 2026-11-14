/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.Convex.EffectiveDomain
public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compactness of subgradient images of convex functions

Let `E` be a finite-dimensional real inner product space and let `f : E → EReal` be convex
(convex real epigraph, never `⊥`), with `D` the interior of its effective domain `{x | f x ≠ ⊤}`.
Since `f` is continuous on `D`, its subgradients for the inner product are bounded over every
compact `K ⊆ D`, and the graph of the subdifferential over a closed `K ⊆ D` is closed. More
generally, closedness of this graph only needs finiteness and continuity of the real representative
on `K`. Hence
the subgradient image `∂f(K) = ⋃ x ∈ K, ∂f(x)` of a compact subset of `D` is compact. The same
compactness, with Rademacher's theorem, shows that `f` has a subgradient at every point of `D`;
in particular a real function convex on an open set has a supporting hyperplane at each point,
its differentiability at a point of that open set is equivalent to uniqueness of its subgradient
there, and a real function convex on the whole space agrees on any compact set with a globally
convex Lipschitz function and admits a Borel measurable subgradient selection obtained by taking
the minimum-norm subgradient at each point.

For a real function `u` continuous on the compact closure of a set `Ω`, every slope of an affine
function through a point of the graph over `Ω` that lies below `u` on the frontier of `Ω` is a
supporting slope on the closure at some point of `Ω`. The argument works for continuous linear
functionals on a real normed space; the inner-product form is a specialization.
Consequently, if `w ≤ u` on the frontier
of `Ω`, the subgradients of `w` relative to `Ω` at points where `u < w`, and their small
perturbations, are subgradients of `u` relative to `Ω`: this is the comparison step behind the
comparison principle for the Monge–Ampère equation.

In a seminormed real inner product space, if real functions `F k` converge to `u` locally
uniformly on an open set `Ω`, with `u` continuous on `Ω`, their subgradients relative to `Ω` at
points of a compact `K ⊆ Ω` are eventually bounded. If the space is proper, every open
neighbourhood of the subgradient image of `K` under `u` eventually contains that of `K` under `F k`.

## Main statements

* `TauCeti.mul_norm_le_of_forall_add_inner_le` — a subgradient of `u` at `x` relative to `Ω` is
  bounded in terms of a bound for `|u|` on a ball about `x` inside `Ω`;
* `TauCeti.exists_norm_le_of_mem_subdifferential` — the subgradients of `f` are bounded over
  compact subsets of `D`;
* `TauCeti.isClosed_setOf_mem_subdifferential` — the graph of the subdifferential over a closed
  set on which the function is finite and its real representative is continuous is closed;
* `TauCeti.isCompact_setOf_mem_subdifferential` and `TauCeti.isCompact_subgradientImage` — the
  graph of the subdifferential over a compact subset of `D`, and the subgradient image of such a
  set, are compact;
* `TauCeti.nonempty_subdifferential_of_mem_interior` — the subdifferential is nonempty at every
  point of `D`, and `TauCeti.eventually_nonempty_subdifferential` at every point near a point
  around which `f` is finite;
* `TauCeti.hasGradientAt_toReal_of_forall_mem_subdifferential_eq` and
  `TauCeti.differentiableAt_toReal_iff_subsingleton_subdifferential` — at an interior point of the
  effective domain, the real representative is differentiable if and only if the subdifferential
  has at most one element;
* `ConvexOn.exists_forall_add_inner_le`,
  `ConvexOn.differentiableAt_iff_subsingleton_subdifferential`,
  `ConvexOn.exists_convexOn_lipschitzWith_eqOn` and
  `ConvexOn.exists_measurable_forall_add_inner_le` — supporting hyperplanes, subgradient
  characterization of differentiability on open convex domains, global convex Lipschitz
  modification outside a compact set, and Borel measurable subgradient selection on the whole
  space;
* `TauCeti.exists_forall_add_apply_le_of_forall_frontier` — continuous-linear-functional slopes
  below the boundary values support the function on the closure at an interior-domain point;
* `TauCeti.exists_forall_add_inner_le_of_forall_frontier` — slopes of affine functions through a
  point of the graph that lie below the boundary values are subgradients at points of `Ω`;
* `TauCeti.exists_forall_add_inner_add_le_of_forall_frontier_le` — if `w ≤ u` on the frontier of
  `Ω`, small perturbations of a subgradient of `w` at a point where `u < w` are subgradients of
  `u` at points of `Ω`;
* `TauCeti.exists_eventually_norm_le_of_tendstoLocallyUniformlyOn` — subgradients of a locally
  uniformly convergent family are eventually bounded over compact sets;
* `TauCeti.eventually_biUnion_subset_of_tendstoLocallyUniformlyOn` — upper semicontinuity of
  subgradient images under locally uniform convergence.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 24.7.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §§1.1–1.2.
-/

public section

namespace TauCeti

open Set Metric

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Subgradients are bounded by the size of the function.** If `y` is a subgradient of `u`
relative to `Ω` at `x`, the closed ball of radius `δ ≥ 0` about `x` lies in `Ω`, and `|u| ≤ M` on
that ball, then `δ * ‖y‖ ≤ 2 * M`. -/
theorem mul_norm_le_of_forall_add_inner_le {Ω : Set E} {u : E → ℝ} {x y : E} {δ M : ℝ}
    (hδ : 0 ≤ δ) (hΩ : closedBall x δ ⊆ Ω) (hM : ∀ z ∈ closedBall x δ, |u z| ≤ M)
    (hy : ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x') : δ * ‖y‖ ≤ 2 * M := by
  have hx := (abs_le.1 (hM x (mem_closedBall_self hδ))).1
  rcases (norm_nonneg y).eq_or_lt with hy0 | hy0'
  · have := (abs_le.1 (hM x (mem_closedBall_self hδ))).2
    rw [← hy0, mul_zero]
    linarith
  -- Compare `u` at `x` and at the point `x + δ • y / ‖y‖` of the sphere in the direction `y`.
  set x' := x + (δ / ‖y‖) • y
  have hx' : x' ∈ closedBall x δ := by
    simp [x', dist_eq_norm, norm_smul, hy0'.ne', abs_of_nonneg hδ]
  have hinner : inner ℝ (x' - x) y = δ * ‖y‖ := by
    simp only [x', add_sub_cancel_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h := hy x' (hΩ hx')
  rw [hinner] at h
  linarith [(abs_le.1 (hM x' hx')).2]

/-- The graph of the subdifferential of `f : E → EReal`, never `⊥`, over a closed set `K` is
closed if `f` is finite on `K` and its real representative is continuous there. -/
theorem isClosed_setOf_mem_subdifferential {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥)
    {K : Set E} (hK : IsClosed K) (hKf : K ⊆ {x | f x ≠ ⊤})
    (hf : ContinuousOn (fun x => (f x).toReal) K) :
    IsClosed {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} := by
  -- The graph is cut out of `K × E` by the subgradient inequalities, which are closed conditions
  -- because `f` is continuous there.
  set h : E → ℝ := fun x => (f x).toReal
  have hG : {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} =
      (K ×ˢ univ) ∩ ⋂ x' ∈ {x' | f x' ≠ ⊤},
        ((K ×ˢ univ) ∩ (fun z : E × E => h z.1 + innerₗ E (x' - z.1) z.2) ⁻¹' Iic (h x')) := by
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_iInter,
      mem_preimage, mem_Iic]
    refine and_congr_right fun hx => ?_
    rw [mem_subdifferential_iff_forall_toReal_add_le _ hbot (hKf hx)]
    exact forall₂_congr fun x' _ => (and_iff_right hx).symm
  rw [hG]
  refine (hK.prod isClosed_univ).inter (isClosed_biInter fun x' _ => ?_)
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hK.prod isClosed_univ)
    isClosed_Iic
  refine ContinuousOn.add (hf.comp continuousOn_fst fun z hz => hz.1) ?_
  simp only [innerₗ_apply_apply]
  exact ((continuous_const.sub continuous_fst).inner continuous_snd).continuousOn

end Seminormed

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
include hf hbot

/-- **Subgradients of a convex function are locally bounded.** The subgradients of a convex
`f : E → EReal` on a finite-dimensional real inner product space are bounded over a compact
subset `K` of the interior of the effective domain. -/
theorem exists_norm_le_of_mem_subdifferential {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    ∃ R, ∀ x ∈ K, ∀ y ∈ subdifferential (innerₗ E) f x, ‖y‖ ≤ R := by
  -- `f` is continuous, hence bounded, on a compact thickening of `K` inside the domain.
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open isOpen_interior hKD
  obtain ⟨M, hM⟩ := hK.cthickening.exists_bound_of_continuousOn
    ((convexOn_toReal hf hbot).continuousOn_interior.mono hKδ)
  refine ⟨2 * M / δ, fun x hx y hy => ?_⟩
  have hball : closedBall x δ ⊆ cthickening δ K := closedBall_subset_cthickening hx δ
  rw [le_div_iff₀ hδ, mul_comm]
  refine mul_norm_le_of_forall_add_inner_le (Ω := {x | f x ≠ ⊤}) (u := fun x => (f x).toReal)
    hδ.le ((hball.trans hKδ).trans interior_subset)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hM z (hball hz)) ?_
  simpa only [innerₗ_apply_apply, mem_ofPred_eq] using
    (mem_subdifferential_iff_forall_toReal_add_le _ hbot (ne_top_of_mem_subdifferential _ hy)).1 hy

/-- The graph of the subdifferential of a convex `f : E → EReal` over a compact subset `K` of the
interior of the effective domain is compact. -/
theorem isCompact_setOf_mem_subdifferential {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    IsCompact {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} := by
  obtain ⟨R, hR⟩ := exists_norm_le_of_mem_subdifferential hf hbot hK hKD
  exact (hK.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset
    (isClosed_setOf_mem_subdifferential hbot hK.isClosed (hKD.trans interior_subset)
      ((convexOn_toReal hf hbot).continuousOn_interior.mono hKD))
    fun z hz => ⟨hz.1, mem_closedBall_zero_iff.2 (hR z.1 hz.1 z.2 hz.2)⟩

/-- **Subgradient images of compact sets are compact.** For a convex `f : E → EReal` on a
finite-dimensional real inner product space, the subgradient image of a compact subset of the
interior of the effective domain is compact. -/
theorem isCompact_subgradientImage {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    IsCompact (subgradientImage (innerₗ E) f K) := by
  convert (isCompact_setOf_mem_subdifferential hf hbot hK hKD).image continuous_snd using 1
  ext y
  simp

/-- **Subgradients exist in the interior of the domain.** A convex `f : E → EReal` on a
finite-dimensional real inner product space has a subgradient at every interior point of its
effective domain. -/
theorem nonempty_subdifferential_of_mem_interior {x : E} (hx : x ∈ interior {x | f x ≠ ⊤}) :
    (subdifferential (innerₗ E) f x).Nonempty := by
  -- On a closed ball `K` about `x` inside the domain, the graph `G` of the subdifferential is
  -- compact, so the set of points of `K` carrying a subgradient, its first projection, is closed.
  -- It contains every point of `K` at which the real representative is differentiable, since the
  -- gradient is a subgradient there, and these points are dense by Rademacher's theorem (for a
  -- Haar measure on `E` with its Borel σ-algebra).
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨r, hr, hrD⟩ : ∃ r > 0, closedBall x r ⊆ interior {x | f x ≠ ⊤} :=
    nhds_basis_closedBall.mem_iff.1 (isOpen_interior.mem_nhds hx)
  set G := {z : E × E | z.1 ∈ closedBall x r ∧ z.2 ∈ subdifferential (innerₗ E) f z.1}
  have hcl : x ∈ closure (Prod.fst '' G) := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨z, hz, hdz⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
      (measure_ball_pos (MeasureTheory.Measure.addHaar : MeasureTheory.Measure E) x
        (lt_min hε hr)).ne'
      (MeasureTheory.ae_restrict_of_ae
        (convexOn_toReal hf hbot).ae_differentiableAt_of_mem_interior)
    have hzK : z ∈ closedBall x r :=
      ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hz)
    refine ⟨z, ⟨(z, _), ⟨hzK, gradient_toReal_mem_subdifferential hf hbot
      (interior_subset (hrD hzK)) (hdz (hrD hzK))⟩, rfl⟩, ?_⟩
    rw [dist_comm]
    exact (mem_ball.1 hz).trans_le (min_le_left _ _)
  rw [((isCompact_setOf_mem_subdifferential hf hbot (isCompact_closedBall x r) hrD).image
    continuous_fst).isClosed.closure_eq] at hcl
  obtain ⟨⟨x₀, y⟩, hz, rfl⟩ := hcl
  exact ⟨y, hz.2⟩

open scoped Topology in
/-- If a convex `f : E → EReal` is finite at every point near `x`, then it has a subgradient at
every point near `x`. -/
theorem eventually_nonempty_subdifferential {x : E} (hdom : ∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) :
    ∀ᶠ x' in 𝓝 x, (subdifferential (innerₗ E) f x').Nonempty :=
  Filter.eventually_of_mem (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hdom))
    fun _ hx' => nonempty_subdifferential_of_mem_interior hf hbot hx'

open scoped Topology in
/-- **A unique subgradient at an interior domain point is the gradient.** If `f : E → EReal` has
convex real epigraph, never takes the value `⊥`, and has `y` as its only subgradient at an interior
point `x` of its effective domain, then `y` is the gradient of the real representative at `x`. -/
theorem hasGradientAt_toReal_of_forall_mem_subdifferential_eq {x y : E}
    (hx : x ∈ interior {x | f x ≠ ⊤})
    (hy : ∀ y' ∈ subdifferential (innerₗ E) f x, y' = y) :
    HasGradientAt (fun x' => (f x').toReal) y x := by
  classical
  obtain ⟨r, hr, hrD⟩ : ∃ r > 0, closedBall x r ⊆ interior {x | f x ≠ ⊤} :=
    nhds_basis_closedBall.mem_iff.1 (isOpen_interior.mem_nhds hx)
  let T : E → E := fun z =>
    if hz : z ∈ closedBall x r then
      (nonempty_subdifferential_of_mem_interior hf hbot (hrD hz)).choose
    else y
  have hTmem : ∀ z ∈ closedBall x r, T z ∈ subdifferential (innerₗ E) f z := fun z hz => by
    simpa only [T, dite_eq_left hz] using
      (nonempty_subdifferential_of_mem_interior hf hbot (hrD hz)).choose_spec
  have hTx : T x = y := hy _ (hTmem x (mem_closedBall_self hr.le))
  obtain ⟨R, hR⟩ := exists_norm_le_of_mem_subdifferential hf hbot (isCompact_closedBall x r) hrD
  have hclosed := isClosed_setOf_mem_subdifferential hbot isClosed_closedBall
    (hrD.trans interior_subset) ((convexOn_toReal hf hbot).continuousOn_interior.mono hrD)
  have hcont : ContinuousAt T x := by
    rw [ContinuousAt, hTx]
    refine (isCompact_closedBall (0 : E) R).tendsto_nhds_of_unique_mapClusterPt
      (Filter.eventually_of_mem (closedBall_mem_nhds x hr) fun z hz =>
        mem_closedBall_zero_iff.2 (hR z hz (T z) (hTmem z hz))) ?_
    intro q _ hq
    obtain ⟨w, hTw, hw⟩ := hq.exists_seq_tendsto
    have hmem : ∀ᶠ n in Filter.atTop,
        (w n, T (w n)) ∈ {z : E × E | z.1 ∈ closedBall x r ∧
          z.2 ∈ subdifferential (innerₗ E) f z.1} := by
      filter_upwards [hw.eventually (closedBall_mem_nhds x hr)] with n hn
      exact ⟨hn, hTmem (w n) hn⟩
    exact hy q (hclosed.mem_of_tendsto (hw.prodMk_nhds hTw) hmem).2
  exact hTx ▸ hasGradientAt_toReal_of_continuousAt_subgradient hcont
    (Filter.eventually_of_mem (closedBall_mem_nhds x hr) hTmem)

end FiniteDimensional

/-- If a function `f : E → EReal` with convex real epigraph takes the value `⊥` somewhere, then it
equals `⊥` at every interior point of its effective domain. -/
private theorem eq_bot_of_mem_interior_of_eq_bot {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → EReal} (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) {z₀ x : E}
    (hz₀ : f z₀ = ⊥) (hx : x ∈ interior {z | f z ≠ ⊤}) : f x = ⊥ := by
  have hcont : Continuous fun t : ℝ => x + t • (x - z₀) := by fun_prop
  have hnhds : (fun t : ℝ => x + t • (x - z₀)) ⁻¹' interior {z | f z ≠ ⊤} ∈ nhds (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds (by simpa using hx))
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.1 hnhds
  set t := δ / 2
  have ht : 0 < t := half_pos hδ
  have hw : x + t • (x - z₀) ∈ interior {z | f z ≠ ⊤} :=
    hδB (by rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]; exact half_lt_self hδ)
  have hwr : f (x + t • (x - z₀)) ≤ (f (x + t • (x - z₀))).toReal :=
    EReal.le_coe_toReal (interior_subset hw)
  set r := (f (x + t • (x - z₀))).toReal
  set a := t / (1 + t)
  set b := 1 / (1 + t)
  have ha : 0 < a := by positivity
  have hb : 0 ≤ b := by positivity
  have hab : a + b = 1 := by simp only [a, b]; field_simp; ring
  refine (EReal.eq_bot_iff_forall_lt _).2 fun c =>
    lt_of_le_of_lt ?_ (EReal.coe_lt_coe_iff.2 (sub_one_lt c))
  have hcomb := hf (x := (z₀, (c - 1 - b * r) / a)) (y := (x + t • (x - z₀), r))
    (by simp [hz₀]) hwr ha.le hb hab
  have hfst : a • z₀ + b • (x + t • (x - z₀)) = x := by
    simp only [a, b, smul_add, smul_smul, smul_sub]
    have h1 : 1 + t ≠ 0 := by positivity
    calc (t / (1 + t)) • z₀ +
          ((1 / (1 + t)) • x + ((1 / (1 + t) * t) • x - (1 / (1 + t) * t) • z₀))
        = ((1 + t) / (1 + t)) • x + ((t - t) / (1 + t)) • z₀ := by
          simp only [sub_self, zero_div, zero_smul, add_zero]
          module
      _ = x := by simp [div_self h1]
  have hsnd : a * ((c - 1 - b * r) / a) + b * r = c - 1 := by
    rw [mul_div_cancel₀ _ ha.ne']; ring
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hfst, hsnd, mem_ofPred_eq] using hcomb

section DifferentiableIff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Subgradient characterization of differentiability.** Let `f : E → EReal` have convex real
epigraph on a finite-dimensional real inner product space, and let `x` lie in the interior of its
effective domain. Then the real representative `x' ↦ (f x').toReal` is differentiable at `x` if and
only if `∂f(x)` has at most one element. -/
theorem differentiableAt_toReal_iff_subsingleton_subdifferential {f : E → EReal}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) {x : E} (hx : x ∈ interior {z | f z ≠ ⊤}) :
    DifferentiableAt ℝ (fun x' => (f x').toReal) x ↔
      (subdifferential (innerₗ E) f x).Subsingleton := by
  refine ⟨fun hd y₁ hy₁ y₂ hy₂ => ?_, fun hsub => ?_⟩
  · have hdom := mem_interior_iff_mem_nhds.1 hx
    rw [← gradient_toReal_eq_of_mem_subdifferential hy₁ hdom hd,
      ← gradient_toReal_eq_of_mem_subdifferential hy₂ hdom hd]
  · by_cases hbot : ∀ z, f z ≠ ⊥
    · obtain ⟨y, hy⟩ := nonempty_subdifferential_of_mem_interior hf hbot hx
      exact (hasGradientAt_toReal_of_forall_mem_subdifferential_eq hf hbot hx
        fun y' hy' => hsub hy' hy).differentiableAt
    · push Not at hbot
      obtain ⟨z₀, hz₀⟩ := hbot
      have hev : (fun x' => (f x').toReal) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_interior.mem_nhds hx] with x' hx'
        simp [eq_bot_of_mem_interior_of_eq_bot hf hz₀ hx']
      exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hev

end DifferentiableIff

section OpenDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Supporting hyperplanes of convex functions.** A real function convex on an open subset `Ω`
of a finite-dimensional real inner product space has a subgradient relative to `Ω` at every point
`x ∈ Ω`: some `p` satisfies `u x + ⟪y - x, p⟫ ≤ u y` for every `y ∈ Ω`. -/
theorem _root_.ConvexOn.exists_forall_add_inner_le {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω)
    (hu : ConvexOn ℝ Ω u) {x : E} (hx : x ∈ Ω) :
    ∃ p : E, ∀ y ∈ Ω, u x + inner ℝ (y - x) p ≤ u y := by
  classical
  obtain ⟨p, hp⟩ := nonempty_subdifferential_of_mem_interior
    (convexOn_iff_convex_epigraph_ite.1 hu) ite_ne_bot (by rwa [setOf_ite_ne_top, hΩ.interior_eq])
  exact ⟨p, by simpa only [innerₗ_apply_apply] using
    (mem_subdifferential_ite_iff (innerₗ E) hx).1 hp⟩

/-- **Subgradient characterization of differentiability on an open domain.** A real function `u`
convex on an open subset `Ω` of a finite-dimensional real inner product space is differentiable at
`x ∈ Ω` if and only if it has at most one subgradient relative to `Ω` at `x`. -/
theorem _root_.ConvexOn.differentiableAt_iff_subsingleton_subdifferential {Ω : Set E} {u : E → ℝ}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) {x : E} (hx : x ∈ Ω) :
    DifferentiableAt ℝ u x ↔ {p : E | ∀ y ∈ Ω, u x + inner ℝ (y - x) p ≤ u y}.Subsingleton := by
  classical
  let f : E → EReal := fun z => if z ∈ Ω then (u z : EReal) else ⊤
  have hev : (fun z => (f z).toReal) =ᶠ[nhds x] u := by
    filter_upwards [hΩ.mem_nhds hx] with z hz
    simp [f, hz]
  have hsub : subdifferential (innerₗ E) f x =
      {p : E | ∀ y ∈ Ω, u x + inner ℝ (y - x) p ≤ u y} := by
    ext p
    simpa only [f, innerₗ_apply_apply, mem_ofPred_eq] using
      mem_subdifferential_ite_iff (innerₗ E) hx
  rw [← hev.differentiableAt_iff, ← hsub]
  exact differentiableAt_toReal_iff_subsingleton_subdifferential
    (convexOn_iff_convex_epigraph_ite.1 hu) (by rwa [setOf_ite_ne_top, hΩ.interior_eq])

/-- At every point `x`, a real convex function `u` on `E` has a unique subgradient of minimal
norm. -/
private theorem existsUnique_mem_subdifferential_norm_le {u : E → ℝ} (hu : ConvexOn ℝ univ u)
    (x : E) :
    ∃! p : E, (∀ y, u x + inner ℝ (y - x) p ≤ u y) ∧
      ∀ q, (∀ y, u x + inner ℝ (y - x) q ≤ u y) → ‖p‖ ≤ ‖q‖ := by
  let f : E → EReal := fun z => (u z : EReal)
  have hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} := by
    simpa only [f, mem_univ, ite_true] using convexOn_iff_convex_epigraph_ite.1 hu
  have hbot : ∀ z, f z ≠ ⊥ := fun z => EReal.coe_ne_bot (u z)
  let K : Set E := subdifferential (innerₗ E) f x
  have hKmem : ∀ q, q ∈ K ↔ ∀ y, u x + inner ℝ (y - x) q ≤ u y := fun q => by
    simpa only [K, f, innerₗ_apply_apply] using mem_subdifferential_coe_iff (innerₗ E) u
  have hKne : K.Nonempty := by
    obtain ⟨p, hp⟩ := hu.exists_forall_add_inner_le isOpen_univ (mem_univ x)
    exact ⟨p, (hKmem p).2 fun y => hp y (mem_univ y)⟩
  have hKconv : Convex ℝ K := convex_subdifferential (innerₗ E) f x
  have hKcomp : IsCompact K := by
    have hD : ({x} : Set E) ⊆ interior {z | f z ≠ ⊤} := by simp [f]
    convert isCompact_subgradientImage hf hbot isCompact_singleton hD using 1
    ext p
    simp [K]
  obtain ⟨p, hpK, hpmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hKne hKcomp.isComplete hKconv (0 : E)
  have hple : ∀ q ∈ K, ‖p‖ ≤ ‖q‖ := fun q hq => by
    let wq : K := ⟨q, hq⟩
    have hle : ⨅ w : K, ‖(0 : E) - (w : E)‖ ≤ ‖(0 : E) - (wq : E)‖ :=
      ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ wq
    rw [← hpmin] at hle
    simpa [wq] using hle
  refine ⟨p, ⟨(hKmem p).1 hpK, fun q hq => hple q ((hKmem q).2 hq)⟩, fun p' ⟨hp'K, hp'le⟩ => ?_⟩
  have hp'K' : p' ∈ K := (hKmem p').2 hp'K
  have hp'min : ‖(0 : E) - p'‖ = ⨅ w : K, ‖(0 : E) - w‖ := by
    have heq : ‖p'‖ = ‖p‖ := le_antisymm (hp'le p ((hKmem p).1 hpK)) (hple p' hp'K')
    simpa [heq] using hpmin
  have h₁ := (norm_eq_iInf_iff_real_inner_le_zero hKconv hpK).1 hpmin p' hp'K'
  have h₂ := (norm_eq_iInf_iff_real_inner_le_zero hKconv hp'K').1 hp'min p hpK
  have hsq : ‖p' - p‖ ^ 2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [zero_sub, inner_neg_left] at h₁ h₂
    have h₃ : inner ℝ (p' - p) (p' - p) = inner ℝ p' (p' - p) - inner ℝ p (p' - p) :=
      inner_sub_left p' p (p' - p)
    have h₄ : -inner ℝ p' (p - p') = inner ℝ p' (p' - p) := by
      rw [← inner_neg_right, neg_sub]
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 (le_antisymm hsq (sq_nonneg _))))

/-- For a real convex function `u` on `E`, a closed set `F ⊆ E`, and `a : ℝ`, the set of points `x`
admitting a subgradient in `F` of norm at most `a` is Borel measurable. -/
private theorem measurableSet_exists_forall_add_inner_le_mem [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} (hu : ConvexOn ℝ univ u) {F : Set E} (hF : IsClosed F) (a : ℝ) :
    MeasurableSet {x : E | ∃ p ∈ F, (∀ y, u x + inner ℝ (y - x) p ≤ u y) ∧ ‖p‖ ≤ a} := by
  let f : E → EReal := fun z => (u z : EReal)
  have hbot : ∀ z, f z ≠ ⊥ := fun z => EReal.coe_ne_bot (u z)
  have hcontOn : ContinuousOn (fun z => (f z).toReal) univ := by
    simpa only [f, EReal.toReal_coe] using hu.continuousOn isOpen_univ
  have hG : IsClosed {z : E × E | z.2 ∈ subdifferential (innerₗ E) f z.1} := by
    simpa only [mem_univ, true_and] using isClosed_setOf_mem_subdifferential hbot isClosed_univ
      (fun z _ => EReal.coe_ne_top (u z)) hcontOn
  have heq : {x : E | ∃ p ∈ F, (∀ y, u x + inner ℝ (y - x) p ≤ u y) ∧ ‖p‖ ≤ a} =
      ⋃ R : ℕ, Prod.fst '' ({z : E × E | z.2 ∈ subdifferential (innerₗ E) f z.1} ∩
        (closedBall (0 : E) R ×ˢ (F ∩ closedBall (0 : E) a))) := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_image, Prod.exists, exists_and_right, exists_eq_right,
      mem_inter_iff, mem_prod, mem_closedBall_zero_iff]
    refine ⟨fun ⟨p, hpF, hp, hpa⟩ => ?_, fun ⟨_, p, hp, ⟨_, hpF, hpa⟩⟩ => ?_⟩
    · obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
      exact ⟨R, p, (mem_subdifferential_coe_iff (innerₗ E) u).2 fun y => by
        simpa only [innerₗ_apply_apply] using hp y, hR, hpF, hpa⟩
    · exact ⟨p, hpF, fun y => by
        simpa only [innerₗ_apply_apply] using (mem_subdifferential_coe_iff (innerₗ E) u).1 hp y,
        hpa⟩
  rw [heq]
  refine MeasurableSet.iUnion fun R => ?_
  have hcomp : IsCompact (closedBall (0 : E) R ×ˢ (F ∩ closedBall (0 : E) a)) :=
    (isCompact_closedBall 0 R).prod ((isCompact_closedBall 0 a).inter_left hF)
  exact ((hcomp.inter_left hG).image continuous_fst).isClosed.measurableSet

/-- A sequence of subgradients in a closed set `F` whose norms converge beneath `‖p‖ + 1 / (n + 1)`
forces the minimal-norm subgradient `p` to lie in `F`. -/
private theorem mem_of_forall_exists_mem_subdifferential_norm_lt {u : E → ℝ} {F : Set E}
    (hF : IsClosed F) {x p : E}
    (hp : (∀ y, u x + inner ℝ (y - x) p ≤ u y) ∧
      ∀ q, (∀ y, u x + inner ℝ (y - x) q ≤ u y) → ‖p‖ ≤ ‖q‖)
    (huniq : ∀ q, ((∀ y, u x + inner ℝ (y - x) q ≤ u y) ∧
      ∀ w, (∀ y, u x + inner ℝ (y - x) w ≤ u y) → ‖q‖ ≤ ‖w‖) → q = p)
    (hseq : ∀ n : ℕ, ∃ q ∈ F, (∀ y, u x + inner ℝ (y - x) q ≤ u y) ∧
      ‖q‖ < ‖p‖ + 1 / ((n : ℝ) + 1)) : p ∈ F := by
  choose g hgF hg hgn using hseq
  have hKcl : IsClosed (F ∩ {q : E | ∀ y, u x + inner ℝ (y - x) q ≤ u y}) := by
    refine hF.inter ?_
    have : {q : E | ∀ y, u x + inner ℝ (y - x) q ≤ u y} =
        ⋂ y : E, (fun q : E => u x + inner ℝ (y - x) q) ⁻¹' Iic (u y) := by ext q; simp
    rw [this]
    exact isClosed_iInter fun y => isClosed_Iic.preimage (by fun_prop)
  have hcomp : IsCompact ((F ∩ {q : E | ∀ y, u x + inner ℝ (y - x) q ≤ u y}) ∩
      closedBall 0 (‖p‖ + 1)) := (isCompact_closedBall 0 (‖p‖ + 1)).inter_left hKcl
  obtain ⟨q, hq, φ, hφ, hlim⟩ := hcomp.tendsto_subseq fun n => ⟨⟨hgF n, hg n⟩, by
    rw [mem_closedBall_zero_iff]
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 :=
      div_le_one_of_le₀ (le_add_of_nonneg_left n.cast_nonneg) (by positivity)
    linarith [hgn n]⟩
  have hub : Filter.Tendsto (fun k => ‖p‖ + 1 / ((φ k : ℝ) + 1)) Filter.atTop (nhds (‖p‖ + 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  rw [add_zero] at hub
  have hqnorm : ‖q‖ ≤ ‖p‖ :=
    le_of_tendsto_of_tendsto hlim.norm hub (Filter.Eventually.of_forall fun k => (hgn (φ k)).le)
  exact huniq q ⟨hq.1.2, fun w hw => hqnorm.trans (hp.2 w hw)⟩ ▸ hq.1.1

/-- **Borel measurable subgradient selection.** Every real function `u` convex on a
finite-dimensional real inner product space admits a Borel measurable map `T : E → E` such that
`T x` is a subgradient of `u` at `x` for every `x` (constructed as the unique subgradient of
minimal norm). -/
theorem _root_.ConvexOn.exists_measurable_forall_add_inner_le [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} (hu : ConvexOn ℝ univ u) :
    ∃ T : E → E, Measurable T ∧ ∀ x y, u x + inner ℝ (y - x) (T x) ≤ u y := by
  choose T hT hTuniq using existsUnique_mem_subdifferential_norm_le hu
  refine ⟨T, measurable_of_isClosed fun F hF => ?_, fun x y => (hT x).1 y⟩
  have hpre : T ⁻¹' F =
      ⋂ n : ℕ, ⋃ r : ℚ,
        {x : E | ∃ p ∈ F, (∀ y, u x + inner ℝ (y - x) p ≤ u y) ∧ ‖p‖ ≤ (r : ℝ)} ∩
        {x : E | ∃ q ∈ (univ : Set E), (∀ y, u x + inner ℝ (y - x) q ≤ u y) ∧
          ‖q‖ ≤ (r : ℝ) - 1 / ((n : ℝ) + 1)}ᶜ := by
    ext x
    simp only [mem_preimage, mem_iInter, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_ofPred_eq,
      mem_univ, true_and, not_exists, not_and, not_le]
    refine ⟨fun hxF n => ?_, fun hx =>
      mem_of_forall_exists_mem_subdifferential_norm_lt hF (hT x) (hTuniq x) fun n => ?_⟩
    · obtain ⟨r, hr₁, hr₂⟩ :=
        exists_rat_btwn (lt_add_of_pos_right ‖T x‖ (by positivity : (0 : ℝ) < 1 / (n + 1)))
      exact ⟨r, ⟨T x, hxF, (hT x).1, hr₁.le⟩, fun q hq => by linarith [(hT x).2 q hq]⟩
    · obtain ⟨r, ⟨p, hpF, hp, hpr⟩, hq⟩ := hx n
      exact ⟨p, hpF, hp, by linarith [hq (T x) (hT x).1]⟩
  rw [hpre]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun r =>
    (measurableSet_exists_forall_add_inner_le_mem hu hF r).inter
      (measurableSet_exists_forall_add_inner_le_mem hu isClosed_univ _).compl

/-- **Global convex Lipschitz envelope over a compact set.** Let `u` be convex on the whole of a
finite-dimensional real inner product space `E`, and let `K ⊆ E` be compact. Then `u` agrees on `K`
with a globally convex, globally Lipschitz function `v : E → ℝ` (constructed as the supremum of a
family of supporting affine functions over `K`). -/
theorem _root_.ConvexOn.exists_convexOn_lipschitzWith_eqOn {u : E → ℝ} (hu : ConvexOn ℝ univ u)
    {K : Set E} (hK : IsCompact K) :
    ∃ (L : NNReal) (v : E → ℝ), ConvexOn ℝ univ v ∧ LipschitzWith L v ∧ EqOn u v K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, 0, convexOn_const 0 convex_univ, LipschitzWith.const 0, by simp⟩
  have : Nonempty K := hKne.to_subtype
  let f : E → EReal := fun z => (u z : EReal)
  have hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} := by
    simpa only [f, mem_univ, ite_true] using convexOn_iff_convex_epigraph_ite.1 hu
  obtain ⟨M, hM⟩ := exists_norm_le_of_mem_subdifferential hf (fun z => EReal.coe_ne_bot (u z))
    hK (by simp [f])
  let L : NNReal := ⟨max M 0, le_max_right _ _⟩
  choose p hp using fun z : K => hu.exists_forall_add_inner_le isOpen_univ (mem_univ (z : E))
  have hpL : ∀ z : K, ‖p z‖ ≤ (L : ℝ) := fun z => (hM z z.2 (p z)
    ((mem_subdifferential_coe_iff (innerₗ E) u).2 fun y => by
      simpa only [innerₗ_apply_apply] using hp z y (mem_univ y))).trans (le_max_left _ _)
  let g : K → E → ℝ := fun z y => u z + inner ℝ (y - z) (p z)
  have hbdd : ∀ y, BddAbove (range fun z : K => g z y) := fun y =>
    ⟨u y, forall_mem_range.2 fun z => hp z y (mem_univ y)⟩
  let v : E → ℝ := fun y => ⨆ z : K, g z y
  have hstep : ∀ y₁ y₂, v y₁ - v y₂ ≤ (L : ℝ) * dist y₁ y₂ := fun y₁ y₂ => by
    rw [sub_le_iff_le_add]
    refine ciSup_le fun z => ?_
    have hlin : g z y₁ = g z y₂ + inner ℝ (y₁ - y₂) (p z) := by
      simp only [g, inner_sub_left]; ring
    have hcs : inner ℝ (y₁ - y₂) (p z) ≤ (L : ℝ) * dist y₁ y₂ :=
      (real_inner_le_norm _ _).trans <| by
        rw [mul_comm, ← dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (hpL z) dist_nonneg
    linarith [le_ciSup (hbdd y₂) z]
  refine ⟨L, v, ⟨convex_univ, fun x _ y _ a b ha hb hab => ciSup_le fun z => ?_⟩,
    lipschitzWith_iff_dist_le_mul.2 fun y₁ y₂ => ?_, fun y hy => le_antisymm ?_ ?_⟩
  · have haff : g z (a • x + b • y) = a * g z x + b * g z y := by
      simp only [g, inner_sub_left, inner_add_left, real_inner_smul_left]
      linear_combination (u z - inner ℝ (z : E) (p z)) * hab.symm
    exact haff.le.trans (add_le_add (mul_le_mul_of_nonneg_left (le_ciSup (hbdd x) z) ha)
      (mul_le_mul_of_nonneg_left (le_ciSup (hbdd y) z) hb))
  · rw [Real.dist_eq, abs_sub_le_iff]
    exact ⟨hstep y₁ y₂, dist_comm y₁ y₂ ▸ hstep y₂ y₁⟩
  · simpa [g] using le_ciSup (hbdd y) ⟨y, hy⟩
  · exact ciSup_le fun z => hp z y (mem_univ y)

end OpenDomain

section CompactClosure

/-- A slope of an affine function through a graph point over the domain that lies below `u` on
the frontier is a supporting slope on the closure at some point of the domain. -/
theorem exists_forall_add_apply_le_of_forall_frontier
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} {u : E → ℝ}
    (hS : IsCompact (closure S)) (hu : ContinuousOn u (closure S)) {x₀ : E} (hx₀ : x₀ ∈ S)
    {p : E →L[ℝ] ℝ} (hp : ∀ y ∈ frontier S, u x₀ + p (y - x₀) ≤ u y) :
    ∃ x ∈ S, ∀ y ∈ closure S, u x + p (y - x) ≤ u y := by
  let φ := fun x => u x - p x
  have hφ : ContinuousOn φ (closure S) := hu.sub p.continuous.continuousOn
  obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn ⟨x₀, subset_closure hx₀⟩ hφ
  by_cases hxs : x ∈ S
  · refine ⟨x, hxs, fun y hy => ?_⟩
    have h := isMinOn_iff.1 hmin y hy
    simp only [φ] at h
    rw [map_sub]
    linarith
  · refine ⟨x₀, hx₀, fun y hy => ?_⟩
    have h := isMinOn_iff.1 hmin y hy
    have hfront := hp x ⟨hx, fun hi => hxs (interior_subset hi)⟩
    simp only [φ] at h
    rw [map_sub] at hfront ⊢
    linarith

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Slopes below the boundary values are subgradients.** Let `Ω` have compact closure, let `u`
be continuous on its closure, and let `x₀ ∈ Ω`. If the affine function
`x ↦ u x₀ + ⟪x - x₀, p⟫` lies below `u`
on the frontier of `Ω`, then `p` is a subgradient of `u` relative to `Ω` at some point `x₁ ∈ Ω`:
`u x₁ + ⟪x - x₁, p⟫ ≤ u x` for every `x ∈ Ω`. -/
theorem exists_forall_add_inner_le_of_forall_frontier {Ω : Set E} {u : E → ℝ}
    (hΩ : IsCompact (closure Ω)) (hu : ContinuousOn u (closure Ω)) {x₀ : E} (hx₀ : x₀ ∈ Ω)
    {p : E} (hp : ∀ x ∈ frontier Ω, u x₀ + inner ℝ (x - x₀) p ≤ u x) :
    ∃ x₁ ∈ Ω, ∀ x ∈ Ω, u x₁ + inner ℝ (x - x₁) p ≤ u x := by
  obtain ⟨x, hx, h⟩ := exists_forall_add_apply_le_of_forall_frontier hΩ hu hx₀
    (p := innerSL ℝ p) (fun y hy => by
      simpa only [innerSL_apply_apply, real_inner_comm p (y - x₀)] using hp y hy)
  refine ⟨x, hx, fun y hy => ?_⟩
  simpa only [innerSL_apply_apply, real_inner_comm p (y - x)] using h y (subset_closure hy)

/-- **Supporting slopes of a function lying above at `x₀` and below on the frontier.** Let `Ω` have
compact closure, let `u` and `w` be continuous on its closure with `w ≤ u` on the frontier of `Ω`,
and let `p` be a subgradient of `w` relative to `Ω` at `x₀ ∈ Ω`. Then for every `q` with
`‖q‖ * diam Ω ≤ w x₀ - u x₀`, the slope `p + q` is a subgradient of `u` relative to `Ω` at some
point `x₁ ∈ Ω`. For `q = 0` this says that the subgradients of `w` at points where `u ≤ w` are
subgradients of `u`. -/
theorem exists_forall_add_inner_add_le_of_forall_frontier_le {Ω : Set E}
    {u w : E → ℝ} (hΩ : IsCompact (closure Ω)) (hu : ContinuousOn u (closure Ω))
    (hw : ContinuousOn w (closure Ω)) (hfr : ∀ x ∈ frontier Ω, w x ≤ u x) {x₀ : E}
    (hx₀ : x₀ ∈ Ω) {p q : E} (hp : ∀ x ∈ Ω, w x₀ + inner ℝ (x - x₀) p ≤ w x)
    (hq : ‖q‖ * diam Ω ≤ w x₀ - u x₀) :
    ∃ x₁ ∈ Ω, ∀ x ∈ Ω, u x₁ + inner ℝ (x - x₁) (p + q) ≤ u x := by
  -- The affine function through `(x₀, u x₀)` with slope `p + q` lies below `w` on the frontier.
  refine exists_forall_add_inner_le_of_forall_frontier hΩ hu hx₀ fun x hx => ?_
  have hxc := frontier_subset_closure hx
  have h₁ : w x₀ + inner ℝ (x - x₀) p ≤ w x := le_on_closure hp (continuousOn_const.add
    ((continuous_id.sub continuous_const).inner continuous_const).continuousOn) hw hxc
  have h₂ : inner ℝ (x - x₀) q ≤ ‖q‖ * diam Ω := by
    refine (real_inner_le_norm _ _).trans ?_
    rw [mul_comm, ← dist_eq_norm, ← diam_closure Ω]
    gcongr
    exact dist_le_diam_of_mem hΩ.isBounded hxc (subset_closure hx₀)
  rw [inner_add_right]
  linarith [hfr x hx]

end CompactClosure

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped Topology in
/-- **Subgradients are eventually locally bounded.** Let `F k → u` locally uniformly on an open
set `Ω`, with `u` continuous on `Ω`, and let `K ⊆ Ω` be compact. Then the subgradients of `F k`
relative to `Ω` at points of `K` are eventually bounded, uniformly in `k`. -/
theorem exists_eventually_norm_le_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι}
    {F : ι → E → ℝ} {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hFu : TendstoLocallyUniformlyOn F u l Ω) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ R, ∀ᶠ k in l, ∀ x ∈ K, ∀ y, (∀ x' ∈ Ω, F k x + inner ℝ (x' - x) y ≤ F k x') →
      ‖y‖ ≤ R := by
  -- Compact induction combines finitely many local bounds by taking their maximum.
  -- Each local bound controls a smaller ball, leaving room for the norm estimate at its points.
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨0, Filter.Eventually.of_forall fun _ x hx => (notMem_empty x hx).elim⟩
  · rintro s t hst ⟨R, hR⟩
    exact ⟨R, hR.mono fun _ hk x hx => hk x (hst hx)⟩
  · rintro s t ⟨R, hR⟩ ⟨S, hS⟩
    refine ⟨max R S, ?_⟩
    filter_upwards [hR, hS] with k hkR hkS x hx y hy
    rcases hx with hx | hx
    · exact (hkR x hx y hy).trans (le_max_left _ _)
    · exact (hkS x hx y hy).trans (le_max_right _ _)
  · intro x hx
    have hxΩ := hKΩ hx
    obtain ⟨t, ht, hFt⟩ := hFu _ (dist_mem_uniformity zero_lt_one) x hxΩ
    rw [hΩ.nhdsWithin_eq hxΩ] at ht
    have hux : ∀ᶠ z in 𝓝 x, |u z| < |u x| + 1 :=
      (hu.continuousAt (hΩ.mem_nhds hxΩ)).abs.eventually_lt_const (lt_add_one _)
    obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.1
      (Filter.inter_mem (Filter.inter_mem (hΩ.mem_nhds hxΩ) ht) hux)
    refine ⟨ball x (r / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (half_pos hr)),
      2 * (|u x| + 2) / (r / 2), ?_⟩
    filter_upwards [hFt] with k hk z hz y hy
    have hsub : closedBall z (r / 2) ⊆ closedBall x r :=
      closedBall_subset_closedBall' (by linarith [mem_ball.1 hz])
    rw [le_div_iff₀ (half_pos hr), mul_comm]
    refine mul_norm_le_of_forall_add_inner_le (half_pos hr).le
      (fun w hw => (hball (hsub hw)).1.1) (fun w hw => ?_) hy
    have hw' := hball (hsub hw)
    have huw : |u w| < |u x| + 1 := hw'.2
    have hF : |F k w - u w| < 1 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hk w hw'.1.2
    linarith [abs_sub_abs_le_abs_sub (F k w) (u w)]

end Seminormed

section Proper

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- **Upper semicontinuity of subgradient images.** Let `F k → u` locally uniformly on an open
set `Ω`, with `u` continuous on `Ω`, and let `K ⊆ Ω` be compact. Then every open set `V`
containing the subgradients of `u` relative to `Ω` at points of `K` eventually contains the
subgradients of `F k` relative to `Ω` at points of `K`. -/
theorem eventually_biUnion_subset_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι}
    {F : ι → E → ℝ} {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hFu : TendstoLocallyUniformlyOn F u l Ω) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {V : Set E} (hV : IsOpen V)
    (hKV : ⋃ x ∈ K, {y | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x'} ⊆ V) :
    ∀ᶠ k in l, ⋃ x ∈ K, {y | ∀ x' ∈ Ω, F k x + inner ℝ (x' - x) y ≤ F k x'} ⊆ V := by
  obtain ⟨R, hbd⟩ := exists_eventually_norm_le_of_tendstoLocallyUniformlyOn hΩ hu hFu hK hKΩ
  -- A pair `(x, y)` with `x ∈ K`, `‖y‖ ≤ R` and `y ∉ V` violates one of the relaxed subgradient
  -- inequalities `u x + ⟪x' - x, y⟫ ≤ u x' + η`; by compactness, finitely many of them suffice.
  set Z : Ω × Ioi (0 : ℝ) → Set (E × E) := fun i =>
    {p | p.1 ∈ closure K ∧ u p.1 + inner ℝ ((i.1 : E) - p.1) p.2 ≤ u i.1 + i.2}
  have hZ : ∀ i, IsClosed (Z i) := fun i => by
    have : Z i = (closure K ×ˢ univ) ∩
        (fun p : E × E => u p.1 + inner ℝ ((i.1 : E) - p.1) p.2) ⁻¹' Iic (u i.1 + i.2) := by
      ext p
      simp [Z]
    rw [this]
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (isClosed_closure.prod isClosed_univ)
      isClosed_Iic
    exact ((hu.mono (hK.closure_subset_of_isOpen hΩ hKΩ)).comp continuousOn_fst
      fun p (hp : p ∈ closure K ×ˢ univ) => hp.1).add
      ((continuous_const.sub continuous_fst).inner continuous_snd).continuousOn
  have hempty : Disjoint (K ×ˢ (closedBall (0 : E) R \ V)) (⋂ i, Z i) := by
    refine disjoint_left.2 ?_
    rintro p ⟨hpK, -, hpV⟩ hpZ
    refine hpV (hKV ?_)
    refine mem_biUnion hpK fun x' hx' => le_of_forall_pos_le_add fun η hη => ?_
    exact (mem_iInter.1 hpZ ⟨⟨x', hx'⟩, ⟨η, hη⟩⟩).2
  obtain ⟨t, ht⟩ := (hK.prod ((isCompact_closedBall _ _).diff hV)).elim_finite_subfamily_closed
    Z hZ hempty
  -- Eventually `|F k - u| < η / 2` on `K` and at `x'` for each of these finitely many `(x', η)`.
  have hclose : ∀ᶠ k in l, ∀ i ∈ t, |F k i.1 - u i.1| < (i.2 : ℝ) / 2 ∧
      ∀ x ∈ K, |F k x - u x| < (i.2 : ℝ) / 2 := by
    refine (Filter.eventually_all_finset t).2 fun i _ => ?_
    have hi : 0 < (i.2 : ℝ) / 2 := half_pos i.2.2
    filter_upwards [hFu.eventually_forall_dist_lt isCompact_singleton
      (singleton_subset_iff.2 i.1.2) hi, hFu.eventually_forall_dist_lt hK hKΩ hi] with k h₁ h₂
    simp only [Real.dist_eq] at h₁ h₂
    exact ⟨h₁ _ rfl, h₂⟩
  filter_upwards [hbd, hclose] with k hk hk' y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 hy
  by_contra hyV
  have hmem : (x, y) ∈ K ×ˢ (closedBall (0 : E) R \ V) :=
    ⟨hx, mem_closedBall_zero_iff.2 (hk x hx y hxy), hyV⟩
  refine disjoint_left.1 ht hmem (mem_iInter₂.2 fun i hi => ⟨subset_closure hx, ?_⟩)
  obtain ⟨h₁, h₂⟩ := hk' i hi
  have h₃ := hxy i.1 i.1.2
  dsimp only
  linarith [(abs_lt.1 h₁).2, (abs_lt.1 (h₂ x hx)).1]

end Proper

end TauCeti

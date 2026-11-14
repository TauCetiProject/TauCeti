/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.EffectiveDomain
public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.Convex.Differentiability
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

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
in particular a real function convex on an open set has a supporting hyperplane at each point.
At a point of `D` where the subgradient is unique, compactness of the graph forces any local
subgradient selection to be continuous there, so `f` is differentiable at points of `D` with
subsingleton subdifferential.

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
* `TauCeti.mem_interior_setOf_ne_top_of_subsingleton_subdifferential`,
  `TauCeti.hasGradientAt_toReal_of_subsingleton_subdifferential`, and
  `TauCeti.differentiableAt_toReal_iff_subsingleton_subdifferential` — a unique subgradient forces
  an interior effective-domain point, where differentiability is equivalent to uniqueness of the
  subgradient;
* `ConvexOn.exists_forall_add_inner_le` — a real function convex on an open set has a subgradient
  relative to that set at each of its points;
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

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorems 24.7
  and 25.1.
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

/-- If an `EReal`-valued function with convex epigraph takes the value `⊥` somewhere, then it is
identically `⊥` on the interior of `{z | f z ≠ ⊤}` (Rockafellar, Theorem 7.2). -/
theorem eq_bot_of_mem_interior_of_eq_bot {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → EReal} (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) {z₀ y : E}
    (hz₀ : f z₀ = ⊥) (hy : y ∈ interior {z | f z ≠ ⊤}) : f y = ⊥ := by
  have hg : Continuous fun t : ℝ => y + t • (y - z₀) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : {t : ℝ | y + t • (y - z₀) ∈ interior {z | f z ≠ ⊤}} ∈ nhds (0 : ℝ) :=
    hg.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds (by simpa using hy))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hmem
  set δ := r / 2
  have hδ : 0 < δ := half_pos hr
  set w := y + δ • (y - z₀)
  have hfw : f w ≠ ⊤ := interior_subset <| hball <| Metric.mem_ball.2 <| by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact half_lt_self hr
  set M := (f w).toReal
  have hwM : f w ≤ M := by
    rcases eq_or_ne (f w) ⊥ with h | h
    · simp [h]
    · exact (EReal.coe_toReal hfw h).ge
  by_contra hybot
  have hytop : f y ≠ ⊤ := interior_subset hy
  set c := (f y).toReal - 1
  set a := δ / (1 + δ)
  set b := 1 / (1 + δ)
  have ha : 0 < a := div_pos hδ (by linarith)
  have hb : 0 ≤ b := div_nonneg zero_le_one (by linarith)
  have hab : a + b = 1 := by simp only [a, b]; field_simp; ring
  have hcomb := hf (x := (z₀, (c - b * M) / a)) (y := (w, M))
    (by simp [hz₀]) hwM ha.le hb hab
  have hfst : a • z₀ + b • w = y := by
    have ha' : a - b * δ = 0 := by simp only [a, b]; field_simp; ring
    have hb' : b * (1 + δ) = 1 := by simp only [b]; field_simp
    calc a • z₀ + b • w
        = (a - b * δ) • z₀ + (b * (1 + δ)) • y := by dsimp only [w]; module
      _ = y := by rw [ha', hb', zero_smul, one_smul, zero_add]
  have hsnd : a * ((c - b * M) / a) + b * M = c := by
    rw [mul_div_cancel₀ _ ha.ne', sub_add_cancel]
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hfst, hsnd, mem_ofPred_eq] at hcomb
  rw [← EReal.coe_toReal hytop hybot, EReal.coe_le_coe_iff] at hcomb
  linarith

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

omit hbot in
/-- **A unique subgradient forces an interior effective-domain point** (Rockafellar, Theorem 23.4).
If a convex `f : E → EReal` on a finite-dimensional real inner product space has a unique
subgradient at `x`, then `x` lies in the interior of `{z | f z ≠ ⊤}`. -/
theorem mem_interior_setOf_ne_top_of_subsingleton_subdifferential {x y : E}
    (hy : y ∈ subdifferential (innerₗ E) f x)
    (hsub : (subdifferential (innerₗ E) f x).Subsingleton) :
    x ∈ interior {z | f z ≠ ⊤} := by
  by_contra hx
  set C := {z | f z ≠ ⊤}
  have hC : Convex ℝ C := convex_setOf_ne_top hf
  have hxC : x ∈ C := ne_top_of_mem_subdifferential (innerₗ E) hy
  suffices ∃ w : E, w ≠ 0 ∧ ∀ z ∈ C, inner ℝ (z - x) w ≤ 0 by
    obtain ⟨w, hw0, hw⟩ := this
    have hyw : y + w ∈ subdifferential (innerₗ E) f x := by
      rw [mem_subdifferential_iff]
      refine ⟨ne_bot_of_mem_subdifferential (innerₗ E) hy, hxC, fun z => ?_⟩
      by_cases hz : f z = ⊤
      · simp [hz]
      · refine le_trans ?_ (add_le_of_mem_subdifferential (innerₗ E) hy z)
        rw [innerₗ_apply_apply, innerₗ_apply_apply, inner_add_right]
        exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by linarith [hw z hz]))
    exact hw0 (by simpa using hsub hyw hy)
  rcases (interior C).eq_empty_or_nonempty with hemp | hne
  · have hspan : affineSpan ℝ C ≠ ⊤ :=
      fun htop => (hC.interior_nonempty_iff_affineSpan_eq_top.2 htop).ne_empty hemp
    have hdir : (affineSpan ℝ C).direction ≠ ⊤ := fun htop =>
      hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ⟨x, subset_affineSpan ℝ C hxC⟩).1 htop)
    have horth : (affineSpan ℝ C).directionᗮ ≠ ⊥ := fun hbot => hdir <| by
      rw [← (affineSpan ℝ C).direction.orthogonal_orthogonal, hbot,
        Submodule.bot_orthogonal_eq_top]
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 horth
    refine ⟨w, hw0, fun z hz => le_of_eq ?_⟩
    have hsub' : z - x ∈ (affineSpan ℝ C).direction := by
      simpa only [vsub_eq_sub] using
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hz) (subset_affineSpan ℝ C hxC)
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).1 hw _ hsub'
  · obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hC.interior isOpen_interior hx
    set w := (InnerProductSpace.toDual ℝ E).symm φ
    have hφw (z : E) : φ z = inner ℝ w z := InnerProductSpace.toDual_symm_apply.symm
    have hw0 : w ≠ 0 := by
      intro hw0
      obtain ⟨a, ha⟩ := hne
      simpa [hφw, hw0] using hφ a ha
    refine ⟨w, hw0, fun z hz => ?_⟩
    have hzcl : z ∈ closure (interior C) :=
      (hC.closure_interior_eq_closure_of_nonempty_interior hne).symm ▸ subset_closure hz
    have hle : φ z ≤ φ x :=
      le_on_closure (fun a ha => (hφ a ha).le) φ.continuous.continuousOn continuousOn_const hzcl
    rw [hφw, hφw] at hle
    rw [real_inner_comm, inner_sub_right]
    linarith

omit hbot in
open scoped Topology in
/-- **Uniqueness of the subgradient implies differentiability.** For a convex `f : E → EReal` on a
finite-dimensional real inner product space, if `y` is the only subgradient of `f` at `x`, then `y`
is the gradient of the real representative of `f` at `x`. -/
theorem hasGradientAt_toReal_of_subsingleton_subdifferential {x y : E}
    (hy : y ∈ subdifferential (innerₗ E) f x)
    (hsub : (subdifferential (innerₗ E) f x).Subsingleton) :
    HasGradientAt (fun z => (f z).toReal) y x := by
  have hbot : ∀ z, f z ≠ ⊥ := apply_ne_bot_of_mem_subdifferential (innerₗ E) hy
  have hx : x ∈ interior {z | f z ≠ ⊤} :=
    mem_interior_setOf_ne_top_of_subsingleton_subdifferential hf hy hsub
  obtain ⟨r, hr, hrD⟩ : ∃ r > 0, closedBall x r ⊆ interior {z | f z ≠ ⊤} :=
    nhds_basis_closedBall.mem_iff.1 (isOpen_interior.mem_nhds hx)
  have hex : ∀ z, ∃ w, z ∈ closedBall x r → w ∈ subdifferential (innerₗ E) f z := fun z => by
    by_cases hz : z ∈ closedBall x r
    · obtain ⟨w, hw⟩ := nonempty_subdifferential_of_mem_interior hf hbot (hrD hz)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨y, fun hz' => (hz hz').elim⟩
  choose T hTz using hex
  have hTx : T x = y := hsub (hTz x (mem_closedBall_self hr.le)) hy
  -- Compactness of the subdifferential graph over the closed ball makes `T` continuous at `x`.
  have hG := isCompact_setOf_mem_subdifferential hf hbot (isCompact_closedBall x r) hrD
  have hcont : ContinuousAt T x := by
    intro V hV
    obtain ⟨U, hUV, hU, hxU⟩ := _root_.mem_nhds_iff.1 hV
    have hF : IsClosed (Prod.fst '' ({z : E × E | z.1 ∈ closedBall x r ∧
        z.2 ∈ subdifferential (innerₗ E) f z.1} \ Prod.snd ⁻¹' U)) :=
      ((hG.diff (hU.preimage continuous_snd)).image continuous_fst).isClosed
    have hxF : x ∉ Prod.fst '' ({z : E × E | z.1 ∈ closedBall x r ∧
        z.2 ∈ subdifferential (innerₗ E) f z.1} \ Prod.snd ⁻¹' U) := by
      rintro ⟨⟨z, w⟩, ⟨⟨-, hw⟩, hwU⟩, rfl⟩
      dsimp only at hw
      exact hwU (show w ∈ U from hsub (hTz z (mem_closedBall_self hr.le)) hw ▸ hxU)
    rw [Filter.mem_map]
    filter_upwards [closedBall_mem_nhds x hr, hF.compl_mem_nhds hxF] with z hzK hzF
    exact hUV (by_contra fun hzU => hzF ⟨(z, T z), ⟨⟨hzK, hTz z hzK⟩, hzU⟩, rfl⟩)
  refine hTx ▸ hasGradientAt_toReal_of_continuousAt_subgradient hcont ?_
  filter_upwards [closedBall_mem_nhds x hr] with z hzK using hTz z hzK

omit hbot in
open scoped Topology in
/-- **Characterization of differentiability by a unique subgradient** (Rockafellar, Theorem 25.1).
At an interior point `x` of the effective domain of a convex `f : E → EReal` on a
finite-dimensional real inner product space, the real representative of `f` is differentiable at
`x` if and only if the subdifferential of `f` at `x` has at most one element. -/
theorem differentiableAt_toReal_iff_subsingleton_subdifferential {x : E}
    (hx : x ∈ interior {z | f z ≠ ⊤}) :
    DifferentiableAt ℝ (fun z => (f z).toReal) x ↔
      (subdifferential (innerₗ E) f x).Subsingleton := by
  by_cases hbot : ∀ z, f z ≠ ⊥
  · refine ⟨fun hd y₁ hy₁ y₂ hy₂ => ?_, fun hsub => ?_⟩
    · have hdom := mem_interior_iff_mem_nhds.1 hx
      exact (gradient_toReal_eq_of_mem_subdifferential hy₁ hdom hd).symm.trans
        (gradient_toReal_eq_of_mem_subdifferential hy₂ hdom hd)
    · obtain ⟨y, hy⟩ := nonempty_subdifferential_of_mem_interior hf hbot hx
      exact (hasGradientAt_toReal_of_subsingleton_subdifferential hf hy hsub).differentiableAt
  · push Not at hbot
    obtain ⟨z₀, hz₀⟩ := hbot
    have hd : DifferentiableAt ℝ (fun z => (f z).toReal) x := by
      refine (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_interior.mem_nhds hx] with z hz
      simp [eq_bot_of_mem_interior_of_eq_bot hf hz₀ hz]
    rw [subdifferential_eq_empty_of_eq_bot (innerₗ E) (eq_bot_of_mem_interior_of_eq_bot hf hz₀ hx)]
    exact ⟨fun _ => subsingleton_empty, fun _ => hd⟩

end FiniteDimensional

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

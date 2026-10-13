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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Continuous

/-!
# Compactness of subgradient images of convex functions

Let `E` be a finite-dimensional real inner product space and let `f : E → EReal` be convex
(convex real epigraph, never `⊥`), with `D` the interior of its effective domain `{x | f x ≠ ⊤}`.
Since `f` is continuous on `D`, its subgradients for the inner product are bounded over every
compact `K ⊆ D`, and the graph of the subdifferential over a closed `K ⊆ D` is closed. Hence
the subgradient image `∂f(K) = ⋃ x ∈ K, ∂f(x)` of a compact subset of `D` is compact.

For a real function `u` continuous on the closure of a bounded set `Ω`, every slope of an affine
function through a point of the graph over `Ω` that lies below `u` on the frontier of `Ω` is a
subgradient of `u` relative to `Ω` at some point of `Ω`. Consequently, if `w ≤ u` on the frontier
of `Ω`, the subgradients of `w` relative to `Ω` at points where `u < w`, and their small
perturbations, are subgradients of `u` relative to `Ω`: this is the comparison step behind the
comparison principle for the Monge–Ampère equation.

If real functions `F k` converge to `u` locally uniformly on an open set `Ω`, with `u` continuous
on `Ω`, the subgradients of `F k` relative to `Ω` at points of a compact `K ⊆ Ω` are eventually
bounded, and every open neighbourhood of the subgradient image of `K` under `u` eventually
contains that of `K` under `F k`.

## Main statements

* `TauCeti.mul_norm_le_of_forall_add_inner_le` — a subgradient of `u` at `x` relative to `Ω` is
  bounded in terms of a bound for `|u|` on a ball about `x` inside `Ω`;
* `TauCeti.exists_norm_le_of_mem_subdifferential` — the subgradients of `f` are bounded over
  compact subsets of `D`;
* `TauCeti.isClosed_setOf_mem_subdifferential` — the graph of the subdifferential over a closed
  subset of `D` is closed;
* `TauCeti.isCompact_subgradientImage` — the subgradient image of a compact subset of `D` is
  compact;
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
include hf hbot

omit [FiniteDimensional ℝ E] hf hbot in
/-- **Subgradients are bounded by the size of the function.** If `y` is a subgradient of `u`
relative to `Ω` at `x`, the closed ball of radius `δ ≥ 0` about `x` lies in `Ω`, and `|u| ≤ M` on
that ball, then `δ * ‖y‖ ≤ 2 * M`. -/
theorem mul_norm_le_of_forall_add_inner_le {Ω : Set E} {u : E → ℝ} {x y : E} {δ M : ℝ}
    (hδ : 0 ≤ δ) (hΩ : closedBall x δ ⊆ Ω) (hM : ∀ z ∈ closedBall x δ, |u z| ≤ M)
    (hy : ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x') : δ * ‖y‖ ≤ 2 * M := by
  have hx := (abs_le.1 (hM x (mem_closedBall_self hδ))).1
  rcases eq_or_ne y 0 with rfl | hy0
  · have := (abs_le.1 (hM x (mem_closedBall_self hδ))).2
    simp only [norm_zero, mul_zero]
    linarith
  -- Compare `u` at `x` and at the point `x + δ • y / ‖y‖` of the sphere in the direction `y`.
  have hy0' : 0 < ‖y‖ := norm_pos_iff.2 hy0
  set x' := x + (δ / ‖y‖) • y
  have hx' : x' ∈ closedBall x δ := by
    simp [x', dist_eq_norm, norm_smul, hy0'.ne', abs_of_nonneg hδ]
  have hinner : inner ℝ (x' - x) y = δ * ‖y‖ := by
    simp only [x', add_sub_cancel_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h := hy x' (hΩ hx')
  rw [hinner] at h
  linarith [(abs_le.1 (hM x' hx')).2]

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

/-- The graph of the subdifferential of a convex `f : E → EReal` over a closed subset `K` of the
interior of the effective domain is closed. -/
theorem isClosed_setOf_mem_subdifferential {K : Set E} (hK : IsClosed K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
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
    rw [mem_subdifferential_iff_forall_toReal_add_le _ hbot (interior_subset (hKD hx))]
    exact forall₂_congr fun x' _ => (and_iff_right hx).symm
  rw [hG]
  refine (hK.prod isClosed_univ).inter (isClosed_biInter fun x' _ => ?_)
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hK.prod isClosed_univ)
    isClosed_Iic
  refine ContinuousOn.add (((convexOn_toReal hf hbot).continuousOn_interior.mono hKD).comp
    continuousOn_fst fun z hz => hz.1) ?_
  simp only [innerₗ_apply_apply]
  exact ((continuous_const.sub continuous_fst).inner continuous_snd).continuousOn

/-- **Subgradient images of compact sets are compact.** For a convex `f : E → EReal` on a
finite-dimensional real inner product space, the subgradient image of a compact subset of the
interior of the effective domain is compact. -/
theorem isCompact_subgradientImage {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    IsCompact (subgradientImage (innerₗ E) f K) := by
  obtain ⟨R, hR⟩ := exists_norm_le_of_mem_subdifferential hf hbot hK hKD
  have hG : IsCompact {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} :=
    (hK.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset
      (isClosed_setOf_mem_subdifferential hf hbot hK.isClosed hKD)
      fun z hz => ⟨hz.1, mem_closedBall_zero_iff.2 (hR z.1 hz.1 z.2 hz.2)⟩
  convert hG.image continuous_snd using 1
  ext y
  simp

omit [FiniteDimensional ℝ E] hf hbot in
/-- **Slopes below the boundary values are subgradients.** Let `Ω` be bounded and `u` continuous
on its closure, and let `x₀ ∈ Ω`. If the affine function `x ↦ u x₀ + ⟪x - x₀, p⟫` lies below `u`
on the frontier of `Ω`, then `p` is a subgradient of `u` relative to `Ω` at some point `x₁ ∈ Ω`:
`u x₁ + ⟪x - x₁, p⟫ ≤ u x` for every `x ∈ Ω`. -/
theorem exists_forall_add_inner_le_of_forall_frontier [ProperSpace E] {Ω : Set E} {u : E → ℝ}
    (hΩ : Bornology.IsBounded Ω) (hu : ContinuousOn u (closure Ω)) {x₀ : E} (hx₀ : x₀ ∈ Ω)
    {p : E} (hp : ∀ x ∈ frontier Ω, u x₀ + inner ℝ (x - x₀) p ≤ u x) :
    ∃ x₁ ∈ Ω, ∀ x ∈ Ω, u x₁ + inner ℝ (x - x₁) p ≤ u x := by
  -- Minimize `u - ⟪·, p⟫` over the compact closure of `Ω`.
  have hcont : ContinuousOn (fun x => u x - inner ℝ x p) (closure Ω) :=
    hu.sub (continuous_id.inner continuous_const).continuousOn
  obtain ⟨x₁, hx₁, hmin⟩ := hΩ.isCompact_closure.exists_isMinOn ⟨x₀, subset_closure hx₀⟩ hcont
  have hmin' : ∀ x ∈ Ω, u x₁ - inner ℝ x₁ p ≤ u x - inner ℝ x p := fun x hx =>
    isMinOn_iff.1 hmin x (subset_closure hx)
  by_cases h₁ : x₁ ∈ Ω
  · refine ⟨x₁, h₁, fun x hx => ?_⟩
    have := hmin' x hx
    rw [inner_sub_left]
    linarith
  · -- A minimum on the frontier is no smaller than the value at `x₀`, which is then a minimum.
    refine ⟨x₀, hx₀, fun x hx => ?_⟩
    have h₂ := hp x₁ ⟨hx₁, fun h => h₁ (interior_subset h)⟩
    have h₃ := hmin' x hx
    rw [inner_sub_left] at h₂ ⊢
    linarith

omit [FiniteDimensional ℝ E] hf hbot in
/-- **Supporting slopes of a function lying above at `x₀` and below on the frontier.** Let `Ω` be
bounded, let `u` and `w` be continuous on its closure with `w ≤ u` on the frontier of `Ω`, and let
`p` be a subgradient of `w` relative to `Ω` at `x₀ ∈ Ω`. Then for every `q` with
`‖q‖ * diam Ω ≤ w x₀ - u x₀`, the slope `p + q` is a subgradient of `u` relative to `Ω` at some
point `x₁ ∈ Ω`. For `q = 0` this says that the subgradients of `w` at points where `u ≤ w` are
subgradients of `u`. -/
theorem exists_forall_add_inner_add_le_of_forall_frontier_le [ProperSpace E] {Ω : Set E}
    {u w : E → ℝ} (hΩ : Bornology.IsBounded Ω) (hu : ContinuousOn u (closure Ω))
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
    exact dist_le_diam_of_mem hΩ.closure hxc (subset_closure hx₀)
  rw [inner_add_right]
  linarith [hfr x hx]

omit hf hbot in
/-- **Subgradients are eventually locally bounded.** Let `F k → u` locally uniformly on an open
set `Ω`, with `u` continuous on `Ω`, and let `K ⊆ Ω` be compact. Then the subgradients of `F k`
relative to `Ω` at points of `K` are eventually bounded, uniformly in `k`. -/
theorem exists_eventually_norm_le_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι}
    {F : ι → E → ℝ} {u : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hFu : TendstoLocallyUniformlyOn F u l Ω) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ R, ∀ᶠ k in l, ∀ x ∈ K, ∀ y, (∀ x' ∈ Ω, F k x + inner ℝ (x' - x) y ≤ F k x') →
      ‖y‖ ≤ R := by
  -- `F k` is eventually bounded by `M + 1` on a compact thickening of `K` inside `Ω`.
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨M, hM⟩ := hK.cthickening.exists_bound_of_continuousOn (hu.mono hKδ)
  refine ⟨2 * (M + 1) / δ, ?_⟩
  filter_upwards [hFu.eventually_forall_abs_sub_lt hK.cthickening hKδ one_pos]
    with k hk x hx y hy
  rw [le_div_iff₀ hδ, mul_comm]
  refine mul_norm_le_of_forall_add_inner_le hδ.le
    ((closedBall_subset_cthickening hx δ).trans hKδ) (fun z hz => ?_) hy
  have hz' := closedBall_subset_cthickening hx δ hz
  have h := hM z hz'
  rw [Real.norm_eq_abs] at h
  linarith [abs_sub_abs_le_abs_sub (F k z) (u z), hk z hz']

omit hf hbot in
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
    {p | p.1 ∈ K ∧ u p.1 + inner ℝ ((i.1 : E) - p.1) p.2 ≤ u i.1 + i.2}
  have hZ : ∀ i, IsClosed (Z i) := fun i => by
    have : Z i = (K ×ˢ univ) ∩
        (fun p : E × E => u p.1 + inner ℝ ((i.1 : E) - p.1) p.2) ⁻¹' Iic (u i.1 + i.2) := by
      ext p
      simp [Z]
    rw [this]
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hK.isClosed.prod isClosed_univ)
      isClosed_Iic
    exact ((hu.mono hKΩ).comp continuousOn_fst fun p hp => hp.1).add
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
    filter_upwards [hFu.eventually_forall_abs_sub_lt isCompact_singleton
      (singleton_subset_iff.2 i.1.2) hi, hFu.eventually_forall_abs_sub_lt hK hKΩ hi] with k h₁ h₂
    exact ⟨h₁ _ rfl, h₂⟩
  filter_upwards [hbd, hclose] with k hk hk' y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 hy
  by_contra hyV
  have hmem : (x, y) ∈ K ×ˢ (closedBall (0 : E) R \ V) :=
    ⟨hx, mem_closedBall_zero_iff.2 (hk x hx y hxy), hyV⟩
  refine disjoint_left.1 ht hmem (mem_iInter₂.2 fun i hi => ⟨hx, ?_⟩)
  obtain ⟨h₁, h₂⟩ := hk' i hi
  have h₃ := hxy i.1 i.1.2
  dsimp only
  linarith [(abs_lt.1 h₁).2, (abs_lt.1 (h₂ x hx)).1]

end TauCeti

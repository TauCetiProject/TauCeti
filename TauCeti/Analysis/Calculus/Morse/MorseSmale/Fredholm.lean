/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Basic

/-!
# The Morse–Smale condition is surjectivity of the linearized operators

Let `f` be a `C²` function with globally Lipschitz gradient on a finite-dimensional real inner
product space `E`, and `γ` a trajectory of its negative gradient, `γ' = -∇f(γ)`, running from a
nondegenerate critical point `p` at `-∞` to a nondegenerate critical point `q` at `+∞`. Linearizing
the trajectory equation at `γ` gives the equation `v' + Hess f(γ) v = 0` and the trajectory
operator `D_γ ξ = ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)`. This file identifies the
two descriptions of a regular trajectory: the dynamical one, transversality of the unstable set of
`p` and the stable set of `q` along `γ`, and the analytic one, surjectivity of `D_γ`.

The tangent spaces of the invariant sets are spaces of decaying solutions of the linearized
equation:

* the tangent space of the stable set `W^s(q)` at `γ 0` is the space of initial values of the
  solutions square integrable on `(0, ∞)`;
* the tangent space of the unstable set `W^u(p)` at `γ 0` is the space of initial values of the
  solutions square integrable on `(-∞, 0)`.

Tangent spaces are taken intrinsically, as spans of tangent cones. Since `D_γ` is onto exactly when
these two spaces of decaying solutions span `E`
(`IsIntegralCurve.surjective_trajectoryOperator_hessianOperator_iff_sup_eq_top`), it is onto
exactly when `W^u(p)` and `W^s(q)` are transverse at `γ 0`. Hence `f` is Morse–Smale exactly when
the linearized operator along every connecting trajectory is onto. This is the comparison between
the description of the spaces of trajectories as intersections of unstable and stable sets and
Schwarz's description of them as zero sets of a Fredholm section: the regular points of the two
descriptions coincide.

## Proofs

The derivative of the flow carries a tangent vector `w` of `W^s(q)` at `γ 0` to the solution
`v t = Dφ_t(γ 0) w` of the linearized equation, and keeps it tangent to `W^s(q)` at `γ t`. Near
`q`, the stable set is straightened onto the stable linear subspace `E^s` of `Hess f(q)` by a chart
whose derivative at `q` is the identity. So at points of `W^s(q)` close to `q` its tangent vectors
are close to `E^s`, on which `Hess f(q)` is coercive; with the continuity of the Hessian this gives
`c ‖u‖² ≤ ⟪Hess f(z) u, u⟫` for some `c > 0`, every point `z` of `W^s(q)` near `q` and every
tangent vector `u` there
(`IsNondegenerateCriticalPoint.exists_pos_eventually_forall_mem_span_tangentConeAt_stableSet`).
As `γ t → q`, this coercivity holds along `v` for large `t`, so `‖v‖²` decays exponentially and `v`
is square integrable on `(0, ∞)`. This proves one inclusion, and both spaces have dimension
`dim E - ind q`. The unstable statement is the stable one for `-f` and the reversed trajectory.

## Main results

* `IsNondegenerateCriticalPoint.eventually_exists_norm_sub_le_of_mem_span_tangentConeAt_stableSet`:
  near a nondegenerate critical point `q` the tangent spaces of the stable set of `q` are uniformly
  close to the stable linear subspace of the Hessian.
* `IsNondegenerateCriticalPoint.exists_pos_eventually_forall_mem_span_tangentConeAt_stableSet`:
  near a nondegenerate critical point `q` the Hessian is uniformly coercive on the tangent spaces
  of the stable set of `q`.
* `IsIntegralCurve.span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn`: the tangent space
  of `W^s(q)` at `γ 0` is the space of solutions of the linearized equation decaying at `+∞`.
* `IsIntegralCurve.span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn`: the tangent
  space of `W^u(p)` at `γ 0` is the space of solutions of the linearized equation decaying at
  `-∞`.
* `IsIntegralCurve.surjective_trajectoryOperator_iff_span_tangentConeAt_sup_eq_top`:
  the linearized operator along `γ` is onto exactly when `W^u(p)` and `W^s(q)` are transverse at
  `γ 0`.
* `TauCeti.isMorseSmale_iff_forall_surjective_trajectoryOperator`: the negative gradient flow is
  Morse–Smale exactly when the linearized operator along every trajectory between nondegenerate
  critical points is onto.

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (the linearized operator, its kernel and cokernel through decaying solutions, and
  transversality).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic Geometry and Topology*, IAS/Park City
  Math. Ser. **7**, 1999, Lecture 2 (the linearized operator is onto exactly when the unstable and
  stable manifolds intersect transversally).
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Gradient NNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {q : E}
  {K : ℝ≥0}

/-- A perturbation estimate for coercivity: if `H₀` is coercive with constant `α` on `S`, then `H`
is coercive with constant `α / 4` on the vectors `u` within `δ ‖u‖` of `S`, as long as `H` is
within `δ` of `H₀`, for `δ` small in terms of `α` and `‖H₀‖`. -/
private theorem div_four_mul_norm_sq_le_inner_of_norm_sub_le {S : Submodule ℝ E}
    {H₀ H : E →L[ℝ] E} {α δ : ℝ} (hα : 0 < α) (hS : ∀ s ∈ S, α * ‖s‖ ^ 2 ≤ ⟪H₀ s, s⟫)
    (hδpos : 0 ≤ δ) (hδ : δ ≤ min (1 / 4) (α / (4 * (3 * ‖H₀‖ + 1)))) (hH : ‖H - H₀‖ ≤ δ)
    {u w : E} (hw : w ∈ S) (hwu : ‖u - w‖ ≤ δ * ‖u‖) :
    α / 4 * ‖u‖ ^ 2 ≤ ⟪H u, u⟫ := by
  have hδ0 : δ ≤ 1 / 4 := hδ.trans (min_le_left _ _)
  have hδ1 : δ * (4 * (3 * ‖H₀‖ + 1)) ≤ α := by
    have h := hδ.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at h
  have hnu := norm_nonneg u
  have hH₀ := norm_nonneg H₀
  have hw_lower : (1 - δ) * ‖u‖ ≤ ‖w‖ := by
    nlinarith [norm_sub_norm_le u w]
  have hw_upper : ‖w‖ ≤ (1 + δ) * ‖u‖ := by
    nlinarith [norm_le_insert' w u, norm_sub_rev w u]
  -- `⟪H u, u⟫ = ⟪H₀ w, w⟫ + ⟪H₀ (u - w), u⟫ + ⟪H₀ w, u - w⟫ + ⟪(H - H₀) u, u⟫`, and the last
  -- three terms are small.
  have hsplit : ⟪H u, u⟫ = ⟪H₀ w, w⟫ + ⟪H₀ (u - w), u⟫ + ⟪H₀ w, u - w⟫ + ⟪(H - H₀) u, u⟫ := by
    simp only [map_sub, sub_apply, inner_sub_left, inner_sub_right]
    ring
  have e1 : -(‖H₀‖ * (δ * ‖u‖) * ‖u‖) ≤ ⟪H₀ (u - w), u⟫ := by
    have h1 := abs_real_inner_le_norm (H₀ (u - w)) u
    have h2 : ‖H₀ (u - w)‖ ≤ ‖H₀‖ * (δ * ‖u‖) :=
      (H₀.le_opNorm _).trans (mul_le_mul_of_nonneg_left hwu hH₀)
    nlinarith [neg_abs_le ⟪H₀ (u - w), u⟫]
  have e2 : -(‖H₀‖ * ((1 + δ) * ‖u‖) * (δ * ‖u‖)) ≤ ⟪H₀ w, u - w⟫ := by
    have h1 := abs_real_inner_le_norm (H₀ w) (u - w)
    have h2 : ‖H₀ w‖ ≤ ‖H₀‖ * ((1 + δ) * ‖u‖) :=
      (H₀.le_opNorm _).trans (mul_le_mul_of_nonneg_left hw_upper hH₀)
    nlinarith [neg_abs_le ⟪H₀ w, u - w⟫, mul_le_mul h2 hwu (norm_nonneg _) (by positivity)]
  have e3 : -(δ * ‖u‖ * ‖u‖) ≤ ⟪(H - H₀) u, u⟫ := by
    have h1 := abs_real_inner_le_norm ((H - H₀) u) u
    have h2 : ‖(H - H₀) u‖ ≤ δ * ‖u‖ :=
      ((H - H₀).le_opNorm u).trans (mul_le_mul_of_nonneg_right hH hnu)
    nlinarith [neg_abs_le ⟪(H - H₀) u, u⟫]
  have key : ‖H₀‖ * (δ * ‖u‖) * ‖u‖ + ‖H₀‖ * ((1 + δ) * ‖u‖) * (δ * ‖u‖) + δ * ‖u‖ * ‖u‖ ≤
      α / 4 * ‖u‖ ^ 2 := by
    have : ‖H₀‖ * δ * (2 + δ) + δ ≤ α / 4 := by nlinarith [mul_nonneg hH₀ hδpos]
    calc _ = (‖H₀‖ * δ * (2 + δ) + δ) * ‖u‖ ^ 2 := by ring
      _ ≤ α / 4 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have main : α / 2 * ‖u‖ ^ 2 ≤ ⟪H₀ w, w⟫ := by
    have hww : (1 - δ) ^ 2 * ‖u‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by nlinarith) hw_lower 2
    have h12 : 1 / 2 ≤ (1 - δ) ^ 2 := by nlinarith
    nlinarith [hS w hw, mul_le_mul_of_nonneg_left hww hα.le,
      mul_le_mul_of_nonneg_right h12 (sq_nonneg ‖u‖)]
  linarith

variable [FiniteDimensional ℝ E]

namespace IsNondegenerateCriticalPoint

/-- **The stable set is tangent to the stable linear subspace at its critical point.** For a `C²`
function with globally Lipschitz gradient and a nondegenerate critical point `q`, for every `ε > 0`
the tangent vectors `u` of the stable set `W^s(q)` at its points close enough to `q` are within
`ε ‖u‖` of the stable linear subspace `E^s` of `Hess f(q)`. -/
theorem eventually_exists_norm_sub_le_of_mem_span_tangentConeAt_stableSet
    (h : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 q, z ∈ Flow.stableSet (negativeGradientFlow f hf) q →
      ∀ u ∈ Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) z),
        ∃ s ∈ h.contDiffAt.stableLinearSubspace, ‖u - s‖ ≤ ε * ‖u‖ := by
  set W := Flow.stableSet (negativeGradientFlow f hf) q
  set S := h.contDiffAt.stableLinearSubspace
  obtain ⟨r, hr, ρ, hρ, Q, hQs, -, -, hQd, hQC, -, hQset, -⟩ :=
    h.exists_localStableSet_chart_of_contDiffAt (n := 1)
      (by simpa [one_add_one_eq_two] using hfs.contDiffAt)
  have h0 : (0 : E) ∈ Q.source := by simp [hQs, hρ]
  -- Near `q`, the chart `z ↦ Q (z - q)` carries the stable set into `S`.
  have hsrc : ∀ᶠ z in 𝓝 q, z - q ∈ Q.source :=
    ((continuous_sub_right q).tendsto' q 0 (sub_self q)) (Q.open_source.mem_nhds h0)
  have hmaps : ∀ᶠ z in 𝓝 q, z ∈ W → Q (z - q) ∈ S := by
    filter_upwards [hsrc, h.eventually_forall_dist_le_of_mem_stableSet
      (isNegativeGradient_negativeGradientFlow f hf) (hfs.differentiable (by norm_num)) hr]
      with z hz hzc hzW
    refine (hQset _ hz).1 ((h.mem_localStableSet_iff_negativeGradientFlow hf).2
      ⟨fun t ht ↦ ?_, ?_⟩)
    · rw [add_sub_cancel, mem_closedBall_zero_iff, ← dist_eq_norm]
      exact hzc hzW t ht
    · rw [hQs] at hz
      exact (mem_ball_zero_iff.1 hz).le
  -- Near `q`, the derivative of the chart is within `ε` of the identity, its derivative at `q`.
  have hL : ∀ᶠ z in 𝓝 q, ‖fderiv ℝ Q (z - q) - ContinuousLinearMap.id ℝ E‖ ≤ ε := by
    have hon : ContDiffOn ℝ 1 Q Q.source := fun z hz ↦ (hQC z hz).contDiffWithinAt
    have hQcont : ContinuousAt (fun z ↦ fderiv ℝ Q (z - q)) q :=
      ((hon.continuousOn_fderiv_of_isOpen Q.open_source le_rfl).continuousAt
        (Q.open_source.mem_nhds h0)).comp_of_eq (continuous_sub_right q).continuousAt (sub_self q)
    have := hQcont.tendsto
    rw [sub_self, hQd.fderiv] at this
    filter_upwards [this (Metric.closedBall_mem_nhds _ hε)] with z hz
    simpa [dist_eq_norm] using hz
  filter_upwards [hmaps.eventually_nhds, hsrc, hL] with z hzmaps hz hzL hzW u hu
  -- The derivative of the chart carries the tangent space of `W` at `z` into `S`.
  have hd : HasFDerivAt (fun z' ↦ Q (z' - q)) (fderiv ℝ Q (z - q)) z :=
    ((hQC _ hz).differentiableAt one_ne_zero).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const q)
  obtain ⟨U, hU, hUo, hzU⟩ := _root_.mem_nhds_iff.1 hzmaps
  have hcone : Submodule.span ℝ (tangentConeAt ℝ W z) ≤
      S.comap (fderiv ℝ Q (z - q) : E →ₗ[ℝ] E) := by
    refine Submodule.span_le.2 fun v hv ↦ ?_
    rw [← tangentConeAt_inter_nhds (hUo.mem_nhds hzU)] at hv
    have hS' : tangentConeAt ℝ (S : Set E) (Q (z - q)) = S :=
      Submodule.tangentConeAt_eq S (Submodule.closed_of_finiteDimensional S) (hU hzU hzW)
    rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, ← SetLike.mem_coe,
      ← hS']
    refine tangentConeAt_mono ?_ (hd.hasFDerivWithinAt.mapsTo_tangent_cone hv)
    rintro _ ⟨z', ⟨hz'W, hz'U⟩, rfl⟩
    exact hU hz'U hz'W
  refine ⟨fderiv ℝ Q (z - q) u, hcone hu, ?_⟩
  have := (fderiv ℝ Q (z - q) - ContinuousLinearMap.id ℝ E).le_opNorm u
  rw [sub_apply, ContinuousLinearMap.id_apply, norm_sub_rev] at this
  exact this.trans (mul_le_mul_of_nonneg_right hzL (norm_nonneg u))

/-- **The Hessian is coercive on the tangent spaces of a stable set near its critical point.**
For a `C²` function with globally Lipschitz gradient and a nondegenerate critical point `q`, there
is `c > 0` such that at every point `z` of the stable set `W^s(q)` close enough to `q`, every
tangent vector `u` of `W^s(q)` at `z` satisfies `c ‖u‖² ≤ ⟪Hess f(z) u, u⟫`. -/
theorem exists_pos_eventually_forall_mem_span_tangentConeAt_stableSet
    (h : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f)) :
    ∃ c > 0, ∀ᶠ z in 𝓝 q, z ∈ Flow.stableSet (negativeGradientFlow f hf) q →
      ∀ u ∈ Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) z),
        c * ‖u‖ ^ 2 ≤ ⟪hessianOperator f z u, u⟫ := by
  -- Tangent vectors are close to `E^s`, where `Hess f(q)` is coercive, and `Hess f(z)` is close
  -- to `Hess f(q)`.
  obtain ⟨α, hα, hS⟩ := h.contDiffAt.exists_pos_forall_mul_norm_sq_le_inner_hessianOperator
  set δ := min (1 / 4) (α / (4 * (3 * ‖hessianOperator f q‖ + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hH : ∀ᶠ z in 𝓝 q, ‖hessianOperator f z - hessianOperator f q‖ ≤ δ := by
    have := (hfs.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.tendsto q
    filter_upwards [this (Metric.closedBall_mem_nhds _ hδ)] with z hz
    simpa [dist_eq_norm] using hz
  refine ⟨α / 4, by positivity, ?_⟩
  filter_upwards [h.eventually_exists_norm_sub_le_of_mem_span_tangentConeAt_stableSet hfs hf hδ,
    hH] with z hz hzH hzW u hu
  obtain ⟨s, hs, hus⟩ := hz hzW u hu
  exact div_four_mul_norm_sq_le_inner_of_norm_sub_le hα hS hδ.le le_rfl hzH hs hus

end IsNondegenerateCriticalPoint

end TauCeti

namespace IsIntegralCurve

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {p q : E} {K : ℝ≥0} {γ : ℝ → E}

/-- **The tangent space of the stable set is the space of solutions decaying at `+∞`.** For a
`C²` function with globally Lipschitz gradient and a negative gradient trajectory `γ` converging to
a nondegenerate critical point `q` at `+∞`, the tangent space at `γ 0` of the stable set of `q` is
the space of initial values of the solutions of the linearized equation `v' + Hess f(γ) v = 0`
that are square integrable on `(0, ∞)`. -/
theorem span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hq : IsNondegenerateCriticalPoint f q)
    (htop : Tendsto γ atTop (𝓝 q)) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) (γ 0)) =
      squareIntegrableSolutionsOn (fun s ↦ hessianOperator f (γ s)) (Ioi 0) := by
  have hγφ (t : ℝ) : γ t = negativeGradientFlow f hf t (γ 0) := eq_negativeGradientFlow f hf hγ t
  have hW0 : γ 0 ∈ Flow.stableSet (negativeGradientFlow f hf) q :=
    Flow.mem_stableSet.2 (by simpa only [← hγφ] using htop)
  have hW (t : ℝ) : γ t ∈ Flow.stableSet (negativeGradientFlow f hf) q := by
    rw [hγφ]
    exact Flow.isInvariant_stableSet _ q t hW0
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 fun w hw ↦ ?_) ?_
  · -- `v t = Dφ_t(γ 0) w` solves the linearized equation and stays tangent to the stable set,
    -- where the Hessian is eventually coercive, so it decays.
    have hv (t : ℝ) : HasDerivAt (fun t ↦ fderiv ℝ (negativeGradientFlow f hf t) (γ 0) w)
        (-hessianOperator f (γ t) (fderiv ℝ (negativeGradientFlow f hf t) (γ 0) w)) t := by
      have h := (hasDerivAt_fderiv_negativeGradientFlow f hf hfs (γ 0) t).clm_apply
        (hasDerivAt_const t w)
      rw [← hγφ, fderiv_gradient] at h
      simpa using h
    obtain ⟨c, hc, hev⟩ := hq.exists_pos_eventually_forall_mem_span_tangentConeAt_stableSet hfs hf
    have h := mem_squareIntegrableSolutionsOn_Ioi_of_eventually_mul_norm_sq_le_inner hv hc ?_
    · simpa [Flow.map_zero] using h
    filter_upwards [htop.eventually hev] with t ht
    refine ht (hW t) _ (Submodule.subset_span ?_)
    have hmaps := ((differentiable_negativeGradientFlow_apply f hf hfs t)
      (γ 0)).hasFDerivAt.hasFDerivWithinAt.mapsTo_tangent_cone hw
    rw [← hγφ] at hmaps
    refine tangentConeAt_mono ?_ hmaps
    rintro _ ⟨z, hz, rfl⟩
    exact Flow.isInvariant_stableSet _ q t hz
  · have h1 := hq.finrank_span_tangentConeAt_stableSet_add_morseIndex hfs hf (hW 0)
    have h2 := hγ.finrank_squareIntegrableSolutionsOn_Ioi_hessianOperator_add_morseIndex hfs hq htop
    omega

/-- **The tangent space of the unstable set is the space of solutions decaying at `-∞`.** For a
`C²` function with globally Lipschitz gradient and a negative gradient trajectory `γ` coming from a
nondegenerate critical point `p` at `-∞`, the tangent space at `γ 0` of the unstable set of `p` is
the space of initial values of the solutions of the linearized equation `v' + Hess f(γ) v = 0`
that are square integrable on `(-∞, 0)`. -/
theorem span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hp : IsNondegenerateCriticalPoint f p)
    (hbot : Tendsto γ atBot (𝓝 p)) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) (γ 0)) =
      squareIntegrableSolutionsOn (fun s ↦ hessianOperator f (γ s)) (Iio 0) := by
  have hgrad : ∇ (-f) = fun y ↦ -∇ f y := funext fun _ ↦ gradient_neg
  have hf' : LipschitzWith K (∇ (-f)) := by
    rw [hgrad]
    exact hf.neg
  -- Reversing time turns `γ` into a negative gradient trajectory of `-f` converging to `p`.
  have hγ' : IsIntegralCurve (fun τ ↦ γ (-τ)) (fun _ x ↦ -∇ (-f) x) := fun τ ↦ by
    simpa [hgrad, Function.comp_def] using (hγ (-τ)).scomp τ (hasDerivAt_neg τ)
  have h := span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn hγ' hfs.neg hf' hp.neg
    (hbot.comp tendsto_neg_atTop_atBot)
  rw [← unstableSet_negativeGradientFlow_eq_stableSet_neg hf hf', neg_zero] at h
  rw [h, squareIntegrableSolutionsOn_Iio_eq_Ioi]
  simp only [hessianOperator_neg]

/-- **The linearized operator is onto exactly when the trajectory is transverse.** For a `C²`
function with globally Lipschitz gradient and a negative gradient trajectory `γ` from a
nondegenerate critical point `p` to a nondegenerate critical point `q`, the linearized operator
`ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is onto exactly when the unstable set of
`p` and the stable set of `q` are transverse at `γ 0`, that is, when their tangent spaces there
span `E`. -/
theorem surjective_trajectoryOperator_iff_span_tangentConeAt_sup_eq_top
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hbot : Tendsto γ atBot (𝓝 p))
    (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s)) :
    Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) ↔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) (γ 0)) ⊔
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) (γ 0)) =
          ⊤ := by
  rw [hγ.surjective_trajectoryOperator_hessianOperator_iff_sup_eq_top hfs hp hq hbot htop hAL,
    hγ.span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn hfs hf hp hbot,
    hγ.span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn hfs hf hq htop]

end IsIntegralCurve

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0}

/-- **Morse–Smale means every linearized operator is onto.** For a `C²` function with globally
Lipschitz gradient, the negative gradient flow is Morse–Smale exactly when, along every negative
gradient trajectory `γ` between nondegenerate critical points, the linearized operator
`ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is onto. -/
theorem isMorseSmale_iff_forall_surjective_trajectoryOperator (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) :
    IsMorseSmale f hf ↔ ∀ ⦃p q : E⦄ ⦃γ : ℝ → E⦄, IsNondegenerateCriticalPoint f p →
      IsNondegenerateCriticalPoint f q → IsIntegralCurve γ (fun _ x ↦ -∇ f x) →
      Tendsto γ atBot (𝓝 p) → Tendsto γ atTop (𝓝 q) →
      ∀ AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)),
        AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
          (fun s ↦ hessianOperator f (γ s)) →
        Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) := by
  constructor
  · intro h p q γ hp hq hγ hbot htop AL hAL
    have hγφ (t : ℝ) : γ t = negativeGradientFlow f hf t (γ 0) :=
      eq_negativeGradientFlow f hf hγ t
    refine (hγ.surjective_trajectoryOperator_iff_span_tangentConeAt_sup_eq_top
      hfs hf hp hq hbot htop hAL).2 (h.transverse_at hp hq ⟨?_, ?_⟩)
    · exact Flow.mem_unstableSet.2 (by simpa only [← hγφ] using hbot)
    · exact Flow.mem_stableSet.2 (by simpa only [← hγφ] using htop)
  · intro h
    refine IsMorseSmale.of_forall fun p q y hp hq hy ↦ ?_
    -- Every point of `W^u(p) ∩ W^s(q)` is the value at time `0` of its orbit.
    have hγ := (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y
    have hbot := Flow.mem_unstableSet.1 hy.1
    have htop := Flow.mem_stableSet.1 hy.2
    have hmem := hfs.memLp_top_hessianOperator_comp hγ.continuous hbot htop
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))
    have := (hγ.surjective_trajectoryOperator_iff_span_tangentConeAt_sup_eq_top
      hfs hf hp hq hbot htop hmem.coeFn_toLp).1 (h hp hq hγ hbot htop _ hmem.coeFn_toLp)
    simpa only [Flow.map_zero_apply] using this

end TauCeti

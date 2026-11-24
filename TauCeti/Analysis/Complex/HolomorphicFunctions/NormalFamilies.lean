/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.Equicontinuity
public import TauCeti.Analysis.Normed.Group.LocallyBounded
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Normal families: equicontinuity of a locally bounded family of holomorphic maps

A family of holomorphic maps on an open subset `U` of a proper complex normed space, such as `ℂ`
or `ℂⁿ`, that is *locally bounded* — uniformly bounded on every compact subset of `U` — is
automatically equicontinuous on `U` (`TauCeti.IsLocallyBoundedOn.equicontinuousOn`).  This is the
analytic heart of Montel's normal-families theorem: for a proper target, equicontinuity and the
pointwise norm bounds give relative compactness by the compact-open Arzelà–Ascoli theorem.  For a
complex normed space, properness is equivalent to finite-dimensionality.

The analytic input to equicontinuity is Mathlib's Schwarz lemma
`Complex.dist_le_div_mul_dist_of_mapsTo_ball`: a holomorphic map of a ball of radius `r` around `c`,
on any complex normed space, into the closed ball of radius `2 * C` around `f c` satisfies
`dist (f z) (f c) ≤ 2 * C / r * dist z c`.  A bound `C` on the norms gives exactly this mapping
property, and when `C` bounds the whole family on a compact ball the constant is uniform in the
family, which is equicontinuity at `c`.

The remaining estimates concern one complex variable.  They are stated for maps `ℂ → E` into a
complex normed space, because nothing in a Cauchy estimate uses the multiplicative structure of
the target: Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, their sole analytic
input, is itself `E`-valued.  It bounds `‖deriv f c‖` at the *centre* of a disc; halving the radius
turns that pointwise bound into one that is uniform over a ball
(`norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le`), and the mean value inequality on that
ball then bounds `dist (f z) (f w)` by a multiple of `dist z w` with a constant depending only on
the sup bound (`dist_le_of_forall_mem_closedBall_two_mul_norm_le`).  The same estimate bounds the
derivatives of a locally bounded family on compact sets.  Only
`TauCeti.IsLocallyBoundedOn.equicontinuousOn_deriv` needs `E` complete, and that is because it
differentiates twice.  Taking `E = ℂ` recovers the scalar statements.

Local boundedness and its general compact-open API are defined in
`TauCeti/Analysis/Normed/Group/LocallyBounded.lean`.

## Main results

* `TauCeti.norm_deriv_le_of_forall_mem_closedBall_norm_le` and
  `TauCeti.norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le`: Cauchy's estimate from a sup
  bound on a closed ball, at the centre and then uniformly over the ball of half the radius.
* `TauCeti.dist_le_of_forall_mem_closedBall_two_mul_norm_le` and
  `TauCeti.lipschitzOnWith_of_forall_mem_closedBall_two_mul_norm_le`: a sup bound `M` on
  `closedBall c (2 * r)` makes a holomorphic function `M / r`-Lipschitz on `ball c r`.
* `TauCeti.norm_inv_smul_sub_inv_smul_le`: the same bound makes `z ↦ (w - z)⁻¹ • f z` Lipschitz
  near `y`, uniformly in poles `w` at a fixed positive distance.
* `TauCeti.IsLocallyBoundedOn.equicontinuousOn`: a locally bounded family of holomorphic
  maps on an open subset of a proper complex normed space is equicontinuous.  With
  `TauCeti.IsLocallyBoundedOn.exists_forall_norm_le`, this supplies the hypotheses of the
  compact-open Arzelà–Ascoli theorem when the target is proper.
* `TauCeti.IsLocallyBoundedOn.deriv` and `TauCeti.IsLocallyBoundedOn.equicontinuousOn_deriv`: the
  derivatives of a locally bounded family of holomorphic functions are again locally bounded, hence
  also equicontinuous.

## References

* Ahlfors, *Complex Analysis*, Ch. 5.
* Conway, *Functions of One Complex Variable I*, VII.
* The Montel equicontinuity argument in the Riemann mapping formalization
  [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505).
-/

public section

namespace TauCeti

open Filter Metric Set Topology

variable {ι E : Type*} {U : Set ℂ} {f : ℂ → E}

section Estimates

variable [NormedAddCommGroup E] [NormedSpace ℂ E] {F : ι → ℂ → E}

/-- **Cauchy's estimate on a closed ball.** If `f` is holomorphic on an open set `U` containing
`closedBall c r` and `‖f‖ ≤ M` on that closed ball, then `‖deriv f c‖ ≤ M / r`.

This is Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` with its `DiffContOnCl`
hypothesis and its bound on the boundary circle both supplied from a sup bound on a closed ball
inside the domain of holomorphy, which is the form the family estimates below consume. -/
theorem norm_deriv_le_of_forall_mem_closedBall_norm_le (hf : DifferentiableOn ℂ f U) {c : ℂ}
    {r M : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ U)
    (hM : ∀ w ∈ closedBall c r, ‖f w‖ ≤ M) : ‖deriv f c‖ ≤ M / r := by
  have hd := hf.diffContOnCl_ball hsub
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd fun w hw =>
    hM w (sphere_subset_closedBall hw)

/-- **Cauchy's estimate, uniformly on a ball.** If `f` is holomorphic on an open set `U` containing
`closedBall c (2 * r)` and `‖f‖ ≤ M` on that closed ball, then `‖deriv f z‖ ≤ M / r` at *every*
point `z` of `ball c r`, not just at the centre.

Halving the radius is what leaves room to recentre `norm_deriv_le_of_forall_mem_closedBall_norm_le`
at an arbitrary `z ∈ ball c r`: the ball `closedBall z r` is still inside `closedBall c (2 * r)`. -/
theorem norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le (hf : DifferentiableOn ℂ f U)
    {c : ℂ} {r M : ℝ} (hr : 0 < r) (hsub : closedBall c (2 * r) ⊆ U)
    (hM : ∀ w ∈ closedBall c (2 * r), ‖f w‖ ≤ M) {z : ℂ} (hz : z ∈ ball c r) :
    ‖deriv f z‖ ≤ M / r := by
  have hzc : closedBall z r ⊆ closedBall c (2 * r) :=
    closedBall_subset_closedBall' (by have := (mem_ball.1 hz).le; linarith)
  exact norm_deriv_le_of_forall_mem_closedBall_norm_le hf hr (hzc.trans hsub)
    fun w hw => hM w (hzc hw)

/-- **A sup bound makes a holomorphic function Lipschitz on half the ball.** If `f` is holomorphic
on an open `U ⊇ closedBall c (2 * r)` and `‖f‖ ≤ M` there, then `f` moves points of `ball c r` by
at most `M / r` times the distance between them.

The constant `M / r` depends only on the sup bound and the radius, which is what makes this
estimate usable uniformly across a family; see `norm_inv_smul_sub_inv_smul_le`. -/
theorem dist_le_of_forall_mem_closedBall_two_mul_norm_le (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : ℂ} {r M : ℝ} (hr : 0 < r) (hsub : closedBall c (2 * r) ⊆ U)
    (hM : ∀ w ∈ closedBall c (2 * r), ‖f w‖ ≤ M) {z w : ℂ} (hz : z ∈ ball c r)
    (hw : w ∈ ball c r) : dist (f z) (f w) ≤ M / r * dist z w := by
  have hball : ball c r ⊆ U := fun x hx =>
    hsub (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hx))
  rw [dist_eq_norm, dist_eq_norm]
  exact (convex_ball c r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hf x (hball hx)).differentiableAt (hU.mem_nhds (hball hx)))
    (fun x hx => norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le hf hr hsub hM hx)
    hw hz

/-- The `LipschitzOnWith` form of `dist_le_of_forall_mem_closedBall_two_mul_norm_le`. -/
theorem lipschitzOnWith_of_forall_mem_closedBall_two_mul_norm_le (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hsub : closedBall c (2 * r) ⊆ U) (hM : ∀ w ∈ closedBall c (2 * r), ‖f w‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal (M / r)) f (ball c r) := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
  refine (dist_le_of_forall_mem_closedBall_two_mul_norm_le hU hf hr hsub hM hz hw).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg

/-- **A Lipschitz bound for the Cauchy kernel against a holomorphic function.** If `f` is
holomorphic on an open `U ⊇ closedBall y (2 * r)` and `‖f‖ ≤ M` there, and `w` is at distance at
least `d > 0` from `x ∈ ball y r` and from `y`, then the values of `z ↦ (w - z)⁻¹ • f z` at `x` and
`y` differ by at most `M * (r⁻¹ * d⁻¹ + (d ^ 2)⁻¹) * dist x y`.

The constant depends only on `M`, `r` and `d`, so the bound is uniform over a bounded family of
holomorphic functions and over poles `w` kept at distance `d`. -/
theorem norm_inv_smul_sub_inv_smul_le (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {y : ℂ}
    {r M : ℝ} (hr : 0 < r) (hsub : closedBall y (2 * r) ⊆ U)
    (hM : ∀ z ∈ closedBall y (2 * r), ‖f z‖ ≤ M) {d : ℝ} (hd : 0 < d) {w x : ℂ}
    (hxy : dist x y < r) (hwx : d ≤ ‖w - x‖) (hwy : d ≤ ‖w - y‖) :
    ‖(w - x)⁻¹ • f x - (w - y)⁻¹ • f y‖ ≤ M * (r⁻¹ * d⁻¹ + (d ^ 2)⁻¹) * dist x y := by
  have hx0 : w - x ≠ 0 := norm_pos_iff.1 (hd.trans_le hwx)
  have hy0 : w - y ≠ 0 := norm_pos_iff.1 (hd.trans_le hwy)
  have hfy : ‖f y‖ ≤ M := hM y (mem_closedBall_self (by positivity))
  -- Cauchy's estimate makes `f` `M / r`-Lipschitz on `ball y r`.
  have hlip : dist (f x) (f y) ≤ M / r * dist x y :=
    dist_le_of_forall_mem_closedBall_two_mul_norm_le hU hf hr hsub hM (mem_ball.2 hxy)
      (mem_ball_self hr)
  have hsplit : (w - x)⁻¹ • f x - (w - y)⁻¹ • f y =
      (w - x)⁻¹ • (f x - f y) + ((x - y) * ((w - x)⁻¹ * (w - y)⁻¹)) • f y := by
    have hinv : (w - x)⁻¹ - (w - y)⁻¹ = (x - y) * ((w - x)⁻¹ * (w - y)⁻¹) := by
      field_simp
      ring
    rw [← hinv, smul_sub, sub_smul]
    abel
  have hxi : ‖(w - x)⁻¹‖ ≤ d⁻¹ := by rw [norm_inv]; exact inv_anti₀ hd hwx
  have hyi : ‖(w - y)⁻¹‖ ≤ d⁻¹ := by rw [norm_inv]; exact inv_anti₀ hd hwy
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, norm_mul, ← dist_eq_norm]
  calc _ ≤ d⁻¹ * (M / r * dist x y) + dist x y * (d⁻¹ * d⁻¹) * M := by
        gcongr
    _ = M * (r⁻¹ * d⁻¹ + (d ^ 2)⁻¹) * dist x y := by ring

/-- **The derivatives of a locally bounded family of holomorphic functions are locally bounded.**

On a compact `K ⊆ U` choose `δ > 0` with `cthickening δ K ⊆ U`; a bound `C` for the family on that
compact thickening bounds each derivative on `K` by `C / δ`, by Cauchy's estimate on
`closedBall z δ` for `z ∈ K`. -/
theorem IsLocallyBoundedOn.deriv (hb : IsLocallyBoundedOn F U) (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    IsLocallyBoundedOn (fun i => _root_.deriv (F i)) U := by
  refine isLocallyBoundedOn_def.mpr fun K hKU hK => ?_
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨C, hC⟩ := isLocallyBoundedOn_def.mp hb _ hδU hK.cthickening
  refine ⟨C / δ, fun i z hz => ?_⟩
  have hsub : closedBall z δ ⊆ cthickening δ K := closedBall_subset_cthickening hz δ
  exact norm_deriv_le_of_forall_mem_closedBall_norm_le (hF i) hδ (hsub.trans hδU)
    fun w hw => hC i w (hsub hw)

end Estimates

section Equicontinuity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup E]
  [NormedSpace ℂ E]

/-- **The equicontinuity half of Montel's theorem.** A locally bounded family of holomorphic maps
on an open subset `U` of a proper complex normed space `V`, such as `ℂ` or `ℂⁿ`, is equicontinuous
on `U`.

For a complex normed space, properness is equivalent to finite-dimensionality. Around a point
`z₀ ∈ U`, local boundedness gives one constant `C` bounding the whole family on a closed ball
`closedBall z₀ r ⊆ U`, and the Schwarz lemma then bounds `dist (F i z) (F i z₀)` by
`2 * C / r * dist z z₀` on the open ball, uniformly in `i`. -/
theorem IsLocallyBoundedOn.equicontinuousOn [ProperSpace V] {U : Set V} {F : ι → V → E}
    (hb : IsLocallyBoundedOn F U) (hU : IsOpen U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    EquicontinuousOn F U := by
  intro z₀ hz₀
  refine EquicontinuousAt.equicontinuousWithinAt ?_ U
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hr : 0 < R / 2 := half_pos hR
  have hsub : closedBall z₀ (R / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hR)).trans hRU
  obtain ⟨C, hC⟩ := isLocallyBoundedOn_def.mp hb _ hsub (isCompact_closedBall z₀ (R / 2))
  refine Metric.equicontinuousAt_of_continuity_modulus (fun z => 2 * C / (R / 2) * dist z z₀) ?_
    F ?_
  · have hcont : Continuous fun z : V => 2 * C / (R / 2) * dist z z₀ :=
      continuous_const.mul (continuous_id.dist continuous_const)
    simpa using hcont.tendsto z₀
  · filter_upwards [ball_mem_nhds z₀ hr] with z hz i
    rw [dist_comm]
    exact Complex.dist_le_div_mul_dist_of_mapsTo_ball
      ((hF i).mono (ball_subset_closedBall.trans hsub))
      (mapsTo_closedBall_of_forall_norm_le (fun y hy => hC i y (ball_subset_closedBall hy))
        (mem_ball_self hr)) hz

end Equicontinuity

section Derivatives

variable [NormedAddCommGroup E] [NormedSpace ℂ E] {F : ι → ℂ → E}

/-- The derivatives of a locally bounded family of holomorphic functions are equicontinuous.

The result follows by applying the preceding equicontinuity theorem to the locally bounded
derivative family.  This is the one statement in this file that needs `E` complete, because
that theorem asks the derivatives themselves to be holomorphic, and holomorphy of `deriv f`
(`DifferentiableOn.deriv`) rests on the Cauchy integral formula. -/
theorem IsLocallyBoundedOn.equicontinuousOn_deriv [CompleteSpace E]
    (hb : IsLocallyBoundedOn F U) (hU : IsOpen U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    EquicontinuousOn (fun i => _root_.deriv (F i)) U :=
  (hb.deriv hU hF).equicontinuousOn hU fun i => (hF i).deriv hU

end Derivatives

end TauCeti

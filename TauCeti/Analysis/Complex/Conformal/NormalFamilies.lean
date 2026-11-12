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
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Normal families: equicontinuity of a locally bounded family of holomorphic functions

A family of holomorphic functions on an open set `U ⊆ ℂ` that is *locally bounded* — uniformly
bounded on every compact subset of `U` — is automatically equicontinuous on `U`.  This is the
analytic heart of Montel's normal-families theorem: for a proper target, equicontinuity and the
pointwise norm bounds give relative compactness by the compact-open Arzelà–Ascoli theorem.

The estimates here are stated for maps `ℂ → E` into a complex normed space, because nothing in a
Cauchy estimate uses the multiplicative structure of the target: Mathlib's
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, which is the sole analytic input, is itself
`E`-valued.  Only `TauCeti.IsLocallyBoundedOn.equicontinuousOn_deriv` needs `E` complete, and
that is because it differentiates twice.  Taking `E = ℂ` recovers the scalar statements.

Local boundedness and its general compact-open API are defined in
`TauCeti/Analysis/Normed/Group/LocallyBounded.lean`. The estimates below specialize the domain to
`ℂ` and the target to a complex normed space.

The mechanism is Cauchy's estimate for the first derivative.  Mathlib's
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` bounds `‖deriv f c‖` at the *centre* of a
disc; halving the radius turns that pointwise bound into one that is uniform over a ball
(`norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le`), and the mean value inequality on that
ball then bounds `dist (f z) (f w)` by a multiple of `dist z w` with a constant depending only on
the sup bound (`dist_le_of_forall_mem_closedBall_two_mul_norm_le`).  That constant is uniform in
the family, which is exactly equicontinuity.

## Main results

* `TauCeti.norm_deriv_le_of_forall_mem_closedBall_norm_le` and
  `TauCeti.norm_deriv_le_of_forall_mem_closedBall_two_mul_norm_le`: Cauchy's estimate from a sup
  bound on a closed ball, at the centre and then uniformly over the ball of half the radius.
* `TauCeti.dist_le_of_forall_mem_closedBall_two_mul_norm_le` and
  `TauCeti.lipschitzOnWith_of_forall_mem_closedBall_two_mul_norm_le`: a sup bound `M` on
  `closedBall c (2 * r)` makes a holomorphic function `M / r`-Lipschitz on `ball c r`.
* `TauCeti.IsLocallyBoundedOn.equicontinuousOn`: a locally bounded family of holomorphic
  functions is equicontinuous.  With `TauCeti.IsLocallyBoundedOn.exists_forall_norm_le`, this
  supplies the hypotheses of the compact-open Arzelà–Ascoli theorem when the target is proper.
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

/-- Every point of an open set admits a radius `r > 0` with `closedBall z (2 * r) ⊆ U`.

The doubled radius is what lets the Cauchy estimate below be applied at every point of
`ball z r`, not just at `z`. -/
private theorem exists_pos_closedBall_two_mul_subset (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    ∃ r > 0, closedBall z (2 * r) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ :=
    isCompact_singleton.exists_cthickening_subset_open hU (singleton_subset_iff.2 hz)
  refine ⟨δ / 2, by positivity, ?_⟩
  have htwo : 2 * (δ / 2) = δ := by ring
  rw [htwo]
  exact (closedBall_subset_cthickening (mem_singleton z) δ).trans hδU

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
estimate usable uniformly across a family; see `IsLocallyBoundedOn.equicontinuousOn`. -/
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

/-- **The equicontinuity half of Montel's theorem.** A locally bounded family of holomorphic
functions on an open set `U ⊆ ℂ` is equicontinuous on `U`.

Around a point `z₀ ∈ U` pick `r > 0` with `closedBall z₀ (2 * r) ⊆ U`; local boundedness supplies
one constant `C` bounding the whole family on that compact ball, and
`dist_le_of_forall_mem_closedBall_two_mul_norm_le` then makes every member of the family
`C / r`-Lipschitz on `ball z₀ r`.  A single Lipschitz constant is a common continuity modulus. -/
theorem IsLocallyBoundedOn.equicontinuousOn (hb : IsLocallyBoundedOn F U) (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) : EquicontinuousOn F U := by
  intro z₀ hz₀
  refine EquicontinuousAt.equicontinuousWithinAt ?_ U
  obtain ⟨r, hr, hsub⟩ := exists_pos_closedBall_two_mul_subset hU hz₀
  obtain ⟨C, hC⟩ := isLocallyBoundedOn_def.mp hb _ hsub (isCompact_closedBall z₀ (2 * r))
  refine Metric.equicontinuousAt_of_continuity_modulus (fun z => C / r * dist z₀ z) ?_ F ?_
  · have hcont : Continuous fun z : ℂ => C / r * dist z₀ z :=
      continuous_const.mul (continuous_const.dist continuous_id)
    simpa using hcont.tendsto z₀
  · filter_upwards [ball_mem_nhds z₀ hr] with z hz i
    exact dist_le_of_forall_mem_closedBall_two_mul_norm_le hU (hF i) hr hsub (hC i)
      (mem_ball_self hr) hz

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

/-- The derivatives of a locally bounded family of holomorphic functions are equicontinuous.

The result follows by applying the preceding equicontinuity theorem to the locally bounded
derivative family.  This is the one statement in this file that needs `E` complete, because
that theorem asks the derivatives themselves to be holomorphic, and holomorphy of `deriv f`
(`DifferentiableOn.deriv`) rests on the Cauchy integral formula. -/
theorem IsLocallyBoundedOn.equicontinuousOn_deriv [CompleteSpace E]
    (hb : IsLocallyBoundedOn F U) (hU : IsOpen U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    EquicontinuousOn (fun i => _root_.deriv (F i)) U :=
  (hb.deriv hU hF).equicontinuousOn hU fun i => (hF i).deriv hU

end Estimates

end TauCeti

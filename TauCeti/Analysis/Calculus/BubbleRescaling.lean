/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.PointPicking
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Choosing bubble rescalings

For maps whose derivatives blow up on shrinking balls, choose nearby centres and inverse
derivative scales. The rescaled maps have derivative norm one at the origin and derivative
norm at most two on expanding closed balls. The centres converge to the original limiting
point, and the scales tend to zero. These are the normalization and domain-exhaustion inputs
for extracting a nonconstant bubble; convergence of the rescaled maps is not asserted here.

The point-picking argument follows McDuff–Salamon, *J-holomorphic Curves and Symplectic
Topology*, Section 4.2. The domain need only have compact closed balls; the target may be any
real normed space.
-/

public section

open Filter Metric Set
open scoped Topology

namespace TauCeti

/-- Select bubble centres and scales from derivative blowup on shrinking balls.

The hypothesis `r i * ‖duᵢ(xᵢ)‖ → ∞` ensures that the rescaled domains exhaust the domain
vector space. Derivative continuity is only needed through its norm on the original balls.
No equation, energy bound, or convergence of the rescaled maps is assumed or concluded. -/
theorem exists_bubble_rescalings
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℕ → E → F} {x : ℕ → E} {r : ℕ → ℝ} {z₀ : E}
    (hr : ∀ i, 0 < r i)
    (hcont : ∀ i, ContinuousOn (fun z => ‖fderiv ℝ (u i) z‖)
      (closedBall (x i) (2 * r i)))
    (hpos : ∀ i, 0 < ‖fderiv ℝ (u i) (x i)‖)
    (hx : Tendsto x atTop (𝓝 z₀)) (hsmall : Tendsto r atTop (𝓝 0))
    (hlarge : Tendsto (fun i => r i * ‖fderiv ℝ (u i) (x i)‖) atTop atTop) :
    ∃ (c : ℕ → E) (ε R : ℕ → ℝ),
      Tendsto c atTop (𝓝 z₀) ∧ Tendsto ε atTop (𝓝 0) ∧ Tendsto R atTop atTop ∧
      (∀ i, 0 < ε i ∧ 0 < R i) ∧
      (∀ i, MapsTo (fun w => c i + ε i • w) (closedBall 0 (R i))
        (closedBall (x i) (2 * r i))) ∧
      (∀ i, ‖fderiv ℝ (fun w => u i (c i + ε i • w)) 0‖ = 1) ∧
      (∀ i w, w ∈ closedBall 0 (R i) →
        ‖fderiv ℝ (fun w => u i (c i + ε i • w)) w‖ ≤ 2) := by
  -- Pick controlled balls before changing coordinates.
  have hpick (i : ℕ) := exists_pos_mul_le_and_forall_le_two_mul (hr i) (hcont i) (hpos i)
  choose c hc δ hδ hδr hprod hnorm hsub hbound using hpick
  let M : ℕ → ℝ := fun i => ‖fderiv ℝ (u i) (c i)‖
  let ε : ℕ → ℝ := fun i => (M i)⁻¹
  let R : ℕ → ℝ := fun i => δ i * M i
  have hM (i) : 0 < M i := hnorm i
  have hε (i) : 0 < ε i := inv_pos.mpr (hM i)
  have hR (i) : 0 < R i := mul_pos (hδ i) (hM i)
  have hRlarge : Tendsto R atTop atTop := tendsto_atTop_mono hprod hlarge
  -- The radius-times-derivative bound forces inverse derivative scales to vanish.
  have hMlarge : Tendsto M atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlarge
    filter_upwards [hsmall.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with i hi
    calc
      r i * ‖fderiv ℝ (u i) (x i)‖ ≤ δ i * M i := hprod i
      _ ≤ M i := mul_le_of_le_one_left (hM i).le (le_trans (hδr i) hi.le)
  have hεsmall : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hMlarge
  -- Point picking moves the centres by at most twice the original shrinking radius.
  have hcsmall : Tendsto (fun i => dist (c i) (x i)) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => dist_nonneg) (fun i => hc i)
    simpa using tendsto_const_nhds.mul hsmall
  have hclimit : Tendsto c atTop (𝓝 z₀) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun i => dist_nonneg)
      (fun i => dist_triangle (c i) (x i) z₀)
    simpa using hcsmall.add (tendsto_iff_dist_tendsto_zero.mp hx)
  -- The exact affine chain rule transports the controlled balls and derivative bounds.
  have hderiv (i : ℕ) (w : E) :
      fderiv ℝ (fun w => u i (c i + ε i • w)) w =
        ε i • fderiv ℝ (u i) (c i + ε i • w) := by
    rw [fderiv_comp_smul (f := fun v => u i (c i + v)), fderiv_comp_add_left]
  have hnormderiv (i : ℕ) (w : E) :
      ‖fderiv ℝ (fun w => u i (c i + ε i • w)) w‖ =
        ε i * ‖fderiv ℝ (u i) (c i + ε i • w)‖ := by
    rw [hderiv, norm_smul, Real.norm_of_nonneg (hε i).le]
  have hmem (i : ℕ) {w : E} (hw : w ∈ closedBall 0 (R i)) :
      c i + ε i • w ∈ closedBall (c i) (δ i) := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (hε i).le]
    have hw' : ‖w‖ ≤ R i := by simpa using hw
    calc
      ε i * ‖w‖ ≤ ε i * R i := mul_le_mul_of_nonneg_left hw' (hε i).le
      _ = δ i := by dsimp [ε, R]; field_simp [ne_of_gt (hM i)]
  refine ⟨c, ε, R, hclimit, hεsmall, hRlarge, fun i => ⟨hε i, hR i⟩,
    fun i w hw => hsub i (hmem i hw), ?_, ?_⟩
  · intro i
    rw [hnormderiv]
    simp only [smul_zero, add_zero]
    exact inv_mul_cancel₀ (ne_of_gt (hM i))
  · intro i w hw
    rw [hnormderiv]
    calc
      ε i * ‖fderiv ℝ (u i) (c i + ε i • w)‖ ≤ ε i * (2 * M i) :=
        mul_le_mul_of_nonneg_left (hbound i _ (hmem i hw)) (hε i).le
      _ = 2 := by dsimp [ε]; field_simp [ne_of_gt (hM i)]

end TauCeti

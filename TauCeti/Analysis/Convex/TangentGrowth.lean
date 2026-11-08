/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.Analysis.Convex.Differentiability
import TauCeti.Analysis.Calculus.PowerGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.Calculus.Gradient

/-!
# Gradient Hölder bounds from tangent growth

For a convex real function differentiable at two points, a one-sided power bound above a
tangent plane controls the change of its gradient. Uniform tangent growth and bounded gradients
on a set give the standard `HolderOnWith` bound for the gradient. A local comparison of the tangent
errors in the two directions gives this growth by a scalar differential inequality along rays.

The soft-comparison implication follows the tangent-growth argument of Forzani and Maldonado,
Nonlinear Analysis 57 (2004), 815–829, Theorem 7. The proof is adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Convex/Section/Engulfing.lean).
-/

public section

open Set Metric
open scoped Gradient ContDiff NNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A one-sided tangent growth bound for a convex function differentiable at `x` and `y`
bounds the change of its gradient, with the same power exponent. -/
theorem norm_gradient_sub_le_of_tangent_growth {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {x y : E} (hdx : DifferentiableAt ℝ u x) (hdy : DifferentiableAt ℝ u y)
    {C α : ℝ≥0} {r₀ : ℝ}
    (hgrowth : ∀ z, ‖z - x‖ ≤ r₀ →
      u z ≤ u x + inner ℝ (gradient u x) (z - x) + C * ‖z - x‖ ^ (1 + (α : ℝ)))
    (hy : ‖y - x‖ ≤ r₀ / 2) :
    ‖gradient u y - gradient u x‖ ≤ 2 ^ (1 + (α : ℝ)) * C * ‖y - x‖ ^ (α : ℝ) := by
  have hC := C.coe_nonneg
  have hα := α.coe_nonneg
  set v : E := gradient u y - gradient u x with hvdef
  set r : ℝ := ‖y - x‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  have hRHS : 0 ≤ 2 ^ (1 + (α : ℝ)) * (C : ℝ) * r ^ (α : ℝ) := by positivity
  by_cases hv : v = 0
  · rw [hv, norm_zero]; exact hRHS
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hrpos : 0 < r := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · exfalso
      have : y = x := by rwa [hrdef, eq_comm, norm_eq_zero, sub_eq_zero] at h
      exact
        hv
          (by rw [hvdef, this, sub_self])
  -- the test point `z = y + w` with `w = (r/‖v‖) • v`, `‖w‖ = r`
  set w : E := (r / ‖v‖) • v with hwdef
  have hwnorm : ‖w‖ = r := by
    rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hrpos hvpos),
      div_mul_cancel₀ _ hvpos.ne']
  have hzx : ‖y + w - x‖ ≤ 2 * r := by
    calc
      ‖y + w - x‖ = ‖(y - x) + w‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖w‖ := norm_add_le _ _
      _ = 2 * r := by rw [← hrdef, hwnorm]; ring
  have hzr₀ : ‖y + w - x‖ ≤ r₀ :=
    hzx.trans
      (by linarith)
  -- supporting plane at `y`, supporting plane at `x`, growth at `x`
  have h1 : ⟪gradient u y, w⟫ ≤ u (y + w) - u y := by
    simpa only [add_sub_cancel_left] using hconv.inner_gradient_sub_le hdy (y + w)
  have h2 := hconv.inner_gradient_sub_le hdx y
  have h3 := hgrowth (y + w) hzr₀
  have hsplit : ⟪gradient u x, y + w - x⟫ = ⟪gradient u x, y - x⟫ + ⟪gradient u x, w⟫ := by
    rw [show y + w - x = (y - x) + w by abel, inner_add_right]
  have hpow : ‖y + w - x‖ ^ (1 + (α : ℝ)) ≤ (2 * r) ^ (1 + (α : ℝ)) :=
    Real.rpow_le_rpow (norm_nonneg _) hzx (by linarith)
  have hkey : ⟪v, w⟫ ≤ (C : ℝ) * (2 * r) ^ (1 + (α : ℝ)) := by
    have : ⟪v, w⟫ = ⟪gradient u y, w⟫ - ⟪gradient u x, w⟫ := by rw [hvdef, inner_sub_left]
    rw [this]
    have hC' : (C : ℝ) * ‖y + w - x‖ ^ (1 + (α : ℝ)) ≤ (C : ℝ) * (2 * r) ^ (1 + (α : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow hC
    linarith
  have hvw : ⟪v, w⟫ = r * ‖v‖ := by
    rw [hwdef, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h2r : (2 * r) ^ (1 + (α : ℝ)) = 2 ^ (1 + (α : ℝ)) * (r * r ^ (α : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hr0, Real.rpow_add hrpos, Real.rpow_one]
  rw [hvw,
    h2r] at hkey
  -- divide by `r > 0`
  have : r * ‖v‖ ≤ r * (2 ^ (1 + (α : ℝ)) * (C : ℝ) * r ^ (α : ℝ)) := by
    calc
      r * ‖v‖ ≤ (C : ℝ) * (2 ^ (1 + (α : ℝ)) * (r * r ^ (α : ℝ))) := hkey
      _ = r * (2 ^ (1 + (α : ℝ)) * (C : ℝ) * r ^ (α : ℝ)) := by ring
  exact le_of_mul_le_mul_left this hrpos

/-- Uniform tangent growth and bounded gradients on a set give a Hölder bound for the gradient.
Differentiability is required only at points of that set. -/
theorem exists_holderOnWith_gradient_of_tangent_growth {u : E → ℝ}
    (hu : ConvexOn ℝ univ u) {K : Set E}
    (hd : ∀ x ∈ K, DifferentiableAt ℝ u x)
    (hgrad : Bornology.IsBounded (gradient u '' K)) {C α : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (hgrowth : ∀ x ∈ K, ∀ z, ‖z - x‖ ≤ r →
      u z ≤ u x + inner ℝ (gradient u x) (z - x) + C * ‖z - x‖ ^ (1 + (α : ℝ))) :
    ∃ C' : ℝ≥0, HolderOnWith C' α (gradient u) K := by
  obtain ⟨M, hM⟩ := hgrad.exists_norm_le
  let B : ℝ≥0 := (max M 0).toNNReal
  let A : ℝ≥0 := (2 ^ (1 + (α : ℝ)) * (C : ℝ)).toNNReal
  let δ : ℝ≥0 := (r / 2).toNNReal
  have hBcoe : (B : ℝ) = max M 0 := Real.coe_toNNReal _ (le_max_right _ _)
  have hAcoe : (A : ℝ) = 2 ^ (1 + (α : ℝ)) * C := Real.coe_toNNReal _ (by positivity)
  have hδcoe : (δ : ℝ) = r / 2 := Real.coe_toNNReal _ (half_pos hr).le
  have hδ : 0 < δ := by rw [← NNReal.coe_pos, hδcoe]; exact half_pos hr
  refine ⟨_, HolderOnWith.of_dist_lt_of_dist_le (K := A) (D := 2 * B) hδ ?_ ?_⟩
  · intro x hx y hy hxy
    have hnear : ‖y - x‖ ≤ r / 2 := by
      rw [hδcoe, dist_eq_norm, norm_sub_rev] at hxy
      exact hxy.le
    simp only [dist_eq_norm, hAcoe]
    simpa only [norm_sub_rev] using
      norm_gradient_sub_le_of_tangent_growth hu (hd x hx) (hd y hy) (hgrowth x hx) hnear
  · intro x hx y hy
    have hb (z : E) (hz : z ∈ K) : ‖gradient u z‖ ≤ B := by
      rw [hBcoe]
      exact (hM (gradient u z) ⟨z, hz, rfl⟩).trans (le_max_left _ _)
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      (dist_le_norm_add_norm (gradient u x) (gradient u y)).trans
        (by linarith [hb x hx, hb y hy] : ‖gradient u x‖ + ‖gradient u y‖ ≤ 2 * (B : ℝ))

private theorem hasDerivAt_defect_ray
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    (x v : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (u (x + s • v) - u x - inner ℝ (gradient u x) ((x + s • v) - x)))
      ⟪gradient u (x + t • v) - gradient u x, v⟫ t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add x
  have hu :
      HasDerivAt (fun s : ℝ => u (x + s • v))
        ⟪gradient u (x + t • v), v⟫ t := by
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      (hdiff (x + t • v)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hp
  have hlin :
      HasDerivAt
        (fun s : ℝ => s * ⟪gradient u x, v⟫)
        ⟪gradient u x, v⟫ t := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id t).mul_const ⟪gradient u x, v⟫
  have heq : (fun s : ℝ => (u (x + s • v) - u x - inner ℝ (gradient u x) ((x + s • v) - x))) =
      ((fun s : ℝ => u (x + s • v) - u x) - fun s : ℝ => s * ⟪gradient u x, v⟫) := by
    funext s
    simp only [ Pi.sub_apply, add_sub_cancel_left, inner_smul_right]
  rw [heq, inner_sub_left]
  exact (hu.sub_const (u x)).sub hlin

/-- Local soft engulfing, in the stated direction, makes the tangent-defect
quotient monotone along each ray whose endpoint lies in the allowed ball.

Only differentiability is needed for this analytic implication. -/
private theorem monotoneOn_ray_quotient_of_soft
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    {r₀ κ : ℝ} (hκ : 1 ≤ κ) {x : E}
    (hsoft : ∀ z : E, ‖z - x‖ ≤ r₀ →
      (u z - u x - inner ℝ (gradient u x) (z - x)) ≤
        κ * (u x - u z - inner ℝ (gradient u z) (x - z)))
    {v : E} (hv : ‖v‖ ≤ r₀) :
    MonotoneOn
      (fun t : ℝ =>
        (u (x + t • v) - u x - inner ℝ (gradient u x) ((x + t • v) - x)) / t ^ (1 + κ⁻¹))
      (Ioc (0 : ℝ) 1) := by
  refine monotoneOn_div_rpow_of_mul_le_mul_deriv
    (f' := fun t : ℝ ↦ ⟪gradient u (x + t • v) - gradient u x, v⟫)
    (convex_Ioc (0 : ℝ) 1) (fun t ht ↦ ht.1) ?_ ?_ ?_
  · intro t _
    exact (hasDerivAt_defect_ray hdiff x v t).continuousAt.continuousWithinAt
  · intro t _
    exact hasDerivAt_defect_ray hdiff x v t
  · intro t ht
    have ht := interior_subset ht
    have hdist : ‖x + t • v - x‖ ≤ r₀ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht.1]
      calc
        t * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ r₀ := by simpa only [one_mul] using hv
    have hrev :
        (u x - u (x + t • v) - inner ℝ (gradient u (x + t • v)) (x - (x + t • v))) =
          t * ⟪gradient u (x + t • v) - gradient u x, v⟫ -
            (u (x + t • v) - u x - inner ℝ (gradient u x) ((x + t • v) - x)) := by
      simp only [
        show x - (x + t • v) = -(t • v) by abel,
        add_sub_cancel_left, inner_neg_right, inner_smul_right,
        inner_sub_left]
      ring
    have hs := hsoft (x + t • v) hdist
    rw [hrev] at hs
    have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
    have hdiv :
        (u (x + t • v) - u x - inner ℝ (gradient u x) ((x + t • v) - x)) / κ ≤
          t * ⟪gradient u (x + t • v) - gradient u x, v⟫ -
            (u (x + t • v) - u x - inner ℝ (gradient u x) ((x + t • v) - x)) := by
      apply (div_le_iff₀ hkpos).mpr
      simpa only [mul_comm] using hs
    have hscaled :
        κ⁻¹ * (u (x + t • v) - u x - inner ℝ (gradient u x) ((x + t • v) - x)) ≤
          t * ⟪gradient u (x + t • v) - gradient u x, v⟫ -
            (u (x + t • v) - u x - inner ℝ (gradient u x) ((x + t • v) - x)) := by
      simpa only [div_eq_mul_inv, mul_comm] using hdiv
    nlinarith only [hscaled]

/-- Pointwise ray growth from local soft engulfing, for `0 < t ≤ 1`. -/
private theorem defect_ray_le_of_soft
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    {r₀ κ : ℝ} (hκ : 1 ≤ κ) {x : E}
    (hsoft : ∀ z : E, ‖z - x‖ ≤ r₀ →
      (u z - u x - inner ℝ (gradient u x) (z - x)) ≤
        κ * (u x - u z - inner ℝ (gradient u z) (x - z)))
    {v : E} (hv : ‖v‖ ≤ r₀)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    (u (x + t • v) - u x - inner ℝ (gradient u x) ((x + t • v) - x)) ≤
      (u (x + v) - u x - inner ℝ (gradient u x) ((x + v) - x)) * t ^ (1 + κ⁻¹) := by
  have hmono :=
    monotoneOn_ray_quotient_of_soft hdiff hκ hsoft hv
  have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  have hquot := hmono ht hone ht.2
  have hquot' :
      (u (x + t • v) - u x - inner ℝ (gradient u x) ((x + t • v) - x)) / t ^ (1 + κ⁻¹) ≤
        (u (x + v) - u x - inner ℝ (gradient u x) ((x + v) - x)) := by
    simpa only [one_smul, Real.one_rpow, div_one] using hquot
  exact
    (div_le_iff₀ (Real.rpow_pos_of_pos ht.1 (1 + κ⁻¹))).mp hquot'

/-- Quantitative radial growth from a sphere bound and local soft engulfing.

The norm hypothesis is precisely membership in the closed ball of radius `R`.
The case `z = x` is included. -/
private theorem defect_le_sphere_bound_of_soft
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    {R κ : ℝ} (hR : 0 < R) (hκ : 1 ≤ κ) {x : E}
    (hsoft : ∀ z : E, ‖z - x‖ ≤ R →
      (u z - u x - inner ℝ (gradient u x) (z - x)) ≤
        κ * (u x - u z - inner ℝ (gradient u z) (x - z)))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z : E, ‖z - x‖ = R → (u z - u x - inner ℝ (gradient u x) (z - x)) ≤ M) :
    ∀ z : E, ‖z - x‖ ≤ R →
      (u z - u x - inner ℝ (gradient u x) (z - x)) ≤ M * (‖z - x‖ / R) ^ (1 + κ⁻¹) := by
  intro z hz
  by_cases hzx : z = x
  · have hzdef : (u z - u x - inner ℝ (gradient u x) (z - x)) = 0 := by
      simp [ hzx]
    rw [hzdef]
    exact mul_nonneg hM
      (Real.rpow_nonneg
        (div_nonneg (norm_nonneg _) hR.le) _)
  · have hr : 0 < ‖z - x‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
    let v : E := (R / ‖z - x‖) • (z - x)
    have hvnorm : ‖v‖ = R := by
      dsimp only [v]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hR hr),
        div_mul_cancel₀ _ hr.ne']
    have ht : ‖z - x‖ / R ∈ Ioc (0 : ℝ) 1 := by
      refine ⟨div_pos hr hR, ?_⟩
      apply (div_le_iff₀ hR).mpr
      simpa only [one_mul] using hz
    have hscale :
        (‖z - x‖ / R) * (R / ‖z - x‖) = (1 : ℝ) := by
      field_simp [hR.ne', hr.ne']
    have hpath : x + (‖z - x‖ / R) • v = z := by
      dsimp only [v]
      rw [smul_smul, hscale, one_smul]
      abel
    have hb : (u (x + v) - u x - inner ℝ (gradient u x) ((x + v) - x)) ≤ M := by
      apply hbound (x + v)
      simpa only [add_sub_cancel_left] using hvnorm
    have hgrowth :=
      defect_ray_le_of_soft hdiff hκ hsoft (le_of_eq hvnorm) ht
    rw [hpath] at hgrowth
    exact hgrowth.trans
      (mul_le_mul_of_nonneg_right hb
        (Real.rpow_nonneg
          (div_nonneg (norm_nonneg _) hR.le) _))

/-- A global Lipschitz bound and a bound on the gradient at the centre give
the explicit sphere constant `M = (L + B) * R`.

Neither convexity nor positivity of the tangent defect is needed here. -/
private theorem defect_le_of_lipschitz_soft
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    {L : NNReal} (hLip : LipschitzWith L u)
    {R κ : ℝ} (hR : 0 < R) (hκ : 1 ≤ κ)
    {x : E} {B : ℝ} (hB : ‖gradient u x‖ ≤ B)
    (hsoft : ∀ z : E, ‖z - x‖ ≤ R →
      (u z - u x - inner ℝ (gradient u x) (z - x)) ≤
        κ * (u x - u z - inner ℝ (gradient u z) (x - z))) :
    ∀ z : E, ‖z - x‖ ≤ R →
      (u z - u x - inner ℝ (gradient u x) (z - x)) ≤
        (((L : ℝ) + B) * R) *
          (‖z - x‖ / R) ^ (1 + κ⁻¹) := by
  have hB0 : 0 ≤ B := (norm_nonneg (gradient u x)).trans hB
  refine defect_le_sphere_bound_of_soft hdiff hR hκ hsoft
    (mul_nonneg (add_nonneg L.coe_nonneg hB0) hR.le) ?_
  intro z hz
  have huabs : |u z - u x| ≤ (L : ℝ) * ‖z - x‖ := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using
      hLip.dist_le_mul z x
  have hu : u z - u x ≤ (L : ℝ) * ‖z - x‖ :=
    (le_abs_self _).trans huabs
  have hinner :
      -⟪gradient u x, z - x⟫ ≤ B * ‖z - x‖ := by
    calc
      -⟪gradient u x, z - x⟫ ≤ |⟪gradient u x, z - x⟫| :=
        neg_le_abs _
      _ ≤ ‖gradient u x‖ * ‖z - x‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ B * ‖z - x‖ :=
        mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  calc
    (u z - u x - inner ℝ (gradient u x) (z - x)) ≤ ((L : ℝ) + B) * ‖z - x‖ := by
      nlinarith only [hu, hinner]
    _ = ((L : ℝ) + B) * R := by rw [hz]


/-- A uniform local comparison between the two tangent errors of a differentiable convex
Lipschitz function gives a Hölder gradient on any set of allowed centers. -/
theorem exists_holderOnWith_gradient_of_soft_comparison {u : E → ℝ}
    (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    {L : ℝ≥0} (hLip : LipschitzWith L u) {K : Set E}
    {r : ℝ} (hr : 0 < r) {κ : ℝ≥0} (hκ : 1 ≤ κ)
    (hsoft : ∀ x ∈ K, ∀ z, ‖z - x‖ ≤ r →
      u z - u x - inner ℝ (gradient u x) (z - x) ≤
        κ * (u x - u z - inner ℝ (gradient u z) (x - z))) :
    ∃ C : ℝ≥0, HolderOnWith C κ⁻¹ (gradient u) K := by
  have hgrad (x : E) : ‖gradient u x‖ ≤ L := by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hLip
  have hbounded : Bornology.IsBounded (gradient u '' K) :=
    isBounded_iff_forall_norm_le.2 ⟨L, by rintro _ ⟨x, _, rfl⟩; exact hgrad x⟩
  let A : ℝ := (((L : ℝ) + L) * r) / r ^ (1 + (κ : ℝ)⁻¹)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine exists_holderOnWith_gradient_of_tangent_growth hu (fun x _ ↦ hd x) hbounded hr
    (C := A.toNNReal) (α := κ⁻¹) ?_
  intro x hx z hz
  have hκ' : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hrad := defect_le_of_lipschitz_soft hd hLip hr hκ' (hgrad x) (hsoft x hx) z hz
  have hgrowth :
      u z - u x - inner ℝ (gradient u x) (z - x) ≤ A * ‖z - x‖ ^ (1 + (κ : ℝ)⁻¹) := by
    refine hrad.trans_eq ?_
    dsimp only [A]
    rw [Real.div_rpow (norm_nonneg _) hr.le]
    ring
  have hsum : u z ≤ u x + inner ℝ (gradient u x) (z - x) +
      A * ‖z - x‖ ^ (1 + (κ : ℝ)⁻¹) := by linarith only [hgrowth]
  simpa only [NNReal.coe_inv, Real.coe_toNNReal _ hA] using hsum

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Monge–Ampère measure of a cone

Let `E` be a finite-dimensional real inner product space, `a : E` and `0 ≤ r`, and let `μ` be a
measure on `E` absolutely continuous with respect to a Haar measure. In positive dimension, the
*cone* `u x = r * ‖x - a‖` with vertex `a` and slope `r` is the basic example of a convex function
whose Aleksandrov Monge–Ampère measure is singular: all of its mass sits at the vertex,

  `MA_u = μ (closedBall 0 r) • δ_a`

(`TauCeti.mongeAmpereMeasure_mul_norm_sub`; this formula holds in every dimension). The
subdifferential of the cone at `x` is the set of `y` with `‖y‖ ≤ r` and `⟪x - a, y⟫ = r * ‖x - a‖`
(`TauCeti.mem_subdifferential_mul_norm_sub_iff`). At the vertex this is the whole closed ball of
radius `r`, while at every other point it is the single gradient `(r / ‖x - a‖) • (x - a)`, which
lies on the sphere of radius `r`. In positive dimension spheres are null for a Haar measure, so
only the vertex carries mass.

The cone is also the standard example showing that the pointwise Hessian determinant does not
determine the Aleksandrov measure. The cone is twice differentiable away from its vertex, and there
its Hessian has determinant `0`, because the gradient is constant along each ray from `a`
(`TauCeti.det_fderiv_gradient_mul_norm_sub_eq_zero`). In positive dimension and for a Haar measure
`μ`, this gives `det D²u = 0` almost everywhere, yet for `r > 0` the Aleksandrov measure is not
`det (D²u) dμ` (`TauCeti.mongeAmpereMeasure_mul_norm_sub_ne_withDensity_det`): it is mutually
singular with `μ` (`TauCeti.mutuallySingular_mongeAmpereMeasure_mul_norm_sub`). So an identity
`det D²u = f` almost everywhere is strictly weaker than `MA_u = f dμ`.

## Main statements

* `TauCeti.mem_subdifferential_mul_norm_sub_iff` — the subdifferential of the cone;
* `TauCeti.subdifferential_mul_norm_sub_self` and `TauCeti.subdifferential_mul_norm_sub_of_ne` —
  it is the closed ball of radius `r` at the vertex and the gradient elsewhere;
* `TauCeti.mongeAmpereMeasure_mul_norm_sub` — for `μ` absolutely continuous with respect to a Haar
  measure, the Monge–Ampère measure of the cone is `μ (closedBall 0 r) • δ_a`;
* `TauCeti.mutuallySingular_mongeAmpereMeasure_mul_norm_sub` — in positive dimension this measure
  is mutually singular with `μ`;
* `TauCeti.differentiableAt_gradient_mul_norm_sub` and
  `TauCeti.det_fderiv_gradient_mul_norm_sub_eq_zero` — away from the vertex the cone is twice
  differentiable and its Hessian has determinant `0`;
* `TauCeti.mongeAmpereMeasure_mul_norm_sub_ne_withDensity_det` — in positive dimension, for a Haar
  measure `μ` and `r > 0`, the Monge–Ampère measure of the cone is not `det (D²u) dμ`.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.1.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, §2.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric InnerProductSpace
open scoped Topology ENNReal Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℝ} {a x y : E}

section Subdifferential

/-- **The subdifferential of a cone.** For `0 ≤ r`, `y` is a subgradient of `x ↦ r * ‖x - a‖` at
`x` exactly when `‖y‖ ≤ r` and `⟪x - a, y⟫ = r * ‖x - a‖`. -/
theorem mem_subdifferential_mul_norm_sub_iff (hr : 0 ≤ r) :
    y ∈ subdifferential (innerₗ E) (fun x => ((r * ‖x - a‖ : ℝ) : EReal)) x ↔
      ‖y‖ ≤ r ∧ ⟪x - a, y⟫_ℝ = r * ‖x - a‖ := by
  rw [mem_subdifferential_coe_iff]
  simp only [innerₗ_apply_apply]
  constructor
  · intro h
    -- Testing at `x + y` gives `‖y‖ ^ 2 ≤ r * ‖y‖`, and testing at `a` gives
    -- `r * ‖x - a‖ ≤ ⟪x - a, y⟫`.
    have hy : ‖y‖ ≤ r := by
      have h₁ := h (x + y)
      rw [add_sub_cancel_left, real_inner_self_eq_norm_sq, add_sub_right_comm] at h₁
      have h₂ := mul_le_mul_of_nonneg_left (norm_add_le (x - a) y) hr
      nlinarith [norm_nonneg y]
    have h₁ := h a
    rw [sub_self, norm_zero, mul_zero] at h₁
    have h₄ : ⟪a - x, y⟫_ℝ = -⟪x - a, y⟫_ℝ := by rw [← inner_neg_left, neg_sub]
    have h₂ := real_inner_le_norm (x - a) y
    have h₃ := mul_le_mul_of_nonneg_left hy (norm_nonneg (x - a))
    exact ⟨hy, by linarith⟩
  · rintro ⟨hy, hxy⟩ x'
    have h₁ := real_inner_le_norm (x' - a) y
    have h₂ := mul_le_mul_of_nonneg_left hy (norm_nonneg (x' - a))
    have h₃ : ⟪x' - x, y⟫_ℝ = ⟪x' - a, y⟫_ℝ - ⟪x - a, y⟫_ℝ := by
      rw [← inner_sub_left, sub_sub_sub_cancel_right]
    linarith

/-- At its vertex, the subdifferential of the cone `x ↦ r * ‖x - a‖` is the closed ball of radius
`r`. -/
theorem subdifferential_mul_norm_sub_self (hr : 0 ≤ r) (a : E) :
    subdifferential (innerₗ E) (fun x => ((r * ‖x - a‖ : ℝ) : EReal)) a = closedBall 0 r := by
  ext y
  rw [mem_subdifferential_mul_norm_sub_iff hr]
  simp

/-- Away from its vertex, the subdifferential of the cone `x ↦ r * ‖x - a‖` is the single point
`(r / ‖x - a‖) • (x - a)`. -/
theorem subdifferential_mul_norm_sub_of_ne (hr : 0 ≤ r) (hx : x ≠ a) :
    subdifferential (innerₗ E) (fun x => ((r * ‖x - a‖ : ℝ) : EReal)) x =
      {(r / ‖x - a‖) • (x - a)} := by
  have hd : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  ext y
  rw [mem_subdifferential_mul_norm_sub_iff hr, mem_singleton_iff]
  constructor
  · rintro ⟨hy, hxy⟩
    -- Equality in the Cauchy–Schwarz inequality `⟪x - a, y⟫ ≤ ‖x - a‖ * ‖y‖ ≤ ‖x - a‖ * r`.
    have h₁ := real_inner_le_norm (x - a) y
    have hny : ‖y‖ = r := le_antisymm hy (le_of_mul_le_mul_left (by linarith) hd)
    have h₂ := inner_eq_norm_mul_iff_real.1 (hxy.trans (by rw [hny, mul_comm]))
    rw [hny] at h₂
    rw [div_eq_inv_mul, mul_smul, h₂, smul_smul, inv_mul_cancel₀ hd.ne', one_smul]
  · rintro rfl
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hr hd.le), div_mul_cancel₀ _ hd.ne',
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    refine ⟨le_rfl, ?_⟩
    field_simp

/-- Every subgradient of the cone `x ↦ r * ‖x - a‖` away from its vertex has norm `r`. -/
theorem norm_eq_of_mem_subdifferential_mul_norm_sub (hr : 0 ≤ r) (hx : x ≠ a)
    (hy : y ∈ subdifferential (innerₗ E) (fun x => ((r * ‖x - a‖ : ℝ) : EReal)) x) :
    ‖y‖ = r := by
  have hd : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  rw [subdifferential_mul_norm_sub_of_ne hr hx, mem_singleton_iff] at hy
  rw [hy, norm_smul, Real.norm_of_nonneg (div_nonneg hr hd.le), div_mul_cancel₀ _ hd.ne']

end Subdifferential

section Gradient

variable [CompleteSpace E]

/-- Away from its vertex, the cone `x ↦ r * ‖x - a‖` has gradient `(r / ‖x - a‖) • (x - a)`. -/
theorem hasGradientAt_mul_norm_sub (r : ℝ) (hx : x ≠ a) :
    HasGradientAt (fun x => r * ‖x - a‖) ((r / ‖x - a‖) • (x - a)) x := by
  -- The gradient of the norm cone of slope `1` is its unique subgradient.
  have h₁ : HasGradientAt (fun x => ‖x - a‖) ((1 / ‖x - a‖) • (x - a)) x := by
    have h := hasGradientAt_toReal_of_mem_subdifferential
      (f := fun x => ((1 * ‖x - a‖ : ℝ) : EReal))
      (by rw [subdifferential_mul_norm_sub_of_ne zero_le_one hx]; exact mem_singleton _)
      (Eventually.of_forall fun _ => EReal.coe_ne_top _)
      (by simpa only [EReal.toReal_coe, one_mul, id] using
        (differentiableAt_id.sub_const a).norm ℝ (sub_ne_zero.2 hx))
    simpa only [EReal.toReal_coe, one_mul] using h
  rw [hasGradientAt_iff_hasFDerivAt] at h₁ ⊢
  convert h₁.const_mul r using 1
  rw [div_eq_mul_inv, mul_smul, map_smul, one_div]

/-- Away from its vertex, the gradient of the cone `x ↦ r * ‖x - a‖` is
`(r / ‖x - a‖) • (x - a)`. -/
@[simp]
theorem gradient_mul_norm_sub (r : ℝ) (hx : x ≠ a) :
    ∇ (fun x => r * ‖x - a‖) x = (r / ‖x - a‖) • (x - a) :=
  (hasGradientAt_mul_norm_sub r hx).gradient

/-- Away from its vertex, the gradient of the cone `x ↦ r * ‖x - a‖` is differentiable: the cone
is twice differentiable there. -/
theorem differentiableAt_gradient_mul_norm_sub (r : ℝ) (hx : x ≠ a) :
    DifferentiableAt ℝ (∇ fun x => r * ‖x - a‖) x := by
  have hd : DifferentiableAt ℝ (fun x => (r * ‖x - a‖⁻¹) • (x - a)) x :=
    ((differentiableAt_const r).mul
      (((differentiableAt_id.sub_const a).norm ℝ (sub_ne_zero.2 hx)).inv
        (norm_ne_zero_iff.2 (sub_ne_zero.2 hx)))).smul (differentiableAt_id.sub_const a)
  exact hd.congr_of_eventuallyEq <| eventually_of_mem (isOpen_ne.mem_nhds hx) fun x' hx' => by
    rw [gradient_mul_norm_sub r hx', div_eq_mul_inv]

/-- The gradient of the cone `x ↦ r * ‖x - a‖` is constant along each open ray from the vertex `a`,
so away from `a` its derivative vanishes in the radial direction `x - a`. -/
@[simp]
theorem fderiv_gradient_mul_norm_sub_apply_sub (r : ℝ) (hx : x ≠ a) :
    fderiv ℝ (∇ fun x => r * ‖x - a‖) x (x - a) = 0 := by
  have hd : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  -- Along the line `t ↦ x + t • (x - a)`, the gradient is constant for `t > -1`.
  have hconst : (fun t : ℝ => (∇ fun x => r * ‖x - a‖) (x + t • (x - a))) =ᶠ[𝓝 0]
      fun _ => (∇ fun x => r * ‖x - a‖) x := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t (ht : -1 < t)
    have ht' : 0 < 1 + t := by linarith
    have hxt : x + t • (x - a) - a = (1 + t) • (x - a) := by
      rw [add_smul, one_smul, add_sub_right_comm, add_comm]
    have hne : x + t • (x - a) ≠ a := by
      rw [← sub_ne_zero, hxt]
      exact smul_ne_zero ht'.ne' (sub_ne_zero.2 hx)
    rw [gradient_mul_norm_sub r hne, gradient_mul_norm_sub r hx, hxt, norm_smul,
      Real.norm_of_nonneg ht'.le, smul_smul]
    congr 1
    field_simp
  have hline : HasDerivAt (fun t : ℝ => (∇ fun x => r * ‖x - a‖) (x + t • (x - a)))
      (fderiv ℝ (∇ fun x => r * ‖x - a‖) x (x - a)) 0 := by
    simpa only [Function.comp_def, one_smul, id] using
      (differentiableAt_gradient_mul_norm_sub r hx).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
        (((hasDerivAt_id (0 : ℝ)).smul_const (x - a)).const_add x) (by simp)
  exact hline.unique ((hasDerivAt_const _ _).congr_of_eventuallyEq hconst)

/-- **The Hessian of a cone is degenerate.** Away from its vertex `a`, the Hessian of the cone
`x ↦ r * ‖x - a‖` has determinant `0`, since it annihilates the radial direction `x - a`. -/
@[simp]
theorem det_fderiv_gradient_mul_norm_sub_eq_zero [FiniteDimensional ℝ E] (r : ℝ) (hx : x ≠ a) :
    (fderiv ℝ (∇ fun x => r * ‖x - a‖) x).det = 0 := by
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  exact ⟨x - a, fderiv_gradient_mul_norm_sub_apply_sub r hx, sub_ne_zero.2 hx⟩

end Gradient

section Measure

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}
  [ν.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The cone `x ↦ r * ‖x - a‖` with `0 ≤ r` has convex real epigraph. -/
private theorem convex_epigraph_mul_norm_sub (hr : 0 ≤ r) (a : E) :
    Convex ℝ {p : E × ℝ | ((r * ‖p.1 - a‖ : ℝ) : EReal) ≤ p.2} := by
  have h : ConvexOn ℝ univ fun x : E => r * ‖x - a‖ := by
    simpa only [smul_eq_mul, dist_eq_norm] using (convexOn_dist a convex_univ).smul hr
  simpa only [EReal.coe_le_coe_iff, mem_univ, true_and] using h.convex_epigraph

/-- **The Monge–Ampère measure of a cone.** For `0 ≤ r` and a measure `μ` absolutely continuous
with respect to a Haar measure, the Aleksandrov Monge–Ampère measure of the cone
`x ↦ r * ‖x - a‖` is the point mass `μ (closedBall 0 r) • δ_a` at its vertex. -/
theorem mongeAmpereMeasure_mul_norm_sub (hμ : μ ≪ ν) (hr : 0 ≤ r) (a : E) :
    mongeAmpereMeasure μ (fun x => ((r * ‖x - a‖ : ℝ) : EReal)) =
      μ (closedBall 0 r) • dirac a := by
  ext s hs
  rw [mongeAmpereMeasure_apply μ (convex_epigraph_mul_norm_sub hr a)
    (fun _ => EReal.coe_ne_bot _) hμ hs, Measure.smul_apply, dirac_apply' _ hs, smul_eq_mul]
  have hD : interior {x : E | ((r * ‖x - a‖ : ℝ) : EReal) ≠ ⊤} = univ := by
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, ofPred_true, interior_univ]
  rw [hD, inter_univ]
  by_cases ha : a ∈ s
  · -- The subgradient image of `s ∋ a` is the closed ball of radius `r`.
    rw [indicator_of_mem ha, Pi.one_apply, mul_one]
    congr 1
    refine Subset.antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨x, -, hy⟩ := (mem_subgradientImage_iff _).1 hy
      exact mem_closedBall_zero_iff.2 ((mem_subdifferential_mul_norm_sub_iff hr).1 hy).1
    · exact (mem_subgradientImage_iff _).2 ⟨a, ha, by rwa [subdifferential_mul_norm_sub_self hr]⟩
  · -- The subgradient image of `s ∌ a` lies in the sphere of radius `r`, a Haar-null set.
    rw [indicator_of_notMem ha, mul_zero]
    rcases subsingleton_or_nontrivial E with hE | hE
    · have : s = ∅ := eq_empty_of_forall_notMem fun x hx => ha (Subsingleton.elim x a ▸ hx)
      simp [this]
    refine measure_mono_null (fun y hy => ?_) (hμ (addHaar_sphere ν 0 r))
    obtain ⟨x, hx, hy⟩ := (mem_subgradientImage_iff _).1 hy
    exact mem_sphere_zero_iff_norm.2
      (norm_eq_of_mem_subdifferential_mul_norm_sub hr (ne_of_mem_of_not_mem hx ha) hy)

/-- **The Monge–Ampère measure of a cone is singular.** In positive dimension, the Aleksandrov
Monge–Ampère measure of the cone `x ↦ r * ‖x - a‖`, for `0 ≤ r`, is mutually singular with every
measure `μ` absolutely continuous with respect to a Haar measure. -/
theorem mutuallySingular_mongeAmpereMeasure_mul_norm_sub [Nontrivial E] (hμ : μ ≪ ν) (hr : 0 ≤ r)
    (a : E) : mongeAmpereMeasure μ (fun x => ((r * ‖x - a‖ : ℝ) : EReal)) ⟂ₘ μ := by
  rw [mongeAmpereMeasure_mul_norm_sub hμ hr a]
  exact ⟨{a}ᶜ, (measurableSet_singleton a).compl, by simp, by simpa using hμ (measure_singleton a)⟩

/-- **The Hessian determinant does not determine the Monge–Ampère measure.** In positive
dimension, for a Haar measure `μ` and `0 < r`, the cone `x ↦ r * ‖x - a‖` is twice differentiable
off its vertex with Hessian determinant `0` there
(`TauCeti.det_fderiv_gradient_mul_norm_sub_eq_zero`), yet its Aleksandrov Monge–Ampère measure is
not `det (D²u) dx`. -/
theorem mongeAmpereMeasure_mul_norm_sub_ne_withDensity_det [μ.IsAddHaarMeasure] [Nontrivial E]
    (hr : 0 < r) (a : E) :
    mongeAmpereMeasure μ (fun x => ((r * ‖x - a‖ : ℝ) : EReal)) ≠
      μ.withDensity fun x => ENNReal.ofReal (fderiv ℝ (∇ fun x => r * ‖x - a‖) x).det := by
  have h0 : (μ.withDensity fun x => ENNReal.ofReal (fderiv ℝ (∇ fun x => r * ‖x - a‖) x).det) =
      0 := by
    rw [← withDensity_zero (μ := μ)]
    refine withDensity_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton a)] with x hx
    simp [det_fderiv_gradient_mul_norm_sub_eq_zero r hx]
  rw [h0, mongeAmpereMeasure_mul_norm_sub AbsolutelyContinuous.rfl hr.le a]
  intro h
  have h' := congrArg (fun m : Measure E => m {a}) h
  simp only [Measure.smul_apply, dirac_apply_of_mem (mem_singleton a), smul_eq_mul, mul_one] at h'
  exact (measure_closedBall_pos μ 0 hr).ne' h'

end Measure

end TauCeti

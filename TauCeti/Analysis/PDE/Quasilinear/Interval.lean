/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Quasilinear divergence-form equations on an interval

On a bounded interval `(x₀, x₁)` consider the quasilinear Dirichlet problem

`-(A(x, u) u')' = f + F'` in `(x₀, x₁)`, `u(x₀) = g₀`, `u(x₁) = g₁`,

where the coefficient `A(x, y)` is measurable in `x`, continuous in `y`, and uniformly elliptic and
bounded, `λ ≤ A ≤ M` with `λ > 0`, and the data are `f ∈ L¹` and `F ∈ Lᵖ`, `1 ≤ p ≤ ∞`. A solution
is `u ∈ W^{1,p}(x₀, x₁)` whose continuous representative `ū` takes the boundary values and satisfies

`∫ A(t, ū t) u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

This file proves that a solution exists
(`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`). No uniqueness is claimed, and
none holds for general `A(x, u)`. Since the solution solves the linear equation with the measurable
coefficient `a = A(·, ū)`, with `λ ≤ a ≤ M`, the global Hölder estimate
`TauCeti.PDE.exists_norm_intervalRepresentativeL_le_and_holderWith` applies to it, with a constant
that does not depend on `A` beyond `λ` and `M`.

## The argument

The proof is Schauder's compact-map argument. For a fixed measurable coefficient `a` with
`λ ≤ a ≤ M`, the linear problem `-(a u')' = f + F'` with the same boundary values is solved
explicitly: the flux `a u' + F` has derivative `-f`, so `a u' = k - Φ - F` with `Φ t = ∫_{x₀}^t f`,
and the constant `k` is fixed by `∫ u' = g₁ - g₀`,

`k = (g₁ - g₀ + ∫ a⁻¹ (Φ + F)) / ∫ a⁻¹`, `u t = g₀ + ∫_{x₀}^t a⁻¹ (k - Φ - F)`.

Since `∫ a⁻¹ ≥ (x₁ - x₀) / M`, the constant obeys `|k| ≤ K` with `K` independent of `a`. Freezing
`a = A(·, v)` for `v ∈ C([x₀, x₁])` defines a map `T` of `C([x₀, x₁])` into itself.

* `T` is continuous: by dominated convergence, uniform convergence of `v` gives `L¹` convergence of
  the derivatives `a⁻¹ (k - Φ - F)`, hence uniform convergence of their primitives.
* `T` has relatively compact range: every derivative is dominated by `λ⁻¹ (K + |Φ + F|)`, a fixed
  integrable function, so the range of `T` is bounded and equicontinuous, and the Arzelà–Ascoli
  theorem applies.

Schauder's fixed-point theorem (`TauCeti.schauderFixedPoint_closedConvex_continuousOn`) on a large
closed ball of `C([x₀, x₁])` then gives `u = T u`. The fixed point is absolutely continuous with
derivative in `Lᵖ`, hence the representative of a Sobolev class, and the weak equation follows from
the first integral `A(·, u) u' + F = k - Φ`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 11.1 (Schauder's theorem) and Section 11.3 (the quasilinear Dirichlet problem).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 8.4
  (one-dimensional boundary value problems).
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace Topology Metric
open scoped Distributions Interval

namespace TauCeti.PDE

variable {x₀ x₁ : ℝ}

/-! ### The linear problem with a frozen coefficient -/

/-- The data `Φ + F` of the first integral `a u' + Φ + F = k`, where `Φ t = ∫_{x₀}^t f`. -/
private def fluxData (x₀ : ℝ) (f F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ s in x₀..t, f s) + F t

/-- The constant `k` of the first integral of the solution of `-(a u')' = f + F'` with boundary
values `g₀` and `g₁`. -/
private def fluxConst (x₀ x₁ g₀ g₁ : ℝ) (f F a : ℝ → ℝ) : ℝ :=
  (g₁ - g₀ + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * fluxData x₀ f F t) / ∫ t in Ioo x₀ x₁, (a t)⁻¹

/-- The derivative `a⁻¹ (k - Φ - F)` of the solution of `-(a u')' = f + F'` with boundary values
`g₀` and `g₁`. -/
private def solDeriv (x₀ x₁ g₀ g₁ : ℝ) (f F a : ℝ → ℝ) (t : ℝ) : ℝ :=
  (a t)⁻¹ * (fluxConst x₀ x₁ g₀ g₁ f F a - fluxData x₀ f F t)

section Linear

variable {f F a : ℝ → ℝ} {lam M : ℝ}

private theorem integrableOn_fluxData (hx : x₀ < x₁) (hf : IntegrableOn f (Ioo x₀ x₁))
    (hF : IntegrableOn F (Ioo x₀ x₁)) : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  refine Integrable.add ?_ hF
  exact Integrable.of_bound
    (((TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)).mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    _ ((ae_restrict_mem measurableSet_Ioo).mono fun t ht =>
      TauCeti.intervalIntegral.norm_intervalIntegral_le_setIntegral_norm hf
        (left_mem_Icc.2 hx.le) (Ioo_subset_Icc_self ht))

private theorem ae_norm_inv_le (hlam : 0 < lam)
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ‖(a t)⁻¹‖ ≤ lam⁻¹ :=
  haM.mono fun t ht => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hlam.trans_le ht.1)]
    exact inv_anti₀ hlam ht.1

/-- `∫ a⁻¹ ≥ (x₁ - x₀) / M`. -/
private theorem div_le_setIntegral_inv (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M) :
    (x₁ - x₀) / M ≤ ∫ t in Ioo x₀ x₁, (a t)⁻¹ := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have h := integral_mono_ae (integrable_const M⁻¹)
    (Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _ (ae_norm_inv_le hlam haM))
    (haM.mono fun t ht => inv_anti₀ (hlam.trans_le ht.1) ht.2)
  rwa [setIntegral_const, Real.volume_real_Ioo_of_le hx.le, smul_eq_mul, ← div_eq_mul_inv] at h

/-- The constant of the first integral is bounded independently of the coefficient:
`|k| ≤ M / (x₁ - x₀) * (|g₁ - g₀| + λ⁻¹ ∫ |Φ + F|)`. -/
private theorem abs_fluxConst_le (hx : x₀ < x₁) (hlam : 0 < lam) (hM : 0 < M)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    |fluxConst x₀ x₁ g₀ g₁ f F a| ≤ M / (x₁ - x₀) *
      (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t|) := by
  have hL : 0 < x₁ - x₀ := sub_pos.2 hx
  have hD := div_le_setIntegral_inv hx hlam ha haM
  have hD0 : 0 < ∫ t in Ioo x₀ x₁, (a t)⁻¹ := (div_pos hL hM).trans_le hD
  -- `|∫ a⁻¹ (Φ + F)| ≤ λ⁻¹ ∫ |Φ + F|`.
  have hN : |∫ t in Ioo x₀ x₁, (a t)⁻¹ * fluxData x₀ f F t| ≤
      lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t| := by
    refine abs_integral_le_integral_abs.trans ?_
    rw [← integral_const_mul]
    refine integral_mono_ae (hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable
      (ae_norm_inv_le hlam haM)).abs (hG.abs.const_mul _) ?_
    filter_upwards [ae_norm_inv_le hlam haM] with t ht
    rw [abs_mul, ← Real.norm_eq_abs (a t)⁻¹]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  rw [fluxConst, abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  calc _ ≤ |g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t| :=
        (abs_add_le _ _).trans (by gcongr)
    _ = M / (x₁ - x₀) * (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t|) *
          ((x₁ - x₀) / M) := by field_simp
    _ ≤ _ := by gcongr

/-- The derivative of the solution is dominated by `λ⁻¹ (K + |Φ + F|)` whenever `|k| ≤ K`. -/
private theorem ae_abs_solDeriv_le (hlam : 0 < lam)
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M) {g₀ g₁ K : ℝ}
    (hK : |fluxConst x₀ x₁ g₀ g₁ f F a| ≤ K) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      |solDeriv x₀ x₁ g₀ g₁ f F a t| ≤ lam⁻¹ * (K + |fluxData x₀ f F t|) := by
  filter_upwards [ae_norm_inv_le hlam haM] with t ht
  rw [solDeriv, abs_mul, ← Real.norm_eq_abs (a t)⁻¹]
  exact mul_le_mul ht ((abs_sub _ _).trans (by gcongr)) (abs_nonneg _)
    ((norm_nonneg _).trans ht)

private theorem integrableOn_solDeriv (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    IntegrableOn (solDeriv x₀ x₁ g₀ g₁ f F a) (Ioo x₀ x₁) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  exact ((integrable_const _).sub hG).bdd_mul ha.aemeasurable.inv.aestronglyMeasurable
    (ae_norm_inv_le hlam haM)

/-- The solution takes the boundary value `g₁` at `x₁`: `∫_{x₀}^{x₁} u' = g₁ - g₀`. -/
private theorem intervalIntegral_solDeriv (hx : x₀ < x₁) (hlam : 0 < lam) (hM : 0 < M)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    ∫ t in x₀..x₁, solDeriv x₀ x₁ g₀ g₁ f F a t = g₁ - g₀ := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hD0 : (∫ t in Ioo x₀ x₁, (a t)⁻¹) ≠ 0 :=
    ((div_pos (sub_pos.2 hx) hM).trans_le (div_le_setIntegral_inv hx hlam ha haM)).ne'
  have hinv : Integrable (fun t => (a t)⁻¹) (volume.restrict (Ioo x₀ x₁)) :=
    Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _ (ae_norm_inv_le hlam haM)
  have heq : ∀ t, solDeriv x₀ x₁ g₀ g₁ f F a t =
      (a t)⁻¹ * fluxConst x₀ x₁ g₀ g₁ f F a - (a t)⁻¹ * fluxData x₀ f F t := fun t =>
    mul_sub _ _ _
  simp_rw [intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo, heq]
  rw [integral_sub (hinv.mul_const _) ?_, integral_mul_const, fluxConst, ← mul_div_assoc,
    mul_div_cancel_left₀ _ hD0]
  · ring
  · exact hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable (ae_norm_inv_le hlam haM)

end Linear

/-! ### Continuous dependence on the coefficient -/

section Dependence

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {f F : ℝ → ℝ}
  {a : X → ℝ → ℝ} {lam M : ℝ}

/-- For a family of coefficients `a v` depending continuously on a parameter `v`, with uniform
bounds `λ ≤ a v ≤ M`, the constant of the first integral depends continuously on `v`. -/
private theorem continuous_fluxConst (hx : x₀ < x₁) (hlam : 0 < lam) (hM : 0 < M)
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ v, lam ≤ a v t ∧ a v t ≤ M)
    (hac : ∀ t, Continuous fun v => a v t)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    Continuous fun v => fluxConst x₀ x₁ g₀ g₁ f F (a v) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have haM' : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M := fun v =>
    haM.mono fun t ht => ht v
  -- Off a null set, `v ↦ (a v t)⁻¹` is continuous, since `a v t ≥ λ > 0`.
  have hinvc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous fun v => (a v t)⁻¹ :=
    haM.mono fun t ht => (hac t).inv₀ fun v => (hlam.trans_le (ht v).1).ne'
  have hD : Continuous fun v => ∫ t in Ioo x₀ x₁, (a v t)⁻¹ :=
    continuous_of_dominated (fun v => (ha v).aemeasurable.inv.aestronglyMeasurable)
      (fun v => ae_norm_inv_le hlam (haM' v)) (integrable_const _) hinvc
  have hN : Continuous fun v => ∫ t in Ioo x₀ x₁, (a v t)⁻¹ * fluxData x₀ f F t :=
    continuous_of_dominated
      (fun v => (ha v).aemeasurable.inv.aestronglyMeasurable.mul hG.aestronglyMeasurable)
      (fun v => (ae_norm_inv_le hlam (haM' v)).mono fun t ht => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ht (norm_nonneg _))
      (hG.norm.const_mul _) (hinvc.mono fun t ht => ht.mul continuous_const)
  exact (continuous_const.add hN).div hD fun v =>
    ((div_pos (sub_pos.2 hx) hM).trans_le (div_le_setIntegral_inv hx hlam (ha v) (haM' v))).ne'

/-- For a family of coefficients as in `continuous_fluxConst`, the derivatives of the solutions
depend continuously on the parameter in `L¹(x₀, x₁)`. -/
private theorem continuous_integral_abs_solDeriv_sub (hx : x₀ < x₁) (hlam : 0 < lam) (hM : 0 < M)
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ v, lam ≤ a v t ∧ a v t ≤ M)
    (hac : ∀ t, Continuous fun v => a v t)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) (v₀ : X) :
    Continuous fun v => ∫ t in Ioo x₀ x₁,
      |solDeriv x₀ x₁ g₀ g₁ f F (a v) t - solDeriv x₀ x₁ g₀ g₁ f F (a v₀) t| := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have haM' : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M := fun v =>
    haM.mono fun t ht => ht v
  set K := M / (x₁ - x₀) * (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t|)
  have hK : ∀ v, |fluxConst x₀ x₁ g₀ g₁ f F (a v)| ≤ K := fun v =>
    abs_fluxConst_le hx hlam hM (ha v) (haM' v) hG g₀ g₁
  have hkc := continuous_fluxConst hx hlam hM ha haM hac hG g₀ g₁
  refine continuous_of_dominated (bound := fun t => 2 * (lam⁻¹ * (K + |fluxData x₀ f F t|)))
    (fun v => ((integrableOn_solDeriv hlam (ha v) (haM' v) hG g₀ g₁).sub
      (integrableOn_solDeriv hlam (ha v₀) (haM' v₀) hG g₀ g₁)).abs.aestronglyMeasurable)
    (fun v => ?_) (((integrable_const K).add hG.abs).const_mul _ |>.const_mul _) ?_
  · filter_upwards [ae_abs_solDeriv_le hlam (haM' v) (hK v),
      ae_abs_solDeriv_le hlam (haM' v₀) (hK v₀)] with t h₁ h₂
    rw [Real.norm_eq_abs, abs_abs, two_mul]
    exact (abs_sub _ _).trans (add_le_add h₁ h₂)
  · filter_upwards [haM] with t ht
    refine (((hac t).inv₀ fun v => (hlam.trans_le (ht v).1).ne').mul
      (hkc.sub continuous_const)).sub continuous_const |>.abs

end Dependence

/-! ### The fixed point -/

section FixedPoint

variable {f F : ℝ → ℝ} {lam M : ℝ}

/-- **The fixed point of the solution map.** Let `a v`, for `v ∈ C([x₀, x₁])`, be coefficients with
uniform bounds `λ ≤ a v ≤ M` that depend continuously on `v` at almost every point. Then some
`u ∈ C([x₀, x₁])` is the solution of the linear problem with the coefficient `a u`. -/
private theorem exists_eq_add_intervalIntegral_solDeriv (hx : x₀ < x₁) (hlam : 0 < lam)
    (hM : 0 < M) {a : C(Icc x₀ x₁, ℝ) → ℝ → ℝ}
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ v, lam ≤ a v t ∧ a v t ≤ M)
    (hac : ∀ t, Continuous fun v => a v t)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    ∃ u : C(Icc x₀ x₁, ℝ), ∀ t : Icc x₀ x₁,
      u t = g₀ + ∫ s in x₀..t, solDeriv x₀ x₁ g₀ g₁ f F (a u) s := by
  have haM' : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M := fun v =>
    haM.mono fun t ht => ht v
  -- The uniform bound `|k| ≤ K` and the common dominating function `b = λ⁻¹ (K + |Φ + F|)`.
  set K := M / (x₁ - x₀) * (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t|)
  set b : ℝ → ℝ := fun t => lam⁻¹ * (K + |fluxData x₀ f F t|)
  have hK0 : 0 ≤ K :=
    (abs_nonneg _).trans (abs_fluxConst_le hx hlam hM (ha 0) (haM' 0) hG g₀ g₁)
  have hb0 : ∀ t, 0 ≤ b t := fun t =>
    mul_nonneg (inv_nonneg.2 hlam.le) (add_nonneg hK0 (abs_nonneg _))
  have hbi : IntegrableOn b (Ioo x₀ x₁) :=
    have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) :=
      Real.isFiniteMeasure_restrict_Ioo x₀ x₁
    ((integrable_const K).add hG.abs).const_mul _
  have hdi : ∀ v, IntegrableOn (solDeriv x₀ x₁ g₀ g₁ f F (a v)) (Ioo x₀ x₁) := fun v =>
    integrableOn_solDeriv hlam (ha v) (haM' v) hG g₀ g₁
  have hdb : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      |solDeriv x₀ x₁ g₀ g₁ f F (a v) t| ≤ b t := fun v =>
    ae_abs_solDeriv_le hlam (haM' v) (abs_fluxConst_le hx hlam hM (ha v) (haM' v) hG g₀ g₁)
  have hx₀ : x₀ ∈ Icc x₀ x₁ := left_mem_Icc.2 hx.le
  -- The solution map `T`.
  let T : C(Icc x₀ x₁, ℝ) → C(Icc x₀ x₁, ℝ) := fun v =>
    ⟨fun t => g₀ + ∫ s in x₀..t, solDeriv x₀ x₁ g₀ g₁ f F (a v) s, continuous_const.add
      ((TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo (hdi v)
        (left_mem_Icc.2 hx.le)).comp_continuous continuous_subtype_val Subtype.prop)⟩
  have hT : ∀ v (t : Icc x₀ x₁), T v t = g₀ + ∫ s in x₀..t, solDeriv x₀ x₁ g₀ g₁ f F (a v) s :=
    fun _ _ => rfl
  -- `T` is continuous, by `L¹` continuity of the derivatives in `v`.
  have hTc : Continuous T := by
    refine continuous_iff_continuousAt.2 fun v₀ => tendsto_iff_dist_tendsto_zero.2 ?_
    have hD := continuous_integral_abs_solDeriv_sub hx hlam hM ha haM hac hG g₀ g₁ v₀
    refine squeeze_zero (fun _ => dist_nonneg) (fun v => ?_) (by simpa using hD.tendsto v₀)
    refine (ContinuousMap.dist_le (integral_nonneg fun _ => abs_nonneg _)).2 fun t => ?_
    rw [hT, hT, Real.dist_eq, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
      (TauCeti.intervalIntegral.intervalIntegrable_of_integrableOn_Ioo (hdi v) hx₀ t.2)
      (TauCeti.intervalIntegral.intervalIntegrable_of_integrableOn_Ioo (hdi v₀) hx₀ t.2)]
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      TauCeti.intervalIntegral.norm_intervalIntegral_le_setIntegral_norm ((hdi v).sub (hdi v₀))
        hx₀ t.2
  -- The values of `T` are bounded by `R`, and its increments by those of the primitive of `b`.
  set R := |g₀| + ∫ t in Ioo x₀ x₁, b t
  have hTR : ∀ v, ‖T v‖ ≤ R := fun v => by
    refine (ContinuousMap.norm_le _ (add_nonneg (abs_nonneg _) (integral_nonneg hb0))).2
      fun t => ?_
    rw [hT, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    have h := TauCeti.intervalIntegral.norm_intervalIntegral_le_setIntegral_norm (hdi v) hx₀ t.2
    simp only [Real.norm_eq_abs] at h
    exact h.trans (integral_mono_ae (hdi v).abs hbi (hdb v))
  have hTinc : ∀ v (y z : Icc x₀ x₁), dist (T v y) (T v z) ≤ |∫ s in y..z, b s| :=
    fun v y z => by
      rw [hT, hT, Real.dist_eq, add_sub_add_left_eq_sub, abs_sub_comm,
        intervalIntegral.integral_interval_sub_left
          (TauCeti.intervalIntegral.intervalIntegrable_of_integrableOn_Ioo (hdi v) hx₀ z.2)
          (TauCeti.intervalIntegral.intervalIntegrable_of_integrableOn_Ioo (hdi v) hx₀ y.2)]
      simpa only [Real.norm_eq_abs] using
        TauCeti.intervalIntegral.norm_intervalIntegral_le_abs_intervalIntegral hbi
          ((hdb v).mono fun t ht => (Real.norm_eq_abs _).trans_le ht) y.2 z.2
  -- By the Arzelà–Ascoli theorem, the range of `T` is relatively compact.
  have hK : IsCompact (closure (range T)) := by
    refine ArzelaAscoli.isCompact_closure_range_of_equicontinuous (fun y => ?_)
      fun _ => ⟨closedBall 0 R, isCompact_closedBall 0 R, fun v => ?_⟩
    · refine Metric.equicontinuousAt_of_continuity_modulus
        (fun z : Icc x₀ x₁ => |∫ s in y..z, b s|) ?_ _
        (Eventually.of_forall fun z v => hTinc v y z)
      have hBc : Continuous fun z : Icc x₀ x₁ => ∫ s in y..z, b s :=
        (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hbi
          y.2).comp_continuous continuous_subtype_val Subtype.prop
      simpa using hBc.abs.tendsto y
    · exact mem_closedBall_zero_iff.2 (((T v).norm_coe_le_norm _).trans (hTR v))
  -- Schauder's fixed-point theorem on the closed ball of radius `R`.
  obtain ⟨u, -, hu⟩ := schauderFixedPoint_closedConvex_continuousOn isClosed_closedBall
    (convex_closedBall 0 R) (nonempty_closedBall.2 ((norm_nonneg _).trans (hTR 0)))
    hTc.continuousOn (fun v _ => mem_closedBall_zero_iff.2 (hTR v))
    (hK.of_isClosed_subset isClosed_closure (closure_mono (image_subset_range _ _)))
  exact ⟨u, fun t => by rw [← hT u t, hu.eq]⟩

end FixedPoint

/-! ### The weak solution -/

variable {p : ENNReal} [Fact (1 ≤ p)] {f F : ℝ → ℝ} {A : ℝ → ℝ → ℝ} {lam M : ℝ}

/-- A fixed point `u` of the solution map is the continuous representative of a Sobolev class
with the prescribed boundary values that solves the quasilinear equation weakly. -/
private theorem exists_w1p_of_eq_add_intervalIntegral (hx : x₀ < x₁) (hlam : 0 < lam)
    (hM : 0 < M) (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ A t y ∧ A t y ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) (u : C(Icc x₀ x₁, ℝ)) (ha : Measurable fun t => A t (u (projIcc x₀ x₁ hx.le t)))
    (hu : ∀ t : Icc x₀ x₁, u t = g₀ + ∫ s in x₀..t,
      solDeriv x₀ x₁ g₀ g₁ f F (fun t => A t (u (projIcc x₀ x₁ hx.le t))) s) :
    ∃ w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalTraceL hx w = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx w (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient w t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  set a : ℝ → ℝ := fun t => A t (u (projIcc x₀ x₁ hx.le t))
  set h := solDeriv x₀ x₁ g₀ g₁ f F a
  set k := fluxConst x₀ x₁ g₀ g₁ f F a
  have hFi : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  have hG := integrableOn_fluxData hx hf hFi
  have haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M := hA.mono fun t ht => ht _
  -- The derivative `h` lies in `Lᵖ`, being dominated by `λ⁻¹ (|k| + ‖f‖₁ + |F|)`.
  have hhLp : MemLp h p (volume.restrict (Ioo x₀ x₁)) := by
    refine MemLp.of_le (g := fun t => lam⁻¹ * (|k| + ∫ s in Ioo x₀ x₁, |f s|) + lam⁻¹ * ‖F t‖)
      ((memLp_const _).add (hF.norm.const_mul _))
      (integrableOn_solDeriv hlam ha.aestronglyMeasurable haM hG g₀ g₁).aestronglyMeasurable ?_
    filter_upwards [ae_abs_solDeriv_le (K := |k|) hlam haM le_rfl,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    have hΦ := TauCeti.intervalIntegral.norm_intervalIntegral_le_setIntegral_norm hf
      (left_mem_Icc.2 hx.le) (Ioo_subset_Icc_self htI)
    simp only [Real.norm_eq_abs] at hΦ
    have hGt : |fluxData x₀ f F t| ≤ (∫ s in Ioo x₀ x₁, |f s|) + |F t| :=
      (abs_add_le _ _).trans (add_le_add_left hΦ _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    calc |h t| ≤ lam⁻¹ * (|k| + |fluxData x₀ f F t|) := ht
      _ ≤ lam⁻¹ * (|k| + ((∫ s in Ioo x₀ x₁, |f s|) + |F t|)) := by gcongr
      _ = _ := by rw [Real.norm_eq_abs]; ring
  obtain ⟨w, hw, hgrad⟩ := W1p.exists_intervalRepresentativeL_eq_and_gradient_ae_eq hx g₀ hhLp
  have hwu : W1p.intervalRepresentativeL hx w = u :=
    ContinuousMap.ext fun t => (hw t).trans (hu t).symm
  refine ⟨w, ?_, fun φ => ?_⟩
  · -- The boundary values.
    have hend : ∫ s in x₀..x₁, h s = g₁ - g₀ :=
      intervalIntegral_solDeriv hx hlam hM ha.aestronglyMeasurable haM hG g₀ g₁
    rw [W1p.intervalTraceL_apply, hwu, hu, hu]
    simp only [intervalIntegral.integral_same, add_zero, hend, add_sub_cancel]
  -- The weak equation, from the first integral `a h = k - Φ - F`, where `k - Φ` has weak
  -- derivative `-f`.
  have hline : ∀ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 = deriv (φ : ℝ → ℝ) t := fun t =>
    (φ.contDiff.differentiable (by simp) t).lineDeriv_eq_fderiv
  have hw : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩
      (fun t => k - ∫ s in x₀..t, f s) (-f) 1 :=
    ((hasWeakLineDerivOn_const k).sub (hasWeakLineDerivOn_intervalIntegral_left hf)).congr_ae_deriv
      (EventuallyEq.of_eq (zero_sub f))
  have hkΦ : ∫ t in Ioo x₀ x₁, (k - ∫ s in x₀..t, f s) * deriv φ t =
      ∫ t in Ioo x₀ x₁, f t * φ t := by
    have e := hw.integral_lineDeriv_smul_eq_neg_integral_smul φ
    rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
      ← setIntegral_smul_eq_integral_smul] at e
    simp only [Opens.coe_mk, hline, smul_eq_mul, Pi.neg_apply, mul_neg, MeasureTheory.integral_neg,
      neg_neg] at e
    simpa only [mul_comm] using e
  have h1 := integrable_lineDeriv_smul_of_locallyIntegrableOn
    (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩) (μ := volume) hw.locallyIntegrableOn φ 1
  have h2 := integrable_lineDeriv_smul_of_locallyIntegrableOn
    (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩) (μ := volume) hFi.locallyIntegrableOn φ 1
  simp only [hline, smul_eq_mul] at h1 h2
  have hcongr : (fun t => A t (W1p.intervalRepresentativeL hx w (projIcc x₀ x₁ hx.le t)) *
      W1p.gradient w t * deriv φ t) =ᵐ[volume.restrict (Ioo x₀ x₁)]
      fun t => (k - ∫ s in x₀..t, f s) * deriv φ t - F t * deriv φ t := by
    filter_upwards [hgrad, haM] with t ht hat
    have ha0 : a t ≠ 0 := (hlam.trans_le hat.1).ne'
    rw [hwu, ht]
    simp only [h, solDeriv, fluxData]
    field_simp
    ring
  rw [integral_congr_ae hcongr, integral_sub (h1.integrableOn.congr_fun (fun t _ => mul_comm _ _)
    measurableSet_Ioo) (h2.integrableOn.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioo),
    hkΦ]

/-- **Existence for the quasilinear Dirichlet problem on an interval.** Let `x₀ < x₁` and let
`A : ℝ → ℝ → ℝ` be measurable in its first variable and continuous in its second, with
`λ ≤ A t y ≤ M` for almost every `t ∈ (x₀, x₁)` and every `y`, where `λ > 0`. Let `f ∈ L¹(x₀, x₁)`,
`F ∈ Lᵖ(x₀, x₁)` with `1 ≤ p ≤ ∞`, and `g₀, g₁ ∈ ℝ`. Then there is `u ∈ W^{1,p}(x₀, x₁)` whose
continuous representative `ū` takes the boundary values `ū x₀ = g₀`, `ū x₁ = g₁`, and which solves
`-(A(x, u) u')' = f + F'` weakly:

`∫ A(t, ū t) u' φ' = ∫ f φ - ∫ F φ'` for every `φ ∈ C_c^∞(x₀, x₁)`. -/
theorem exists_intervalTraceL_eq_and_forall_setIntegral_eq (hx : x₀ < x₁) (hlam : 0 < lam)
    (hAm : ∀ y, Measurable fun t => A t y) (hAc : ∀ t, Continuous (A t))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ A t y ∧ A t y ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  have hM : 0 < M := by
    have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by simp [hx])
    obtain ⟨t, ht⟩ := hA.exists
    linarith [(ht 0).1, (ht 0).2]
  -- Freeze the coefficient at `v ∈ C([x₀, x₁])`: `a v = A(·, v)`. It is measurable because `A`
  -- is a Carathéodory function.
  set a : C(Icc x₀ x₁, ℝ) → ℝ → ℝ := fun v t => A t (v (projIcc x₀ x₁ hx.le t))
  have ham : ∀ v, Measurable (a v) := fun v =>
    (measurable_uncurry_of_continuous_of_measurable (u := fun y t => A t y) hAc hAm).comp
      ((v.continuous.comp continuous_projIcc).measurable.prodMk measurable_id)
  obtain ⟨u, hu⟩ := exists_eq_add_intervalIntegral_solDeriv hx hlam hM
    (fun v => (ham v).aestronglyMeasurable) (hA.mono fun t ht v => ht _)
    (fun t => (hAc t).comp (continuous_eval_const _))
    (integrableOn_fluxData hx hf (hF.integrable Fact.out)) g₀ g₁
  exact exists_w1p_of_eq_add_intervalIntegral hx hlam hM hA hf hF g₀ g₁ u (ham u) hu

end TauCeti.PDE

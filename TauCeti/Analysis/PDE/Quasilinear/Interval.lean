/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Quasilinear divergence-form equations on an interval

On a bounded interval `(x₀, x₁)` consider the quasilinear Dirichlet problem

`-(A(x, u) u')' = f + F'` in `(x₀, x₁)`, `u(x₀) = g₀`, `u(x₁) = g₁`,

where the coefficient `A(x, y)` is a Carathéodory function on `(x₀, x₁)`, measurable in `x` and,
for almost every `x`, continuous in `y`, and is uniformly elliptic and bounded, `λ ≤ A ≤ M` with
`λ > 0`, and the data are `f ∈ L¹` and `F ∈ Lᵖ`, `1 ≤ p ≤ ∞`. A solution is `u ∈ W^{1,p}(x₀, x₁)`
whose continuous representative `ū` takes the boundary values and satisfies

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
    (hF : IntegrableOn F (Ioo x₀ x₁)) : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁) :=
  ((TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
    (left_mem_Icc.2 hx.le)).integrableOn_Icc.mono_set Ioo_subset_Icc_self).add hF

/-- The constant of the first integral is bounded independently of the coefficient:
`|k| ≤ M / (x₁ - x₀) * (|g₁ - g₀| + λ⁻¹ ∫ |Φ + F|)`. -/
private theorem abs_fluxConst_le (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    |fluxConst x₀ x₁ g₀ g₁ f F a| ≤ M / (x₁ - x₀) *
      (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t|) := by
  rw [fluxConst]
  exact abs_add_setIntegral_inv_mul_div_le hx hlam ha haM hG (g₁ - g₀)

/-- The derivative of the solution is dominated by `λ⁻¹ (K + |Φ + F|)` whenever `|k| ≤ K`. -/
private theorem ae_abs_solDeriv_le (hlam : 0 < lam)
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) {g₀ g₁ K : ℝ}
    (hK : |fluxConst x₀ x₁ g₀ g₁ f F a| ≤ K) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      |solDeriv x₀ x₁ g₀ g₁ f F a t| ≤ lam⁻¹ * (K + |fluxData x₀ f F t|) := by
  filter_upwards [hlama.norm_inv_le_inv hlam] with t ht
  rw [solDeriv, abs_mul, ← Real.norm_eq_abs (a t)⁻¹]
  exact mul_le_mul ht ((abs_sub _ _).trans (by gcongr)) (abs_nonneg _)
    ((norm_nonneg _).trans ht)

private theorem integrableOn_solDeriv (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    IntegrableOn (solDeriv x₀ x₁ g₀ g₁ f F a) (Ioo x₀ x₁) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  exact ((integrable_const _).sub hG).bdd_mul ha.aemeasurable.inv.aestronglyMeasurable
    (hlama.norm_inv_le_inv hlam)

/-- The solution takes the boundary value `g₁` at `x₁`: `∫_{x₀}^{x₁} u' = g₁ - g₀`. -/
private theorem intervalIntegral_solDeriv (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    ∫ t in x₀..x₁, solDeriv x₀ x₁ g₀ g₁ f F a t = g₁ - g₀ := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hD0 : (∫ t in Ioo x₀ x₁, (a t)⁻¹) ≠ 0 :=
    (setIntegral_inv_pos (by simp [hx]) measure_Ioo_lt_top.ne hlam ha hlama).ne'
  have hle := hlama.norm_inv_le_inv hlam
  have hinv : Integrable (fun t => (a t)⁻¹) (volume.restrict (Ioo x₀ x₁)) :=
    Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _ hle
  have heq : ∀ t, solDeriv x₀ x₁ g₀ g₁ f F a t =
      (a t)⁻¹ * fluxConst x₀ x₁ g₀ g₁ f F a - (a t)⁻¹ * fluxData x₀ f F t := fun t =>
    mul_sub _ _ _
  simp_rw [intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo, heq]
  rw [integral_sub (hinv.mul_const _) ?_, integral_mul_const, fluxConst, ← mul_div_assoc,
    mul_div_cancel_left₀ _ hD0]
  · ring
  · exact hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable hle

end Linear

/-! ### Continuous dependence on the coefficient -/

section Dependence

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {f F : ℝ → ℝ}
  {a : X → ℝ → ℝ} {lam M : ℝ}

/-- For a family of coefficients `a v` depending continuously on a parameter `v` at almost every
point, with a uniform lower bound `λ ≤ a v`, the constant of the first integral depends
continuously on `v`. -/
private theorem continuous_fluxConst (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ v, lam ≤ a v t)
    (hac : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous fun v => a v t)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    Continuous fun v => fluxConst x₀ x₁ g₀ g₁ f F (a v) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hlama' : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t := fun v =>
    hlama.mono fun t ht => ht v
  have hle : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ‖(a v t)⁻¹‖ ≤ lam⁻¹ := fun v =>
    (hlama' v).norm_inv_le_inv hlam
  -- Off a null set, `v ↦ (a v t)⁻¹` is continuous, since `a v t ≥ λ > 0`.
  have hinvc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous fun v => (a v t)⁻¹ := by
    filter_upwards [hlama, hac] with t ht hct
    exact hct.inv₀ fun v => (hlam.trans_le (ht v)).ne'
  have hD : Continuous fun v => ∫ t in Ioo x₀ x₁, (a v t)⁻¹ :=
    continuous_of_dominated (fun v => (ha v).aemeasurable.inv.aestronglyMeasurable)
      hle (integrable_const _) hinvc
  have hN : Continuous fun v => ∫ t in Ioo x₀ x₁, (a v t)⁻¹ * fluxData x₀ f F t :=
    continuous_of_dominated
      (fun v => (ha v).aemeasurable.inv.aestronglyMeasurable.mul hG.aestronglyMeasurable)
      (fun v => (hle v).mono fun t ht => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ht (norm_nonneg _))
      (hG.norm.const_mul _) (hinvc.mono fun t ht => ht.mul continuous_const)
  exact (continuous_const.add hN).div hD fun v =>
    (setIntegral_inv_pos (by simp [hx]) measure_Ioo_lt_top.ne hlam (ha v) (hlama' v)).ne'

/-- For a family of coefficients as in `continuous_fluxConst`, the derivatives of the solutions
depend continuously on the parameter in `L¹(x₀, x₁)`. -/
private theorem continuous_integral_abs_solDeriv_sub (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ v, lam ≤ a v t ∧ a v t ≤ M)
    (hac : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous fun v => a v t)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) (v₀ : X) :
    Continuous fun v => ∫ t in Ioo x₀ x₁,
      |solDeriv x₀ x₁ g₀ g₁ f F (a v) t - solDeriv x₀ x₁ g₀ g₁ f F (a v₀) t| := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have haM' : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M := fun v =>
    haM.mono fun t ht => ht v
  set K := M / (x₁ - x₀) * (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t|)
  have hK : ∀ v, |fluxConst x₀ x₁ g₀ g₁ f F (a v)| ≤ K := fun v =>
    abs_fluxConst_le hx hlam (ha v) (haM' v) hG g₀ g₁
  have hlama : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t := fun v =>
    (haM' v).mono fun _ ht => ht.1
  have hkc := continuous_fluxConst hx hlam ha (haM.mono fun _ ht v => (ht v).1) hac hG g₀ g₁
  refine continuous_of_dominated (bound := fun t => 2 * (lam⁻¹ * (K + |fluxData x₀ f F t|)))
    (fun v => ((integrableOn_solDeriv hlam (ha v) (hlama v) hG g₀ g₁).sub
      (integrableOn_solDeriv hlam (ha v₀) (hlama v₀) hG g₀ g₁)).abs.aestronglyMeasurable)
    (fun v => ?_) (((integrable_const K).add hG.abs).const_mul _ |>.const_mul _) ?_
  · filter_upwards [ae_abs_solDeriv_le hlam (hlama v) (hK v),
      ae_abs_solDeriv_le hlam (hlama v₀) (hK v₀)] with t h₁ h₂
    rw [Real.norm_eq_abs, abs_abs, two_mul]
    exact (abs_sub _ _).trans (add_le_add h₁ h₂)
  · filter_upwards [haM, hac] with t ht hct
    refine ((hct.inv₀ fun v => (hlam.trans_le (ht v).1).ne').mul
      (hkc.sub continuous_const)).sub continuous_const |>.abs

end Dependence

/-! ### The fixed point -/

section FixedPoint

variable {f F : ℝ → ℝ} {lam M : ℝ}

/-- **The fixed point of the solution map.** Let `a v`, for `v ∈ C([x₀, x₁])`, be coefficients with
uniform bounds `λ ≤ a v ≤ M` that depend continuously on `v` at almost every point. Then some
`u ∈ C([x₀, x₁])` is the solution of the linear problem with the coefficient `a u`. -/
private theorem exists_eq_add_intervalIntegral_solDeriv (hx : x₀ < x₁) (hlam : 0 < lam)
    {a : C(Icc x₀ x₁, ℝ) → ℝ → ℝ}
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ v, lam ≤ a v t ∧ a v t ≤ M)
    (hac : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous fun v => a v t)
    (hG : IntegrableOn (fluxData x₀ f F) (Ioo x₀ x₁)) (g₀ g₁ : ℝ) :
    ∃ u : C(Icc x₀ x₁, ℝ), ∀ t : Icc x₀ x₁,
      u t = g₀ + ∫ s in x₀..t, solDeriv x₀ x₁ g₀ g₁ f F (a u) s := by
  have haM' : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M := fun v =>
    haM.mono fun t ht => ht v
  have hlama : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t := fun v =>
    (haM' v).mono fun _ ht => ht.1
  -- The uniform bound `|k| ≤ K` and the common dominating function `b = λ⁻¹ (K + |Φ + F|)`.
  set K := M / (x₁ - x₀) * (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |fluxData x₀ f F t|)
  have hbi : IntegrableOn (fun t => lam⁻¹ * (K + |fluxData x₀ f F t|)) (Ioo x₀ x₁) :=
    have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) :=
      Real.isFiniteMeasure_restrict_Ioo x₀ x₁
    ((integrable_const K).add hG.abs).const_mul _
  have hdi : ∀ v, IntegrableOn (solDeriv x₀ x₁ g₀ g₁ f F (a v)) (Ioo x₀ x₁) := fun v =>
    integrableOn_solDeriv hlam (ha v) (hlama v) hG g₀ g₁
  have hdb : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      ‖solDeriv x₀ x₁ g₀ g₁ f F (a v) t‖ ≤ lam⁻¹ * (K + |fluxData x₀ f F t|) := fun v =>
    (ae_abs_solDeriv_le hlam (hlama v) (abs_fluxConst_le hx hlam (ha v) (haM' v) hG g₀ g₁)).mono
      fun _ ht => (Real.norm_eq_abs _).trans_le ht
  -- The solution map `T`.
  let T : C(Icc x₀ x₁, ℝ) → C(Icc x₀ x₁, ℝ) := fun v =>
    ⟨fun t => g₀ + ∫ s in x₀..t, solDeriv x₀ x₁ g₀ g₁ f F (a v) s, continuous_const.add
      ((TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo (hdi v)
        (left_mem_Icc.2 hx.le)).comp_continuous continuous_subtype_val Subtype.prop)⟩
  have hT : ∀ v (t : Icc x₀ x₁), T v t = g₀ + ∫ s in x₀..t, solDeriv x₀ x₁ g₀ g₁ f F (a v) s :=
    fun _ _ => rfl
  have hx₀ : x₀ ∈ Icc x₀ x₁ := left_mem_Icc.2 hx.le
  have hTR := fun v => TauCeti.intervalIntegral.norm_le_of_forall_eq_add_integral hx₀ (hdi v) hbi
    (hdb v) (hT v)
  have hTc : Continuous T := TauCeti.intervalIntegral.continuous_of_forall_eq_add_integral hx₀ hdi
    (fun v₀ => by simpa only [Real.norm_eq_abs] using
      continuous_integral_abs_solDeriv_sub hx hlam ha haM hac hG g₀ g₁ v₀) hT
  -- Schauder's fixed-point theorem on a closed ball containing the range of `T`.
  obtain ⟨u, -, hu⟩ := schauderFixedPoint_closedConvex_continuousOn isClosed_closedBall
    (convex_closedBall 0 _) (nonempty_closedBall.2 ((norm_nonneg _).trans (hTR 0)))
    hTc.continuousOn (fun v _ => mem_closedBall_zero_iff.2 (hTR v))
    ((TauCeti.intervalIntegral.isCompact_closure_range_of_forall_eq_add_integral hx₀ hdi hbi hdb
      hT).of_isClosed_subset isClosed_closure (closure_mono (image_subset_range _ _)))
  exact ⟨u, fun t => by rw [← hT u t, hu.eq]⟩

end FixedPoint

/-! ### The weak solution -/

variable {p : ENNReal} [Fact (1 ≤ p)] {f F a : ℝ → ℝ} {A : ℝ → ℝ → ℝ} {lam M : ℝ}

/-- The solution `u` of the linear problem with a measurable coefficient `a ≥ λ > 0` is the
continuous representative of a Sobolev class with the prescribed boundary values that solves
`-(a u')' = f + F'` weakly. -/
private theorem exists_w1p_of_eq_add_intervalIntegral (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) (u : C(Icc x₀ x₁, ℝ))
    (hu : ∀ t : Icc x₀ x₁, u t = g₀ + ∫ s in x₀..t, solDeriv x₀ x₁ g₀ g₁ f F a s) :
    ∃ w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalRepresentativeL hx w = u ∧ W1p.intervalTraceL hx w = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient w t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  set k := fluxConst x₀ x₁ g₀ g₁ f F a
  have hFi : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  -- The derivative `a⁻¹ (k - Φ - F)` lies in `Lᵖ`: `a⁻¹` is bounded, the primitive `Φ` is
  -- continuous on `[x₀, x₁]`, and `F ∈ Lᵖ`.
  have hhLp : MemLp (solDeriv x₀ x₁ g₀ g₁ f F a) p (volume.restrict (Ioo x₀ x₁)) := by
    have hGLp : MemLp (fluxData x₀ f F) p (volume.restrict (Ioo x₀ x₁)) :=
      ((TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
        (left_mem_Icc.2 hx.le)).memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
        Ioo_subset_Icc_self p).add hF
    exact (memLp_top_of_bound ha.aemeasurable.inv.aestronglyMeasurable lam⁻¹
      (hlama.norm_inv_le_inv hlam)).mul ((memLp_const k).sub hGLp)
  obtain ⟨w, hw, hgrad⟩ := W1p.exists_intervalRepresentativeL_eq_and_gradient_ae_eq hx
    (left_mem_Icc.2 hx.le) g₀ hhLp
  have hwu : W1p.intervalRepresentativeL hx w = u :=
    ContinuousMap.ext fun t => (hw t).trans (hu t).symm
  refine ⟨w, hwu, ?_, setIntegral_mul_deriv_eq_sub_of_ae_add_eq_sub_intervalIntegral hf
    hFi.locallyIntegrableOn (k := k) ?_⟩
  · -- The boundary values.
    have hend := intervalIntegral_solDeriv hx hlam ha hlama (integrableOn_fluxData hx hf hFi) g₀ g₁
    rw [W1p.intervalTraceL_apply, hwu, hu, hu]
    simp only [intervalIntegral.integral_same, add_zero, hend, add_sub_cancel]
  · -- The first integral `a u' + F = k - Φ`.
    filter_upwards [hgrad, hlama] with t ht hat
    have ha0 : a t ≠ 0 := (hlam.trans_le hat).ne'
    rw [ht]
    simp only [solDeriv, fluxData]
    field_simp
    ring

/-- **Existence for the quasilinear Dirichlet problem on an interval.** Let `x₀ < x₁` and let
`A : ℝ → ℝ → ℝ` be a Carathéodory function on `(x₀, x₁)`: `t ↦ A t y` is almost everywhere strongly
measurable on `(x₀, x₁)` for every `y`, and `A t` is continuous for almost every `t ∈ (x₀, x₁)`.
Assume `λ ≤ A t y ≤ M` for almost every `t ∈ (x₀, x₁)` and every `y`, where `λ > 0`. Let
`f ∈ L¹(x₀, x₁)`, `F ∈ Lᵖ(x₀, x₁)` with `1 ≤ p ≤ ∞`, and `g₀, g₁ ∈ ℝ`. Then there is
`u ∈ W^{1,p}(x₀, x₁)` whose continuous representative `ū` takes the boundary values `ū x₀ = g₀`,
`ū x₁ = g₁`, and which solves `-(A(x, u) u')' = f + F'` weakly:

`∫ A(t, ū t) u' φ' = ∫ f φ - ∫ F φ'` for every `φ ∈ C_c^∞(x₀, x₁)`. -/
theorem exists_intervalTraceL_eq_and_forall_setIntegral_eq (hx : x₀ < x₁) (hlam : 0 < lam)
    (hAm : ∀ y, AEStronglyMeasurable (fun t => A t y) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (A t))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ A t y ∧ A t y ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  -- Freeze the coefficient at `v ∈ C([x₀, x₁])`: `a v = A(·, v)`. It is measurable because `A`
  -- is a Carathéodory function.
  set a : C(Icc x₀ x₁, ℝ) → ℝ → ℝ := fun v t => A t (v (projIcc x₀ x₁ hx.le t))
  have ham : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)) := fun v =>
    (v.continuous.comp continuous_projIcc).aestronglyMeasurable.apply_of_forall_of_continuousAt
      hAm (hAc.mono fun _ ht => ht.continuousAt)
  obtain ⟨u, hu⟩ := exists_eq_add_intervalIntegral_solDeriv hx hlam ham
    (hA.mono fun t ht v => ht _) (hAc.mono fun _ ht => ht.comp (continuous_eval_const _))
    (integrableOn_fluxData hx hf (hF.integrable Fact.out)) g₀ g₁
  obtain ⟨w, hwu, hw, hweak⟩ := exists_w1p_of_eq_add_intervalIntegral hx hlam (ham u)
    (hA.mono fun _ ht => (ht _).1) hf hF g₀ g₁ u hu
  exact ⟨w, hw, by rwa [hwu]⟩

end TauCeti.PDE

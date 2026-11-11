/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# The Dirichlet problem for divergence-form equations on an interval

On a bounded interval `(x₀, x₁)` consider the one-dimensional divergence-form equation

`-(a u')' = f + F'`, `u x₀ = g₀`, `u x₁ = g₁`,

with data `f ∈ L¹(x₀, x₁)` and `F ∈ Lᵖ(x₀, x₁)`. A solution is `u ∈ W^{1,p}(x₀, x₁)` whose endpoint
trace is `(g₀, g₁)` and which satisfies

`∫ a u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

This file proves two existence theorems.

* **The linear problem.** For a measurable coefficient with `λ ≤ a ≤ M`, `λ > 0`, the problem has
  exactly one solution (`TauCeti.PDE.existsUnique_intervalTraceL_eq_forall_integral_eq`). No
  regularity of `a` beyond measurability is needed, and `a` need not be continuous.
* **The quasilinear problem.** Let `A : ℝ → ℝ → ℝ` be a Carathéodory function, measurable in the
  space variable and continuous in the solution variable, with `λ ≤ A t v` for some `λ > 0`.
  Then `-(A(t, u) u')' = f + F'` has a solution with the prescribed boundary values
  (`TauCeti.PDE.exists_intervalTraceL_eq_forall_quasilinear_integral_eq`). No upper bound on `A`
  and no Lipschitz dependence on `u` are assumed, so `A(t, u) = 1 + u²` is allowed; nor is
  uniqueness claimed, since none is available for coefficients depending on `t` and `u` jointly.

## The argument

In one dimension the linear equation is integrated once: the flux `a u' + F` has weak derivative
`-f`, so `a u' = k - Φ - F` with `Φ t = ∫_{x₀}^t f` and a constant `k`. Hence

`u t = g₀ + ∫_{x₀}^t (k - Φ - F) / a`,

and `k` is fixed by `u x₁ = g₁`, which is possible because `∫ 1 / a > 0`. This explicit formula
gives existence; uniqueness follows from the global Hölder estimate
`TauCeti.PDE.exists_norm_intervalRepresentativeL_le_and_holderWith` applied to the difference of
two solutions.

For the quasilinear problem, let `T` send `w ∈ C([x₀, x₁])` to the solution of the linear problem
with coefficient `a = A(·, w)`. Schauder's fixed-point theorem
(`TauCeti.schauderFixedPoint_closedConvex_continuousOn`) gives a fixed point `u = T u`, which is
the required solution. Its hypotheses are checked as follows.

* Writing `u - g₀` as a convex combination shows `‖T w - g₀‖_∞ ≤ |g₁ - g₀| + 2 ‖Φ + F‖₁ / λ`, a
  bound independent of `w`, so `T` maps a closed ball into itself.
* On that ball `A(t, w t) ≤ m t`, where `m t` is the maximum of `A t` over the ball's range of
  values; `m` is measurable and positive, so `∫ 1 / A(·, w) ≥ ∫ 1 / m > 0` uniformly, which
  bounds `k` and makes the image equicontinuous. Arzelà–Ascoli
  (`ArzelaAscoli.isCompact_closure_range_of_equicontinuous`) then makes it relatively compact.
* If `w_n → w` uniformly then `A(t, w_n t) → A(t, w t)` for every `t`, and dominated convergence
  gives `T w_n → T w` uniformly.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4 (one-dimensional boundary value problems).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 11.1 and Chapter 11 (quasilinear existence by Schauder's fixed-point theorem).
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace Topology Metric
open scoped ENNReal NNReal Distributions

namespace TauCeti.PDE

variable {x₀ x₁ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {a f F ψ : ℝ → ℝ} {lam : ℝ}

/-! ### The explicit solution of the linear problem -/

/-- The flux constant `k` of the solution: with `ψ = Φ + F`, the solution has `a u' = k - ψ`,
and `k` is chosen so that `u x₁ - u x₀ = d`. -/
private def fluxConst (x₀ x₁ : ℝ) (a ψ : ℝ → ℝ) (d : ℝ) : ℝ :=
  (d + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * ψ t) / ∫ t in Ioo x₀ x₁, (a t)⁻¹

/-- The explicit solution `g₀ + ∫ s in x₀..t, (a s)⁻¹ * (k - ψ s)`. -/
private def solution (x₀ x₁ : ℝ) (a ψ : ℝ → ℝ) (g₀ g₁ : ℝ) (t : ℝ) : ℝ :=
  g₀ + ∫ s in x₀..t, (a s)⁻¹ * (fluxConst x₀ x₁ a ψ (g₁ - g₀) - ψ s)

private theorem ae_norm_inv_le (hlam : 0 < lam)
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ‖(a t)⁻¹‖ ≤ lam⁻¹ := hla.mono fun t ht => by
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hlam.trans_le ht)]
  exact inv_anti₀ hlam ht

private theorem integrable_inv (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) :
    Integrable (fun t => (a t)⁻¹) (volume.restrict (Ioo x₀ x₁)) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  exact Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _ (ae_norm_inv_le hlam hla)

private theorem integrable_inv_mul (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) {h : ℝ → ℝ}
    (hh : IntegrableOn h (Ioo x₀ x₁)) :
    Integrable (fun t => (a t)⁻¹ * h t) (volume.restrict (Ioo x₀ x₁)) :=
  hh.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable (ae_norm_inv_le hlam hla)

private theorem integrableOn_inv_mul_sub (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    (k : ℝ) : IntegrableOn (fun s => (a s)⁻¹ * (k - ψ s)) (Ioo x₀ x₁) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  exact integrable_inv_mul hlam ha hla ((integrable_const k).sub hψ)

/-- `∫ 1 / a > 0`, although `a` need not be bounded above. -/
private theorem integral_inv_pos (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) :
    0 < ∫ t in Ioo x₀ x₁, (a t)⁻¹ := by
  refine (integral_pos_iff_support_of_nonneg_ae (hla.mono fun t ht =>
    (inv_pos.2 (hlam.trans_le ht)).le) (integrable_inv hlam ha hla)).2 (pos_iff_ne_zero.2 ?_)
  intro h
  have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by simp [hx])
  obtain ⟨t, ht, ht'⟩ := (hla.and (measure_eq_zero_iff_ae_notMem.1 h)).exists
  exact ht' (Function.mem_support.2 (inv_ne_zero (hlam.trans_le ht).ne'))

private theorem continuousOn_solution (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    (g₀ g₁ : ℝ) : ContinuousOn (solution x₀ x₁ a ψ g₀ g₁) (Icc x₀ x₁) :=
  continuousOn_const.add
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo
      (integrableOn_inv_mul_sub hlam ha hla hψ _) (left_mem_Icc.2 hx.le))

@[simp]
private theorem solution_left (a ψ : ℝ → ℝ) (g₀ g₁ : ℝ) : solution x₀ x₁ a ψ g₀ g₁ x₀ = g₀ := by
  simp [solution]

/-- The increment of the explicit solution over `[y, z] ⊆ [x₀, x₁]`. -/
private theorem solution_sub_solution (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    (g₀ g₁ : ℝ) {y z : ℝ} (hy : x₀ ≤ y) (hyz : y ≤ z) (hz : z ≤ x₁) :
    solution x₀ x₁ a ψ g₀ g₁ z - solution x₀ x₁ a ψ g₀ g₁ y =
      fluxConst x₀ x₁ a ψ (g₁ - g₀) * (∫ s in Ioo y z, (a s)⁻¹) -
        ∫ s in Ioo y z, (a s)⁻¹ * ψ s := by
  set k := fluxConst x₀ x₁ a ψ (g₁ - g₀)
  have hsub : Ioo y z ⊆ Ioo x₀ x₁ := Ioo_subset_Ioo hy hz
  have h1 : IntegrableOn (fun s => (a s)⁻¹ * k) (Ioo x₀ x₁) :=
    (integrable_inv hlam ha hla).mul_const k
  have h2 : IntegrableOn (fun s => (a s)⁻¹ * ψ s) (Ioo x₀ x₁) := integrable_inv_mul hlam ha hla hψ
  have hi := integrableOn_inv_mul_sub hlam ha hla hψ k
  have hx₀ : x₀ ∈ Icc x₀ x₁ := ⟨le_rfl, hy.trans (hyz.trans hz)⟩
  rw [solution, solution, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left
      (IntegrableOn.intervalIntegrable_of_mem_Icc hi hx₀ ⟨hy.trans hyz, hz⟩)
      (IntegrableOn.intervalIntegrable_of_mem_Icc hi hx₀ ⟨hy, hyz.trans hz⟩),
    intervalIntegral.integral_of_le hyz, integral_Ioc_eq_integral_Ioo]
  simp_rw [mul_sub]
  rw [integral_sub (h1.mono_set hsub) (h2.mono_set hsub), integral_mul_const, mul_comm]

/-- `|∫_S a⁻¹ ψ| ≤ (∫_S |ψ|) / λ` for `S ⊆ (x₀, x₁)`. -/
private theorem abs_setIntegral_inv_mul_le (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    {S : Set ℝ} (hS : S ⊆ Ioo x₀ x₁) :
    |∫ s in S, (a s)⁻¹ * ψ s| ≤ (∫ s in S, |ψ s|) / lam := by
  refine abs_integral_le_integral_abs.trans ?_
  rw [div_eq_inv_mul, ← integral_const_mul]
  refine integral_mono_ae (IntegrableOn.mono_set (integrable_inv_mul hlam ha hla hψ) hS).abs
    ((hψ.mono_set hS).abs.const_mul _)
    ((ae_restrict_of_ae_restrict_of_subset hS (ae_norm_inv_le hlam hla)).mono fun s hs => ?_)
  dsimp only
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using hs) (abs_nonneg _)

/-- `0 ≤ ∫_{y}^{z} a⁻¹ ≤ (z - y) / λ` for `[y, z] ⊆ [x₀, x₁]`. -/
private theorem setIntegral_inv_le (hlam : 0 < lam)
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) {y z : ℝ} (hy : x₀ ≤ y)
    (hyz : y ≤ z) (hz : z ≤ x₁) :
    0 ≤ ∫ s in Ioo y z, (a s)⁻¹ ∧ ∫ s in Ioo y z, (a s)⁻¹ ≤ (z - y) / lam := by
  have hla' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hy hz) hla
  have : IsFiniteMeasure (volume.restrict (Ioo y z)) := Real.isFiniteMeasure_restrict_Ioo y z
  refine ⟨integral_nonneg_of_ae (hla'.mono fun s hs => (inv_pos.2 (hlam.trans_le hs)).le), ?_⟩
  by_cases hint : Integrable (fun s => (a s)⁻¹) (volume.restrict (Ioo y z))
  · calc ∫ s in Ioo y z, (a s)⁻¹ ≤ ∫ _ in Ioo y z, lam⁻¹ :=
          integral_mono_ae hint (integrable_const _)
            (hla'.mono fun s hs => inv_anti₀ hlam hs)
      _ = (z - y) / lam := by
          rw [setIntegral_const, Real.volume_real_Ioo_of_le hyz, smul_eq_mul, div_eq_mul_inv]
  · rw [integral_undef hint]
    exact div_nonneg (sub_nonneg.2 hyz) hlam.le

/-- `|k| ≤ (|d| + ‖ψ‖₁ / λ) / ∫ a⁻¹`. -/
private theorem abs_fluxConst_le (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    (d : ℝ) :
    |fluxConst x₀ x₁ a ψ d| ≤
      (|d| + (∫ t in Ioo x₀ x₁, |ψ t|) / lam) / ∫ t in Ioo x₀ x₁, (a t)⁻¹ := by
  have hJ : 0 ≤ ∫ t in Ioo x₀ x₁, (a t)⁻¹ :=
    integral_nonneg_of_ae (hla.mono fun t ht => (inv_pos.2 (hlam.trans_le ht)).le)
  rw [fluxConst, abs_div, abs_of_nonneg hJ]
  gcongr
  exact (abs_add_le _ _).trans (add_le_add le_rfl
    (abs_setIntegral_inv_mul_le hlam ha hla hψ subset_rfl))

/-- The modulus of continuity of the explicit solution. -/
private theorem abs_solution_sub_solution_le (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    (g₀ g₁ : ℝ) {y z : ℝ} (hy : y ∈ Icc x₀ x₁) (hz : z ∈ Icc x₀ x₁) :
    |solution x₀ x₁ a ψ g₀ g₁ z - solution x₀ x₁ a ψ g₀ g₁ y| ≤
      (|fluxConst x₀ x₁ a ψ (g₁ - g₀)| * |z - y| + |(∫ s in y..z, |ψ s|)|) / lam := by
  wlog hyz : y ≤ z generalizing y z
  · rw [abs_sub_comm, abs_sub_comm z, intervalIntegral.integral_symm, abs_neg]
    exact this hz hy (le_of_not_ge hyz)
  set k := fluxConst x₀ x₁ a ψ (g₁ - g₀)
  have hJ := setIntegral_inv_le hlam hla hy.1 hyz hz.2
  rw [solution_sub_solution hlam ha hla hψ g₀ g₁ hy.1 hyz hz.2, abs_of_nonneg (sub_nonneg.2 hyz),
    intervalIntegral.integral_of_le hyz, integral_Ioc_eq_integral_Ioo,
    abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _), add_div]
  refine (abs_sub _ _).trans (add_le_add ?_
    (abs_setIntegral_inv_mul_le hlam ha hla hψ (Ioo_subset_Ioo hy.1 hz.2)))
  rw [abs_mul, abs_of_nonneg hJ.1, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hJ.2 (abs_nonneg k)

/-- The explicit solution stays within `|g₁ - g₀| + 2 ‖ψ‖₁ / λ` of `g₀`, whatever `a`. -/
private theorem abs_solution_sub_le (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    (g₀ g₁ : ℝ) {t : ℝ} (ht : t ∈ Icc x₀ x₁) :
    |solution x₀ x₁ a ψ g₀ g₁ t - g₀| ≤ |g₁ - g₀| + 2 * (∫ s in Ioo x₀ x₁, |ψ s|) / lam := by
  have hJ := integral_inv_pos hx hlam ha hla
  have hJt := setIntegral_inv_le hlam hla le_rfl ht.1 ht.2
  -- `∫_{x₀}^t a⁻¹ ≤ ∫_{x₀}^{x₁} a⁻¹`, so `k ∫_{x₀}^t a⁻¹` is a fraction of `k ∫ a⁻¹`.
  have hJJ : ∫ s in Ioo x₀ t, (a s)⁻¹ ≤ ∫ s in Ioo x₀ x₁, (a s)⁻¹ :=
    setIntegral_mono_set (integrable_inv hlam ha hla)
      (hla.mono fun s hs => (inv_pos.2 (hlam.trans_le hs)).le)
      (Ioo_subset_Ioo_right ht.2).eventuallyLE
  have hN : (∫ s in Ioo x₀ t, |ψ s|) ≤ ∫ s in Ioo x₀ x₁, |ψ s| :=
    setIntegral_mono_set hψ.abs (Eventually.of_forall fun _ => abs_nonneg _)
      (Ioo_subset_Ioo_right ht.2).eventuallyLE
  have hk : |fluxConst x₀ x₁ a ψ (g₁ - g₀) * ∫ s in Ioo x₀ t, (a s)⁻¹| ≤
      |g₁ - g₀| + (∫ s in Ioo x₀ x₁, |ψ s|) / lam := by
    rw [fluxConst, abs_mul, abs_div, abs_of_pos hJ, abs_of_nonneg hJt.1, div_mul_eq_mul_div,
      div_le_iff₀ hJ]
    refine mul_le_mul ((abs_add_le _ _).trans (add_le_add le_rfl
      (abs_setIntegral_inv_mul_le hlam ha hla hψ subset_rfl))) hJJ hJt.1 (by positivity)
  have h := solution_sub_solution hlam ha hla hψ g₀ g₁ le_rfl ht.1 ht.2
  rw [solution_left] at h
  rw [h]
  refine (abs_sub _ _).trans ?_
  have := abs_setIntegral_inv_mul_le hlam ha hla hψ (Ioo_subset_Ioo_right ht.2)
  calc _ ≤ |g₁ - g₀| + (∫ s in Ioo x₀ x₁, |ψ s|) / lam + (∫ s in Ioo x₀ t, |ψ s|) / lam :=
        add_le_add hk this
    _ ≤ _ := by
        rw [add_assoc, mul_div_assoc, two_mul]
        gcongr

/-- The explicit solution takes the boundary value `g₁` at `x₁`. -/
private theorem solution_right (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    (g₀ g₁ : ℝ) : solution x₀ x₁ a ψ g₀ g₁ x₁ = g₁ := by
  have hJ := integral_inv_pos hx hlam ha hla
  have h := solution_sub_solution hlam ha hla hψ g₀ g₁ le_rfl hx.le le_rfl
  rw [solution_left, fluxConst, div_mul_cancel₀ _ hJ.ne'] at h
  linarith

/-! ### Weak solutions from the explicit formula -/

/-- If `Φ` is the primitive of `f` from `x₀`, then `∫ (k - Φ) φ' = ∫ f φ` for every test function
`φ`. -/
private theorem setIntegral_sub_primitive_mul_deriv (hf : IntegrableOn f (Ioo x₀ x₁)) (k : ℝ)
    (φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ)) :
    ∫ t in Ioo x₀ x₁, (k - ∫ s in x₀..t, f s) * deriv φ t = ∫ t in Ioo x₀ x₁, f t * φ t := by
  have hW : TauCeti.HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩
      (fun t => k - ∫ s in x₀..t, f s) (0 - f) 1 :=
    (TauCeti.hasWeakLineDerivOn_const k).sub (TauCeti.hasWeakLineDerivOn_intervalIntegral_left hf)
  have hline : ∀ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 = deriv (φ : ℝ → ℝ) t := fun t =>
    (φ.contDiff.differentiable (by simp) t).lineDeriv_eq_fderiv
  have h := hW.integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [← TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    ← TauCeti.setIntegral_smul_eq_integral_smul] at h
  simp only [Opens.coe_mk, hline, smul_eq_mul, Pi.sub_apply, Pi.zero_apply, zero_sub, mul_neg,
    MeasureTheory.integral_neg, neg_neg] at h
  simp only [mul_comm _ (deriv _ _), mul_comm (f _)]
  exact h

/-- The explicit formula, with `ψ = Φ + F`, is the continuous representative of a weak solution
of `-(a u')' = f + F'` with endpoint values `(g₀, g₁)`. Only the lower bound `λ ≤ a` is used. -/
private theorem exists_intervalRepresentativeL_eq_solution (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hf : IntegrableOn f (Ioo x₀ x₁))
    (hF : MemLp F p (volume.restrict (Ioo x₀ x₁))) (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      (∀ t : Icc x₀ x₁, W1p.intervalRepresentativeL hx u t =
        solution x₀ x₁ a (fun t => (∫ s in x₀..t, f s) + F t) g₀ g₁ t) ∧
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  set Φ : ℝ → ℝ := fun t => ∫ s in x₀..t, f s
  set ψ : ℝ → ℝ := fun t => Φ t + F t
  set k := fluxConst x₀ x₁ a ψ (g₁ - g₀)
  -- `Φ` is continuous on `[x₀, x₁]` and bounded by `‖f‖₁`, so `ψ ∈ Lᵖ`.
  have hΦc : ContinuousOn Φ (Icc x₀ x₁) :=
    TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)
  have hΦ : MemLp Φ p (volume.restrict (Ioo x₀ x₁)) :=
    hΦc.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self p
  have hψp : MemLp ψ p (volume.restrict (Ioo x₀ x₁)) := hΦ.add hF
  have hψ : IntegrableOn ψ (Ioo x₀ x₁) := hψp.integrable Fact.out
  -- The derivative `a⁻¹ (k - ψ)` of the formula lies in `Lᵖ`.
  have hg : MemLp (fun s => (a s)⁻¹ * (k - ψ s)) p (volume.restrict (Ioo x₀ x₁)) := by
    refine ((memLp_const k).sub hψp |>.const_mul lam⁻¹).of_le
      (ha.aemeasurable.inv.aestronglyMeasurable.mul
        (aestronglyMeasurable_const.sub hψp.aestronglyMeasurable))
      ((ae_norm_inv_le hlam hla).mono fun s hs => ?_)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_pos.2 hlam).le, Pi.sub_apply]
    exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
  obtain ⟨u, hu, hgu⟩ :=
    W1p.exists_intervalRepresentativeL_eq_add_intervalIntegral (p := p) hx g₀ hg
  refine ⟨u, hu, ?_, fun φ => ?_⟩
  · rw [W1p.intervalTraceL_apply, hu, hu]
    exact Prod.ext (solution_left a ψ g₀ g₁) (solution_right hx hlam ha hla hψ g₀ g₁)
  -- `a u' = k - Φ - F` almost everywhere.
  have hflux : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      a t * W1p.gradient u t * deriv φ t = (k - Φ t) * deriv φ t - F t * deriv φ t := by
    filter_upwards [hgu, hla] with t ht hat
    rw [ht, ← mul_assoc, mul_inv_cancel₀ (hlam.trans_le hat).ne']
    ring
  have hφ' : ∃ C, ∀ t, ‖deriv (φ : ℝ → ℝ) t‖ ≤ C :=
    ((φ.contDiff.continuous_deriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
      φ.hasCompactSupport.deriv.norm).imp fun _ h t => h ⟨t, rfl⟩
  obtain ⟨C, hC⟩ := hφ'
  have hdφ : AEStronglyMeasurable (deriv (φ : ℝ → ℝ)) (volume.restrict (Ioo x₀ x₁)) :=
    (φ.contDiff.continuous_deriv (by simp)).aestronglyMeasurable
  have hΦi : IntegrableOn (fun t => k - Φ t) (Ioo x₀ x₁) :=
    (integrable_const k).sub (hΦ.integrable Fact.out)
  rw [integral_congr_ae hflux, integral_sub (hΦi.mul_bdd hdφ (Eventually.of_forall hC))
    ((hF.integrable Fact.out).mul_bdd hdφ (Eventually.of_forall hC)),
    setIntegral_sub_primitive_mul_deriv hf k φ]

/-! ### The linear problem -/

/-- **The Dirichlet problem on an interval.** Let `x₀ < x₁`, `0 < λ`, and let `a` be measurable
on `(x₀, x₁)` with `λ ≤ a ≤ M` almost everywhere. For every `f ∈ L¹(x₀, x₁)`, `F ∈ Lᵖ(x₀, x₁)` and
boundary values `g₀`, `g₁` there is exactly one `u ∈ W^{1,p}(x₀, x₁)` with endpoint trace
`(g₀, g₁)` solving `-(a u')' = f + F'` weakly:

`∫ a u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ`.

The coefficient need not be continuous; the upper bound `M` is used only for uniqueness. -/
theorem existsUnique_intervalTraceL_eq_forall_integral_eq (hx : x₀ < x₁) {M : ℝ}
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃! u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p, W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  obtain ⟨u, -, hu⟩ := exists_intervalRepresentativeL_eq_solution hx hlam ha
    (haM.mono fun _ ht => ht.1) hf hF g₀ g₁
  refine ⟨u, hu, fun v hv => ?_⟩
  -- The difference `d = v - u` solves the homogeneous problem with zero boundary values.
  set d := v - u
  have htr : W1p.intervalTraceL hx d = 0 := by
    rw [map_sub, hv.1, hu.1, sub_self]
  have hint : ∀ (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p) (φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ)),
      IntegrableOn (fun t => a t * W1p.gradient w t * deriv φ t) (Ioo x₀ x₁) := fun w φ => by
    obtain ⟨C, hC⟩ : ∃ C, ∀ t, ‖deriv (φ : ℝ → ℝ) t‖ ≤ C :=
      ((φ.contDiff.continuous_deriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
        φ.hasCompactSupport.deriv.norm).imp fun _ h t => h ⟨t, rfl⟩
    exact (((Lp.memLp (W1p.gradient w)).integrable Fact.out).bdd_mul ha
      (haM.mono fun t ht => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [ht.1, ht.2], ht.2⟩)).mul_bdd
      (φ.contDiff.continuous_deriv (by simp)).aestronglyMeasurable (Eventually.of_forall hC)
  have hd : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient d t * deriv φ t =
        (∫ t in Ioo x₀ x₁, (0 : ℝ → ℝ) t * φ t) -
          ∫ t in Ioo x₀ x₁, (0 : ℝ → ℝ) t * deriv φ t := fun φ => by
    have hsub : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), a t * W1p.gradient d t * deriv φ t =
        a t * W1p.gradient v t * deriv φ t - a t * W1p.gradient u t * deriv φ t := by
      filter_upwards [Lp.coeFn_sub (W1p.gradient v) (W1p.gradient u)] with t ht
      rw [W1p.gradient_sub, ht, Pi.sub_apply]
      ring
    rw [integral_congr_ae hsub, integral_sub (hint v φ) (hint u φ), hv.2, hu.2]
    simp
  -- The global Hölder estimate bounds `d` by its boundary values and data, all of which vanish.
  obtain ⟨C, -, hC⟩ := exists_norm_intervalRepresentativeL_le_and_holderWith (p := p) hx (M := M)
    hlam (s := 1) le_rfl
  have hnorm := (hC ha haM integrableOn_zero (MemLp.zero : MemLp (0 : ℝ → ℝ) 1 _) hd).1
  rw [htr] at hnorm
  simp only [Prod.fst_zero, Prod.snd_zero, abs_zero, integral_zero, eLpNorm_zero,
    ENNReal.toReal_zero, add_zero, mul_zero, norm_le_zero_iff] at hnorm
  have h0 : W1p.intervalRepresentativeL hx d =
      W1p.intervalRepresentativeL hx (0 : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p) := by
    rw [hnorm, map_zero]
  exact sub_eq_zero.1 (W1p.intervalRepresentativeL_injective hx h0)

/-! ### The quasilinear problem -/

/-- Two explicit solutions differ by at most the `L¹` distance of their derivatives. -/
private theorem abs_solution_sub_le_integral (hlam : 0 < lam) {b : ℝ → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hlb : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ b t) (hψ : IntegrableOn ψ (Ioo x₀ x₁))
    (g₀ g₁ : ℝ) {t : ℝ} (ht : t ∈ Icc x₀ x₁) :
    |solution x₀ x₁ a ψ g₀ g₁ t - solution x₀ x₁ b ψ g₀ g₁ t| ≤
      ∫ s in Ioo x₀ x₁, |(a s)⁻¹ * (fluxConst x₀ x₁ a ψ (g₁ - g₀) - ψ s) -
        (b s)⁻¹ * (fluxConst x₀ x₁ b ψ (g₁ - g₀) - ψ s)| := by
  have hia := integrableOn_inv_mul_sub hlam ha hla hψ (fluxConst x₀ x₁ a ψ (g₁ - g₀))
  have hib := integrableOn_inv_mul_sub hlam hb hlb hψ (fluxConst x₀ x₁ b ψ (g₁ - g₀))
  have hx₀ : x₀ ∈ Icc x₀ x₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  rw [solution, solution, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub (IntegrableOn.intervalIntegrable_of_mem_Icc hia hx₀ ht)
      (IntegrableOn.intervalIntegrable_of_mem_Icc hib hx₀ ht),
    intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
  exact abs_integral_le_integral_abs.trans (setIntegral_mono_set (hia.sub hib).abs
    (Eventually.of_forall fun _ => abs_nonneg _) (Ioo_subset_Ioo_right ht.2).eventuallyLE)

/-- **Continuous dependence on the coefficient.** If `aₙ → b` almost everywhere, with `λ ≤ aₙ`
and `λ ≤ b`, then the derivatives of the explicit solutions converge in `L¹`. -/
private theorem tendsto_integral_abs_inv_mul_sub (hx : x₀ < x₁) (hlam : 0 < lam)
    {a : ℕ → ℝ → ℝ} {b : ℝ → ℝ} (ha : ∀ n, AEStronglyMeasurable (a n) (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a n t)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hlb : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ b t)
    (hab : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => a n t) atTop (𝓝 (b t)))
    (hψ : IntegrableOn ψ (Ioo x₀ x₁)) (d : ℝ) :
    Tendsto (fun n => ∫ s in Ioo x₀ x₁, |(a n s)⁻¹ * (fluxConst x₀ x₁ (a n) ψ d - ψ s) -
      (b s)⁻¹ * (fluxConst x₀ x₁ b ψ d - ψ s)|) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hinv : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      Tendsto (fun n => (a n t)⁻¹) atTop (𝓝 (b t)⁻¹) := by
    filter_upwards [hab, hlb] with t ht hbt
    exact ht.inv₀ (hlam.trans_le hbt).ne'
  -- The flux constants converge, by dominated convergence in `∫ a⁻¹` and `∫ a⁻¹ ψ`.
  have hJ : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (a n t)⁻¹) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (b t)⁻¹)) :=
    tendsto_integral_of_dominated_convergence (fun _ => lam⁻¹)
      (fun n => (ha n).aemeasurable.inv.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_norm_inv_le hlam (hla n)) hinv
  have hG : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (a n t)⁻¹ * ψ t) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (b t)⁻¹ * ψ t)) :=
    tendsto_integral_of_dominated_convergence (fun t => lam⁻¹ * ‖ψ t‖)
      (fun n => (ha n).aemeasurable.inv.aestronglyMeasurable.mul hψ.aestronglyMeasurable)
      (hψ.norm.const_mul _)
      (fun n => (ae_norm_inv_le hlam (hla n)).mono fun t ht => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ht (norm_nonneg _))
      (hinv.mono fun t ht => ht.mul_const _)
  have hk : Tendsto (fun n => fluxConst x₀ x₁ (a n) ψ d) atTop (𝓝 (fluxConst x₀ x₁ b ψ d)) :=
    (tendsto_const_nhds.add hG).div hJ (integral_inv_pos hx hlam hb hlb).ne'
  set kb := fluxConst x₀ x₁ b ψ d
  -- Dominated convergence for the derivatives, eventually bounded since `|kₙ| ≤ |k| + 1`.
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      ‖|(a n t)⁻¹ * (fluxConst x₀ x₁ (a n) ψ d - ψ t) - (b t)⁻¹ * (kb - ψ t)|‖ ≤
        lam⁻¹ * (|kb| + 1 + |ψ t|) + lam⁻¹ * (|kb| + |ψ t|) := by
    filter_upwards [Metric.tendsto_nhds.1 hk 1 one_pos] with n hn
    filter_upwards [ae_norm_inv_le hlam (hla n), ae_norm_inv_le hlam hlb] with t h1 h2
    rw [Real.dist_eq] at hn
    rw [Real.norm_eq_abs] at h1 h2
    rw [Real.norm_eq_abs, abs_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · refine mul_le_mul h1 ((abs_sub _ _).trans ?_) (abs_nonneg _) (inv_nonneg.2 hlam.le)
      linarith [abs_sub_abs_le_abs_sub (fluxConst x₀ x₁ (a n) ψ d) kb]
    · exact mul_le_mul h2 (abs_sub _ _) (abs_nonneg _) (inv_nonneg.2 hlam.le)
  have hlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto
      (fun n => |(a n t)⁻¹ * (fluxConst x₀ x₁ (a n) ψ d - ψ t) - (b t)⁻¹ * (kb - ψ t)|) atTop
        (𝓝 0) := by
    filter_upwards [hinv] with t ht
    have h := ((ht.mul (hk.sub_const (ψ t))).sub_const ((b t)⁻¹ * (kb - ψ t))).abs
    rwa [sub_self, abs_zero] at h
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t => |(a n t)⁻¹ * (fluxConst x₀ x₁ (a n) ψ d - ψ t) - (b t)⁻¹ * (kb - ψ t)|)
      (volume.restrict (Ioo x₀ x₁)) := fun n =>
    continuous_abs.comp_aestronglyMeasurable
      (((ha n).aemeasurable.inv.mul (aemeasurable_const.sub hψ.aemeasurable)).sub
        (hb.aemeasurable.inv.mul (aemeasurable_const.sub hψ.aemeasurable))).aestronglyMeasurable
  have hint : Integrable (fun t => lam⁻¹ * (|kb| + 1 + |ψ t|) + lam⁻¹ * (|kb| + |ψ t|))
      (volume.restrict (Ioo x₀ x₁)) :=
    (((integrable_const _).add hψ.abs).const_mul _).add
      (((integrable_const _).add hψ.abs).const_mul _)
  have h := tendsto_integral_filter_of_dominated_convergence (f := fun _ => (0 : ℝ)) _
    (Eventually.of_forall hmeas) hbound hint hlim
  rwa [integral_zero] at h

/-- On a ball `|w| ≤ R`, the coefficient `A(·, w)` is at most a measurable function `m`, the
maximum of `A t` over `[-R, R]`, so `∫ 1 / A(·, w)` is bounded below by `∫ 1 / m > 0` uniformly
in `w`. -/
private theorem exists_pos_le_integral_inv (hx : x₀ < x₁) {A : ℝ → ℝ → ℝ}
    (hAm : ∀ v, Measurable fun t => A t v) (hAc : ∀ t, Continuous (A t)) (hlam : 0 < lam)
    (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ v, lam ≤ A t v) (R : ℝ) :
    ∃ J₀ > 0, ∀ w : ℝ → ℝ, Measurable w → (∀ t, |w t| ≤ R) →
      J₀ ≤ ∫ t in Ioo x₀ x₁, (A t (w t))⁻¹ := by
  have hR : -|R| ≤ |R| := (neg_nonpos.2 (abs_nonneg R)).trans (abs_nonneg R)
  set c : ℝ → ℝ := fun v => projIcc (-|R|) |R| hR v
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hbdd : ∀ t, BddAbove (range fun q : ℚ => A t (c q)) := fun t =>
    (isCompact_Icc.image (hAc t)).isBounded.bddAbove.mono <| by
      rintro _ ⟨q, rfl⟩
      exact ⟨c q, (projIcc (-|R|) |R| hR q).2, rfl⟩
  -- `m t = sup_{q ∈ ℚ} A t (c q)` is the maximum of `A t` over `[-|R|, |R|]`.
  set m : ℝ → ℝ := fun t => ⨆ q : ℚ, A t (c q)
  have hmm : Measurable m := Measurable.iSup fun q => hAm _
  have hle : ∀ t v, |v| ≤ R → A t v ≤ m t := fun t v hv => by
    have hcv : c v = v := by
      simp only [c, projIcc_of_mem hR (abs_le.1 (hv.trans (le_abs_self R)))]
    rw [← hcv]
    exact Rat.denseRange_cast.induction_on (p := fun v => A t (c v) ≤ m t) v
      (isClosed_le ((hAc t).comp hc) continuous_const) fun q => le_ciSup (hbdd t) q
  have hlm : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ m t :=
    hA.mono fun t ht => (ht _).trans (le_ciSup (hbdd t) 0)
  refine ⟨∫ t in Ioo x₀ x₁, (m t)⁻¹, integral_inv_pos hx hlam hmm.aestronglyMeasurable hlm,
    fun w hw hwR => ?_⟩
  have hAw : Measurable fun t => A t (w t) :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun v t => A t v) hAc hAm).comp
      (hw.prodMk measurable_id)
  have hlw : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ A t (w t) := hA.mono fun t ht => ht _
  exact integral_mono_ae (integrable_inv hlam hmm.aestronglyMeasurable hlm)
    (integrable_inv hlam hAw.aestronglyMeasurable hlw)
    (hlw.mono fun t ht => inv_anti₀ (hlam.trans_le ht) (hle t (w t) (hwR t)))

/-- **The quasilinear Dirichlet problem on an interval.** Let `x₀ < x₁` and `0 < λ`, and let
`A : ℝ → ℝ → ℝ` be measurable in its first argument and continuous in its second, with
`λ ≤ A t v` for almost every `t ∈ (x₀, x₁)` and every `v`. For every `f ∈ L¹(x₀, x₁)`,
`F ∈ Lᵖ(x₀, x₁)` and boundary values `g₀`, `g₁` there is `u ∈ W^{1,p}(x₀, x₁)` with endpoint
trace `(g₀, g₁)` solving `-(A(t, u) u')' = f + F'` weakly:

`∫ A(t, u) u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ`.

No upper bound on `A` and no Lipschitz dependence on `v` are assumed. Uniqueness is not
claimed. -/
theorem exists_intervalTraceL_eq_forall_quasilinear_integral_eq (hx : x₀ < x₁)
    {A : ℝ → ℝ → ℝ} (hAm : ∀ v, Measurable fun t => A t v) (hAc : ∀ t, Continuous (A t))
    (hlam : 0 < lam) (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ v, lam ≤ A t v)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p, W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.value u t) * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  set ψ : ℝ → ℝ := fun t => (∫ s in x₀..t, f s) + F t
  have hψ : IntegrableOn ψ (Ioo x₀ x₁) :=
    ((TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)).integrableOn_Icc.mono_set Ioo_subset_Icc_self).add
      (hF.integrable Fact.out)
  -- The coefficient `A(·, w)` frozen at `w ∈ C([x₀, x₁])`, and the solution map `T`.
  set coef : C(Icc x₀ x₁, ℝ) → ℝ → ℝ := fun w t => A t (w (projIcc x₀ x₁ hx.le t))
  have hwm : ∀ w : C(Icc x₀ x₁, ℝ), Measurable fun t => w (projIcc x₀ x₁ hx.le t) := fun w =>
    (w.continuous.comp continuous_projIcc).measurable
  have hcm : ∀ w, AEStronglyMeasurable (coef w) (volume.restrict (Ioo x₀ x₁)) := fun w =>
    ((measurable_uncurry_of_continuous_of_measurable (u := fun v t => A t v) hAc hAm).comp
      ((hwm w).prodMk measurable_id)).aestronglyMeasurable
  have hcl : ∀ w, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ coef w t := fun w =>
    hA.mono fun t ht => ht _
  let T : C(Icc x₀ x₁, ℝ) → C(Icc x₀ x₁, ℝ) := fun w =>
    ⟨fun t => solution x₀ x₁ (coef w) ψ g₀ g₁ t,
      (continuousOn_solution hx hlam (hcm w) (hcl w) hψ g₀ g₁).domRestrict⟩
  have hT : ∀ w (t : Icc x₀ x₁), T w t = solution x₀ x₁ (coef w) ψ g₀ g₁ t := fun _ _ => rfl
  set N := ∫ t in Ioo x₀ x₁, |ψ t|
  set R := |g₀| + (|g₁ - g₀| + 2 * N / lam)
  have hN : 0 ≤ N := integral_nonneg fun _ => abs_nonneg _
  have hR : 0 ≤ R := by positivity
  -- `T` maps everything into the closed ball of radius `R`.
  have hTR : ∀ w, ‖T w‖ ≤ R := fun w => (ContinuousMap.norm_le _ hR).2 fun t => by
    rw [hT, Real.norm_eq_abs]
    calc |solution x₀ x₁ (coef w) ψ g₀ g₁ t|
        = |g₀ + (solution x₀ x₁ (coef w) ψ g₀ g₁ t - g₀)| := by rw [add_sub_cancel]
      _ ≤ |g₀| + |solution x₀ x₁ (coef w) ψ g₀ g₁ t - g₀| := abs_add_le _ _
      _ ≤ R := add_le_add le_rfl (abs_solution_sub_le hx hlam (hcm w) (hcl w) hψ g₀ g₁ t.2)
  -- On that ball the flux constants are uniformly bounded.
  obtain ⟨J₀, hJ₀, hJ₀le⟩ := exists_pos_le_integral_inv hx hAm hAc hlam hA R
  set K := (|g₁ - g₀| + N / lam) / J₀
  have hk : ∀ w : C(Icc x₀ x₁, ℝ), ‖w‖ ≤ R →
      |fluxConst x₀ x₁ (coef w) ψ (g₁ - g₀)| ≤ K := fun w hw =>
    (abs_fluxConst_le hlam (hcm w) (hcl w) hψ _).trans
      (div_le_div_of_nonneg_left (by positivity) hJ₀ (hJ₀le _ (hwm w) fun t => by
        rw [← Real.norm_eq_abs]
        exact (w.norm_coe_le_norm _).trans hw))
  -- `T` is continuous, by dominated convergence.
  have hTc : Continuous T := by
    refine continuous_iff_seqContinuous.2 fun w w' hw => ?_
    have hpt : ∀ t, Tendsto (fun n => coef (w n) t) atTop (𝓝 (coef w' t)) := fun t =>
      ((hAc t).tendsto _).comp (((continuous_eval_const _).tendsto _).comp hw)
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (ContinuousMap.norm_le _ (integral_nonneg fun _ => abs_nonneg _)).2 fun t => ?_)
      (tendsto_integral_abs_inv_mul_sub hx hlam (fun n => hcm (w n)) (fun n => hcl (w n))
        (hcm w') (hcl w') (Eventually.of_forall hpt) hψ (g₁ - g₀)))
    rw [ContinuousMap.sub_apply, Function.comp_apply, hT, hT, Real.norm_eq_abs]
    exact abs_solution_sub_le_integral hlam (hcm _) (hcl _) (hcm _) (hcl _) hψ g₀ g₁ t.2
  -- The image of the ball is equicontinuous and bounded, hence relatively compact.
  have hK : IsCompact (closure (T '' closedBall 0 R)) := by
    rw [image_eq_range]
    refine ArzelaAscoli.isCompact_closure_range_of_equicontinuous (fun y₀ => ?_)
      fun t => ⟨closedBall 0 R, isCompact_closedBall _ _, fun w =>
        mem_closedBall_zero_iff.2 ((ContinuousMap.norm_coe_le_norm _ _).trans (hTR _))⟩
    have hprim : Continuous fun y : Icc x₀ x₁ => ∫ s in (y₀ : ℝ)..y, |ψ s| := by
      have hc : ContinuousOn (fun z => ∫ s in (y₀ : ℝ)..z, |ψ s|) (Icc x₀ x₁) :=
        (intervalIntegral.continuousOn_primitive_interval'
          (IntegrableOn.intervalIntegrable_of_mem_Icc hψ.abs (left_mem_Icc.2 hx.le)
            (right_mem_Icc.2 hx.le)) (Icc_subset_uIcc y₀.2)).mono Icc_subset_uIcc
      exact hc.comp_continuous continuous_subtype_val fun y => y.2
    have hb : Continuous fun y : Icc x₀ x₁ =>
        (K * |(y : ℝ) - y₀| + |(∫ s in (y₀ : ℝ)..y, |ψ s|)|) / lam :=
      ((continuous_const.mul (continuous_subtype_val.sub continuous_const).abs).add
        hprim.abs).div_const _
    refine Metric.equicontinuousAt_of_continuity_modulus _ (by simpa using hb.tendsto y₀) _
      (Eventually.of_forall fun y w => ?_)
    rw [Real.dist_eq, hT, hT, abs_sub_comm]
    refine (abs_solution_sub_solution_le hlam (hcm _) (hcl _) hψ g₀ g₁ y₀.2 y.2).trans ?_
    gcongr
    exact hk _ (mem_closedBall_zero_iff.1 w.2)
  obtain ⟨w, -, hw⟩ := schauderFixedPoint_closedConvex_continuousOn isClosed_closedBall
    (convex_closedBall _ _) (nonempty_closedBall.2 hR) hTc.continuousOn
    (fun w _ => mem_closedBall_zero_iff.2 (hTR w)) hK
  -- The fixed point `w = T w` is the representative of the required solution.
  obtain ⟨u, hu, htr, heq⟩ :=
    exists_intervalRepresentativeL_eq_solution hx hlam (hcm w) (hcl w) hf hF g₀ g₁
  have hrep : W1p.intervalRepresentativeL hx u = w := by
    ext t
    rw [hu, ← hT, hw.eq]
  refine ⟨u, htr, fun φ => ?_⟩
  rw [← heq φ]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_ae_eq_intervalRepresentativeL hx u] with t ht
  rw [ht, hrep]

end TauCeti.PDE

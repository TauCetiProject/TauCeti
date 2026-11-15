/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The linear Dirichlet problem on an interval

On a bounded interval `(x₀, x₁)` consider the divergence-form equation

`-(a u' + F)' = f`, `u(x₀) = g₀`, `u(x₁) = g₁`,

with a measurable coefficient `a ≥ λ > 0` and data `f ∈ L¹` and `F ∈ Lᵖ`, `1 ≤ p ≤ ∞`. A solution
is `u ∈ W^{1,p}(x₀, x₁)` whose endpoint trace is `(g₀, g₁)` and which satisfies

`∫ a u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

The problem is solved explicitly: the flux `a u' + F` equals `k - ∫_{x₀}^x f`, so `u' = (k - G) / a`
with `G = ∫_{x₀}^x f + F`, and the constant `k` is fixed by `∫ (k - G) / a = g₁ - g₀`. For a bounded
coefficient `λ ≤ a ≤ M` this is the only solution: the first integral of any solution has the same
constant `k`, so its continuous representative is the explicit one.

The solution depends continuously on the coefficient: if `aₙ → a` almost everywhere with a uniform
lower bound `λ ≤ aₙ`, the derivatives of the solutions converge in `L¹`. Under uniform bounds
`λ ≤ a ≤ M` the solutions also form a relatively compact subset of `C([x₀, x₁])`. These are the two
properties of the frozen-coefficient solution map needed to solve quasilinear problems by a
fixed-point argument (`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`). For a fixed
coefficient the solution is affine in the data `(g₀, g₁, G)`, and for `λ ≤ a ≤ M` Lipschitz from
`ℝ² × L¹` to `C([x₀, x₁])` with a constant depending only on `λ` and `M`. The solution depends
continuously on the coefficient and the data jointly, and for uniformly bounded coefficients and
converging data a subsequence of the solutions converges uniformly; these two facts are what limits
of solutions of varying quasilinear problems need.

## Main declarations

* `TauCeti.PDE.intervalDirichletFluxConst`, `TauCeti.PDE.intervalDirichletSlope`: the flux
  constant `k` and the derivative `(k - G) / a` of the explicit solution.
* `TauCeti.PDE.intervalDirichletSolution`: the explicit solution `g₀ + ∫_{x₀}^x (k - G) / a`, as a
  continuous function on `[x₀, x₁]`.
* `TauCeti.PDE.tendsto_integral_abs_intervalDirichletSlope_sub`: continuous dependence of the
  derivative on the coefficient.
* `TauCeti.PDE.continuous_intervalDirichletSolution`,
  `TauCeti.PDE.isCompact_closure_range_intervalDirichletSolution`: the frozen-solution map
  `v ↦ TauCeti.PDE.intervalDirichletSolution` is continuous and has compact closure of range.
* `TauCeti.PDE.intervalDirichletFluxConst_sub`, `TauCeti.PDE.intervalDirichletSlope_sub`: the flux
  constant and the derivative of the solution are affine in the data.
* `TauCeti.PDE.norm_intervalDirichletSolution_le`,
  `TauCeti.PDE.norm_intervalDirichletSolution_sub_le`,
  `TauCeti.PDE.norm_intervalDirichletSolution_sub_le_of_le`: the bound of the solution, its
  dependence on the data, and its Lipschitz dependence on the data for `λ ≤ a ≤ M`.
* `TauCeti.PDE.tendsto_intervalDirichletSolution_of_tendsto_ae`,
  `TauCeti.PDE.tendsto_intervalDirichletSolution`: continuous dependence on the coefficient, and on
  the coefficient and the data jointly.
* `TauCeti.PDE.exists_strictMono_tendsto_intervalDirichletSolution`: for coefficients with uniform
  bounds and converging data, a subsequence of the solutions converges uniformly.
* `TauCeti.PDE.exists_w1p_intervalRepresentativeL_eq`: the explicit solution, with its continuous
  representative.
* `TauCeti.PDE.exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq`: the linear problem
  `-(a u' + F)' = f` with prescribed endpoint values has a solution in `W^{1,p}(x₀, x₁)`.
* `TauCeti.PDE.gradient_ae_eq_intervalDirichletSlope`,
  `TauCeti.PDE.intervalRepresentativeL_eq_intervalDirichletSolution`: for a bounded coefficient
  every solution is the explicit one.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4 (one-dimensional boundary value problems).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 11 (quasilinear equations by fixed-point theorems).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Distributions

namespace TauCeti.PDE

variable {x₀ x₁ lam M : ℝ} {G a : ℝ → ℝ}

/-- The flux constant `k` of the linear problem `-(a u' + F)' = f` on `(x₀, x₁)` with endpoint
values `g₀` and `g₁`, written in terms of `G = ∫_{x₀}^x f + F`: the flux `a u' + F` is
`k - ∫_{x₀}^x f`, and `k` is fixed by `∫ (k - G) / a = g₁ - g₀`. -/
def intervalDirichletFluxConst (x₀ x₁ g₀ g₁ : ℝ) (G a : ℝ → ℝ) : ℝ :=
  (g₁ - g₀ + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t) / ∫ t in Ioo x₀ x₁, (a t)⁻¹

/-- The defining formula of `intervalDirichletFluxConst`. -/
theorem intervalDirichletFluxConst_def (x₀ x₁ g₀ g₁ : ℝ) (G a : ℝ → ℝ) :
    intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a =
      (g₁ - g₀ + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t) / ∫ t in Ioo x₀ x₁, (a t)⁻¹ :=
  (rfl)

/-- The derivative `(k - G) / a` of the solution of the linear problem `-(a u' + F)' = f` on
`(x₀, x₁)` with endpoint values `g₀` and `g₁`, where `G = ∫_{x₀}^x f + F` and `k` is
`intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a`. -/
def intervalDirichletSlope (x₀ x₁ g₀ g₁ : ℝ) (G a : ℝ → ℝ) (t : ℝ) : ℝ :=
  (a t)⁻¹ * (intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a - G t)

/-- The defining formula of `intervalDirichletSlope`. -/
theorem intervalDirichletSlope_def (x₀ x₁ g₀ g₁ : ℝ) (G a : ℝ → ℝ) (t : ℝ) :
    intervalDirichletSlope x₀ x₁ g₀ g₁ G a t =
      (a t)⁻¹ * (intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a - G t) :=
  (rfl)

/-- For `λ ≤ a ≤ M` the flux constant is bounded by `M / (x₁ - x₀) (|g₁ - g₀| + λ⁻¹ ‖G‖₁)`. -/
theorem abs_intervalDirichletFluxConst_le (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    |intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a| ≤
      M / (x₁ - x₀) * (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t|) :=
  abs_add_setIntegral_inv_mul_div_le hx hlam ha haM hG (g₁ - g₀)

/-- For `λ ≤ a`, a bound `|k| ≤ K` on the flux constant gives `|(k - G) / a| ≤ λ⁻¹ (K + |G|)`. -/
theorem ae_abs_intervalDirichletSlope_le (hlam : 0 < lam) {g₀ g₁ K : ℝ}
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hK : |intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a| ≤ K) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      |intervalDirichletSlope x₀ x₁ g₀ g₁ G a t| ≤ lam⁻¹ * (K + |G t|) := by
  filter_upwards [hla.norm_inv_le_inv hlam] with t ht
  rw [intervalDirichletSlope, abs_mul, ← Real.norm_eq_abs (a t)⁻¹]
  exact mul_le_mul ht ((abs_sub _ _).trans (by gcongr)) (abs_nonneg _)
    (inv_nonneg.2 hlam.le)

/-- The derivative `(k - G) / a` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_intervalDirichletSlope {g₀ g₁ : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hG : AEStronglyMeasurable G (volume.restrict (Ioo x₀ x₁))) :
    AEStronglyMeasurable (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (volume.restrict (Ioo x₀ x₁)) :=
  ha.aemeasurable.inv.aestronglyMeasurable.mul (aestronglyMeasurable_const.sub hG)

/-- For `λ ≤ a`, the derivative `(k - G) / a` is integrable on `(x₀, x₁)`. -/
theorem integrableOn_intervalDirichletSlope (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁) :=
  (((integrable_const _).add hG.abs).const_mul lam⁻¹).mono'
    (aestronglyMeasurable_intervalDirichletSlope ha hG.aestronglyMeasurable)
    ((ae_abs_intervalDirichletSlope_le hlam hla le_rfl).mono fun _ h => by
      rwa [Real.norm_eq_abs])

/-- The explicit solution `y ↦ g₀ + ∫_{x₀}^y (k - G) / a` of the linear problem
`-(a u' + F)' = f` on `(x₀, x₁)` with endpoint values `g₀` and `g₁`, as a continuous function on
`[x₀, x₁]`. Here `hs` is the integrability of its derivative `intervalDirichletSlope`, which
holds whenever `λ ≤ a` (`integrableOn_intervalDirichletSlope`). -/
def intervalDirichletSolution (hx : x₀ ≤ x₁) (g₀ g₁ : ℝ)
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁)) :
    C(Icc x₀ x₁, ℝ) :=
  ⟨fun y => g₀ + ∫ t in x₀..(y : ℝ), intervalDirichletSlope x₀ x₁ g₀ g₁ G a t,
    (continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo
      hs (left_mem_Icc.2 hx))).domRestrict⟩

/-- The values of `intervalDirichletSolution`. -/
@[simp]
theorem intervalDirichletSolution_apply (hx : x₀ ≤ x₁) (g₀ g₁ : ℝ)
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁)) (y : Icc x₀ x₁) :
    intervalDirichletSolution hx g₀ g₁ hs y =
      g₀ + ∫ t in x₀..(y : ℝ), intervalDirichletSlope x₀ x₁ g₀ g₁ G a t :=
  (rfl)

/-- The solution of the linear problem has the prescribed increment `g₁ - g₀`. -/
theorem integral_intervalDirichletSlope (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    ∫ t in Ioo x₀ x₁, intervalDirichletSlope x₀ x₁ g₀ g₁ G a t = g₁ - g₀ := by
  have hc0 := (setIntegral_inv_pos (by simp [hx]) measure_Ioo_lt_top.ne hlam ha hla).ne'
  have hle := hla.norm_inv_le_inv hlam
  have h1 : Integrable (fun t => (a t)⁻¹) (volume.restrict (Ioo x₀ x₁)) :=
    Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _ hle
  have h2 : Integrable (fun t => (a t)⁻¹ * G t) (volume.restrict (Ioo x₀ x₁)) :=
    hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable hle
  simp only [intervalDirichletSlope, mul_sub]
  rw [integral_sub (h1.mul_const _) h2, integral_mul_const, intervalDirichletFluxConst,
    mul_div_cancel₀ _ hc0]
  ring

/-- The explicit solution takes the value `g₀` at `x₀`. -/
theorem intervalDirichletSolution_left (hx : x₀ ≤ x₁) (g₀ g₁ : ℝ)
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁)) :
    intervalDirichletSolution hx g₀ g₁ hs ⟨x₀, left_mem_Icc.2 hx⟩ = g₀ := by
  simp

/-- For `λ ≤ a`, the explicit solution takes the value `g₁` at `x₁`. -/
theorem intervalDirichletSolution_right (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁)) :
    intervalDirichletSolution hx.le g₀ g₁ hs ⟨x₁, right_mem_Icc.2 hx.le⟩ = g₁ := by
  rw [intervalDirichletSolution_apply, intervalIntegral.integral_of_le hx.le,
    integral_Ioc_eq_integral_Ioo, integral_intervalDirichletSlope hx hlam g₀ g₁ ha hla hG,
    add_sub_cancel]

/-- **Continuous dependence on the coefficient.** If `aₙ → a` almost everywhere with a uniform
lower bound `λ ≤ aₙ`, the derivatives of the solutions of the linear problems converge in `L¹`. -/
theorem tendsto_integral_abs_intervalDirichletSlope_sub (hx : x₀ < x₁) (hlam : 0 < lam)
    (g₀ g₁ : ℝ) {an : ℕ → ℝ → ℝ}
    (han : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)))
    (hanl : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => an n t) atTop (𝓝 (a t))) :
    Tendsto (fun n => ∫ t in Ioo x₀ x₁,
      |intervalDirichletSlope x₀ x₁ g₀ g₁ G (an n) t - intervalDirichletSlope x₀ x₁ g₀ g₁ G a t|)
      atTop (𝓝 0) := by
  have hinv : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      Tendsto (fun n => (an n t)⁻¹) atTop (𝓝 (a t)⁻¹) := by
    filter_upwards [hlim, hla] with t ht hat
    exact ht.inv₀ (hlam.trans_le hat).ne'
  -- The two integrals defining the flux constant converge by dominated convergence.
  have hc' : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (an n t)⁻¹) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (a t)⁻¹)) :=
    tendsto_integral_of_dominated_convergence (fun _ => lam⁻¹)
      (fun n => (han n).aemeasurable.inv.aestronglyMeasurable) (integrable_const _)
      (fun n => (hanl n).norm_inv_le_inv hlam) hinv
  have hd : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (an n t)⁻¹ * G t) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => lam⁻¹ * ‖G t‖)
      (fun n => (han n).aemeasurable.inv.aestronglyMeasurable.mul hG.1)
      (hG.norm.const_mul _) (fun n => ?_) ?_
    · filter_upwards [(hanl n).norm_inv_le_inv hlam] with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    · filter_upwards [hinv] with t ht
      exact ht.mul_const _
  have hk : Tendsto (fun n => intervalDirichletFluxConst x₀ x₁ g₀ g₁ G (an n)) atTop
      (𝓝 (intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a)) :=
    (tendsto_const_nhds.add hd).div hc'
      (setIntegral_inv_pos (by simp [hx]) measure_Ioo_lt_top.ne hlam ha hla).ne'
  -- The derivatives converge almost everywhere, under a common integrable bound: the convergent
  -- flux constants are bounded by some `K`.
  obtain ⟨K, hK⟩ := hk.abs.bddAbove_range
  set k := intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a
  have h0 := tendsto_integral_of_dominated_convergence
    (fun t => lam⁻¹ * (K + |G t|) + lam⁻¹ * (|k| + |G t|))
    (F := fun n t =>
      |intervalDirichletSlope x₀ x₁ g₀ g₁ G (an n) t - intervalDirichletSlope x₀ x₁ g₀ g₁ G a t|)
    (f := fun _ => 0)
    (fun n => ((aestronglyMeasurable_intervalDirichletSlope (han n) hG.1).sub
      (aestronglyMeasurable_intervalDirichletSlope ha hG.1)).norm)
    ((((integrable_const K).add hG.abs).const_mul lam⁻¹).add
      (((integrable_const |k|).add hG.abs).const_mul lam⁻¹)) (fun n => ?_) ?_
  · simpa using h0
  · filter_upwards [ae_abs_intervalDirichletSlope_le hlam (hanl n) (hK (mem_range_self n)),
      ae_abs_intervalDirichletSlope_le hlam hla le_rfl] with t h1 h2
    rw [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  · filter_upwards [hinv] with t ht
    have h : Tendsto (fun n => intervalDirichletSlope x₀ x₁ g₀ g₁ G (an n) t) atTop
        (𝓝 (intervalDirichletSlope x₀ x₁ g₀ g₁ G a t)) := ht.mul (hk.sub_const _)
    simpa using (h.sub_const (intervalDirichletSlope x₀ x₁ g₀ g₁ G a t)).abs

/-- **Continuous dependence on the coefficient, in `C([x₀, x₁])`.** If `aₙ → a` almost everywhere
with a uniform lower bound `λ ≤ aₙ`, the solutions of the linear problems with coefficients `aₙ`
converge uniformly on `[x₀, x₁]` to the solution with coefficient `a`. -/
theorem tendsto_intervalDirichletSolution_of_tendsto_ae (hx : x₀ < x₁) (hlam : 0 < lam)
    {g₀ g₁ : ℝ} {an : ℕ → ℝ → ℝ}
    (han : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)))
    (hanl : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t)
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => an n t) atTop (𝓝 (a t)))
    (hsn : ∀ n, IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G (an n)) (Ioo x₀ x₁))
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁)) :
    Tendsto (fun n => intervalDirichletSolution hx.le g₀ g₁ (hsn n)) atTop
      (𝓝 (intervalDirichletSolution hx.le g₀ g₁ hs)) := by
  have hx₀ := left_mem_Icc.2 hx.le
  -- The limit coefficient inherits measurability and the lower bound.
  have ha := aestronglyMeasurable_of_tendsto_ae atTop han hlim
  have hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t := eventually_ge_of_tendsto hlim hanl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_integral_abs_intervalDirichletSlope_sub hx hlam g₀ g₁ han hanl ha hla hG hlim)
  -- The difference is the primitive of the difference of the derivatives.
  refine (intervalIntegral.norm_le_of_forall_eq_add_integral (c := 0) hx₀ ((hsn n).sub hs)
    ((hsn n).sub hs).abs (ae_of_all _ fun t => (Real.norm_eq_abs _).le) fun y => ?_).trans_eq
    (by rw [norm_zero, zero_add]; rfl)
  rw [ContinuousMap.sub_apply, intervalDirichletSolution_apply, intervalDirichletSolution_apply,
    add_sub_add_left_eq_sub, zero_add, ← intervalIntegral.integral_sub
      ((hsn n).intervalIntegrable_of_mem_Icc hx₀ y.2) (hs.intervalIntegrable_of_mem_Icc hx₀ y.2)]
  rfl

/-- **Continuity of the frozen-solution map.** Let `a v`, for `v` in a sequential space `X`, be
coefficients with a uniform lower bound `λ ≤ a v`, such that `a vₙ → a v` almost everywhere whenever
`vₙ → v`. Then the solution of the linear problem with coefficient `a v` depends continuously on
`v` in `C([x₀, x₁])`, by dominated convergence. -/
theorem continuous_intervalDirichletSolution {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    (hx : x₀ < x₁) (hlam : 0 < lam) {g₀ g₁ : ℝ} {a : X → ℝ → ℝ}
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t)
    (hlim : ∀ (vn : ℕ → X) (v : X), Tendsto vn atTop (𝓝 v) →
      ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => a (vn n) t) atTop (𝓝 (a v t)))
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hs : ∀ v, IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G (a v)) (Ioo x₀ x₁)) :
    Continuous fun v => intervalDirichletSolution hx.le g₀ g₁ (hs v) :=
  continuous_iff_seqContinuous.2 fun vn v hv =>
    tendsto_intervalDirichletSolution_of_tendsto_ae hx hlam (fun n => ha (vn n))
      (fun n => hla (vn n)) hG (hlim vn v hv) (fun n => hs (vn n)) (hs v)

/-- **Compactness of the frozen-solution map.** Let `a i`, for `i ∈ ι`, be coefficients with
uniform bounds `λ ≤ a i ≤ M`. The solutions of the linear problems with coefficients `a i` form a
relatively compact subset of `C([x₀, x₁])`: their derivatives are all dominated by one integrable
function, so they are uniformly bounded and equicontinuous. -/
theorem isCompact_closure_range_intervalDirichletSolution {ι : Type*} (hx : x₀ < x₁)
    (hlam : 0 < lam) {g₀ g₁ : ℝ} {a : ι → ℝ → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (a i) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ i, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a i t ∧ a i t ≤ M)
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hs : ∀ i, IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G (a i)) (Ioo x₀ x₁)) :
    IsCompact (closure (range fun i => intervalDirichletSolution hx.le g₀ g₁ (hs i))) :=
  intervalIntegral.isCompact_closure_range_of_forall_eq_add_integral (left_mem_Icc.2 hx.le) hs
    (B := fun t => lam⁻¹ * (M / (x₁ - x₀) * (|g₁ - g₀| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t|) +
      |G t|))
    (((integrable_const _).add hG.abs).const_mul _)
    (fun i => (ae_abs_intervalDirichletSlope_le hlam ((haM i).mono fun _ h => h.1)
      (abs_intervalDirichletFluxConst_le hx hlam g₀ g₁ (ha i) (haM i) hG)).mono
        fun _ h => (Real.norm_eq_abs _).trans_le h)
    (intervalDirichletSolution_apply hx.le g₀ g₁ <| hs ·)

/-- The flux constant is affine in the data: for `λ ≤ a`, the difference of the flux constants of
two problems with the same coefficient is the flux constant of the differences of the endpoint
values and of the data. -/
theorem intervalDirichletFluxConst_sub (hlam : 0 < lam) (g₀ g₁ g₀' g₁' : ℝ) {G' : ℝ → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁)) (hG' : IntegrableOn G' (Ioo x₀ x₁)) :
    intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a - intervalDirichletFluxConst x₀ x₁ g₀' g₁' G' a =
      intervalDirichletFluxConst x₀ x₁ (g₀ - g₀') (g₁ - g₁') (G - G') a := by
  have hle := hla.norm_inv_le_inv hlam
  have h1 := hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable hle
  have h2 := hG'.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable hle
  simp only [intervalDirichletFluxConst_def, Pi.sub_apply, mul_sub]
  rw [integral_sub (f := fun t => (a t)⁻¹ * G t) (g := fun t => (a t)⁻¹ * G' t) h1 h2]
  ring

/-- The derivative of the explicit solution is affine in the data: for `λ ≤ a`, the difference of
the derivatives of two problems with the same coefficient is the derivative of the problem with
the differences of the endpoint values and of the data. -/
theorem intervalDirichletSlope_sub (hlam : 0 < lam) (g₀ g₁ g₀' g₁' : ℝ) {G' : ℝ → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁)) (hG' : IntegrableOn G' (Ioo x₀ x₁)) (t : ℝ) :
    intervalDirichletSlope x₀ x₁ g₀ g₁ G a t - intervalDirichletSlope x₀ x₁ g₀' g₁' G' a t =
      intervalDirichletSlope x₀ x₁ (g₀ - g₀') (g₁ - g₁') (G - G') a t := by
  simp only [intervalDirichletSlope_def,
    ← intervalDirichletFluxConst_sub hlam g₀ g₁ g₀' g₁' ha hla hG hG', Pi.sub_apply]
  ring

/-- **A bound for the solution of the linear problem.** For `λ ≤ a`, the explicit solution is
bounded on `[x₀, x₁]` by `|g₀| + λ⁻¹ ((x₁ - x₀) |k| + ‖G‖₁)`, where `k` is the flux constant and the
`L¹` norm is over `(x₀, x₁)`. For `λ ≤ a ≤ M`, `abs_intervalDirichletFluxConst_le` bounds `|k|` in
terms of the data. -/
theorem norm_intervalDirichletSolution_le (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hG : IntegrableOn G (Ioo x₀ x₁))
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁)) :
    ‖intervalDirichletSolution hx.le g₀ g₁ hs‖ ≤
      |g₀| + lam⁻¹ * ((x₁ - x₀) * |intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a| +
        ∫ t in Ioo x₀ x₁, |G t|) := by
  -- The derivative is dominated by `λ⁻¹ (|k| + |G|)`.
  refine (intervalIntegral.norm_le_of_forall_eq_add_integral (left_mem_Icc.2 hx.le) hs
    (B := fun t => lam⁻¹ * (|intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a| + |G t|))
    (((integrable_const _).add hG.abs).const_mul lam⁻¹)
    ((ae_abs_intervalDirichletSlope_le hlam hla le_rfl).mono fun _ h =>
      (Real.norm_eq_abs _).trans_le h)
    (intervalDirichletSolution_apply hx.le g₀ g₁ hs)).trans_eq ?_
  rw [Real.norm_eq_abs, integral_const_mul, integral_add (integrable_const _) hG.abs,
    setIntegral_const, Real.volume_real_Ioo_of_le hx.le, smul_eq_mul]

/-- **Dependence on the data.** For `λ ≤ a`, the explicit solutions of two problems with the same
coefficient differ on `[x₀, x₁]` by at most `|g₀ - g₀'| + λ⁻¹ ((x₁ - x₀) |k| + ‖G - G'‖₁)`, where
`k` is the flux constant of the problem with the differences of the data. For `λ ≤ a ≤ M`,
`abs_intervalDirichletFluxConst_le` bounds `|k|` by
`M / (x₁ - x₀) (|g₁ - g₁' - (g₀ - g₀')| + λ⁻¹ ‖G - G'‖₁)`, so the solution is Lipschitz in the data
with a constant depending only on `λ` and `M` (`norm_intervalDirichletSolution_sub_le_of_le`). -/
theorem norm_intervalDirichletSolution_sub_le (hx : x₀ < x₁) (hlam : 0 < lam)
    (g₀ g₁ g₀' g₁' : ℝ) {G' : ℝ → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁)) (hG' : IntegrableOn G' (Ioo x₀ x₁))
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁))
    (hs' : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀' g₁' G' a) (Ioo x₀ x₁)) :
    ‖intervalDirichletSolution hx.le g₀ g₁ hs - intervalDirichletSolution hx.le g₀' g₁' hs'‖ ≤
      |g₀ - g₀'| + lam⁻¹ * ((x₁ - x₀) *
        |intervalDirichletFluxConst x₀ x₁ (g₀ - g₀') (g₁ - g₁') (G - G') a| +
          ∫ t in Ioo x₀ x₁, |G t - G' t|) := by
  have hd := integrableOn_intervalDirichletSlope hlam (g₀ - g₀') (g₁ - g₁') ha hla (hG.sub hG')
  -- By affinity, the difference is the solution of the problem with the differences of the data.
  have heq : intervalDirichletSolution hx.le g₀ g₁ hs -
      intervalDirichletSolution hx.le g₀' g₁' hs' =
        intervalDirichletSolution hx.le (g₀ - g₀') (g₁ - g₁') hd := by
    ext y
    have hy := left_mem_Icc.2 hx.le
    rw [ContinuousMap.sub_apply, intervalDirichletSolution_apply, intervalDirichletSolution_apply,
      intervalDirichletSolution_apply, add_sub_add_comm, ← intervalIntegral.integral_sub
        (hs.intervalIntegrable_of_mem_Icc hy y.2) (hs'.intervalIntegrable_of_mem_Icc hy y.2)]
    simp only [intervalDirichletSlope_sub hlam g₀ g₁ g₀' g₁' ha hla hG hG']
  rw [heq]
  simpa only [Pi.sub_apply] using
    norm_intervalDirichletSolution_le hx hlam (g₀ - g₀') (g₁ - g₁') hla (hG.sub hG') hd

/-- **Lipschitz dependence on the data.** For `λ ≤ a ≤ M`, the explicit solutions of two problems
with the same coefficient differ on `[x₀, x₁]` by at most
`|g₀ - g₀'| + λ⁻¹ (M (|g₁ - g₁' - (g₀ - g₀')| + λ⁻¹ ‖G - G'‖₁) + ‖G - G'‖₁)`, with the `L¹` norms
over `(x₀, x₁)`. The bound depends on the coefficient only through `λ` and `M`. -/
theorem norm_intervalDirichletSolution_sub_le_of_le (hx : x₀ < x₁) (hlam : 0 < lam)
    (g₀ g₁ g₀' g₁' : ℝ) {G' : ℝ → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn G (Ioo x₀ x₁)) (hG' : IntegrableOn G' (Ioo x₀ x₁))
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁))
    (hs' : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀' g₁' G' a) (Ioo x₀ x₁)) :
    ‖intervalDirichletSolution hx.le g₀ g₁ hs - intervalDirichletSolution hx.le g₀' g₁' hs'‖ ≤
      |g₀ - g₀'| + lam⁻¹ * (M * (|g₁ - g₁' - (g₀ - g₀')| +
        lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t - G' t|) + ∫ t in Ioo x₀ x₁, |G t - G' t|) := by
  have hk := abs_intervalDirichletFluxConst_le hx hlam (g₀ - g₀') (g₁ - g₁') ha haM (hG.sub hG')
  simp only [Pi.sub_apply] at hk
  calc _ ≤ |g₀ - g₀'| + lam⁻¹ * ((x₁ - x₀) *
          |intervalDirichletFluxConst x₀ x₁ (g₀ - g₀') (g₁ - g₁') (G - G') a| +
            ∫ t in Ioo x₀ x₁, |G t - G' t|) :=
        norm_intervalDirichletSolution_sub_le hx hlam g₀ g₁ g₀' g₁' ha (haM.mono fun _ h => h.1)
          hG hG' hs hs'
    _ ≤ |g₀ - g₀'| + lam⁻¹ * ((x₁ - x₀) * (M / (x₁ - x₀) * (|g₁ - g₁' - (g₀ - g₀')| +
          lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t - G' t|)) + ∫ t in Ioo x₀ x₁, |G t - G' t|) := by
        gcongr
    _ = _ := by rw [← mul_assoc, mul_div_cancel₀ M (sub_pos.2 hx).ne']

/-- **Continuous dependence on all the data.** Let `λ ≤ aₙ` with `aₙ → a` almost everywhere,
`Gₙ → G` in `L¹(x₀, x₁)`, and endpoint values `g₀ₙ → g₀` and `g₁ₙ → g₁`. Then the solutions of the
linear problems with data `(g₀ₙ, g₁ₙ, Gₙ, aₙ)` converge uniformly on `[x₀, x₁]` to the solution
with data `(g₀, g₁, G, a)`. -/
theorem tendsto_intervalDirichletSolution (hx : x₀ < x₁) (hlam : 0 < lam)
    {g₀n g₁n : ℕ → ℝ} {g₀ g₁ : ℝ} (hg₀ : Tendsto g₀n atTop (𝓝 g₀))
    (hg₁ : Tendsto g₁n atTop (𝓝 g₁)) {Gn an : ℕ → ℝ → ℝ}
    (han : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)))
    (hanl : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t)
    (hGn : ∀ n, IntegrableOn (Gn n) (Ioo x₀ x₁)) (hG : IntegrableOn G (Ioo x₀ x₁))
    (hGlim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |Gn n t - G t|) atTop (𝓝 0))
    (hlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => an n t) atTop (𝓝 (a t)))
    (hsn : ∀ n, IntegrableOn (intervalDirichletSlope x₀ x₁ (g₀n n) (g₁n n) (Gn n) (an n))
      (Ioo x₀ x₁))
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁)) :
    Tendsto (fun n => intervalDirichletSolution hx.le (g₀n n) (g₁n n) (hsn n)) atTop
      (𝓝 (intervalDirichletSolution hx.le g₀ g₁ hs)) := by
  have ha := aestronglyMeasurable_of_tendsto_ae atTop han hlim
  have hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t := eventually_ge_of_tendsto hlim hanl
  -- The flux constants `kₙ` of the problems with the differences of the data tend to `0`: their
  -- numerators tend to `0`, and their denominators `∫ aₙ⁻¹` to `∫ a⁻¹ > 0`.
  have hden : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (an n t)⁻¹) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (a t)⁻¹)) :=
    tendsto_integral_of_dominated_convergence (fun _ => lam⁻¹)
      (fun n => (han n).aemeasurable.inv.aestronglyMeasurable) (integrable_const _)
      (fun n => (hanl n).norm_inv_le_inv hlam) (by
        filter_upwards [hlim, hla] with t ht hat
        exact ht.inv₀ (hlam.trans_le hat).ne')
  have hnum : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (an n t)⁻¹ * (Gn n - G) t) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hGlim.const_mul lam⁻¹)
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (((hGn n).sub hG).abs.const_mul _) ?_
    filter_upwards [(hanl n).norm_inv_le_inv hlam] with t ht
    rw [norm_mul, Real.norm_eq_abs ((Gn n - G) t), Pi.sub_apply]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  have hk : Tendsto (fun n => intervalDirichletFluxConst x₀ x₁ (g₀n n - g₀) (g₁n n - g₁)
      (Gn n - G) (an n)) atTop (𝓝 0) := by
    have h := (((hg₁.sub_const g₁).sub (hg₀.sub_const g₀)).add hnum).div hden
      (setIntegral_inv_pos (by simp [hx]) measure_Ioo_lt_top.ne hlam ha hla).ne'
    rw [sub_self, sub_self, sub_self, add_zero, zero_div] at h
    exact h.congr fun n => (intervalDirichletFluxConst_def _ _ _ _ _ _).symm
  -- Compare with the solutions with the limit data and the coefficients `aₙ`.
  have hsy := fun n => integrableOn_intervalDirichletSlope hlam g₀ g₁ (han n) (hanl n) hG
  have hy := tendsto_intervalDirichletSolution_of_tendsto_ae hx hlam han hanl hG hlim hsy hs
  have hB : Tendsto (fun n => |g₀n n - g₀| + lam⁻¹ * ((x₁ - x₀) *
      |intervalDirichletFluxConst x₀ x₁ (g₀n n - g₀) (g₁n n - g₁) (Gn n - G) (an n)| +
        ∫ t in Ioo x₀ x₁, |Gn n t - G t|)) atTop
      (𝓝 (|g₀ - g₀| + lam⁻¹ * ((x₁ - x₀) * |0| + 0))) :=
    (hg₀.sub_const g₀).abs.add (((hk.abs.const_mul (x₁ - x₀)).add hGlim).const_mul lam⁻¹)
  rw [show |g₀ - g₀| + lam⁻¹ * ((x₁ - x₀) * |(0 : ℝ)| + 0) = 0 by simp] at hB
  have hd : Tendsto (fun n => intervalDirichletSolution hx.le (g₀n n) (g₁n n) (hsn n) -
      intervalDirichletSolution hx.le g₀ g₁ (hsy n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => norm_intervalDirichletSolution_sub_le hx hlam _ _ _ _ (han n)
      (hanl n) (hGn n) hG (hsn n) (hsy n)) hB
  simpa using hd.add hy

/-- **Compactness for converging data.** Let `λ ≤ aₙ ≤ M`, and let the data converge: `Gₙ → G` in
`L¹(x₀, x₁)`, `g₀ₙ → g₀` and `g₁ₙ → g₁`. Then a subsequence of the solutions of the linear problems
with data `(g₀ₙ, g₁ₙ, Gₙ, aₙ)` converges uniformly on `[x₀, x₁]`. No convergence of the
coefficients is assumed: the solutions with the limit data `(g₀, g₁, G)` and the coefficients `aₙ`
lie in a compact set (`isCompact_closure_range_intervalDirichletSolution`), and the solutions with
the data `(g₀ₙ, g₁ₙ, Gₙ)` are uniformly close to them. -/
theorem exists_strictMono_tendsto_intervalDirichletSolution (hx : x₀ < x₁) (hlam : 0 < lam)
    {g₀n g₁n : ℕ → ℝ} {g₀ g₁ : ℝ} (hg₀ : Tendsto g₀n atTop (𝓝 g₀))
    (hg₁ : Tendsto g₁n atTop (𝓝 g₁)) {Gn an : ℕ → ℝ → ℝ}
    (han : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)))
    (hanM : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t ∧ an n t ≤ M)
    (hGn : ∀ n, IntegrableOn (Gn n) (Ioo x₀ x₁)) (hG : IntegrableOn G (Ioo x₀ x₁))
    (hGlim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |Gn n t - G t|) atTop (𝓝 0))
    (hsn : ∀ n, IntegrableOn (intervalDirichletSlope x₀ x₁ (g₀n n) (g₁n n) (Gn n) (an n))
      (Ioo x₀ x₁)) :
    ∃ w : C(Icc x₀ x₁, ℝ), ∃ ν : ℕ → ℕ, StrictMono ν ∧
      Tendsto (fun n => intervalDirichletSolution hx.le (g₀n (ν n)) (g₁n (ν n)) (hsn (ν n)))
        atTop (𝓝 w) := by
  have hanl : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t :=
    fun n => (hanM n).mono fun _ h => h.1
  have hsy := fun n => integrableOn_intervalDirichletSlope hlam g₀ g₁ (han n) (hanl n) hG
  obtain ⟨w, -, ν, hν, hyν⟩ := (isCompact_closure_range_intervalDirichletSolution hx hlam han
    hanM hG hsy).tendsto_subseq fun n => subset_closure (mem_range_self n)
  -- The distance to the solutions with the limit data is bounded uniformly in the coefficients
  -- (`norm_intervalDirichletSolution_sub_le_of_le`), and the bound tends to `0`.
  have hd₀ := hg₀.sub_const g₀
  have hB : Tendsto (fun n => |g₀n n - g₀| + lam⁻¹ * (M * (|g₁n n - g₁ - (g₀n n - g₀)| +
      lam⁻¹ * ∫ t in Ioo x₀ x₁, |Gn n t - G t|) + ∫ t in Ioo x₀ x₁, |Gn n t - G t|)) atTop
      (𝓝 (|g₀ - g₀| + lam⁻¹ * (M * (|g₁ - g₁ - (g₀ - g₀)| + lam⁻¹ * 0) + 0))) :=
    hd₀.abs.add ((((((hg₁.sub_const g₁).sub hd₀).abs.add (hGlim.const_mul lam⁻¹)).const_mul
      M).add hGlim).const_mul lam⁻¹)
  rw [show |g₀ - g₀| + lam⁻¹ * (M * (|g₁ - g₁ - (g₀ - g₀)| + lam⁻¹ * 0) + 0) = 0 by simp] at hB
  have hd : Tendsto (fun n => intervalDirichletSolution hx.le (g₀n n) (g₁n n) (hsn n) -
      intervalDirichletSolution hx.le g₀ g₁ (hsy n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => norm_intervalDirichletSolution_sub_le_of_le hx hlam _ _ _ _
      (han n) (hanM n) (hGn n) hG (hsn n) (hsy n)) hB
  exact ⟨w, ν, hν, by simpa using (hd.comp hν.tendsto_atTop).add hyν⟩

variable {p : ℝ≥0∞} {f F : ℝ → ℝ}

/-- The derivative `(k - G) / a` lies in `Lᵖ` when `G ∈ Lᵖ`, since
`|(k - G) / a| ≤ λ⁻¹ (|k| + |G|)`. -/
theorem memLp_intervalDirichletSlope (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : MemLp G p (volume.restrict (Ioo x₀ x₁))) :
    MemLp (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) p (volume.restrict (Ioo x₀ x₁)) := by
  set K := |intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a|
  have hb : MemLp (fun t => lam⁻¹ * (K + ‖G t‖)) p (volume.restrict (Ioo x₀ x₁)) :=
    ((memLp_const K).add hG.norm).const_mul lam⁻¹
  refine MemLp.of_le hb (aestronglyMeasurable_intervalDirichletSlope ha hG.aestronglyMeasurable) ?_
  filter_upwards [ae_abs_intervalDirichletSlope_le hlam hla le_rfl] with t ht
  have hK0 : 0 ≤ K + ‖G t‖ := by positivity
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hlam.le) hK0),
    Real.norm_eq_abs]
  exact ht

variable [Fact (1 ≤ p)]

/-- The explicit solution of the linear problem: `u = g₀ + ∫_{x₀}^x (k - G) / a` lies in
`W^{1,p}(x₀, x₁)`, has endpoint trace `(g₀, g₁)` and solves `-(a u' + F)' = f` weakly. -/
theorem exists_w1p_intervalRepresentativeL_eq (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      (∀ y : Icc x₀ x₁, W1p.intervalRepresentativeL hx u y = g₀ +
        ∫ t in x₀..y, intervalDirichletSlope x₀ x₁ g₀ g₁ (fun t => (∫ s in x₀..t, f s) + F t) a t) ∧
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  set G : ℝ → ℝ := fun t => (∫ s in x₀..t, f s) + F t
  -- `G` lies in `Lᵖ`: the primitive of `f` is continuous on `[x₀, x₁]`, and `F ∈ Lᵖ`.
  have hGp : MemLp G p (volume.restrict (Ioo x₀ x₁)) :=
    ((intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)).memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
      Ioo_subset_Icc_self p).add hF
  have hF1 : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  obtain ⟨u, hu, hgrad⟩ := W1p.exists_intervalRepresentativeL_eq_and_gradient_ae_eq hx
    (left_mem_Icc.2 hx.le) g₀ (memLp_intervalDirichletSlope hlam g₀ g₁ ha hla hGp)
  refine ⟨u, hu, ?_, setIntegral_mul_deriv_eq_sub_of_ae_add_eq_sub_intervalIntegral hf
    hF1.locallyIntegrableOn
    (k := intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a) ?_⟩
  · -- The boundary values.
    rw [W1p.intervalTraceL_apply, hu, hu]
    simp only [intervalIntegral.integral_same, add_zero, intervalIntegral.integral_of_le hx.le,
      integral_Ioc_eq_integral_Ioo,
      integral_intervalDirichletSlope hx hlam g₀ g₁ ha hla (hGp.integrable Fact.out),
      add_sub_cancel]
  · -- The first integral `a u' + F = k - ∫_{x₀}^x f`.
    filter_upwards [hgrad, hla] with t ht hat
    rw [ht, intervalDirichletSlope, mul_inv_cancel_left₀ (hlam.trans_le hat).ne']
    ring

/-- **The linear Dirichlet problem on an interval.** Let `λ ≤ a` almost everywhere on `(x₀, x₁)`,
with `λ > 0` and `a` almost everywhere strongly measurable, and let `f ∈ L¹(x₀, x₁)` and
`F ∈ Lᵖ(x₀, x₁)`. For all `g₀, g₁` there is `u ∈ W^{1,p}(x₀, x₁)` with endpoint values `g₀, g₁`
solving `-(a u' + F)' = f` in the sense of distributions on `(x₀, x₁)`. No upper bound on `a` is
needed. -/
theorem exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq (hx : x₀ < x₁)
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p, W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  obtain ⟨u, -, hu⟩ := exists_w1p_intervalRepresentativeL_eq hx hlam ha hla hf hF g₀ g₁
  exact ⟨u, hu⟩

/-- **The derivative of a solution of the linear problem.** Let `λ ≤ a ≤ M` almost everywhere on
`(x₀, x₁)`, with `λ > 0` and `a` almost everywhere strongly measurable, and let `f` and `F` be
integrable there. If `u ∈ W^{1,p}(x₀, x₁)` has endpoint values `g₀, g₁` and solves
`-(a u' + F)' = f` in the sense of distributions on `(x₀, x₁)`, then `u' = (k - G) / a` almost
everywhere, with `G = ∫_{x₀}^x f + F` and `k` the flux constant fixed by the endpoint values. -/
theorem gradient_ae_eq_intervalDirichletSlope (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁)) {g₀ g₁ : ℝ}
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p} (htr : W1p.intervalTraceL hx u = (g₀, g₁))
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    W1p.gradient u =ᵐ[volume.restrict (Ioo x₀ x₁)]
      intervalDirichletSlope x₀ x₁ g₀ g₁ (fun t => (∫ s in x₀..t, f s) + F t) a := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  set G : ℝ → ℝ := fun t => (∫ s in x₀..t, f s) + F t
  have hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t := haM.mono fun _ h => h.1
  have hG : IntegrableOn G (Ioo x₀ x₁) :=
    (intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf (left_mem_Icc.2 hx.le)).add hF
  have htr' := Prod.ext_iff.1 htr
  simp only [W1p.intervalTraceL_apply] at htr'
  -- The first integral `a u' + F = k - ∫_{x₀}^t f` gives `u' - (k₀ - G) / a = (k - k₀) / a`, where
  -- `k₀` is the flux constant of the explicit solution.
  obtain ⟨k, hk⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral ha
    (haM.mono fun t ht => abs_le.2 ⟨by linarith [ht.1, ht.2], ht.2⟩) hf hF hu
  set k₀ := intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      W1p.gradient u t - intervalDirichletSlope x₀ x₁ g₀ g₁ G a t = (k - k₀) * (a t)⁻¹ := by
    filter_upwards [hk, hla] with t ht hat
    have hg : W1p.gradient u t = (a t)⁻¹ * (k - G t) := by
      rw [eq_inv_mul_iff_mul_eq₀ (hlam.trans_le hat).ne']
      simp only [G]
      linarith
    rw [intervalDirichletSlope_def, hg]
    ring
  -- Both `u'` and `(k₀ - G) / a` integrate to `g₁ - g₀` over `(x₀, x₁)`, so `k = k₀`.
  have hgu : ∫ t in Ioo x₀ x₁, W1p.gradient u t = g₁ - g₀ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le, ← htr'.1,
      ← htr'.2]
    exact W1p.integral_gradient_eq_intervalRepresentativeL_sub hx u ⟨x₀, left_mem_Icc.2 hx.le⟩
      ⟨x₁, right_mem_Icc.2 hx.le⟩
  have hgrad : IntegrableOn (W1p.gradient u) (Ioo x₀ x₁) :=
    (Lp.memLp (W1p.gradient u)).integrable Fact.out
  have hint := integral_sub hgrad (integrableOn_intervalDirichletSlope hlam g₀ g₁ ha hla hG)
  rw [integral_congr_ae hdiff, integral_const_mul, hgu,
    integral_intervalDirichletSlope hx hlam g₀ g₁ ha hla hG, sub_self] at hint
  have hk₀ : k = k₀ := by
    have hpos := setIntegral_inv_pos (by simp [hx]) measure_Ioo_lt_top.ne hlam ha hla
    rcases mul_eq_zero.1 hint with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hpos.ne'
  filter_upwards [hdiff] with t ht
  rwa [hk₀, sub_self, zero_mul, sub_eq_zero] at ht

/-- **Uniqueness for the linear Dirichlet problem on an interval.** Let `λ ≤ a ≤ M` almost
everywhere on `(x₀, x₁)`, with `λ > 0` and `a` almost everywhere strongly measurable, and let `f`
and `F` be integrable there. If `u ∈ W^{1,p}(x₀, x₁)` has endpoint values `g₀, g₁` and solves
`-(a u' + F)' = f` in the sense of distributions on `(x₀, x₁)`, then its continuous representative
is the explicit solution `g₀ + ∫_{x₀}^x (k - G) / a`, with `G = ∫_{x₀}^x f + F`. In particular, for
`λ ≤ a ≤ M`, the solution of `exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq` is
unique. -/
theorem intervalRepresentativeL_eq_intervalDirichletSolution (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁)) {g₀ g₁ : ℝ}
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p} (htr : W1p.intervalTraceL hx u = (g₀, g₁))
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    (hs : IntegrableOn
      (intervalDirichletSlope x₀ x₁ g₀ g₁ (fun t => (∫ s in x₀..t, f s) + F t) a) (Ioo x₀ x₁)) :
    W1p.intervalRepresentativeL hx u = intervalDirichletSolution hx.le g₀ g₁ hs := by
  -- `ū` is the primitive of `u' = (k - G) / a` starting from `ū x₀ = g₀`.
  have heq : ∀ᵐ t ∂volume.restrict (Icc x₀ x₁), W1p.gradient u t =
      intervalDirichletSlope x₀ x₁ g₀ g₁ (fun t => (∫ s in x₀..t, f s) + F t) a t := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact gradient_ae_eq_intervalDirichletSlope hx hlam ha haM hf hF htr hu
  ext y
  have h1 : ∫ t in x₀..(y : ℝ), W1p.gradient u t = W1p.intervalRepresentativeL hx u y - g₀ := by
    have h0 : W1p.intervalRepresentativeL hx u ⟨x₀, left_mem_Icc.2 hx.le⟩ = g₀ := by
      simpa only [W1p.intervalTraceL_apply] using congrArg Prod.fst htr
    rw [← h0]
    exact W1p.integral_gradient_eq_intervalRepresentativeL_sub hx u ⟨x₀, left_mem_Icc.2 hx.le⟩ y
  have h2 : ∫ t in x₀..(y : ℝ), W1p.gradient u t = ∫ t in x₀..(y : ℝ),
      intervalDirichletSlope x₀ x₁ g₀ g₁ (fun t => (∫ s in x₀..t, f s) + F t) a t := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 heq] with t ht hty
    rw [uIoc_of_le y.2.1] at hty
    exact ht ⟨hty.1.le, hty.2.trans y.2.2⟩
  rw [intervalDirichletSolution_apply, ← h2, h1]
  ring

end TauCeti.PDE

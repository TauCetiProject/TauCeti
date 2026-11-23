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
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The linear Dirichlet problem on an interval

On a bounded interval `(x₀, x₁)` consider the divergence-form equation

`-(a u' + F)' = f`, `u(x₀) = g₀`, `u(x₁) = g₁`,

with a measurable coefficient `a ≥ λ > 0` and data `f ∈ L¹` and `F ∈ Lᵖ`, `1 ≤ p ≤ ∞`. A solution
is `u ∈ W^{1,p}(x₀, x₁)` whose endpoint trace is `(g₀, g₁)` and which satisfies

`∫ a u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

The problem is solved explicitly: the flux `a u' + F` equals `k - ∫_{x₀}^x f`, so `u' = (k - G) / a`
with `G = ∫_{x₀}^x f + F`, and the constant `k` is fixed by `∫ (k - G) / a = g₁ - g₀`. The solution
depends continuously on the coefficient: if `aₙ → a` almost everywhere with a uniform lower bound
`λ ≤ aₙ`, the derivatives of the solutions converge in `L¹`. Under uniform bounds `λ ≤ a ≤ M` the
solutions also form a relatively compact subset of `C([x₀, x₁])`. These are the two properties of
the frozen-coefficient solution map needed to solve quasilinear problems by a fixed-point argument
(`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`). For a fixed coefficient the
solution depends Lipschitz continuously on the data `(g₀, g₁, G)` in `L¹`, and when `a ≤ M` every
solution is the explicit one, so the problem is uniquely solvable. These give the stability of the
quasilinear problem under perturbation of its data.

## Main declarations

* `TauCeti.PDE.intervalDirichletFluxConst`, `TauCeti.PDE.intervalDirichletSlope`: the flux
  constant `k` and the derivative `(k - G) / a` of the explicit solution.
* `TauCeti.PDE.intervalDirichletSolution`: the explicit solution `g₀ + ∫_{x₀}^x (k - G) / a`, as a
  continuous function on `[x₀, x₁]`.
* `TauCeti.PDE.tendsto_integral_abs_intervalDirichletSlope_sub`: continuous dependence of the
  derivative on the coefficient, and
  `TauCeti.PDE.integral_abs_intervalDirichletSlope_sub_le`: Lipschitz dependence on the data.
* `TauCeti.PDE.dist_intervalDirichletSolution_le`: two explicit solutions are uniformly as close as
  their left endpoint values and their derivatives in `L¹`.
* `TauCeti.PDE.continuous_intervalDirichletSolution`,
  `TauCeti.PDE.isCompact_closure_range_intervalDirichletSolution`: the frozen-solution map
  `v ↦ TauCeti.PDE.intervalDirichletSolution` is continuous and has compact closure of range.
* `TauCeti.PDE.exists_w1p_intervalRepresentativeL_eq`: the explicit solution, with its continuous
  representative.
* `TauCeti.PDE.intervalRepresentativeL_eq_add_intervalIntegral_intervalDirichletSlope`: uniqueness,
  every solution is the explicit solution with its own endpoint values.
* `TauCeti.PDE.exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq`: the linear problem
  `-(a u' + F)' = f` with prescribed endpoint values has a solution in `W^{1,p}(x₀, x₁)`.
* `TauCeti.PDE.abs_intervalDirichletSolution_sub_le_min_mul_div`: with equal endpoint values `g`,
  the explicit solution stays within `min (y - x₀) (x₁ - y) * N / λ` of `g`, where `N` bounds the
  oscillation of `∫_{x₀}^t f + F`.

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

/-- Two explicit solutions are at uniform distance at most `|g₀ - g₀'|` plus the `L¹` distance of
their derivatives, whatever their data and coefficients. -/
theorem dist_intervalDirichletSolution_le (hx : x₀ ≤ x₁) {g₀ g₁ g₀' g₁' : ℝ} {G' a' : ℝ → ℝ}
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁))
    (hs' : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀' g₁' G' a') (Ioo x₀ x₁)) :
    dist (intervalDirichletSolution hx g₀ g₁ hs) (intervalDirichletSolution hx g₀' g₁' hs') ≤
      |g₀ - g₀'| + ∫ t in Ioo x₀ x₁,
        |intervalDirichletSlope x₀ x₁ g₀ g₁ G a t -
          intervalDirichletSlope x₀ x₁ g₀' g₁' G' a' t| := by
  refine (ContinuousMap.dist_le (add_nonneg (abs_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _))).2 fun y => ?_
  rw [intervalDirichletSolution_apply, intervalDirichletSolution_apply, Real.dist_eq,
    add_sub_add_comm, ← intervalIntegral.integral_sub
      (hs.intervalIntegrable_of_mem_Icc (left_mem_Icc.2 hx) y.property)
      (hs'.intervalIntegrable_of_mem_Icc (left_mem_Icc.2 hx) y.property)]
  refine (abs_add_le _ _).trans ?_
  gcongr
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    intervalIntegral.norm_integral_le_setIntegral_norm (hs.sub hs') (left_mem_Icc.2 hx) y.property

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

/-- **Uniform convergence in the coefficient.** If `aₙ → a` almost everywhere with a uniform lower
bound `λ ≤ aₙ`, the explicit solutions with coefficients `aₙ` converge to the explicit solution with
coefficient `a` uniformly on `[x₀, x₁]`. -/
theorem tendsto_intervalDirichletSolution (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    {an : ℕ → ℝ → ℝ} (han : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)))
    (hanl : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => an n t) atTop (𝓝 (a t)))
    (hsn : ∀ n, IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G (an n)) (Ioo x₀ x₁))
    (hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁)) :
    Tendsto (fun n => intervalDirichletSolution hx.le g₀ g₁ (hsn n)) atTop
      (𝓝 (intervalDirichletSolution hx.le g₀ g₁ hs)) := by
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_integral_abs_intervalDirichletSlope_sub hx hlam g₀ g₁ han hanl ha hla hG hlim))
  refine (dist_intervalDirichletSolution_le hx.le (hsn n) hs).trans_eq ?_
  rw [sub_self, abs_zero, zero_add]

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
  continuous_iff_seqContinuous.2 fun vn v hv => tendsto_intervalDirichletSolution hx hlam g₀ g₁
    (fun n => ha (vn n)) (fun n => hla (vn n)) (ha v) (hla v) hG (hlim vn v hv) (hs <| vn ·) (hs v)

/-- **Lipschitz dependence on the data.** For a fixed coefficient with `λ ≤ a ≤ M`, `λ > 0`, the
derivatives of the explicit solutions with data `(g₀, g₁, G)` and `(g₀', g₁', G')` are at `L¹`
distance at most `λ⁻¹ (M (|(g₁ - g₀) - (g₁' - g₀')| + λ⁻¹ ‖G - G'‖₁) + ‖G - G'‖₁)`, the norms
being over `(x₀, x₁)`. -/
theorem integral_abs_intervalDirichletSlope_sub_le (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M) {G' : ℝ → ℝ}
    (hG : IntegrableOn G (Ioo x₀ x₁)) (hG' : IntegrableOn G' (Ioo x₀ x₁)) (g₀ g₁ g₀' g₁' : ℝ) :
    ∫ t in Ioo x₀ x₁,
        |intervalDirichletSlope x₀ x₁ g₀ g₁ G a t - intervalDirichletSlope x₀ x₁ g₀' g₁' G' a t| ≤
      lam⁻¹ * (M * (|g₁ - g₀ - (g₁' - g₀')| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t - G' t|) +
        ∫ t in Ioo x₀ x₁, |G t - G' t|) := by
  have hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t := haM.mono fun _ h => h.1
  have hinv := hla.norm_inv_le_inv hlam
  have hGG : IntegrableOn (fun t => G t - G' t) (Ioo x₀ x₁) := hG.sub hG'
  -- The difference of the derivatives is the derivative for the difference of the data.
  have hk : intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a -
      intervalDirichletFluxConst x₀ x₁ g₀' g₁' G' a =
        intervalDirichletFluxConst x₀ x₁ 0 (g₁ - g₀ - (g₁' - g₀')) (fun t => G t - G' t) a := by
    have h1 : Integrable (fun t => (a t)⁻¹ * G t) (volume.restrict (Ioo x₀ x₁)) :=
      hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable hinv
    have h2 : Integrable (fun t => (a t)⁻¹ * G' t) (volume.restrict (Ioo x₀ x₁)) :=
      hG'.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable hinv
    simp only [intervalDirichletFluxConst, mul_sub]
    rw [integral_sub h1 h2]
    ring
  have hdiff : ∀ t, intervalDirichletSlope x₀ x₁ g₀ g₁ G a t -
      intervalDirichletSlope x₀ x₁ g₀' g₁' G' a t =
        intervalDirichletSlope x₀ x₁ 0 (g₁ - g₀ - (g₁' - g₀')) (fun t => G t - G' t) a t := by
    intro t
    simp only [intervalDirichletSlope, ← hk]
    ring
  simp only [hdiff]
  set K := M / (x₁ - x₀) *
    (|g₁ - g₀ - (g₁' - g₀') - 0| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t - G' t|)
  have hbound := ae_abs_intervalDirichletSlope_le hlam hla
    (abs_intervalDirichletFluxConst_le hx hlam 0 (g₁ - g₀ - (g₁' - g₀')) ha haM hGG)
  calc _ ≤ ∫ t in Ioo x₀ x₁, lam⁻¹ * (K + |G t - G' t|) :=
        integral_mono_ae (integrableOn_intervalDirichletSlope hlam _ _ ha hla hGG).abs
          (((integrable_const K).add hGG.abs).const_mul _) hbound
    _ = _ := by
        rw [integral_const_mul, integral_add (integrable_const K) hGG.abs, setIntegral_const,
          Real.volume_real_Ioo_of_le hx.le, smul_eq_mul]
        simp only [K, sub_zero]
        field_simp [(sub_pos.2 hx).ne']

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

variable {p : ℝ≥0∞} {f F : ℝ → ℝ}

/-- The function `G = ∫_{x₀}^x f + F` of the data of the linear problem is integrable on
`(x₀, x₁)`. -/
theorem integrableOn_intervalIntegral_add (hx : x₀ < x₁) (hf : IntegrableOn f (Ioo x₀ x₁))
    (hF : IntegrableOn F (Ioo x₀ x₁)) :
    IntegrableOn (fun t => (∫ s in x₀..t, f s) + F t) (Ioo x₀ x₁) :=
  (intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf (left_mem_Icc.2 hx.le)).add hF

/-- The `L¹` distance of `G = ∫_{x₀}^x f + F` and `G' = ∫_{x₀}^x f' + F'` on `(x₀, x₁)` is at most
`(x₁ - x₀) ‖f - f'‖₁ + ‖F - F'‖₁`. -/
private theorem integral_abs_intervalIntegral_add_sub_le (hx : x₀ < x₁) {f' F' : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hf' : IntegrableOn f' (Ioo x₀ x₁))
    (hF : IntegrableOn F (Ioo x₀ x₁)) (hF' : IntegrableOn F' (Ioo x₀ x₁)) :
    ∫ t in Ioo x₀ x₁, |(∫ s in x₀..t, f s) + F t - ((∫ s in x₀..t, f' s) + F' t)| ≤
      (x₁ - x₀) * (∫ t in Ioo x₀ x₁, |f t - f' t|) + ∫ t in Ioo x₀ x₁, |F t - F' t| := by
  have hff' : IntegrableOn (fun t => f t - f' t) (Ioo x₀ x₁) := hf.sub hf'
  have hFF' : IntegrableOn (fun t => F t - F' t) (Ioo x₀ x₁) := hF.sub hF'
  have hΦ : IntegrableOn (fun t => ∫ s in x₀..t, f s - f' s) (Ioo x₀ x₁) :=
    intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hff' (left_mem_Icc.2 hx.le)
  calc _ ≤ ∫ t in Ioo x₀ x₁, (|∫ s in x₀..t, f s - f' s| + |F t - F' t|) := by
        refine setIntegral_mono_on ((integrableOn_intervalIntegral_add hx hf hF).sub
          (integrableOn_intervalIntegral_add hx hf' hF')).abs
          (hΦ.abs.add hFF'.abs) measurableSet_Ioo fun t ht => ?_
        rw [add_sub_add_comm, ← intervalIntegral.integral_sub
          (hf.intervalIntegrable_of_mem_Icc (left_mem_Icc.2 hx.le) (Ioo_subset_Icc_self ht))
          (hf'.intervalIntegrable_of_mem_Icc (left_mem_Icc.2 hx.le) (Ioo_subset_Icc_self ht))]
        exact abs_add_le _ _
    _ = (∫ t in Ioo x₀ x₁, |∫ s in x₀..t, f s - f' s|) + ∫ t in Ioo x₀ x₁, |F t - F' t| :=
        integral_add hΦ.abs hFF'.abs
    _ ≤ _ := by
        gcongr
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.integral_norm_primitive_le hff' (left_mem_Icc.2 hx.le)

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
    (intervalIntegral.memLp_primitive hf (left_mem_Icc.2 hx.le)).add hF
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

/-- **Uniqueness for the linear problem.** Let `λ ≤ a ≤ M` almost everywhere on `(x₀, x₁)`, with
`λ > 0` and `a` almost everywhere strongly measurable, and let `f` and `F` be integrable there.
Every `u ∈ W^{1,p}(x₀, x₁)` solving `-(a u' + F)' = f` in the sense of distributions is the explicit
solution with its own endpoint values `(g₀, g₁)`: its continuous representative is
`ū y = g₀ + ∫_{x₀}^y (k - G) / a`, with `G = ∫_{x₀}^x f + F` and `k` the flux constant. -/
theorem intervalRepresentativeL_eq_add_intervalIntegral_intervalDirichletSlope (hx : x₀ < x₁)
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) (y : Icc x₀ x₁) :
    W1p.intervalRepresentativeL hx u y = (W1p.intervalTraceL hx u).1 +
      ∫ t in x₀..y, intervalDirichletSlope x₀ x₁ (W1p.intervalTraceL hx u).1
        (W1p.intervalTraceL hx u).2 (fun t => (∫ s in x₀..t, f s) + F t) a t := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t := haM.mono fun _ h => h.1
  have hΦ : IntegrableOn (fun t => ∫ s in x₀..t, f s) (Ioo x₀ x₁) :=
    intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf (left_mem_Icc.2 hx.le)
  -- The flux `a u' + F` is `k - ∫_{x₀}^t f`, and the endpoint values of `u` force `k` to be the
  -- flux constant.
  obtain ⟨k, hk⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral ha
    (haM.mono fun t ht => abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hf hF hu
  have hkk : k = intervalDirichletFluxConst x₀ x₁ (W1p.intervalTraceL hx u).1
      (W1p.intervalTraceL hx u).2 (fun t => (∫ s in x₀..t, f s) + F t) a := by
    rw [intervalDirichletFluxConst, eq_div_iff
      (setIntegral_inv_pos (by simp [hx]) measure_Ioo_lt_top.ne hlam ha hla).ne']
    exact mul_setIntegral_inv_eq hx hlam ha hla hF hΦ hk
  -- So `u'` is the derivative of the explicit solution, and integrating it from `x₀` gives `ū`.
  have hgrad : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), W1p.gradient u t =
      intervalDirichletSlope x₀ x₁ (W1p.intervalTraceL hx u).1 (W1p.intervalTraceL hx u).2
        (fun t => (∫ s in x₀..t, f s) + F t) a t := by
    filter_upwards [hk, hla] with t ht hat
    rw [intervalDirichletSlope, ← hkk, eq_inv_mul_iff_mul_eq₀ (hlam.trans_le hat).ne']
    linarith
  have h : ∫ t in x₀..(y : ℝ), W1p.gradient u t =
      W1p.intervalRepresentativeL hx u y -
        W1p.intervalRepresentativeL hx u ⟨x₀, left_mem_Icc.2 hx.le⟩ :=
    W1p.integral_gradient_eq_intervalRepresentativeL_sub hx u ⟨x₀, left_mem_Icc.2 hx.le⟩ y
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hgrad
  rw [intervalIntegral.integral_congr_ae_restrict (ae_restrict_of_ae_restrict_of_subset
    ((uIoc_of_le y.property.1).trans_subset (Ioc_subset_Ioc_right y.property.2)) hgrad)] at h
  have h₀ : (W1p.intervalTraceL hx u).1 =
      W1p.intervalRepresentativeL hx u ⟨x₀, left_mem_Icc.2 hx.le⟩ := by
    rw [W1p.intervalTraceL_apply]
  linarith

/-- **Stability of the linear problem under perturbation of the data.** Let `λ ≤ aₙ ≤ M`, with
`λ > 0`, and let `uₙ ∈ W^{1,p}(x₀, x₁)` solve `-(aₙ uₙ' + Fₙ)' = fₙ` with endpoint values `gₙ`. If
`fₙ → f` and `Fₙ → F` in `L¹(x₀, x₁)` and `gₙ → g`, then the continuous representative `ūₙ` is
uniformly asymptotic to the explicit solution with the same coefficient `aₙ` and the limit data
`(f, F, g)`. -/
theorem tendsto_dist_intervalRepresentativeL_intervalDirichletSolution (hx : x₀ < x₁)
    (hlam : 0 < lam) {an fn Fn : ℕ → ℝ → ℝ} {gn : ℕ → ℝ × ℝ} {g : ℝ × ℝ}
    (han : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)))
    (hanM : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t ∧ an n t ≤ M)
    (hfn : ∀ n, IntegrableOn (fn n) (Ioo x₀ x₁)) (hf : IntegrableOn f (Ioo x₀ x₁))
    (hflim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |fn n t - f t|) atTop (𝓝 0))
    (hFn : ∀ n, IntegrableOn (Fn n) (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    (hFlim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |Fn n t - F t|) atTop (𝓝 0))
    (hglim : Tendsto gn atTop (𝓝 g)) {un : ℕ → W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hutr : ∀ n, W1p.intervalTraceL hx (un n) = gn n)
    (hu : ∀ n, ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, an n t * W1p.gradient (un n) t * deriv φ t =
        (∫ t in Ioo x₀ x₁, fn n t * φ t) - ∫ t in Ioo x₀ x₁, Fn n t * deriv φ t)
    (hs : ∀ n, IntegrableOn (intervalDirichletSlope x₀ x₁ g.1 g.2
      (fun t => (∫ s in x₀..t, f s) + F t) (an n)) (Ioo x₀ x₁)) :
    Tendsto (fun n => dist (W1p.intervalRepresentativeL hx (un n))
      (intervalDirichletSolution hx.le g.1 g.2 (hs n))) atTop (𝓝 0) := by
  set Gn : ℕ → ℝ → ℝ := fun n t => (∫ s in x₀..t, fn n s) + Fn n t
  set G : ℝ → ℝ := fun t => (∫ s in x₀..t, f s) + F t
  have hGn : ∀ n, IntegrableOn (Gn n) (Ioo x₀ x₁) := fun n =>
    integrableOn_intervalIntegral_add hx (hfn n) (hFn n)
  -- Each `ūₙ` is the explicit solution with its own data.
  have hsn : ∀ n, IntegrableOn (intervalDirichletSlope x₀ x₁ (gn n).1 (gn n).2 (Gn n) (an n))
      (Ioo x₀ x₁) := fun n =>
    integrableOn_intervalDirichletSlope hlam _ _ (han n) ((hanM n).mono fun _ h => h.1) (hGn n)
  have hūn : ∀ n, W1p.intervalRepresentativeL hx (un n) =
      intervalDirichletSolution hx.le (gn n).1 (gn n).2 (hsn n) := fun n => by
    ext y
    rw [intervalDirichletSolution_apply, ← hutr n]
    exact intervalRepresentativeL_eq_add_intervalIntegral_intervalDirichletSlope hx hlam (han n)
      (hanM n) (hfn n) (hFn n) (hu n) y
  -- The data converge: `‖Gₙ - G‖₁ → 0` and `gₙ → g`.
  have hGlim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |Gn n t - G t|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun n => integral_abs_intervalIntegral_add_sub_le hx (hfn n) hf (hFn n) hF)
      (by simpa using (hflim.const_mul (x₁ - x₀)).add hFlim)
  have h0 : Tendsto (fun n => |(gn n).1 - g.1|) atTop (𝓝 0) := by
    simpa using (hglim.fst_nhds.sub_const g.1).abs
  have hδ : Tendsto (fun n => |(gn n).2 - (gn n).1 - (g.2 - g.1)|) atTop (𝓝 0) := by
    simpa using ((hglim.snd_nhds.sub hglim.fst_nhds).sub_const (g.2 - g.1)).abs
  have hbound := h0.add
    ((((hδ.add (hGlim.const_mul lam⁻¹)).const_mul M).add hGlim).const_mul lam⁻¹)
  simp only [mul_zero, add_zero] at hbound
  -- The Lipschitz dependence of the explicit solution on the data concludes.
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hbound
  rw [hūn n]
  exact (dist_intervalDirichletSolution_le hx.le (hsn n) (hs n)).trans (add_le_add le_rfl
    (integral_abs_intervalDirichletSlope_sub_le hx hlam (han n) (hanM n) (hGn n)
      (integrableOn_intervalIntegral_add hx hf hF) _ _ _ _))

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


/-- **Decay of the explicit solution towards equal boundary values.** Let `λ ≤ a ≤ M` almost
everywhere on `(x₀, x₁)`, with `λ > 0`, let `f` and `F` be integrable there, and let
`G t = ∫_{x₀}^t f + F t` lie in `[m, m + N]` for almost every `t ∈ (x₀, x₁)`. Then the explicit
solution of `-(a u' + F)' = f` with the value `g` at both endpoints satisfies
`|u y - g| ≤ min (y - x₀) (x₁ - y) * N / λ`. In particular the frozen-coefficient solution map
sends every coefficient between `λ` and `M` into the closed ball of radius `(x₁ - x₀) N / (2 λ)`
about the constant `g`. -/
theorem abs_intervalDirichletSolution_sub_le_min_mul_div (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁)) (g : ℝ) {m N : ℝ}
    (hG : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      m ≤ (∫ s in x₀..t, f s) + F t ∧ (∫ s in x₀..t, f s) + F t ≤ m + N)
    (hs : IntegrableOn
      (intervalDirichletSlope x₀ x₁ g g (fun t => (∫ s in x₀..t, f s) + F t) a) (Ioo x₀ x₁))
    (y : Icc x₀ x₁) :
    |intervalDirichletSolution hx.le g g hs y - g| ≤ min ((y : ℝ) - x₀) (x₁ - y) * N / lam := by
  -- The explicit solution is the continuous representative of a weak solution in `W^{1,1}`.
  obtain ⟨u, hrep, htr, hweak⟩ := exists_w1p_intervalRepresentativeL_eq (p := 1) hx hlam ha
    (haM.mono fun _ h => h.1) hf (memLp_one_iff_integrable.2 hF) g g
  rw [intervalDirichletSolution_apply, ← hrep]
  exact abs_intervalRepresentativeL_sub_le_min_mul_div hx hlam ha haM hf hF hweak htr hG y

end TauCeti.PDE

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
(`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`).

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
* `TauCeti.PDE.exists_w1p_intervalRepresentativeL_eq`: the explicit solution, with its continuous
  representative.
* `TauCeti.PDE.exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq`: the linear problem
  `-(a u' + F)' = f` with prescribed endpoint values has a solution in `W^{1,p}(x₀, x₁)`.

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
    Continuous fun v => intervalDirichletSolution hx.le g₀ g₁ (hs v) := by
  let x₀' : Icc x₀ x₁ := ⟨x₀, left_mem_Icc.2 hx.le⟩
  refine continuous_iff_seqContinuous.2 fun vn v hv => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_integral_abs_intervalDirichletSlope_sub hx hlam g₀ g₁ (fun n => ha (vn n))
      (fun n => hla (vn n)) (ha v) (hla v) hG (hlim vn v hv))
  refine (ContinuousMap.norm_le _ (integral_nonneg fun _ => abs_nonneg _)).2 fun y => ?_
  rw [Function.comp_apply, ContinuousMap.sub_apply, intervalDirichletSolution_apply,
    intervalDirichletSolution_apply, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub ((hs (vn n)).intervalIntegrable_of_mem_Icc x₀'.2 y.2)
      ((hs v).intervalIntegrable_of_mem_Icc x₀'.2 y.2),
    Real.norm_eq_abs, intervalIntegral.integral_of_le y.2.1, ← integral_Icc_eq_integral_Ioo]
  refine abs_integral_le_integral_abs.trans (setIntegral_mono_set ?_
    (ae_of_all _ fun _ => abs_nonneg _)
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right y.2.2)).eventuallySubset)
  exact ((integrableOn_Icc_iff_integrableOn_Ioo (μ := volume)).2 ((hs _).sub (hs _))).abs

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

end TauCeti.PDE

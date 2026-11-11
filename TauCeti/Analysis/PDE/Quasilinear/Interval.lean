/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.Convex.SchauderFixedPoint
public import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.ContinuousMap.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# The quasilinear Dirichlet problem on an interval

On a bounded interval `(x₀, x₁)` consider the divergence-form equation

`-(A(x, u) u' + F)' = f`, `u(x₀) = g₀`, `u(x₁) = g₁`,

with data `f ∈ L¹` and `F ∈ Lᵖ`, `1 ≤ p ≤ ∞`. A solution is `u ∈ W^{1,p}(x₀, x₁)` whose endpoint
trace is `(g₀, g₁)` and which satisfies

`∫ A(x, u) u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

The coefficient `A` is a Carathéodory function: almost everywhere strongly measurable in `x`,
continuous in `u` for almost every `x`, and `λ ≤ A ≤ M` with `λ > 0`. No Lipschitz condition in `u`
and no regularity in `x` is needed, and the theorem claims no uniqueness.

For a fixed measurable coefficient `a ≥ λ` the linear problem is solved explicitly
(`TauCeti.PDE.exists_w1p_intervalRepresentativeL_eq`): `u' = (k - G) / a` with
`G = ∫_{x₀}^x f + F` and a constant `k`. For the quasilinear problem, the map `T`
sending `v ∈ C([x₀, x₁])` to the solution of the linear problem with coefficient `A(x, v(x))` is
continuous, by dominated convergence, and its range has compact closure, by the Arzelà–Ascoli
theorem, since `|(T v)'| ≤ (K + |G|) / λ` with `K` independent of `v`. Schauder's fixed-point
theorem on a large closed ball of `C([x₀, x₁])` gives a fixed point, which solves the quasilinear
problem.

## Main declarations

* `TauCeti.PDE.isCompact_closure_range_intervalDirichletSolution`,
  `TauCeti.PDE.continuous_intervalDirichletSolution`: the frozen-solution map
  `v ↦ TauCeti.PDE.intervalDirichletSolution` has compact closure of range and is continuous.
* `TauCeti.PDE.exists_intervalTraceL_eq_and_forall_integral_apply_value_mul_gradient_eq`: the
  quasilinear problem `-(A(x, u) u' + F)' = f` with prescribed endpoint values has a solution in
  `W^{1,p}(x₀, x₁)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4 (one-dimensional boundary value problems).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 11 (quasilinear equations by fixed-point theorems).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace Topology
open scoped ENNReal Distributions

namespace TauCeti.PDE

variable {x₀ x₁ lam M : ℝ} {G : ℝ → ℝ} {g₀ g₁ : ℝ}

/-- **Compactness of the frozen-solution map.** Let `a i`, for `i ∈ ι`, be coefficients with
uniform bounds `λ ≤ a i ≤ M`. The solutions of the linear problems with coefficients `a i` form a
relatively compact subset of `C([x₀, x₁])`: their derivatives are all dominated by one integrable
function, so they are uniformly bounded and equicontinuous. -/
theorem isCompact_closure_range_intervalDirichletSolution {ι : Type*} (hx : x₀ < x₁)
    (hlam : 0 < lam) {a : ι → ℝ → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (a i) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ i, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a i t ∧ a i t ≤ M)
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hs : ∀ i, IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G (a i)) (Ioo x₀ x₁)) :
    IsCompact (closure (range fun i => intervalDirichletSolution hx.le g₀ g₁ (hs i))) := by
  -- The derivatives of all the solutions are dominated by one integrable function `H`.
  set K := M / (x₁ - x₀) * (|g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam)
  set H : ℝ → ℝ := fun t => lam⁻¹ * (K + |G t|)
  have hH : IntegrableOn H (Ioo x₀ x₁) := ((integrable_const K).add hG.abs).const_mul _
  have hsH : ∀ i, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      |intervalDirichletSlope x₀ x₁ g₀ g₁ G (a i) t| ≤ H t :=
    fun i => ae_abs_intervalDirichletSlope_le hlam ((haM i).mono fun _ h => h.1)
      (abs_intervalDirichletFluxConst_le hx hlam g₀ g₁ (ha i) (haM i) hG)
  have hIcc : ∀ {h : ℝ → ℝ}, IntegrableOn h (Ioo x₀ x₁) → IntegrableOn h (Icc x₀ x₁) :=
    fun hh => by rwa [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  have hII : ∀ {h : ℝ → ℝ}, IntegrableOn h (Ioo x₀ x₁) → ∀ y z : Icc x₀ x₁,
      IntervalIntegrable h volume y z := fun hh y z =>
    ((hIcc hh).mono_set (uIcc_subset_Icc y.2 z.2)).intervalIntegrable
  let x₀' : Icc x₀ x₁ := ⟨x₀, left_mem_Icc.2 hx.le⟩
  -- The common modulus of continuity `Ψ = ∫_{x₀}^x H` and the common bound.
  set Ψ : ℝ → ℝ := fun y => ∫ t in x₀..y, H t with hΨdef
  have hΨc : ContinuousOn Ψ (Icc x₀ x₁) :=
    intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hH (left_mem_Icc.2 hx.le)
  have hmod : ∀ i (y z : Icc x₀ x₁), |intervalDirichletSolution hx.le g₀ g₁ (hs i) y -
      intervalDirichletSolution hx.le g₀ g₁ (hs i) z| ≤ |Ψ y - Ψ z| := by
    intro i y z
    rw [intervalDirichletSolution_apply, intervalDirichletSolution_apply, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hII (hs i) x₀' y) (hII (hs i) x₀' z), hΨdef,
      intervalIntegral.integral_interval_sub_left (hII hH x₀' y) (hII hH x₀' z)]
    refine (Real.norm_eq_abs _).symm.trans_le
      (intervalIntegral.norm_integral_le_abs_of_norm_le ?_ (hII hH z y))
    have h := hsH i
    rw [restrict_Ioo_eq_restrict_Icc] at h
    exact ae_restrict_of_ae_restrict_of_subset
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc z.2 y.2))
      (h.mono fun t ht => by rwa [Real.norm_eq_abs])
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨc
  have hTb : ∀ i (y : Icc x₀ x₁), |intervalDirichletSolution hx.le g₀ g₁ (hs i) y| ≤ |g₀| + C := by
    intro i y
    have h := hmod i y x₀'
    simp only [intervalDirichletSolution_apply, x₀', intervalIntegral.integral_same, add_zero,
      hΨdef, sub_zero] at h ⊢
    calc |g₀ + ∫ t in x₀..(y : ℝ), intervalDirichletSlope x₀ x₁ g₀ g₁ G (a i) t|
        ≤ |g₀| + |∫ t in x₀..(y : ℝ), intervalDirichletSlope x₀ x₁ g₀ g₁ G (a i) t| :=
          abs_add_le _ _
      _ ≤ |g₀| + C := by
          gcongr
          simpa using h.trans (Real.norm_eq_abs (Ψ y) ▸ hC y y.2)
  -- The Arzelà–Ascoli theorem.
  refine ArzelaAscoli.isCompact_closure_range_of_equicontinuous (fun y => ?_) fun y =>
    ⟨closedBall 0 (|g₀| + C), isCompact_closedBall _ _, fun i => by
      rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
      exact hTb i y⟩
  have hlim : Tendsto (fun z : Icc x₀ x₁ => |Ψ z - Ψ y|) (𝓝 y) (𝓝 0) := by
    simpa using ((hΨc.domRestrict.tendsto y).sub_const (Ψ y)).abs
  refine Metric.equicontinuousAt_of_continuity_modulus _ hlim _
    (Eventually.of_forall fun z i => ?_)
  rw [Real.dist_eq, abs_sub_comm (Ψ z)]
  exact hmod i y z

/-- **Continuity of the frozen-solution map.** Let `a v`, for `v` in a sequential space `X`, be
coefficients with uniform bounds `λ ≤ a v ≤ M`, such that `a vₙ → a v` almost everywhere whenever
`vₙ → v`. Then the solution of the linear problem with coefficient `a v` depends continuously on
`v` in `C([x₀, x₁])`, by dominated convergence. -/
theorem continuous_intervalDirichletSolution {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    (hx : x₀ < x₁) (hlam : 0 < lam) {a : X → ℝ → ℝ}
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M)
    (hlim : ∀ (vn : ℕ → X) (v : X), Tendsto vn atTop (𝓝 v) →
      ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => a (vn n) t) atTop (𝓝 (a v t)))
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hs : ∀ v, IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G (a v)) (Ioo x₀ x₁)) :
    Continuous fun v => intervalDirichletSolution hx.le g₀ g₁ (hs v) := by
  have hIcc : ∀ {h : ℝ → ℝ}, IntegrableOn h (Ioo x₀ x₁) → IntegrableOn h (Icc x₀ x₁) :=
    fun hh => by rwa [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  have hII : ∀ {h : ℝ → ℝ}, IntegrableOn h (Ioo x₀ x₁) → ∀ y : Icc x₀ x₁,
      IntervalIntegrable h volume x₀ y := fun hh y =>
    ((hIcc hh).mono_set (uIcc_subset_Icc (left_mem_Icc.2 hx.le) y.2)).intervalIntegrable
  refine continuous_iff_seqContinuous.2 fun vn v hv => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_integral_abs_intervalDirichletSlope_sub hx hlam g₀ g₁ (fun n => ha (vn n))
      (fun n => haM (vn n)) (ha v) (haM v) hG (hlim vn v hv))
  refine (ContinuousMap.norm_le _ (integral_nonneg fun _ => abs_nonneg _)).2 fun y => ?_
  rw [Function.comp_apply, ContinuousMap.sub_apply, intervalDirichletSolution_apply,
    intervalDirichletSolution_apply, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub (hII (hs _) y) (hII (hs _) y),
    Real.norm_eq_abs, intervalIntegral.integral_of_le y.2.1, ← integral_Icc_eq_integral_Ioo]
  refine abs_integral_le_integral_abs.trans (setIntegral_mono_set ?_
    (ae_of_all _ fun _ => abs_nonneg _)
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right y.2.2)).eventuallyLE)
  exact (hIcc ((hs _).sub (hs _))).abs

/-- **The fixed point.** Let `a v` be a coefficient depending on `v ∈ C([x₀, x₁])`, with uniform
bounds `λ ≤ a v ≤ M`, such that `a vₙ → a v` almost everywhere whenever `vₙ → v`. Then for some
`ū ∈ C([x₀, x₁])`, `ū` is the solution of the linear problem with coefficient `a ū`. -/
private theorem exists_intervalDirichletSolution_eq_self (hx : x₀ < x₁) (hlam : 0 < lam)
    {a : C(Icc x₀ x₁, ℝ) → ℝ → ℝ}
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M)
    (hlim : ∀ (vn : ℕ → C(Icc x₀ x₁, ℝ)) (v : C(Icc x₀ x₁, ℝ)), Tendsto vn atTop (𝓝 v) →
      ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => a (vn n) t) atTop (𝓝 (a v t)))
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hs : ∀ v, IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G (a v)) (Ioo x₀ x₁)) :
    ∃ ū, intervalDirichletSolution hx.le g₀ g₁ (hs ū) = ū := by
  have hcpt := isCompact_closure_range_intervalDirichletSolution hx hlam ha haM hG hs
  -- Schauder's fixed-point theorem on a closed ball of `C([x₀, x₁])` containing the range.
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall 0
  have hmem : ∀ v, intervalDirichletSolution hx.le g₀ g₁ (hs v) ∈ closedBall 0 R :=
    fun v => hR (subset_closure (mem_range_self v))
  obtain ⟨ū, -, hū⟩ := schauderFixedPoint_closedConvex_continuousOn
    (C := closedBall (0 : C(Icc x₀ x₁, ℝ)) R) isClosed_closedBall (convex_closedBall _ _)
    (nonempty_closedBall.2 (dist_nonneg.trans (hmem 0)))
    (continuous_intervalDirichletSolution hx hlam ha haM hlim hG hs).continuousOn
    (fun v _ => hmem v) (hcpt.of_isClosed_subset isClosed_closure
      (closure_mono (image_subset_range _ _)))
  exact ⟨ū, hū⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {f F : ℝ → ℝ}

/-- **The quasilinear Dirichlet problem on an interval.** Let `A(x, z)` be almost everywhere
strongly measurable in `x ∈ (x₀, x₁)` for every `z`, continuous in `z` for almost every
`x ∈ (x₀, x₁)`, and satisfy `λ ≤ A(x, z) ≤ M`, with `λ > 0`, for almost every `x ∈ (x₀, x₁)` and
every `z`. Let `f ∈ L¹(x₀, x₁)` and `F ∈ Lᵖ(x₀, x₁)`. For all `g₀, g₁` there is
`u ∈ W^{1,p}(x₀, x₁)` with endpoint values `g₀, g₁` solving `-(A(x, u) u' + F)' = f` in the sense
of distributions on `(x₀, x₁)`. -/
theorem exists_intervalTraceL_eq_and_forall_integral_apply_value_mul_gradient_eq (hx : x₀ < x₁)
    (hlam : 0 < lam) {A : ℝ → ℝ → ℝ}
    (hA : ∀ z, AEStronglyMeasurable (fun t => A t z) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (A t))
    (hAM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ z, lam ≤ A t z ∧ A t z ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p, W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.value u t) * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  -- The coefficient `A(x, v(x))` of the linear problem frozen at `v ∈ C([x₀, x₁])`.
  let coef : C(Icc x₀ x₁, ℝ) → ℝ → ℝ := fun v t => A t (v (projIcc x₀ x₁ hx.le t))
  have hcm : ∀ v, AEStronglyMeasurable (coef v) (volume.restrict (Ioo x₀ x₁)) := fun v =>
    (v.continuous.comp continuous_projIcc).aestronglyMeasurable.apply_of_forall_of_continuousAt hA
      (hAc.mono fun t ht => ht.continuousAt)
  have hcM : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ coef v t ∧ coef v t ≤ M :=
    fun v => hAM.mono fun t ht => ht _
  have hlim : ∀ (vn : ℕ → C(Icc x₀ x₁, ℝ)) (v : C(Icc x₀ x₁, ℝ)), Tendsto vn atTop (𝓝 v) →
      ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => coef (vn n) t) atTop (𝓝 (coef v t)) :=
    fun vn v hv => hAc.mono fun t ht =>
      (ht.tendsto _).comp (((continuous_eval_const _).tendsto v).comp hv)
  have hG : IntegrableOn (fun t => (∫ s in x₀..t, f s) + F t) (Ioo x₀ x₁) :=
    (((intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)).memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
        Ioo_subset_Icc_self p).integrable Fact.out).add (hF.integrable Fact.out)
  -- A fixed point `ū` of the solution map solves the linear problem with coefficient
  -- `A(x, ū(x))`, and is the continuous representative of that solution.
  obtain ⟨ū, hū⟩ := exists_intervalDirichletSolution_eq_self hx hlam hcm hcM hlim hG fun v =>
    integrableOn_intervalDirichletSlope hlam g₀ g₁ (hcm v) ((hcM v).mono fun _ h => h.1) hG
  obtain ⟨u, hrep, htr, hweak⟩ :=
    exists_w1p_intervalRepresentativeL_eq (p := p) hx hlam (hcm ū)
      ((hcM ū).mono fun _ h => h.1) hf hF g₀ g₁
  have hū' : W1p.intervalRepresentativeL hx u = ū := by
    ext y
    rw [hrep, ← DFunLike.congr_fun hū y, intervalDirichletSolution_apply]
  refine ⟨u, htr, fun φ => ?_⟩
  rw [← hweak φ]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_ae_eq_intervalRepresentativeL hx u] with t ht
  rw [ht, hū']

end TauCeti.PDE

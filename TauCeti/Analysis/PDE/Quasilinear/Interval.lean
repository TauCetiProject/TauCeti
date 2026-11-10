/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.ContinuousMap.Ascoli
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
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

For a fixed measurable coefficient `a ≥ λ` the linear problem is solved explicitly: the flux
`a u' + F` equals `k - ∫_{x₀}^x f`, so `u' = (k - G) / a` with `G = ∫_{x₀}^x f + F`, and the
constant `k` is fixed by `∫ (k - G) / a = g₁ - g₀`. For the quasilinear problem, the map `T`
sending `v ∈ C([x₀, x₁])` to the solution of the linear problem with coefficient `A(x, v(x))` is
continuous, by dominated convergence, and its range has compact closure, by the Arzelà–Ascoli
theorem, since `|(T v)'| ≤ (K + |G|) / λ` with `K` independent of `v`. Schauder's fixed-point
theorem on a large closed ball of `C([x₀, x₁])` gives a fixed point, which solves the quasilinear
problem.

## Main declarations

* `TauCeti.PDE.exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq`: the linear problem
  `-(a u' + F)' = f` with prescribed endpoint values has a solution in `W^{1,p}(x₀, x₁)`.
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

variable {x₀ x₁ lam M : ℝ} {G a : ℝ → ℝ}

/-! ### The linear problem -/

/-- The flux constant `k` of the linear problem `-(a u' + F)' = f` with endpoint values `g₀` and
`g₁`, written in terms of `G = ∫_{x₀}^x f + F`: the flux `a u' + F` is `k - ∫_{x₀}^x f`, and `k`
is fixed by `∫ (k - G) / a = g₁ - g₀`. -/
private def fluxConst (x₀ x₁ g₀ g₁ : ℝ) (G a : ℝ → ℝ) : ℝ :=
  (g₁ - g₀ + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t) / ∫ t in Ioo x₀ x₁, (a t)⁻¹

/-- The derivative `(k - G) / a` of the solution of the linear problem. -/
private def slope (x₀ x₁ g₀ g₁ : ℝ) (G a : ℝ → ℝ) (t : ℝ) : ℝ :=
  (a t)⁻¹ * (fluxConst x₀ x₁ g₀ g₁ G a - G t)

private theorem ae_norm_inv_le (hlam : 0 < lam)
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ‖(a t)⁻¹‖ ≤ lam⁻¹ :=
  hla.mono fun t ht => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hlam.trans_le ht)]
    exact inv_anti₀ hlam ht

private theorem integrable_inv (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) :
    Integrable (fun t => (a t)⁻¹) (volume.restrict (Ioo x₀ x₁)) :=
  Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _ (ae_norm_inv_le hlam hla)

private theorem integral_inv_pos (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) :
    0 < ∫ t in Ioo x₀ x₁, (a t)⁻¹ := by
  have hpos : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), 0 < (a t)⁻¹ :=
    hla.mono fun t ht => inv_pos.2 (hlam.trans_le ht)
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun t ht => ht.le)
    (integrable_inv hlam ha hla)]
  exact (Measure.measure_univ_pos.2 (by simp [hx])).trans_le
    (measure_mono_ae (hpos.mono fun t ht _ => ht.ne'))

/-- Since `a ≤ M`, the integral of `1 / a` over `(x₀, x₁)` is at least `(x₁ - x₀) / M > 0`. -/
private theorem div_le_integral_inv (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M) :
    0 < M ∧ (x₁ - x₀) / M ≤ ∫ t in Ioo x₀ x₁, (a t)⁻¹ := by
  have hM : 0 < M := by
    have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by simp [hx])
    obtain ⟨t, ht⟩ := haM.exists
    linarith [ht.1, ht.2]
  refine ⟨hM, ?_⟩
  have h := integral_mono_ae (integrable_const M⁻¹)
    (integrable_inv hlam ha (haM.mono fun _ h => h.1))
    (haM.mono fun t ht => inv_anti₀ (hlam.trans_le ht.1) ht.2)
  rwa [setIntegral_const, Real.volume_real_Ioo_of_le hx.le, smul_eq_mul, ← div_eq_mul_inv] at h

private theorem abs_fluxConst_le (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    |fluxConst x₀ x₁ g₀ g₁ G a| ≤
      M / (x₁ - x₀) * (|g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam) := by
  obtain ⟨hM, hc⟩ := div_le_integral_inv hx hlam ha haM
  have hla := haM.mono fun _ h => h.1
  have hL : 0 < x₁ - x₀ := sub_pos.2 hx
  have hc0 : 0 < ∫ t in Ioo x₀ x₁, (a t)⁻¹ := (div_pos hL hM).trans_le hc
  have hR : |∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t| ≤ (∫ t in Ioo x₀ x₁, |G t|) / lam := by
    refine abs_integral_le_integral_abs.trans ?_
    rw [div_eq_inv_mul, ← integral_const_mul]
    refine integral_mono_ae
      (hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable (ae_norm_inv_le hlam hla)).abs
      (hG.abs.const_mul _) ?_
    filter_upwards [ae_norm_inv_le hlam hla] with t ht
    rw [Real.norm_eq_abs] at ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  rw [fluxConst, abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
  calc |g₁ - g₀ + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t|
      ≤ |g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam := (abs_add_le _ _).trans (by gcongr)
    _ = M / (x₁ - x₀) * (|g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam) * ((x₁ - x₀) / M) := by
        field_simp
    _ ≤ _ := by gcongr

private theorem ae_abs_slope_le (hlam : 0 < lam) {g₀ g₁ K : ℝ}
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hK : |fluxConst x₀ x₁ g₀ g₁ G a| ≤ K) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), |slope x₀ x₁ g₀ g₁ G a t| ≤ lam⁻¹ * (K + |G t|) := by
  filter_upwards [ae_norm_inv_le hlam hla] with t ht
  rw [Real.norm_eq_abs] at ht
  rw [slope, abs_mul]
  exact mul_le_mul ht ((abs_sub _ _).trans (by gcongr)) (abs_nonneg _)
    (inv_nonneg.2 hlam.le)

private theorem aestronglyMeasurable_slope {g₀ g₁ : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    AEStronglyMeasurable (slope x₀ x₁ g₀ g₁ G a) (volume.restrict (Ioo x₀ x₁)) :=
  ha.aemeasurable.inv.aestronglyMeasurable.mul (aestronglyMeasurable_const.sub hG.1)

/-- The solution of the linear problem has the prescribed increment `g₁ - g₀`. -/
private theorem integral_slope (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    ∫ t in Ioo x₀ x₁, slope x₀ x₁ g₀ g₁ G a t = g₁ - g₀ := by
  have hc0 := (integral_inv_pos hx hlam ha hla).ne'
  have h2 : Integrable (fun t => (a t)⁻¹ * G t) (volume.restrict (Ioo x₀ x₁)) :=
    hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable (ae_norm_inv_le hlam hla)
  simp only [slope, mul_sub]
  rw [integral_sub ((integrable_inv hlam ha hla).mul_const _) h2, integral_mul_const, fluxConst,
    mul_div_cancel₀ _ hc0]
  ring

/-- **Continuous dependence on the coefficient.** If `aₙ → a` almost everywhere with uniform
bounds `λ ≤ aₙ ≤ M`, the derivatives of the solutions of the linear problems converge in `L¹`. -/
private theorem tendsto_integral_abs_slope_sub (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    {an : ℕ → ℝ → ℝ} (han : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)))
    (hanM : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t ∧ an n t ≤ M)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => an n t) atTop (𝓝 (a t))) :
    Tendsto (fun n => ∫ t in Ioo x₀ x₁,
      |slope x₀ x₁ g₀ g₁ G (an n) t - slope x₀ x₁ g₀ g₁ G a t|) atTop (𝓝 0) := by
  have hla := haM.mono fun _ h => h.1
  have hanl := fun n => (hanM n).mono fun _ h => h.1
  have hinv : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      Tendsto (fun n => (an n t)⁻¹) atTop (𝓝 (a t)⁻¹) := by
    filter_upwards [hlim, haM] with t ht hat
    exact ht.inv₀ (hlam.trans_le hat.1).ne'
  -- The two integrals defining the flux constant converge by dominated convergence.
  have hc' : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (an n t)⁻¹) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (a t)⁻¹)) :=
    tendsto_integral_of_dominated_convergence (fun _ => lam⁻¹)
      (fun n => (han n).aemeasurable.inv.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_norm_inv_le hlam (hanl n)) hinv
  have hd : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (an n t)⁻¹ * G t) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => lam⁻¹ * ‖G t‖)
      (fun n => (han n).aemeasurable.inv.aestronglyMeasurable.mul hG.1)
      (hG.norm.const_mul _) (fun n => ?_) ?_
    · filter_upwards [ae_norm_inv_le hlam (hanl n)] with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    · filter_upwards [hinv] with t ht
      exact ht.mul_const _
  have hk : Tendsto (fun n => fluxConst x₀ x₁ g₀ g₁ G (an n)) atTop
      (𝓝 (fluxConst x₀ x₁ g₀ g₁ G a)) :=
    (tendsto_const_nhds.add hd).div hc' (integral_inv_pos hx hlam ha hla).ne'
  -- The derivatives converge almost everywhere, under a common integrable bound.
  set K := M / (x₁ - x₀) * (|g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam)
  have h0 := tendsto_integral_of_dominated_convergence (fun t => 2 * (lam⁻¹ * (K + |G t|)))
    (F := fun n t => |slope x₀ x₁ g₀ g₁ G (an n) t - slope x₀ x₁ g₀ g₁ G a t|)
    (f := fun _ => 0)
    (fun n => ((aestronglyMeasurable_slope (han n) hG).sub
      (aestronglyMeasurable_slope ha hG)).norm)
    (((integrable_const K).add hG.abs).const_mul lam⁻¹ |>.const_mul 2) (fun n => ?_) ?_
  · simpa using h0
  · filter_upwards [ae_abs_slope_le hlam (hanl n) (abs_fluxConst_le hx hlam g₀ g₁ (han n)
      (hanM n) hG), ae_abs_slope_le hlam hla (abs_fluxConst_le hx hlam g₀ g₁ ha haM hG)]
      with t h1 h2
    rw [Real.norm_eq_abs, abs_abs]
    linarith [abs_sub (slope x₀ x₁ g₀ g₁ G (an n) t) (slope x₀ x₁ g₀ g₁ G a t)]
  · filter_upwards [hinv] with t ht
    have h : Tendsto (fun n => slope x₀ x₁ g₀ g₁ G (an n) t) atTop
        (𝓝 (slope x₀ x₁ g₀ g₁ G a t)) := ht.mul (hk.sub_const _)
    simpa using (h.sub_const (slope x₀ x₁ g₀ g₁ G a t)).abs

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {f F : ℝ → ℝ}

/-- Against a test function on `(x₀, x₁)`, the function `k - ∫_{x₀}^x f` has distributional
derivative `-f`. -/
private theorem integral_sub_primitive_mul_deriv (hx : x₀ < x₁) (hf : IntegrableOn f (Ioo x₀ x₁))
    (k : ℝ) (φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ)) :
    ∫ t in Ioo x₀ x₁, (k - ∫ s in x₀..t, f s) * deriv φ t = ∫ t in Ioo x₀ x₁, f t * φ t := by
  have hφ0 : φ x₀ = 0 := φ.zero_on_compl (by simp)
  have hφ1 : φ x₁ = 0 := φ.zero_on_compl (by simp)
  have hdφ : Continuous (deriv φ) := φ.contDiff.continuous_deriv (by simp)
  have hΦc : ContinuousOn (fun t => ∫ s in x₀..t, f s) (Icc x₀ x₁) :=
    intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf (left_mem_Icc.2 hx.le)
  have h1 : IntegrableOn (deriv φ) (Ioo x₀ x₁) :=
    hdφ.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have h2 : IntegrableOn (fun t => (∫ s in x₀..t, f s) * deriv φ t) (Ioo x₀ x₁) :=
    (hΦc.mul hdφ.continuousOn).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- `∫ φ' = 0`, and integration by parts against the primitive gives `∫ Φ φ' = -∫ f φ`.
  have he1 : ∫ t in Ioo x₀ x₁, deriv φ t = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le,
      intervalIntegral.integral_deriv_eq_sub
        (fun t _ => (φ.contDiff.differentiable (by simp)) t) (hdφ.intervalIntegrable _ _),
      hφ0, hφ1, sub_zero]
  have he2 := intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hx.le
    (φ.contDiff.of_le (by exact_mod_cast le_top))
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2 hf)
  simp only [smul_eq_mul, hφ1, zero_mul, zero_sub, intervalIntegral.integral_of_le hx.le,
    integral_Ioc_eq_integral_Ioo, mul_comm (deriv φ _), mul_comm (φ _)] at he2
  simp only [sub_mul]
  rw [integral_sub (h1.const_mul k) h2, integral_const_mul, he1, he2]
  ring

/-- The derivative `(k - G) / a` lies in `Lᵖ` when `G = Φ + F` with `Φ, F ∈ Lᵖ`, since
`|(k - G) / a| ≤ λ⁻¹ (|k| + |Φ| + |F|)`. -/
private theorem memLp_slope (hlam : 0 < lam) (g₀ g₁ : ℝ) {Φ : ℝ → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hΦ : MemLp Φ p (volume.restrict (Ioo x₀ x₁))) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁))) :
    MemLp (slope x₀ x₁ g₀ g₁ (fun t => Φ t + F t) a) p (volume.restrict (Ioo x₀ x₁)) := by
  have hG : IntegrableOn (fun t => Φ t + F t) (Ioo x₀ x₁) :=
    (hΦ.integrable Fact.out).add (hF.integrable Fact.out)
  set K := |fluxConst x₀ x₁ g₀ g₁ (fun t => Φ t + F t) a|
  have hb : MemLp (fun t => lam⁻¹ * (K + (‖Φ t‖ + ‖F t‖))) p (volume.restrict (Ioo x₀ x₁)) :=
    ((memLp_const K).add (hΦ.norm.add hF.norm)).const_mul lam⁻¹
  refine MemLp.of_le hb (aestronglyMeasurable_slope ha hG) ?_
  filter_upwards [ae_abs_slope_le hlam hla le_rfl] with t ht
  have hK0 : 0 ≤ K + (‖Φ t‖ + ‖F t‖) := by positivity
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hlam.le) hK0)]
  refine ht.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hlam.le))
  simp only [Real.norm_eq_abs]
  gcongr
  exact abs_add_le _ _

/-- The explicit solution of the linear problem: `u = g₀ + ∫_{x₀}^x (k - G) / a` lies in
`W^{1,p}(x₀, x₁)`, has endpoint trace `(g₀, g₁)` and solves `-(a u' + F)' = f` weakly. -/
private theorem exists_w1p_intervalRepresentativeL_eq (hx : x₀ < x₁) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      (∀ y : Icc x₀ x₁, W1p.intervalRepresentativeL hx u y = g₀ +
        ∫ t in x₀..y, slope x₀ x₁ g₀ g₁ (fun t => (∫ s in x₀..t, f s) + F t) a t) ∧
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  set Φ : ℝ → ℝ := fun t => ∫ s in x₀..t, f s
  set G : ℝ → ℝ := fun t => Φ t + F t
  set s := slope x₀ x₁ g₀ g₁ G a with hsdef
  have hΦc : ContinuousOn Φ (Icc x₀ x₁) :=
    intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)
  have hΦp : MemLp Φ p (volume.restrict (Ioo x₀ x₁)) :=
    hΦc.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self p
  have hF1 : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  have hG : IntegrableOn G (Ioo x₀ x₁) := (hΦp.integrable Fact.out).add hF1
  have hsp : MemLp s p (volume.restrict (Ioo x₀ x₁)) := memLp_slope hlam g₀ g₁ ha hla hΦp hF
  have hsI : IntervalIntegrable s volume x₀ x₁ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2 (hsp.integrable Fact.out)
  -- The candidate `P = g₀ + ∫_{x₀}^x s` is absolutely continuous with derivative `s`.
  set P : ℝ → ℝ := fun y => g₀ + ∫ t in x₀..y, s t with hPdef
  have hP : AbsolutelyContinuousOnInterval P x₀ x₁ :=
    (contDiffOn_const.absolutelyContinuousOnInterval).add
      (hsI.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hdP : deriv P =ᵐ[volume.restrict (Ioo x₀ x₁)] s := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hsI.ae_hasDerivAt_integral] with t ht htI
    exact ((ht (by rw [uIcc_of_le hx.le]; exact Ioo_subset_Icc_self htI) x₀
      left_mem_uIcc).const_add g₀).deriv
  obtain ⟨u, hu, hgu⟩ := hP.exists_w1p_value_gradient_ae_eq (hsp.ae_eq hdP.symm)
  let w : C(Icc x₀ x₁, ℝ) := ⟨fun y => P y, (uIcc_of_le hx.le ▸ hP.continuousOn).domRestrict⟩
  have hrep : W1p.intervalRepresentativeL hx u = w := by
    refine (W1p.intervalRepresentativeL_eq_iff hx u w).2 ?_
    filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht, projIcc_of_mem hx.le (Ioo_subset_Icc_self hmem)]
    rfl
  refine ⟨u, fun y => by rw [hrep]; rfl, ?_, fun φ => ?_⟩
  · rw [W1p.intervalTraceL_apply, hrep]
    simp only [w, ContinuousMap.coe_mk, hPdef, intervalIntegral.integral_same, add_zero,
      intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo]
    rw [hsdef, integral_slope hx hlam g₀ g₁ ha hla hG, add_sub_cancel]
  -- Weak form: the flux `a u' + F` is `k - Φ`, and `Φ` is a primitive of `f`.
  have hdφ : Continuous (deriv φ) := φ.contDiff.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := hdφ.bounded_above_of_compact_support φ.hasCompactSupport.deriv
  have hflux : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), a t * W1p.gradient u t * deriv φ t =
      (fluxConst x₀ x₁ g₀ g₁ G a - Φ t) * deriv φ t - F t * deriv φ t := by
    filter_upwards [hgu, hdP, hla] with t h1 h2 h3
    rw [h1, h2, hsdef, slope, mul_inv_cancel_left₀ (hlam.trans_le h3).ne']
    ring
  have hint1 : IntegrableOn (fun t => (fluxConst x₀ x₁ g₀ g₁ G a - Φ t) * deriv φ t)
      (Ioo x₀ x₁) :=
    ((continuousOn_const.sub hΦc).mul hdφ.continuousOn).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun t => F t * deriv φ t) (Ioo x₀ x₁) :=
    hF1.mul_bdd hdφ.aestronglyMeasurable (ae_of_all _ hC)
  rw [integral_congr_ae hflux, integral_sub hint1 hint2]
  exact congrArg (· - _) (integral_sub_primitive_mul_deriv hx hf _ φ)

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

/-! ### The quasilinear problem -/

/-- **The fixed point.** Let `a v` be a coefficient depending on `v ∈ C([x₀, x₁])`, with uniform
bounds `λ ≤ a v ≤ M`, such that `a vₙ → a v` almost everywhere whenever `vₙ → v`. Then for some
`ū ∈ C([x₀, x₁])`, `ū` is the solution of the linear problem with coefficient `a ū`. -/
private theorem exists_eq_add_intervalIntegral_slope (hx : x₀ < x₁) (hlam : 0 < lam)
    (g₀ g₁ : ℝ) {a : C(Icc x₀ x₁, ℝ) → ℝ → ℝ}
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M)
    (hlim : ∀ (vn : ℕ → C(Icc x₀ x₁, ℝ)) (v : C(Icc x₀ x₁, ℝ)), Tendsto vn atTop (𝓝 v) →
      ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => a (vn n) t) atTop (𝓝 (a v t)))
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    ∃ ū : C(Icc x₀ x₁, ℝ), ∀ y : Icc x₀ x₁,
      ū y = g₀ + ∫ t in x₀..y, slope x₀ x₁ g₀ g₁ G (a ū) t := by
  -- The derivatives of all the frozen solutions are dominated by one integrable function `H`.
  set K := M / (x₁ - x₀) * (|g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam)
  set H : ℝ → ℝ := fun t => lam⁻¹ * (K + |G t|)
  have hH : IntegrableOn H (Ioo x₀ x₁) := ((integrable_const K).add hG.abs).const_mul _
  have hsH : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), |slope x₀ x₁ g₀ g₁ G (a v) t| ≤ H t :=
    fun v => ae_abs_slope_le hlam ((haM v).mono fun _ h => h.1)
      (abs_fluxConst_le hx hlam g₀ g₁ (ha v) (haM v) hG)
  have hsi : ∀ v, IntegrableOn (slope x₀ x₁ g₀ g₁ G (a v)) (Ioo x₀ x₁) := fun v =>
    hH.mono' (aestronglyMeasurable_slope (ha v) hG)
      ((hsH v).mono fun t ht => by rwa [Real.norm_eq_abs])
  have hIcc : ∀ {h : ℝ → ℝ}, IntegrableOn h (Ioo x₀ x₁) → IntegrableOn h (Icc x₀ x₁) :=
    fun hh => by rwa [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  have hII : ∀ {h : ℝ → ℝ}, IntegrableOn h (Ioo x₀ x₁) → ∀ y z : Icc x₀ x₁,
      IntervalIntegrable h volume y z := fun hh y z =>
    ((hIcc hh).mono_set (uIcc_subset_Icc y.2 z.2)).intervalIntegrable
  let x₀' : Icc x₀ x₁ := ⟨x₀, left_mem_Icc.2 hx.le⟩
  -- The solution map `T`.
  have hTex : ∀ v : C(Icc x₀ x₁, ℝ), ∃ w : C(Icc x₀ x₁, ℝ), ∀ y : Icc x₀ x₁,
      w y = g₀ + ∫ t in x₀..y, slope x₀ x₁ g₀ g₁ G (a v) t := fun v =>
    ⟨⟨fun y => g₀ + ∫ t in x₀..(y : ℝ), slope x₀ x₁ g₀ g₁ G (a v) t,
      (continuousOn_const.add
        (intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo (hsi v)
          (left_mem_Icc.2 hx.le))).domRestrict⟩, fun _ => rfl⟩
  choose T hT using hTex
  -- The common modulus of continuity `Ψ = ∫_{x₀}^x H` and the common bound.
  set Ψ : ℝ → ℝ := fun y => ∫ t in x₀..y, H t with hΨdef
  have hΨc : ContinuousOn Ψ (Icc x₀ x₁) :=
    intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hH (left_mem_Icc.2 hx.le)
  have hmod : ∀ v (y z : Icc x₀ x₁), |T v y - T v z| ≤ |Ψ y - Ψ z| := by
    intro v y z
    rw [hT, hT, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      (hII (hsi v) x₀' y) (hII (hsi v) x₀' z), hΨdef,
      intervalIntegral.integral_interval_sub_left (hII hH x₀' y) (hII hH x₀' z)]
    refine (Real.norm_eq_abs _).symm.trans_le
      (intervalIntegral.norm_integral_le_abs_of_norm_le ?_ (hII hH z y))
    have h := hsH v
    rw [restrict_Ioo_eq_restrict_Icc] at h
    exact ae_restrict_of_ae_restrict_of_subset
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc z.2 y.2))
      (h.mono fun t ht => by rwa [Real.norm_eq_abs])
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨc
  have hR : 0 ≤ |g₀| + C :=
    add_nonneg (abs_nonneg _) ((norm_nonneg _).trans (hC x₀ (left_mem_Icc.2 hx.le)))
  have hTb : ∀ v (y : Icc x₀ x₁), |T v y| ≤ |g₀| + C := by
    intro v y
    have h := hmod v y x₀'
    rw [hT v x₀'] at h
    simp only [x₀', intervalIntegral.integral_same, add_zero, hΨdef, sub_zero] at h
    calc |T v y| ≤ |T v y - g₀| + |g₀| := by simpa using abs_add_le (T v y - g₀) g₀
      _ ≤ C + |g₀| := by
          gcongr
          exact h.trans (Real.norm_eq_abs (Ψ y) ▸ hC y y.2)
      _ = |g₀| + C := add_comm _ _
  -- `T` is continuous, by dominated convergence.
  have hTc : Continuous T := by
    refine continuous_iff_seqContinuous.2 fun vn v hv => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (tendsto_integral_abs_slope_sub hx hlam g₀ g₁ (fun n => ha (vn n)) (fun n => haM (vn n))
        (ha v) (haM v) hG (hlim vn v hv))
    refine (ContinuousMap.norm_le _ (integral_nonneg fun _ => abs_nonneg _)).2 fun y => ?_
    rw [Function.comp_apply, ContinuousMap.sub_apply, hT, hT, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hII (hsi _) x₀' y) (hII (hsi _) x₀' y),
      Real.norm_eq_abs, intervalIntegral.integral_of_le y.2.1, ← integral_Icc_eq_integral_Ioo]
    refine abs_integral_le_integral_abs.trans (setIntegral_mono_set ?_
      (ae_of_all _ fun _ => abs_nonneg _)
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right y.2.2)).eventuallyLE)
    exact (hIcc ((hsi _).sub (hsi _))).abs
  -- The range of `T` has compact closure, by the Arzelà–Ascoli theorem.
  have hcpt : IsCompact (closure (range T)) := by
    refine ArzelaAscoli.isCompact_closure_range_of_equicontinuous (fun y => ?_) fun y =>
      ⟨closedBall 0 (|g₀| + C), isCompact_closedBall _ _, fun v => by
        rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
        exact hTb v y⟩
    have hlim : Tendsto (fun z : Icc x₀ x₁ => |Ψ z - Ψ y|) (𝓝 y) (𝓝 0) := by
      simpa using ((hΨc.domRestrict.tendsto y).sub_const (Ψ y)).abs
    refine Metric.equicontinuousAt_of_continuity_modulus _ hlim _
      (Eventually.of_forall fun z v => ?_)
    rw [Real.dist_eq, abs_sub_comm (Ψ z)]
    exact hmod v y z
  -- Schauder's fixed-point theorem on a large closed ball of `C([x₀, x₁])`.
  obtain ⟨ū, -, hū⟩ := schauderFixedPoint_closedConvex_continuousOn
    (C := closedBall (0 : C(Icc x₀ x₁, ℝ)) (|g₀| + C)) isClosed_closedBall
    (convex_closedBall _ _) (nonempty_closedBall.2 hR) hTc.continuousOn
    (fun v _ => mem_closedBall_zero_iff.2 ((ContinuousMap.norm_le _ hR).2
      fun y => by rw [Real.norm_eq_abs]; exact hTb v y))
    (hcpt.of_isClosed_subset isClosed_closure (closure_mono (image_subset_range _ _)))
  exact ⟨ū, fun y => by rw [← hT ū y, hū]⟩

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
  obtain ⟨ū, hū⟩ := exists_eq_add_intervalIntegral_slope hx hlam g₀ g₁ hcm hcM hlim hG
  obtain ⟨u, hrep, htr, hweak⟩ :=
    exists_w1p_intervalRepresentativeL_eq (p := p) hx hlam (hcm ū)
      ((hcM ū).mono fun _ h => h.1) hf hF g₀ g₁
  have hū' : W1p.intervalRepresentativeL hx u = ū := by
    ext y
    exact (hrep y).trans (hū y).symm
  refine ⟨u, htr, fun φ => ?_⟩
  rw [← hweak φ]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_ae_eq_intervalRepresentativeL hx u] with t ht
  rw [ht, hū']

end TauCeti.PDE

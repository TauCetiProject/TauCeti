/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Inv
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

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
`λ ≤ aₙ`, the derivatives of the solutions converge in `L¹`. This is the continuity needed to
solve quasilinear problems by a fixed-point argument.

## Main declarations

* `TauCeti.PDE.intervalDirichletFluxConst`, `TauCeti.PDE.intervalDirichletSlope`: the flux
  constant `k` and the derivative `(k - G) / a` of the explicit solution.
* `TauCeti.PDE.intervalDirichletSolution`: the explicit solution `g₀ + ∫_{x₀}^x (k - G) / a`, as a
  continuous function on `[x₀, x₁]`.
* `TauCeti.PDE.tendsto_integral_abs_intervalDirichletSlope_sub`: continuous dependence of the
  derivative on the coefficient.
* `TauCeti.PDE.exists_w1p_intervalRepresentativeL_eq`: the explicit solution, with its continuous
  representative.
* `TauCeti.PDE.exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq`: the linear problem
  `-(a u' + F)' = f` with prescribed endpoint values has a solution in `W^{1,p}(x₀, x₁)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4 (one-dimensional boundary value problems).
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

/-- For `λ ≤ a ≤ M` the flux constant is bounded by `M / (x₁ - x₀) (|g₁ - g₀| + ‖G‖₁ / λ)`. -/
theorem abs_intervalDirichletFluxConst_le (hx : x₀ < x₁) (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    |intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a| ≤
      M / (x₁ - x₀) * (|g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam) := by
  have hla := haM.mono fun _ h => h.1
  have hM : 0 < M := by
    have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by simp [hx])
    obtain ⟨t, ht⟩ := haM.exists
    linarith [ht.1, ht.2]
  -- Since `a ≤ M`, the integral of `1 / a` is at least `(x₁ - x₀) / M > 0`.
  have hc : (x₁ - x₀) / M ≤ ∫ t in Ioo x₀ x₁, (a t)⁻¹ := by
    have h := measureReal_univ_div_le_integral_inv (integrable_inv_of_le hlam ha hla)
      (haM.mono fun t ht => ⟨hlam.trans_le ht.1, ht.2⟩)
    rwa [measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le hx.le] at h
  have hL : 0 < x₁ - x₀ := sub_pos.2 hx
  have hc0 : 0 < ∫ t in Ioo x₀ x₁, (a t)⁻¹ := (div_pos hL hM).trans_le hc
  have hR : |∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t| ≤ (∫ t in Ioo x₀ x₁, |G t|) / lam := by
    refine abs_integral_le_integral_abs.trans ?_
    rw [div_eq_inv_mul, ← integral_const_mul]
    refine integral_mono_ae
      (hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable
        (ae_norm_inv_le_inv_of_le hlam hla)).abs
      (hG.abs.const_mul _) ?_
    filter_upwards [ae_norm_inv_le_inv_of_le hlam hla] with t ht
    rw [Real.norm_eq_abs] at ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  rw [intervalDirichletFluxConst, abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
  calc |g₁ - g₀ + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t|
      ≤ |g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam := (abs_add_le _ _).trans (by gcongr)
    _ = M / (x₁ - x₀) * (|g₁ - g₀| + (∫ t in Ioo x₀ x₁, |G t|) / lam) * ((x₁ - x₀) / M) := by
        field_simp
    _ ≤ _ := by gcongr

/-- For `λ ≤ a`, a bound `|k| ≤ K` on the flux constant gives `|(k - G) / a| ≤ λ⁻¹ (K + |G|)`. -/
theorem ae_abs_intervalDirichletSlope_le (hlam : 0 < lam) {g₀ g₁ K : ℝ}
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hK : |intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a| ≤ K) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      |intervalDirichletSlope x₀ x₁ g₀ g₁ G a t| ≤ lam⁻¹ * (K + |G t|) := by
  filter_upwards [ae_norm_inv_le_inv_of_le hlam hla] with t ht
  rw [Real.norm_eq_abs] at ht
  rw [intervalDirichletSlope, abs_mul]
  exact mul_le_mul ht ((abs_sub _ _).trans (by gcongr)) (abs_nonneg _)
    (inv_nonneg.2 hlam.le)

/-- The derivative `(k - G) / a` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_intervalDirichletSlope {g₀ g₁ : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    AEStronglyMeasurable (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (volume.restrict (Ioo x₀ x₁)) :=
  ha.aemeasurable.inv.aestronglyMeasurable.mul (aestronglyMeasurable_const.sub hG.1)

/-- For `λ ≤ a`, the derivative `(k - G) / a` is integrable on `(x₀, x₁)`. -/
theorem integrableOn_intervalDirichletSlope (hlam : 0 < lam) (g₀ g₁ : ℝ)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hG : IntegrableOn G (Ioo x₀ x₁)) :
    IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G a) (Ioo x₀ x₁) :=
  (((integrable_const _).add hG.abs).const_mul lam⁻¹).mono'
    (aestronglyMeasurable_intervalDirichletSlope ha hG)
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
  have : NeZero (volume.restrict (Ioo x₀ x₁)) := ⟨by simp [hx]⟩
  have hc0 := (integral_inv_pos_of_le hlam ha hla).ne'
  have h2 : Integrable (fun t => (a t)⁻¹ * G t) (volume.restrict (Ioo x₀ x₁)) :=
    hG.bdd_mul ha.aemeasurable.inv.aestronglyMeasurable (ae_norm_inv_le_inv_of_le hlam hla)
  simp only [intervalDirichletSlope, mul_sub]
  rw [integral_sub ((integrable_inv_of_le hlam ha hla).mul_const _) h2, integral_mul_const,
    intervalDirichletFluxConst, mul_div_cancel₀ _ hc0]
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
  have : NeZero (volume.restrict (Ioo x₀ x₁)) := ⟨by simp [hx]⟩
  have hinv : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      Tendsto (fun n => (an n t)⁻¹) atTop (𝓝 (a t)⁻¹) := by
    filter_upwards [hlim, hla] with t ht hat
    exact ht.inv₀ (hlam.trans_le hat).ne'
  -- The two integrals defining the flux constant converge by dominated convergence.
  have hc' : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (an n t)⁻¹) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (a t)⁻¹)) :=
    tendsto_integral_of_dominated_convergence (fun _ => lam⁻¹)
      (fun n => (han n).aemeasurable.inv.aestronglyMeasurable) (integrable_const _)
      (fun n => ae_norm_inv_le_inv_of_le hlam (hanl n)) hinv
  have hd : Tendsto (fun n => ∫ t in Ioo x₀ x₁, (an n t)⁻¹ * G t) atTop
      (𝓝 (∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => lam⁻¹ * ‖G t‖)
      (fun n => (han n).aemeasurable.inv.aestronglyMeasurable.mul hG.1)
      (hG.norm.const_mul _) (fun n => ?_) ?_
    · filter_upwards [ae_norm_inv_le_inv_of_le hlam (hanl n)] with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    · filter_upwards [hinv] with t ht
      exact ht.mul_const _
  have hk : Tendsto (fun n => intervalDirichletFluxConst x₀ x₁ g₀ g₁ G (an n)) atTop
      (𝓝 (intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a)) :=
    (tendsto_const_nhds.add hd).div hc' (integral_inv_pos_of_le hlam ha hla).ne'
  -- The derivatives converge almost everywhere, under a common integrable bound: the convergent
  -- flux constants are bounded by some `K`.
  obtain ⟨K, hK⟩ := hk.abs.bddAbove_range
  set k := intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a
  have h0 := tendsto_integral_of_dominated_convergence
    (fun t => lam⁻¹ * (K + |G t|) + lam⁻¹ * (|k| + |G t|))
    (F := fun n t =>
      |intervalDirichletSlope x₀ x₁ g₀ g₁ G (an n) t - intervalDirichletSlope x₀ x₁ g₀ g₁ G a t|)
    (f := fun _ => 0)
    (fun n => ((aestronglyMeasurable_intervalDirichletSlope (han n) hG).sub
      (aestronglyMeasurable_intervalDirichletSlope ha hG)).norm)
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

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {f F : ℝ → ℝ}

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
  refine MemLp.of_le hb
    (aestronglyMeasurable_intervalDirichletSlope ha (hG.integrable Fact.out)) ?_
  filter_upwards [ae_abs_intervalDirichletSlope_le hlam hla le_rfl] with t ht
  have hK0 : 0 ≤ K + ‖G t‖ := by positivity
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hlam.le) hK0),
    Real.norm_eq_abs]
  exact ht

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
  set Φ : ℝ → ℝ := fun t => ∫ s in x₀..t, f s
  set G : ℝ → ℝ := fun t => Φ t + F t
  set s := intervalDirichletSlope x₀ x₁ g₀ g₁ G a with hsdef
  have hΦc : ContinuousOn Φ (Icc x₀ x₁) :=
    intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)
  have hΦp : MemLp Φ p (volume.restrict (Ioo x₀ x₁)) :=
    hΦc.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self p
  have hF1 : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  have hGp : MemLp G p (volume.restrict (Ioo x₀ x₁)) := hΦp.add hF
  have hG : IntegrableOn G (Ioo x₀ x₁) := hGp.integrable Fact.out
  have hsp : MemLp s p (volume.restrict (Ioo x₀ x₁)) :=
    memLp_intervalDirichletSlope hlam g₀ g₁ ha hla hGp
  have hsI : IntervalIntegrable s volume x₀ x₁ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2 (hsp.integrable Fact.out)
  -- The candidate `P = g₀ + ∫_{x₀}^x s` is absolutely continuous with derivative `s`.
  set P : ℝ → ℝ := fun y => g₀ + ∫ t in x₀..y, s t
  have hP : AbsolutelyContinuousOnInterval P x₀ x₁ :=
    (contDiffOn_const.absolutelyContinuousOnInterval).add
      (hsI.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hdP : deriv P =ᵐ[volume.restrict (Ioo x₀ x₁)] s := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hsI.ae_hasDerivAt_integral] with t ht htI
    exact ((ht (by rw [uIcc_of_le hx.le]; exact Ioo_subset_Icc_self htI) x₀
      left_mem_uIcc).const_add g₀).deriv
  obtain ⟨u, hu, hgu⟩ := hP.exists_w1p_value_gradient_ae_eq (hsp.ae_eq hdP.symm)
  let w : C(Icc x₀ x₁, ℝ) := intervalDirichletSolution hx.le g₀ g₁ (hsp.integrable Fact.out)
  have hrep : W1p.intervalRepresentativeL hx u = w := by
    refine (W1p.intervalRepresentativeL_eq_iff hx u w).2 ?_
    filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht, projIcc_of_mem hx.le (Ioo_subset_Icc_self hmem)]
    rfl
  refine ⟨u, fun y => by rw [hrep]; rfl, ?_, fun φ => ?_⟩
  · rw [W1p.intervalTraceL_apply, hrep]
    exact Prod.ext (intervalDirichletSolution_left ..)
      (intervalDirichletSolution_right hx hlam g₀ g₁ ha hla hG _)
  -- Weak form: the flux `a u' + F` is `k - Φ`, and `Φ` is a primitive of `f`.
  have hdφ : Continuous (deriv φ) := φ.contDiff.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := hdφ.bounded_above_of_compact_support φ.hasCompactSupport.deriv
  set k := intervalDirichletFluxConst x₀ x₁ g₀ g₁ G a
  have hflux : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), a t * W1p.gradient u t * deriv φ t =
      (k - Φ t) * deriv φ t - F t * deriv φ t := by
    filter_upwards [hgu, hdP, hla] with t h1 h2 h3
    rw [h1, h2, hsdef, intervalDirichletSlope, mul_inv_cancel_left₀ (hlam.trans_le h3).ne']
    ring
  -- `k - Φ` has weak derivative `-f`; both pairings vanish off `(x₀, x₁)`.
  have hw := (TauCeti.hasWeakLineDerivOn_const (μ := volume) (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩)
    (v := (1 : ℝ)) k).sub (TauCeti.hasWeakLineDerivOn_intervalIntegral_left hf)
  have he : ∫ t in Ioo x₀ x₁, (k - Φ t) * deriv φ t = ∫ t in Ioo x₀ x₁, f t * φ t := by
    have hφ0 : ∀ t ∉ Ioo x₀ x₁, φ t = 0 := fun t ht => φ.zero_on_compl ht
    have hφ'0 : ∀ t ∉ Ioo x₀ x₁, deriv φ t = 0 := fun t ht =>
      Function.notMem_support.1 fun h => ht (φ.tsupport_subset (support_deriv_subset h))
    have h := hw.integral_lineDeriv_smul_eq_neg_integral_smul φ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Ioo x₀ x₁)
        fun t ht => by simp [hφ'0 t ht],
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Ioo x₀ x₁)
        fun t ht => by simp [hφ0 t ht]] at h
    simpa [Φ, mul_comm, integral_neg] using h
  have hint1 : IntegrableOn (fun t => (k - Φ t) * deriv φ t) (Ioo x₀ x₁) :=
    ((continuousOn_const.sub hΦc).mul hdφ.continuousOn).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun t => F t * deriv φ t) (Ioo x₀ x₁) :=
    hF1.mul_bdd hdφ.aestronglyMeasurable (ae_of_all _ hC)
  rw [integral_congr_ae hflux, integral_sub hint1 hint2, he]

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

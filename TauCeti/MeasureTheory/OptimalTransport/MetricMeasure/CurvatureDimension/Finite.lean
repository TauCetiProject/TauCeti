/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.OptimalTransport.DynamicPlan
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.Basic
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.DistortionCoefficient
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.RenyiEntropy
import TauCeti.Analysis.Convex.McCannCondition
import TauCeti.Data.EReal.Operations
import TauCeti.MeasureTheory.OptimalTransport.Brenier
import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy.DisplacementConvexity
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space

/-!
# The curvature-dimension condition `CD(K, N)`

Let `M` be a metric-measure space (`TauCeti.MetricMeasureSpace`): a complete separable metric
space `X` with its Borel structure and a reference measure `m` finite on bounded sets. For a
curvature bound `K : ℝ` and a dimension bound `N ≥ 1`, `M` satisfies Sturm's
*curvature-dimension condition* `CD(K, N)` when `m` has full support and, for any two probability
laws `μ₀ = ρ₀ m` and `μ₁ = ρ₁ m` with bounded support, some quadratic optimal dynamic plan `η`
from `μ₀` to `μ₁`, with laws `μ_t = (e_t)_# η`, satisfies for every `t ∈ [0, 1]` and every
`N' ≥ N`

`S_{N'}(μ_t | m) ≤ -∫ [τ_{K,N'}^{(1-t)}(d(γ₀, γ₁)) ρ₀(γ₀)^{-1/N'} +
  τ_{K,N'}^{(t)}(d(γ₀, γ₁)) ρ₁(γ₁)^{-1/N'}] dη(γ)`.

Here `S_{N'}(μ | m) = -∫ ρ^{1-1/N'} dm` is the Rényi entropy (`TauCeti.renyiEntropy`), taken over
the absolutely continuous part of `μ`, and `τ_{K,N'}` is the distortion coefficient
`TauCeti.distortionTau`. This is the synthetic form of the bounds `Ric ≥ K` and `dim ≤ N`: the
coefficients compare the contraction of volume along the transport with the model space of
constant curvature `K / (N - 1)`. The quantification over all `N' ≥ N` follows Sturm and makes the
condition weaker as `N` grows; the condition weakens as `K` decreases since the coefficients
increase with the curvature bound (`TauCeti.MetricMeasureSpace.CurvatureDimension.mono`).

The endpoint laws are those of Sturm's space `P_∞(X, m)`: absolutely continuous with respect to
`m`, with bounded support. Sturm asks for an optimal coupling `q` and a geodesic `(μ_t)` of such
laws, integrating the right side against `q`. Here, as in the dynamic formulation of
Cavalletti–Mondino, one dynamic plan concentrated on constant-speed geodesics carries both: its
endpoint law is the coupling and its time marginals are the geodesic. The plan is not required to
be unique or to be selected measurably in the endpoints, and the intermediate laws are not
required to be absolutely continuous: as in `TauCeti.renyiEntropy`, the entropy ignores their
singular part.

In the flat case the coefficients are `τ_{0,N'}^{(s)}(θ) = s`, and since `μ₀ ≪ m` the right side
is `(1 - t) S_{N'}(μ₀ | m) + t S_{N'}(μ₁ | m)`
(`TauCeti.renyiEntropy_eq_neg_lintegral_rpow_neg`). So `CD(0, N)` is the convexity of every
Rényi entropy `S_{N'}`, `N' ≥ N`, along a common optimal dynamic plan
(`TauCeti.MetricMeasureSpace.curvatureDimension_zero_iff`).

On a real inner product space of finite dimension `n ≥ 1` with an additive Haar measure, the
Rényi integrand `U(r) = -r^{1-1/N'}` satisfies McCann's condition for `N' ≥ n`: here
`sⁿ U(s⁻ⁿ) = -s^{n/N'}` is convex and nonincreasing. McCann's displacement convexity
(`TauCeti.internalEnergy_map_smul_add_smul_gradient_le`) along the Brenier interpolation therefore
gives `CD(0, N)` for every `N ≥ n`, and hence `CD(K, N)` for every `K ≤ 0`
(`TauCeti.MetricMeasureSpace.curvatureDimension_of_nonpos_of_finrank_le`). Conversely, for
`N ≥ 1`, `CD(0, N)` forces `N ≥ n`, already on a finite-dimensional real normed space with an
additive Haar measure: transporting the uniform law on the unit ball to the uniform
law on a ball of radius `δ`, the law at time `1 / 2` is carried by the ball of radius
`1 / 2 + 3 δ / 2`, so Hölder's bound `TauCeti.neg_rpow_mul_rpow_le_renyiEntropy` and the convexity
inequality give `1 / 2 ≤ (1 / 2 + 3 δ / 2)^{n/N}`; letting `δ → 0` gives `n ≤ N`. Thus Haar
measure satisfies `CD(0, N)` exactly when `N ≥ n`
(`TauCeti.MetricMeasureSpace.curvatureDimension_zero_iff_finrank_le`).

## Main definitions

* `TauCeti.MetricMeasureSpace.CurvatureDimension M K N`: the curvature-dimension condition
  `CD(K, N)` of the metric-measure space `M`.

## Main statements

* `TauCeti.MetricMeasureSpace.CurvatureDimension.mono`: `CD(K, N)` implies `CD(K', N')` for
  `K' ≤ K` and `N ≤ N'`.
* `TauCeti.MetricMeasureSpace.curvatureDimension_zero_iff`: `CD(0, N)` is the convexity of the
  Rényi entropies `S_{N'}`, `N' ≥ N`, along a common optimal dynamic plan.
* `TauCeti.MetricMeasureSpace.curvatureDimension_of_nonpos_of_finrank_le`: Haar measure on a real
  inner product space of dimension `n ≥ 1` satisfies `CD(K, N)` for `K ≤ 0` and `N ≥ n`.
* `TauCeti.MetricMeasureSpace.finrank_le_of_curvatureDimension_zero`,
  `TauCeti.MetricMeasureSpace.curvatureDimension_zero_iff_finrank_le`: for `N ≥ 1`, Haar measure
  on a real normed space of dimension `n` satisfies `CD(0, N)` only for `N ≥ n`, and, on an inner
  product space with `n ≥ 1`, exactly then.

## References

* K.-T. Sturm, *On the geometry of metric measure spaces. II*, Acta Math. 196 (2006), 133–177,
  Definition 1.3 and Proposition 1.6.
* F. Cavalletti and A. Mondino, *Optimal maps in essentially non-branching spaces*, Commun.
  Contemp. Math. 19 (2017), 1750007, §2.
* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapters 17 and 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Module Metric
open scoped ENNReal unitInterval Gradient

namespace TauCeti

namespace MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] {M : MetricMeasureSpace X} {K K' N N' : ℝ}

/-- The **curvature-dimension condition** `CD(K, N)` of Sturm for the metric-measure space `M`:
the reference measure `m` has full support, and any two probability laws `μ₀ = ρ₀ m`,
`μ₁ = ρ₁ m` with bounded support are joined by a quadratic optimal dynamic plan `η` such that, for
every time `t` and every `N' ≥ N`, the Rényi entropy of the law `μ_t` at time `t` satisfies
`S_{N'}(μ_t | m) ≤ -∫ [τ_{K,N'}^{(1-t)}(d(γ₀, γ₁)) ρ₀(γ₀)^{-1/N'} +
τ_{K,N'}^{(t)}(d(γ₀, γ₁)) ρ₁(γ₁)^{-1/N'}] dη(γ)`.

It is meaningful for `N ≥ 1`. -/
structure CurvatureDimension (M : MetricMeasureSpace X) (K N : ℝ) : Prop where
  /-- The reference measure has full support. -/
  support_eq_univ : M.support = univ
  /-- Any two absolutely continuous laws with bounded support are joined by a quadratic optimal
  dynamic plan along which the Rényi entropies satisfy the distorted convexity inequality. -/
  exists_isQuadraticOptimalDynamicPlan_renyiEntropy_le : ∀ ⦃μ₀ μ₁ : ProbabilityMeasure X⦄,
    (μ₀ : Measure X) ≪ M.reference → (μ₁ : Measure X) ≪ M.reference →
    Bornology.IsBounded (μ₀ : Measure X).support → Bornology.IsBounded (μ₁ : Measure X).support →
    ∃ η : Measure C(I, X), η.IsQuadraticOptimalDynamicPlan μ₀ μ₁ ∧ ∀ t : I, ∀ N', N ≤ N' →
      renyiEntropy N' M.reference (η.timeMarginal t) ≤
        -((∫⁻ γ, distortionTau K N' (1 - t) (dist (γ 0) (γ 1)) *
              (μ₀ : Measure X).rnDeriv M.reference (γ 0) ^ (-N'⁻¹) +
            distortionTau K N' t (dist (γ 0) (γ 1)) *
              (μ₁ : Measure X).rnDeriv M.reference (γ 1) ^ (-N'⁻¹) ∂η : ℝ≥0∞) : EReal)

/-- `CD(K, N)` implies `CD(K', N')` whenever `K' ≤ K` and `N ≤ N'`: the distortion coefficients
increase with the curvature bound, and the condition already quantifies over all larger
dimension bounds. -/
theorem CurvatureDimension.mono (h : M.CurvatureDimension K N) (hK : K' ≤ K) (hN : N ≤ N') :
    M.CurvatureDimension K' N' := by
  refine ⟨h.support_eq_univ, fun μ₀ μ₁ h₀ h₁ hb₀ hb₁ ↦ ?_⟩
  obtain ⟨η, hη, hle⟩ := h.exists_isQuadraticOptimalDynamicPlan_renyiEntropy_le h₀ h₁ hb₀ hb₁
  refine ⟨η, hη, fun t N'' hN'' ↦ (hle t N'' (hN.trans hN'')).trans ?_⟩
  rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine lintegral_mono fun γ ↦ add_le_add (mul_le_mul_left ?_ _) (mul_le_mul_left ?_ _)
  · exact distortionTau_left_monotone (sub_nonneg.2 t.2.2) (sub_le_self _ t.2.1) hK
  · exact distortionTau_left_monotone t.2.1 t.2.2 hK

/-- In the flat case, the right side of the curvature-dimension inequality is the convex
combination of the endpoint Rényi entropies. -/
private theorem neg_lintegral_distortionTau_zero {μ₀ μ₁ : ProbabilityMeasure X}
    {η : Measure C(I, X)} (hη : η.IsQuadraticOptimalDynamicPlan μ₀ μ₁)
    (h₀ : (μ₀ : Measure X) ≪ M.reference) (h₁ : (μ₁ : Measure X) ≪ M.reference) (hN' : 0 < N')
    (t : I) :
    -((∫⁻ γ, distortionTau 0 N' (1 - t) (dist (γ 0) (γ 1)) *
          (μ₀ : Measure X).rnDeriv M.reference (γ 0) ^ (-N'⁻¹) +
        distortionTau 0 N' t (dist (γ 0) (γ 1)) *
          (μ₁ : Measure X).rnDeriv M.reference (γ 1) ^ (-N'⁻¹) ∂η : ℝ≥0∞) : EReal) =
      ((1 - t : ℝ) : EReal) * renyiEntropy N' M.reference μ₀ +
        (t : ℝ) * renyiEntropy N' M.reference μ₁ := by
  have hf (μ : Measure X) : Measurable fun x ↦ μ.rnDeriv M.reference x ^ (-N'⁻¹) :=
    (Measure.measurable_rnDeriv _ _).pow_const _
  have heval (μ : Measure X) (s : I) :
      ∫⁻ γ, μ.rnDeriv M.reference (γ s) ^ (-N'⁻¹) ∂η =
        ∫⁻ x, μ.rnDeriv M.reference x ^ (-N'⁻¹) ∂(η.timeMarginal s) := by
    rw [Measure.timeMarginal_def, lintegral_map (hf μ) (ContinuousMap.measurable_eval s)]
  have hf₀ : Measurable fun γ : C(I, X) ↦ (μ₀ : Measure X).rnDeriv M.reference (γ 0) ^ (-N'⁻¹) :=
    (hf _).comp (ContinuousMap.measurable_eval 0)
  have hf₁ : Measurable fun γ : C(I, X) ↦ (μ₁ : Measure X).rnDeriv M.reference (γ 1) ^ (-N'⁻¹) :=
    (hf _).comp (ContinuousMap.measurable_eval 1)
  -- The integral against `η` splits into integrals against the endpoint laws.
  have hint : ∫⁻ γ, ENNReal.ofReal (1 - t) * (μ₀ : Measure X).rnDeriv M.reference (γ 0) ^ (-N'⁻¹) +
        ENNReal.ofReal t * (μ₁ : Measure X).rnDeriv M.reference (γ 1) ^ (-N'⁻¹) ∂η =
      ENNReal.ofReal (1 - t) * ∫⁻ x, (μ₀ : Measure X).rnDeriv M.reference x ^ (-N'⁻¹) ∂μ₀ +
        ENNReal.ofReal t * ∫⁻ x, (μ₁ : Measure X).rnDeriv M.reference x ^ (-N'⁻¹) ∂μ₁ := by
    rw [lintegral_add_left (hf₀.const_mul _), lintegral_const_mul _ hf₀,
      lintegral_const_mul _ hf₁, heval, heval, hη.timeMarginal_zero, hη.timeMarginal_one]
  simp only [distortionTau_zero_left]
  rw [hint, renyiEntropy_eq_neg_lintegral_rpow_neg hN' h₀,
    renyiEntropy_eq_neg_lintegral_rpow_neg hN' h₁]
  exact EReal.neg_coe_ennreal_ofReal_mul_add_ofReal_mul (sub_nonneg.2 t.2.2) t.2.1 _ _

/-- **The flat curvature-dimension condition.** For `N > 0`, `CD(0, N)` holds exactly when the
reference measure has full support and any two absolutely continuous laws with bounded support
are joined by a quadratic optimal dynamic plan along which every Rényi entropy `S_{N'}`,
`N' ≥ N`, is convex:
`S_{N'}(μ_t | m) ≤ (1 - t) S_{N'}(μ₀ | m) + t S_{N'}(μ₁ | m)`. -/
theorem curvatureDimension_zero_iff (hN : 0 < N) :
    M.CurvatureDimension 0 N ↔ M.support = univ ∧
      ∀ ⦃μ₀ μ₁ : ProbabilityMeasure X⦄,
        (μ₀ : Measure X) ≪ M.reference → (μ₁ : Measure X) ≪ M.reference →
        Bornology.IsBounded (μ₀ : Measure X).support →
        Bornology.IsBounded (μ₁ : Measure X).support →
        ∃ η : Measure C(I, X), η.IsQuadraticOptimalDynamicPlan μ₀ μ₁ ∧ ∀ t : I, ∀ N', N ≤ N' →
          renyiEntropy N' M.reference (η.timeMarginal t) ≤
            ((1 - t : ℝ) : EReal) * renyiEntropy N' M.reference μ₀ +
              (t : ℝ) * renyiEntropy N' M.reference μ₁ := by
  refine ⟨fun h ↦ ⟨h.support_eq_univ, fun μ₀ μ₁ h₀ h₁ hb₀ hb₁ ↦ ?_⟩,
    fun h ↦ ⟨h.1, fun μ₀ μ₁ h₀ h₁ hb₀ hb₁ ↦ ?_⟩⟩
  · obtain ⟨η, hη, hle⟩ := h.exists_isQuadraticOptimalDynamicPlan_renyiEntropy_le h₀ h₁ hb₀ hb₁
    exact ⟨η, hη, fun t N' hN' ↦ (hle t N' hN').trans_eq
      (neg_lintegral_distortionTau_zero hη h₀ h₁ (hN.trans_le hN') t)⟩
  · obtain ⟨η, hη, hle⟩ := h.2 h₀ h₁ hb₀ hb₁
    exact ⟨η, hη, fun t N' hN' ↦ (hle t N' hN').trans_eq
      (neg_lintegral_distortionTau_zero hη h₀ h₁ (hN.trans_le hN') t).symm⟩

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : MetricMeasureSpace E} [M.reference.IsAddHaarMeasure]

/-- The uniform law on a closed ball of positive radius about `0`. -/
private theorem exists_coe_eq_cond_closedBall {r : ℝ} (hr : 0 < r) :
    ∃ μ : ProbabilityMeasure E, (μ : Measure E) = M.reference[|closedBall 0 r] :=
  ⟨⟨_, cond_isProbabilityMeasure_of_finite (measure_closedBall_pos _ _ hr).ne'
    (M.finite_bounded _ isBounded_closedBall).ne⟩, rfl⟩

/-- Since `m(B_r)^{1/N} = r^{n/N} m(B_1)^{1/N}` for an additive Haar measure `m` on a space of
dimension `n`, the bound `c m(B_1)^{1/N} ≤ m(B_r)^{1/N}` gives `c ≤ r^{n/N}`. -/
private theorem le_rpow_of_ofReal_mul_le_measure_closedBall_rpow {c r : ℝ} (hr : 0 < r)
    (hN : 0 < N)
    (h : ENNReal.ofReal c * M.reference (closedBall 0 1) ^ N⁻¹ ≤
      M.reference (closedBall 0 r) ^ N⁻¹) :
    c ≤ r ^ ((finrank ℝ E : ℝ) / N) := by
  have h₀ : M.reference (closedBall 0 1) ^ N⁻¹ ≠ 0 :=
    (ENNReal.rpow_pos (measure_closedBall_pos _ _ one_pos)
      (M.finite_bounded _ isBounded_closedBall).ne).ne'
  have hfin : M.reference (closedBall 0 1) ^ N⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hN.le) (M.finite_bounded _ isBounded_closedBall).ne
  rw [Measure.addHaar_closedBall' _ _ hr.le,
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hN.le)] at h
  have h' := (ENNReal.mul_le_mul_iff_left h₀ hfin).1 h
  -- `ofReal (rⁿ)^(1/N) = ofReal (r^(n/N))`.
  have hpow : ENNReal.ofReal (r ^ finrank ℝ E) ^ N⁻¹ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / N)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hN.le), ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le, div_eq_mul_inv]
  rwa [hpow, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h'

/-- Under `CD(0, N)` with `N ≥ 1`, transporting the uniform law on the unit ball to the uniform law
on the ball of radius `δ` gives `1 / 2 ≤ (1 / 2 + 3 δ / 2)^{n/N}`. At time `1 / 2` the law is
carried by the ball of radius `1 / 2 + 3 δ / 2`, which bounds its Rényi entropy below, while the
convexity inequality bounds it above by half the entropy of the uniform law on the unit ball. -/
private theorem half_le_rpow_of_curvatureDimension_zero (h : M.CurvatureDimension 0 N)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    1 / 2 ≤ (1 / 2 + 3 / 2 * δ) ^ ((finrank ℝ E : ℝ) / N) := by
  have hN₀ : 0 < N := one_pos.trans_le hN
  have hr : 0 < 1 / 2 + 3 / 2 * δ := by positivity
  obtain ⟨μ₀, hμ₀⟩ := exists_coe_eq_cond_closedBall (M := M) one_pos
  obtain ⟨μ₁, hμ₁⟩ := exists_coe_eq_cond_closedBall (M := M) hδ
  have hcarr {μ : ProbabilityMeasure E} {s : ℝ}
      (hμ : (μ : Measure E) = M.reference[|closedBall 0 s]) :
      ∀ᵐ x ∂(μ : Measure E), x ∈ closedBall (0 : E) s :=
    hμ ▸ ae_cond_mem measurableSet_closedBall
  have hbdd {μ : ProbabilityMeasure E} {s : ℝ}
      (hμ : (μ : Measure E) = M.reference[|closedBall 0 s]) :
      Bornology.IsBounded (μ : Measure E).support :=
    isBounded_closedBall.subset (Measure.support_subset_of_isClosed isClosed_closedBall (hcarr hμ))
  have hent {s : ℝ} (hs : 0 < s) : renyiEntropy N M.reference M.reference[|closedBall 0 s] =
      -((M.reference (closedBall 0 s) ^ N⁻¹ : ℝ≥0∞) : EReal) := by
    rw [ProbabilityTheory.cond]
    exact renyiEntropy_smul_restrict hN₀ measurableSet_closedBall
      (measure_closedBall_pos _ _ hs).ne' (M.finite_bounded _ isBounded_closedBall).ne
  obtain ⟨η, hη, hle⟩ := ((curvatureDimension_zero_iff hN₀).1 h).2 (hμ₀ ▸ cond_absolutelyContinuous)
    (hμ₁ ▸ cond_absolutelyContinuous) (hbdd hμ₀) (hbdd hμ₁)
  have : IsProbabilityMeasure η := hη.isProbabilityMeasure
  set t : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht : (t : ℝ) = 1 / 2 := rfl
  -- At time `1 / 2` almost every path is within `1 / 2 + 3 δ / 2` of `0`.
  have hcarr_t : η.timeMarginal t (closedBall (0 : E) (1 / 2 + 3 / 2 * δ))ᶜ = 0 := by
    have h := mem_ae_iff.1 (ae_timeMarginal_mem_closedBall hη.ae_mem_geodesicPaths
      (hη.timeMarginal_zero ▸ hcarr hμ₀) (hη.timeMarginal_one ▸ hcarr hμ₁) t)
    rwa [ht, show (1 - 1 / 2 : ℝ) * (1 + δ) + δ = 1 / 2 + 3 / 2 * δ by ring] at h
  have hmass : η.timeMarginal t univ = 1 := by
    simp [Measure.timeMarginal_apply η t MeasurableSet.univ]
  have hlow := neg_rpow_mul_rpow_le_renyiEntropy (m := M.reference) hN hcarr_t
  rw [hmass, ENNReal.one_rpow, mul_one] at hlow
  have hup := hle t N le_rfl
  rw [hμ₀, hμ₁, hent one_pos, hent hδ, ht, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hup
  -- Dropping the nonpositive entropy of the small ball leaves half that of the unit ball.
  have hhalf : ((1 / 2 : ℝ) : EReal) ≥ 0 := EReal.coe_nonneg.2 (by norm_num)
  have hdrop : ((1 / 2 : ℝ) : EReal) * -((M.reference (closedBall 0 δ) ^ N⁻¹ : ℝ≥0∞) : EReal) ≤
      0 := by
    rw [mul_neg, EReal.neg_le_zero]
    exact mul_nonneg hhalf (EReal.coe_ennreal_nonneg _)
  have hcoe : ((1 / 2 : ℝ) : EReal) = ((ENNReal.ofReal (1 / 2) : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have key := hlow.trans (hup.trans (add_le_of_nonpos_right hdrop))
  rw [mul_neg, hcoe, ← EReal.coe_ennreal_mul, EReal.neg_le_neg_iff,
    EReal.coe_ennreal_le_coe_ennreal_iff] at key
  exact le_rpow_of_ofReal_mul_le_measure_closedBall_rpow hr hN₀ key

/-- **`CD(0, N)` forces `N ≥ n` for Haar measure.** If an additive Haar reference measure on a
real normed space of finite dimension `n` satisfies `CD(0, N)` with `N ≥ 1`, then `N ≥ n`. -/
theorem finrank_le_of_curvatureDimension_zero (h : M.CurvatureDimension 0 N)
    (hN : 1 ≤ N) : (finrank ℝ E : ℝ) ≤ N := by
  have hlim : Filter.Tendsto (fun δ : ℝ ↦ (1 / 2 + 3 / 2 * δ) ^ ((finrank ℝ E : ℝ) / N))
      (nhdsWithin 0 (Ioi 0)) (nhds ((1 / 2 : ℝ) ^ ((finrank ℝ E : ℝ) / N))) := by
    have hc : Filter.Tendsto (fun δ : ℝ ↦ 1 / 2 + 3 / 2 * δ) (nhds 0) (nhds (1 / 2)) :=
      (by fun_prop : Continuous fun δ : ℝ ↦ 1 / 2 + 3 / 2 * δ).tendsto' 0 _ (by norm_num)
    exact (hc.rpow_const (.inl (by norm_num))).mono_left nhdsWithin_le_nhds
  have hge : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ ((finrank ℝ E : ℝ) / N) := by
    rw [Real.rpow_one]
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ ↦
      half_le_rpow_of_curvatureDimension_zero h hN hδ)
  exact (div_le_one (one_pos.trans_le hN)).1
    ((Real.rpow_le_rpow_left_iff_of_base_lt_one (by norm_num) (by norm_num)).1 hge)

end NormedSpace

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : MetricMeasureSpace E} [M.reference.IsAddHaarMeasure]

/-- **Haar measure satisfies `CD(0, N)` for `N ≥ n`.** On a real inner product space of finite
dimension `n ≥ 1`, an additive Haar reference measure satisfies `CD(0, N)` for every `N ≥ n`. The
dynamic plan is the Brenier interpolation, along which every Rényi entropy `S_{N'}`, `N' ≥ n`, is
convex by McCann's displacement convexity. -/
theorem curvatureDimension_zero_of_finrank_le [Nontrivial E] (hN : (finrank ℝ E : ℝ) ≤ N) :
    M.CurvatureDimension 0 N := by
  have hn : (1 : ℝ) ≤ finrank ℝ E := Nat.one_le_cast.2 finrank_pos
  refine (curvatureDimension_zero_iff (zero_lt_one.trans_le (hn.trans hN))).2
    ⟨by rw [support_def, Measure.support_eq_univ], fun μ₀ μ₁ h₀ h₁ hb₀ hb₁ ↦ ?_⟩
  -- Bounded supports give finite second moments, hence a finite quadratic transport cost.
  have hm (μ : ProbabilityMeasure E) (hb : Bornology.IsBounded (μ : Measure E).support) :
      HasFiniteMoment 2 (μ : Measure E) :=
    hasFiniteMoment_of_ae_mem_of_isBounded 0 hb Measure.support_mem_ae
  have hfin := transportCost_norm_sub_sq_div_two_ne_top (WassersteinSpace.mk μ₀ (hm μ₀ hb₀))
    (WassersteinSpace.mk μ₁ (hm μ₁ hb₁))
  simp only [WassersteinSpace.coe_mk] at hfin
  -- The Brenier map `∇u` from `μ₀` to `μ₁` induces the optimal plan.
  obtain ⟨u, hconv, -, hbot, hdiff, hT, hiff, -⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient h₀ hfin
  have hopt := isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two
    ((hiff (graphPlan (∇ fun x ↦ (u x).toReal) (μ₀ : Measure E))).2 rfl)
  refine ⟨(graphPlan (∇ fun x ↦ (u x).toReal) (μ₀ : Measure E)).map segmentPath,
    ⟨Measure.ae_mem_geodesicPaths_map_segmentPath _, by rwa [Measure.endpointLaw_map_segmentPath]⟩,
    fun t N' hN' ↦ ?_⟩
  have hν : (μ₁ : Measure E) = (μ₀ : Measure E).map (∇ fun x ↦ (u x).toReal) :=
    hT.toHasLaw.map_eq.symm
  have hμD : ∀ᵐ x ∂(μ₀ : Measure E), x ∈ interior {x | u x ≠ ⊤} :=
    hdiff.mono fun x hx ↦ mem_interior_iff_mem_nhds.2 hx.1
  have hN'₁ : 1 ≤ N' := hn.trans (hN.trans hN')
  -- Bounded supports have finite reference mass, so the endpoint entropies are finite.
  have hbot' (μ : ProbabilityMeasure E) (hb : Bornology.IsBounded (μ : Measure E).support) :
      renyiEntropy N' M.reference μ ≠ ⊥ :=
    renyiEntropy_ne_bot_of_measure_compl_eq_zero hN'₁ Measure.measure_compl_support
      (M.finite_bounded _ hb).ne
  have key := internalEnergy_map_smul_add_smul_gradient_le M.reference
    (U := fun r ↦ -(r * r ^ (-N'⁻¹))) (by simp)
    (convexOn_pow_mul_neg_mul_rpow_neg (zero_lt_one.trans_le hN'₁) (hN.trans hN'))
    (antitoneOn_pow_mul_neg_mul_rpow_neg (zero_lt_one.trans_le hN'₁)) hconv hbot h₀ hμD
    (by rw [← renyiEntropy_def]; exact hbot' μ₀ hb₀)
    (by rw [← renyiEntropy_def, ← hν]; exact hbot' μ₁ hb₁) ⟨t.2.1, t.2.2⟩
  rw [Measure.timeMarginal_map_segmentPath,
    map_graphPlan (measurable_gradient _).aemeasurable (by fun_prop), hν]
  simpa only [← renyiEntropy_def] using key

/-- **Haar measure satisfies `CD(K, N)` for `K ≤ 0` and `N ≥ n`.** On a real inner product space
of finite dimension `n ≥ 1`, an additive Haar reference measure satisfies `CD(K, N)` for every
`K ≤ 0` and `N ≥ n`. -/
theorem curvatureDimension_of_nonpos_of_finrank_le [Nontrivial E] (hK : K ≤ 0)
    (hN : (finrank ℝ E : ℝ) ≤ N) : M.CurvatureDimension K N :=
  (curvatureDimension_zero_of_finrank_le hN).mono hK le_rfl

/-- **Haar measure satisfies `CD(0, N)` exactly when `N ≥ n`.** On a real inner product space of
finite dimension `n ≥ 1`, an additive Haar reference measure satisfies `CD(0, N)`, for `N ≥ 1`, if
and only if `N ≥ n`. -/
theorem curvatureDimension_zero_iff_finrank_le [Nontrivial E] (hN : 1 ≤ N) :
    M.CurvatureDimension 0 N ↔ (finrank ℝ E : ℝ) ≤ N :=
  ⟨fun h ↦ finrank_le_of_curvatureDimension_zero h hN, curvatureDimension_zero_of_finrank_le⟩

end Euclidean

end MetricMeasureSpace

end TauCeti

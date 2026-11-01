/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.Basic
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.DistortionCoefficient
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.RenyiEntropy
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
public import TauCeti.Topology.MetricSpace.Length

/-!
# The curvature-dimension conditions `CD(K, N)` and `CD*(K, N)`

Let `M` be a metric-measure space (`TauCeti.MetricMeasureSpace`): a complete separable metric
space `X` with its Borel structure and a reference measure `m` finite on bounded sets. For a
curvature bound `K : ℝ` and a dimension bound `N`, Sturm's *curvature-dimension condition*
`CD(K, N)` compares the Rényi entropy `S_N(μ | m) = -∫ ρ^{1-1/N} dm`
(`TauCeti.renyiEntropy`) along Wasserstein geodesics with the model space of curvature
`K / (N - 1)` and dimension `N`. For a plan `q` on `X × X` whose marginals have densities `ρ₀`,
`ρ₁` with respect to `m`, and a family `β^{(s)}(θ)` of distortion coefficients, write

`T_β^{(t)}(q | m) = -∫ [β^{(1-t)}(d(x₀, x₁)) ρ₀(x₀)^{-1/N} + β^{(t)}(d(x₀, x₁)) ρ₁(x₁)^{-1/N}] dq`

(`TauCeti.distortedRenyiEntropy`). Then `M` satisfies `CD(K, N)` when `m` has full support and
any two laws `μ₀`, `μ₁` of finite second moment, absolutely continuous with respect to `m`, admit
an optimal coupling `q` for the quadratic cost and a `W₂`-geodesic `(μ_t)` of laws absolutely
continuous with respect to `m` such that

`S_{N'}(μ_t | m) ≤ T_{τ_{K,N'}}^{(t)}(q | m)` for all `t ∈ [0, 1]` and all `N' ≥ N`,

where `τ_{K,N'}` is the distortion coefficient `TauCeti.distortionTau`. The *reduced*
curvature-dimension condition `CD*(K, N)` of Bacher and Sturm is the same inequality with the
coefficient `σ_{K,N'}` (`TauCeti.distortionSigma`) in place of `τ_{K,N'}`. By theorems of Sturm and
of Bacher–Sturm, not formalized here, on an `n`-dimensional weighted Riemannian manifold both
conditions are equivalent to the lower bound `Ric + Hess V - dV ⊗ dV / (N - n) ≥ K` on the
Bakry–Émery Ricci tensor; on general metric-measure spaces they are two distinct predicates. Full
support follows the convention of `TauCeti.MetricMeasureSpace.CurvatureDimensionInfinity`; a
reference measure without full support is handled by passing to
`TauCeti.MetricMeasureSpace.supportSpace`.

The coefficients `τ_{K,N}^{(s)}(θ)` and `σ_{K,N}^{(s)}(θ)` are infinite at every time `s` once
`θ` exceeds `π √((N - 1) / K)`, respectively `π √(N / K)`, for `K > 0`. With this convention the
condition at time `t = 0` alone gives the **Bonnet–Myers diameter bound**: if two points were
farther apart, the uniform laws on two small balls about them would have
`T^{(0)}(q | m) = -∞` for every coupling `q`, while their Rényi entropy is finite.

## Main definitions

* `TauCeti.distortedRenyiEntropy β N m q t`: the distorted Rényi entropy `T_β^{(t)}(q | m)`.
* `TauCeti.MetricMeasureSpace.CurvatureDimension M K N`: the condition `CD(K, N)`.
* `TauCeti.MetricMeasureSpace.ReducedCurvatureDimension M K N`: the condition `CD*(K, N)`.

## Main statements

* `TauCeti.distortedRenyiEntropy_zero`: at time `0`, below the critical distance, the distorted
  Rényi entropy of `q` is the Rényi entropy of its first marginal, so both conditions hold with
  equality at the initial endpoint.
* `TauCeti.MetricMeasureSpace.CurvatureDimension.mono`,
  `TauCeti.MetricMeasureSpace.ReducedCurvatureDimension.mono`: the conditions weaken as `K`
  decreases and `N` increases.
* `TauCeti.MetricMeasureSpace.CurvatureDimension.dist_le`,
  `TauCeti.MetricMeasureSpace.CurvatureDimension.diam_univ_le`: the Bonnet–Myers bound
  `diam X ≤ π √((N - 1) / K)` under `CD(K, N)` with `K > 0` and `N > 0`.
* `TauCeti.MetricMeasureSpace.ReducedCurvatureDimension.dist_le`,
  `TauCeti.MetricMeasureSpace.ReducedCurvatureDimension.diam_univ_le`: the weaker bound
  `diam X ≤ π √(N / K)` under `CD*(K, N)` with `K > 0` and `N > 0`.

## References

* K.-T. Sturm, *On the geometry of metric measure spaces. II*, Acta Math. 196 (2006), 133–177,
  Definition 1.3 and the generalized Bonnet–Myers theorem.
* K. Bacher and K.-T. Sturm, *Localization and tensorization properties of the
  curvature-dimension condition for metric measure spaces*, J. Funct. Anal. 259 (2010), 28–56,
  for `CD*(K, N)` and its diameter bound.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal Real

namespace TauCeti

section DistortedRenyiEntropy

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {β β' : ℝ → ℝ → ℝ≥0∞} {N t : ℝ}
  {m : Measure X} {q : Measure (X × X)}

/-- The *distorted Rényi entropy* `T_β^{(t)}(q | m)` of a plan `q` on `X × X` relative to a
reference measure `m`, for a family `β s θ = β^{(s)}(θ)` of distortion coefficients indexed by a
time `s` and a distance `θ`:

`T_β^{(t)}(q | m) = -∫ [β^{(1-t)}(d(x₀, x₁)) ρ₀(x₀)^{-1/N} + β^{(t)}(d(x₀, x₁)) ρ₁(x₁)^{-1/N}] dq`,

where `ρ₀` and `ρ₁` are the densities with respect to `m` of the two marginals of `q`. With
`β = τ_{K,N}` it is the right-hand side of the condition `CD(K, N)`, with `β = σ_{K,N}` that of
`CD*(K, N)`. The integral is in `[0, ∞]`, so the value lies in `[-∞, 0]`. -/
def distortedRenyiEntropy (β : ℝ → ℝ → ℝ≥0∞) (N : ℝ) (m : Measure X) (q : Measure (X × X))
    (t : ℝ) : EReal :=
  -((∫⁻ z, (β (1 - t) (dist z.1 z.2) * q.fst.rnDeriv m z.1 ^ (-N⁻¹) +
    β t (dist z.1 z.2) * q.snd.rnDeriv m z.2 ^ (-N⁻¹)) ∂q : ℝ≥0∞) : EReal)

/-- The distorted Rényi entropy, unfolded. -/
theorem distortedRenyiEntropy_def :
    distortedRenyiEntropy β N m q t =
      -((∫⁻ z, (β (1 - t) (dist z.1 z.2) * q.fst.rnDeriv m z.1 ^ (-N⁻¹) +
        β t (dist z.1 z.2) * q.snd.rnDeriv m z.2 ^ (-N⁻¹)) ∂q : ℝ≥0∞) : EReal) :=
  (rfl)

/-- Larger distortion coefficients give a smaller distorted Rényi entropy. -/
theorem distortedRenyiEntropy_anti (h : ∀ θ, β (1 - t) θ ≤ β' (1 - t) θ)
    (h' : ∀ θ, β t θ ≤ β' t θ) :
    distortedRenyiEntropy β' N m q t ≤ distortedRenyiEntropy β N m q t := by
  rw [distortedRenyiEntropy_def, distortedRenyiEntropy_def, EReal.neg_le_neg_iff,
    EReal.coe_ennreal_le_coe_ennreal_iff]
  gcongr with z
  exacts [h _, h' _]

/-- **The distorted Rényi entropy at time `0`.** If `q`-almost every pair is below the critical
distance, in the sense that `β^{(1)} = 1` and `β^{(0)} = 0` there, and the first marginal of `q` is
absolutely continuous with respect to `m`, then `T_β^{(0)}(q | m) = S_N(q.fst | m)` is the Rényi
entropy of that marginal. So the curvature-dimension inequalities hold with equality at time `0`.
-/
theorem distortedRenyiEntropy_zero [q.fst.HaveLebesgueDecomposition m] (hN : 0 < N) (hq : q.fst ≪ m)
    (h₁ : ∀ᵐ z ∂q, β 1 (dist z.1 z.2) = 1) (h₀ : ∀ᵐ z ∂q, β 0 (dist z.1 z.2) = 0) :
    distortedRenyiEntropy β N m q 0 = renyiEntropy N m q.fst := by
  have hρ : Measurable fun x ↦ q.fst.rnDeriv m x ^ (-N⁻¹) :=
    (Measure.measurable_rnDeriv _ _).pow_const _
  rw [distortedRenyiEntropy_def, renyiEntropy_eq_neg_lintegral hN,
    lintegral_rnDeriv_mul hq hρ.aemeasurable,
    ← (show IsCoupling q q.fst q.snd from ⟨rfl, rfl⟩).lintegral_comp_fst hρ.aemeasurable]
  congr 2
  refine lintegral_congr_ae ?_
  filter_upwards [h₁, h₀] with z hz₁ hz₀
  rw [sub_zero, hz₁, hz₀, one_mul, zero_mul, add_zero]

end DistortedRenyiEntropy

namespace MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] {M : MetricMeasureSpace X} {K K' N N' : ℝ}

/-- The **curvature-dimension condition** `CD(K, N)` of Sturm for the metric-measure space `M`:
the reference measure `m` has full support, and any two laws `μ₀`, `μ₁` of finite second moment,
absolutely continuous with respect to `m`, admit an optimal coupling `q` for the quadratic cost and
a `W₂`-geodesic `(μ_t)` of laws absolutely continuous with respect to `m` along which
`S_{N'}(μ_t | m) ≤ T_{τ_{K,N'}}^{(t)}(q | m)` for every `t ∈ [0, 1]` and every `N' ≥ N`. Here
`S_{N'}` is the Rényi entropy and `T` the distorted Rényi entropy
(`TauCeti.distortedRenyiEntropy`) for the coefficient `τ_{K,N'}` (`TauCeti.distortionTau`).

The condition is meant for `N ≥ 1`, where the coefficients carry their geometric meaning. -/
structure CurvatureDimension (M : MetricMeasureSpace X) (K N : ℝ) : Prop where
  /-- The reference measure has full support. -/
  support_eq_univ : M.support = univ
  /-- Any two absolutely continuous laws of finite second moment are joined by an optimal
  coupling and a `W₂`-geodesic of absolutely continuous laws satisfying the distorted Rényi
  inequalities for all dimensions `N' ≥ N`. -/
  exists_isOptimalCoupling_isGeodesicSegment : ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
    ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    ∃ q : Measure (X × X), IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ ENNReal.toReal 2) q
        ((μ₀ : ProbabilityMeasure X) : Measure X) ((μ₁ : ProbabilityMeasure X) : Measure X) ∧
      ∃ γ : ℝ → WassersteinSpace 2 X, IsGeodesicSegment γ μ₀ μ₁ ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ((γ t : ProbabilityMeasure X) : Measure X) ≪ M.reference ∧
          ∀ N' ≥ N, renyiEntropy N' M.reference ((γ t : ProbabilityMeasure X) : Measure X) ≤
            distortedRenyiEntropy (distortionTau K N') N' M.reference q t

/-- The **reduced curvature-dimension condition** `CD*(K, N)` of Bacher and Sturm: the condition
`CD(K, N)` (`TauCeti.MetricMeasureSpace.CurvatureDimension`) with the distortion coefficient
`σ_{K,N'}` (`TauCeti.distortionSigma`) in place of `τ_{K,N'}`. That is, `m` has full support, and
any two laws `μ₀`, `μ₁` of finite second moment, absolutely continuous with respect to `m`, admit
an optimal coupling `q` for the quadratic cost and a `W₂`-geodesic `(μ_t)` of laws absolutely
continuous with respect to `m` along which `S_{N'}(μ_t | m) ≤ T_{σ_{K,N'}}^{(t)}(q | m)` for every
`t ∈ [0, 1]` and every `N' ≥ N`.

The condition is meant for `N ≥ 1`, where the coefficients carry their geometric meaning. -/
structure ReducedCurvatureDimension (M : MetricMeasureSpace X) (K N : ℝ) : Prop where
  /-- The reference measure has full support. -/
  support_eq_univ : M.support = univ
  /-- Any two absolutely continuous laws of finite second moment are joined by an optimal
  coupling and a `W₂`-geodesic of absolutely continuous laws satisfying the reduced distorted
  Rényi inequalities for all dimensions `N' ≥ N`. -/
  exists_isOptimalCoupling_isGeodesicSegment : ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
    ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    ∃ q : Measure (X × X), IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ ENNReal.toReal 2) q
        ((μ₀ : ProbabilityMeasure X) : Measure X) ((μ₁ : ProbabilityMeasure X) : Measure X) ∧
      ∃ γ : ℝ → WassersteinSpace 2 X, IsGeodesicSegment γ μ₀ μ₁ ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ((γ t : ProbabilityMeasure X) : Measure X) ≪ M.reference ∧
          ∀ N' ≥ N, renyiEntropy N' M.reference ((γ t : ProbabilityMeasure X) : Measure X) ≤
            distortedRenyiEntropy (distortionSigma K N') N' M.reference q t

/-- `CD(K, N)` implies `CD(K', N')` for `K' ≤ K` and `N ≤ N'`. -/
theorem CurvatureDimension.mono (h : M.CurvatureDimension K N) (hK : K' ≤ K) (hN : N ≤ N') :
    M.CurvatureDimension K' N' := by
  refine ⟨h.support_eq_univ, fun μ₀ μ₁ h₀ h₁ ↦ ?_⟩
  obtain ⟨q, hq, γ, hγ, hle⟩ := h.exists_isOptimalCoupling_isGeodesicSegment h₀ h₁
  refine ⟨q, hq, γ, hγ, fun t ht ↦ ⟨(hle t ht).1, fun N'' hN'' ↦ ?_⟩⟩
  refine ((hle t ht).2 N'' (hN.trans hN'')).trans (distortedRenyiEntropy_anti
    (fun θ ↦ distortionTau_left_monotone (sub_nonneg.2 ht.2) (sub_le_self _ ht.1) hK)
    (fun θ ↦ distortionTau_left_monotone ht.1 ht.2 hK))

/-- `CD*(K, N)` implies `CD*(K', N')` for `K' ≤ K` and `0 ≤ N ≤ N'`. -/
theorem ReducedCurvatureDimension.mono (h : M.ReducedCurvatureDimension K N) (hK : K' ≤ K)
    (hN : N ≤ N') (hN₀ : 0 ≤ N) : M.ReducedCurvatureDimension K' N' := by
  refine ⟨h.support_eq_univ, fun μ₀ μ₁ h₀ h₁ ↦ ?_⟩
  obtain ⟨q, hq, γ, hγ, hle⟩ := h.exists_isOptimalCoupling_isGeodesicSegment h₀ h₁
  refine ⟨q, hq, γ, hγ, fun t ht ↦ ⟨(hle t ht).1, fun N'' hN'' ↦ ?_⟩⟩
  have hN''₀ : 0 ≤ N'' := hN₀.trans (hN.trans hN'')
  refine ((hle t ht).2 N'' (hN.trans hN'')).trans (distortedRenyiEntropy_anti
    (fun θ ↦ distortionSigma_left_monotone (sub_nonneg.2 ht.2) (sub_le_self _ ht.1) hN''₀ hK)
    (fun θ ↦ distortionSigma_left_monotone ht.1 ht.2 hN''₀ hK))

/-- The uniform law `m[|B(x, r)]` on a ball of positive radius about a point of the support of a
metric-measure space, as an element of `P₂(X)`. -/
private theorem exists_coe_eq_cond_ball {x : X} (hx : x ∈ M.support) {r : ℝ} (hr : 0 < r) :
    ∃ μ : WassersteinSpace 2 X,
      ((μ : ProbabilityMeasure X) : Measure X) = M.reference[|ball x r] := by
  have hpos : M.reference (ball x r) ≠ 0 :=
    ((M.mem_support_iff x).1 hx _ (ball_mem_nhds x hr)).ne'
  have hfin : M.reference (ball x r) ≠ ∞ := (M.finite_bounded _ isBounded_ball).ne
  have hprob : IsProbabilityMeasure M.reference[|ball x r] :=
    cond_isProbabilityMeasure_of_finite hpos hfin
  -- The law is carried by the ball, so its distance from `x` is bounded by `r`.
  have hmom : HasFiniteMoment 2 M.reference[|ball x r] :=
    hasFiniteMoment_def.2 ⟨x, MemLp.of_enorm_bound (C := ENNReal.ofReal r)
      measurable_edist_right.aestronglyMeasurable ENNReal.ofReal_ne_top
      ((ae_cond_mem measurableSet_ball).mono fun y hy ↦ by
        rw [enorm_eq_self, edist_comm, edist_dist]
        exact ENNReal.ofReal_le_ofReal (mem_ball.1 hy).le)⟩
  exact ⟨.mk ⟨_, hprob⟩ hmom,
    (congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)).trans
      (ProbabilityMeasure.coe_mk _ _)⟩

/-- **The Bonnet–Myers mechanism.** Let `β^{(1)}(θ) = ∞` for every distance `θ > D`. If the
inequality `S_N(μ₀ | m) ≤ T_β^{(0)}(q | m)` holds for some coupling `q` of any two absolutely
continuous laws of finite second moment, then any two points of the support of `m` are at distance
at most `D`: otherwise the uniform laws on two small balls about them would violate it, since
`T_β^{(0)}(q | m) = -∞` while their Rényi entropy is finite. -/
private theorem dist_le_of_renyiEntropy_le_distortedRenyiEntropy {β : ℝ → ℝ → ℝ≥0∞} {D : ℝ}
    (hN : 0 < N) (hβ : ∀ θ, D < θ → β 1 θ = ⊤)
    (h : ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
      ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
      ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
      ∃ q : Measure (X × X), IsCoupling q
          ((μ₀ : ProbabilityMeasure X) : Measure X) ((μ₁ : ProbabilityMeasure X) : Measure X) ∧
        renyiEntropy N M.reference ((μ₀ : ProbabilityMeasure X) : Measure X) ≤
          distortedRenyiEntropy β N M.reference q 0)
    {x y : X} (hx : x ∈ M.support) (hy : y ∈ M.support) : dist x y ≤ D := by
  by_contra! hlt
  set r := (dist x y - D) / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  set m := M.reference
  obtain ⟨μ₀, hμ₀⟩ := exists_coe_eq_cond_ball hx hr
  obtain ⟨μ₁, hμ₁⟩ := exists_coe_eq_cond_ball hy hr
  have hac₀ : ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ m := by
    rw [hμ₀]
    exact cond_absolutelyContinuous
  have hac₁ : ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ m := by
    rw [hμ₁]
    exact cond_absolutelyContinuous
  obtain ⟨q, hq, hle⟩ := h hac₀ hac₁
  have : IsProbabilityMeasure q := hq.isProbabilityMeasure
  -- The entropy of the uniform law on `B(x, r)` is finite.
  have hfin : renyiEntropy N m ((μ₀ : ProbabilityMeasure X) : Measure X) ≠ ⊥ := by
    have hpos : m (ball x r) ≠ 0 := ((M.mem_support_iff x).1 hx _ (ball_mem_nhds x hr)).ne'
    have hm : m (ball x r) ≠ ∞ := (M.finite_bounded _ isBounded_ball).ne
    rw [hμ₀, ProbabilityTheory.cond, renyiEntropy_smul_restrict hN measurableSet_ball hpos hm, Ne,
      EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hN.le) hm
  -- Almost every pair of `q` lies in `B(x, r) × B(y, r)`, hence beyond the distance `D`, and has
  -- a finite first density; there the integrand is infinite.
  have hae : ∀ᵐ z ∂q, β (1 - 0) (dist z.1 z.2) * q.fst.rnDeriv m z.1 ^ (-N⁻¹) +
      β 0 (dist z.1 z.2) * q.snd.rnDeriv m z.2 ^ (-N⁻¹) = ⊤ := by
    have hρ : ∀ᵐ x' ∂((μ₀ : ProbabilityMeasure X) : Measure X),
        ((μ₀ : ProbabilityMeasure X) : Measure X).rnDeriv m x' < ∞ :=
      hac₀.ae_le (Measure.rnDeriv_lt_top _ _)
    have hball₀ : ∀ᵐ x' ∂((μ₀ : ProbabilityMeasure X) : Measure X), x' ∈ ball x r := by
      rw [hμ₀]
      exact ae_cond_mem measurableSet_ball
    have hball₁ : ∀ᵐ y' ∂((μ₁ : ProbabilityMeasure X) : Measure X), y' ∈ ball y r := by
      rw [hμ₁]
      exact ae_cond_mem measurableSet_ball
    rw [hq.fst_eq]
    filter_upwards [hq.measurePreserving_fst.quasiMeasurePreserving.ae hρ,
      hq.measurePreserving_fst.quasiMeasurePreserving.ae hball₀,
      hq.measurePreserving_snd.quasiMeasurePreserving.ae hball₁] with z hzρ hz₀ hz₁
    have hD : D < dist z.1 z.2 := by
      rw [mem_ball] at hz₀ hz₁
      linarith [dist_triangle x z.1 y, dist_triangle z.1 z.2 y, dist_comm x z.1]
    have hne : ((μ₀ : ProbabilityMeasure X) : Measure X).rnDeriv m z.1 ^ (-N⁻¹) ≠ 0 := by
      rw [Ne, ENNReal.rpow_eq_zero_iff]
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith [inv_pos.2 hN]
      · exact hzρ.ne h
    rw [sub_zero, hβ _ hD, ENNReal.top_mul hne, top_add]
  have hbot : distortedRenyiEntropy β N m q 0 = ⊥ := by
    rw [distortedRenyiEntropy_def, lintegral_congr_ae hae, lintegral_const,
      ENNReal.top_mul (by simp), EReal.coe_ennreal_top, EReal.neg_top]
  exact hfin (le_bot_iff.1 (hbot ▸ hle))

/-- The hypothesis of `dist_le_of_renyiEntropy_le_distortedRenyiEntropy`, extracted at time `0` and
dimension `N` from the defining inequalities of either curvature-dimension condition. -/
private theorem exists_isCoupling_renyiEntropy_le {β : ℝ → ℝ → ℝ → ℝ≥0∞}
    (h : ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
      ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
      ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
      ∃ q : Measure (X × X), IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ ENNReal.toReal 2) q
          ((μ₀ : ProbabilityMeasure X) : Measure X) ((μ₁ : ProbabilityMeasure X) : Measure X) ∧
        ∃ γ : ℝ → WassersteinSpace 2 X, IsGeodesicSegment γ μ₀ μ₁ ∧
          ∀ t ∈ Icc (0 : ℝ) 1, ((γ t : ProbabilityMeasure X) : Measure X) ≪ M.reference ∧
            ∀ N' ≥ N, renyiEntropy N' M.reference ((γ t : ProbabilityMeasure X) : Measure X) ≤
              distortedRenyiEntropy (β N') N' M.reference q t)
    ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄ (h₀ : ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference)
    (h₁ : ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference) :
    ∃ q : Measure (X × X), IsCoupling q
        ((μ₀ : ProbabilityMeasure X) : Measure X) ((μ₁ : ProbabilityMeasure X) : Measure X) ∧
      renyiEntropy N M.reference ((μ₀ : ProbabilityMeasure X) : Measure X) ≤
        distortedRenyiEntropy (β N) N M.reference q 0 := by
  obtain ⟨q, hq, γ, hγ, hle⟩ := h h₀ h₁
  refine ⟨q, hq.toIsCoupling, ?_⟩
  simpa only [hγ.source] using (hle 0 (left_mem_Icc.2 zero_le_one)).2 N le_rfl

/-- **The Bonnet–Myers diameter bound under `CD(K, N)`.** If `M` satisfies `CD(K, N)` with `K > 0`
and `N > 0`, any two points are at distance at most `π √((N - 1) / K)`. -/
theorem CurvatureDimension.dist_le (h : M.CurvatureDimension K N) (hK : 0 < K) (hN : 0 < N)
    (x y : X) : dist x y ≤ π * √((N - 1) / K) :=
  dist_le_of_renyiEntropy_le_distortedRenyiEntropy hN
    (fun _ hθ ↦ distortionTau_eq_top_of_lt hK hθ)
    (exists_isCoupling_renyiEntropy_le (β := fun N' ↦ distortionTau K N')
      h.exists_isOptimalCoupling_isGeodesicSegment)
    (h.support_eq_univ ▸ mem_univ x) (h.support_eq_univ ▸ mem_univ y)

/-- **The Bonnet–Myers diameter bound under `CD(K, N)`**, for `K > 0` and `N > 0`: the space has
diameter at most `π √((N - 1) / K)`. -/
theorem CurvatureDimension.diam_univ_le (h : M.CurvatureDimension K N) (hK : 0 < K)
    (hN : 0 < N) : diam (univ : Set X) ≤ π * √((N - 1) / K) :=
  diam_le_of_forall_dist_le (by positivity) fun x _ y _ ↦ h.dist_le hK hN x y

/-- **The diameter bound under `CD*(K, N)`.** If `M` satisfies `CD*(K, N)` with `K > 0` and
`N > 0`, any two points are at distance at most `π √(N / K)`. -/
theorem ReducedCurvatureDimension.dist_le (h : M.ReducedCurvatureDimension K N) (hK : 0 < K)
    (hN : 0 < N) (x y : X) : dist x y ≤ π * √(N / K) :=
  dist_le_of_renyiEntropy_le_distortedRenyiEntropy hN
    (fun _ hθ ↦ distortionSigma_eq_top_of_lt hK hN hθ)
    (exists_isCoupling_renyiEntropy_le (β := fun N' ↦ distortionSigma K N')
      h.exists_isOptimalCoupling_isGeodesicSegment)
    (h.support_eq_univ ▸ mem_univ x) (h.support_eq_univ ▸ mem_univ y)

/-- **The diameter bound under `CD*(K, N)`**, for `K > 0` and `N > 0`: the space has diameter at
most `π √(N / K)`. -/
theorem ReducedCurvatureDimension.diam_univ_le (h : M.ReducedCurvatureDimension K N)
    (hK : 0 < K) (hN : 0 < N) : diam (univ : Set X) ≤ π * √(N / K) :=
  diam_le_of_forall_dist_le (by positivity) fun x _ y _ ↦ h.dist_le hK hN x y

end MetricMeasureSpace

end TauCeti

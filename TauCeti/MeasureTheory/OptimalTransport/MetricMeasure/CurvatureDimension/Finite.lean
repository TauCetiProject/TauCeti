/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.CurvatureDimension.Basic
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
any two laws `μ₀`, `μ₁` of bounded support, absolutely continuous with respect to `m` (Sturm's space
`P_∞(X, d, m)`), admit an optimal coupling `q` for the quadratic cost and a `W₂`-geodesic `(μ_t)`
in `P_∞(X, d, m)` such that

`S_{N'}(μ_t | m) ≤ T_{τ_{K,N'}}^{(t)}(q | m)` for all `t ∈ [0, 1]` and all `N' ≥ N`,

where `τ_{K,N'}` is the distortion coefficient `TauCeti.distortionTau`. The *reduced*
curvature-dimension condition `CD*(K, N)` of Bacher and Sturm is the same inequality with the
coefficient `σ_{K,N'}` (`TauCeti.distortionSigma`) in place of `τ_{K,N'}`. Both are instances of
one condition for a general family of coefficients, stated once with its monotonicity and diameter
bound. By theorems of Sturm and of Bacher–Sturm, not formalized here, on an `n`-dimensional
weighted Riemannian manifold with `N > n` both conditions are equivalent to the lower bound
`Ric + Hess V - dV ⊗ dV / (N - n) ≥ K` on the Bakry–Émery Ricci tensor; on general
metric-measure spaces they are two distinct predicates. Full support follows the convention of
`TauCeti.MetricMeasureSpace.CurvatureDimensionInfinity`; a reference measure without full support
is handled by passing to `TauCeti.MetricMeasureSpace.supportSpace`.

The coefficients `τ_{K,N}^{(s)}(θ)` and `σ_{K,N}^{(s)}(θ)` are infinite at every time `s` once
`θ` exceeds `π √((N - 1) / K)`, respectively `π √(N / K)`, for `K > 0`. With this convention the
condition at time `t = 0` alone gives the **Bonnet–Myers diameter bound**: if two points were
farther apart, the uniform laws on two small balls about them would have
`T^{(0)}(q | m) = -∞` for every coupling `q`, while their Rényi entropy is finite.

## Main definitions

* `TauCeti.MetricMeasureSpace.DistortedCurvatureDimension M β N`: the curvature-dimension
  condition for a family `β` of distortion coefficients.
* `TauCeti.MetricMeasureSpace.CurvatureDimension M K N`: the condition `CD(K, N)`.
* `TauCeti.MetricMeasureSpace.ReducedCurvatureDimension M K N`: the condition `CD*(K, N)`.

## Main statements

* `TauCeti.MetricMeasureSpace.DistortedCurvatureDimension.mono`,
  `TauCeti.MetricMeasureSpace.DistortedCurvatureDimension.dist_le`: the general condition weakens
  for smaller coefficients and larger `N`, and bounds distances by any `D` beyond which the
  coefficients at time `1` are infinite.
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

namespace MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] {M : MetricMeasureSpace X}
  {β β' : ℝ → ℝ → ℝ → ℝ≥0∞} {K K' N N' D : ℝ}

/-- The **curvature-dimension condition for a family of distortion coefficients** `β`, where
`β N' s θ = β_{N'}^{(s)}(θ)`: the reference measure `m` has full support, and any two laws `μ₀`,
`μ₁` of bounded support, absolutely continuous with respect to `m`, admit an optimal coupling `q`
for the quadratic cost and a `W₂`-geodesic `(μ_t)` of laws of bounded support, absolutely
continuous with respect to `m`, along which `S_{N'}(μ_t | m) ≤ T_{β_{N'}}^{(t)}(q | m)` for every
`t ∈ [0, 1]` and every `N' ≥ N`. Here `S_{N'}` is the Rényi entropy and `T` the distorted Rényi
entropy (`TauCeti.distortedRenyiEntropy`). The laws range over Sturm's space `P_∞(X, d, m)`.

With `β = τ_K` this is `CD(K, N)` (`TauCeti.MetricMeasureSpace.CurvatureDimension`), with
`β = σ_K` it is `CD*(K, N)` (`TauCeti.MetricMeasureSpace.ReducedCurvatureDimension`). -/
structure DistortedCurvatureDimension (M : MetricMeasureSpace X) (β : ℝ → ℝ → ℝ → ℝ≥0∞)
    (N : ℝ) : Prop where
  /-- The reference measure has full support. -/
  support_eq_univ : M.support = univ
  /-- Any two absolutely continuous laws of bounded support are joined by an optimal coupling and
  a `W₂`-geodesic of absolutely continuous laws of bounded support satisfying the distorted Rényi
  inequalities for all dimensions `N' ≥ N`. -/
  exists_isOptimalCoupling_isGeodesicSegment : ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
    Bornology.IsBounded ((μ₀ : ProbabilityMeasure X) : Measure X).support →
    ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    Bornology.IsBounded ((μ₁ : ProbabilityMeasure X) : Measure X).support →
    ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    ∃ q : Measure (X × X), IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ ENNReal.toReal 2) q
        ((μ₀ : ProbabilityMeasure X) : Measure X) ((μ₁ : ProbabilityMeasure X) : Measure X) ∧
      ∃ γ : ℝ → WassersteinSpace 2 X, IsGeodesicSegment γ μ₀ μ₁ ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          Bornology.IsBounded ((γ t : ProbabilityMeasure X) : Measure X).support ∧
          ((γ t : ProbabilityMeasure X) : Measure X) ≪ M.reference ∧
          ∀ N' ≥ N, renyiEntropy N' M.reference ((γ t : ProbabilityMeasure X) : Measure X) ≤
            distortedRenyiEntropy (β N') N' M.reference q t

/-- The **curvature-dimension condition** `CD(K, N)` of Sturm for the metric-measure space `M`:
the reference measure `m` has full support, and any two laws `μ₀`, `μ₁` of bounded support,
absolutely continuous with respect to `m`, admit an optimal coupling `q` for the quadratic cost and
a `W₂`-geodesic `(μ_t)` of such laws along which `S_{N'}(μ_t | m) ≤ T_{τ_{K,N'}}^{(t)}(q | m)` for
every `t ∈ [0, 1]` and every `N' ≥ N`. It is
`TauCeti.MetricMeasureSpace.DistortedCurvatureDimension` for the coefficient `τ_{K,N'}`
(`TauCeti.distortionTau`).

The condition is meant for `N ≥ 1`, where the coefficients carry their geometric meaning. -/
def CurvatureDimension (M : MetricMeasureSpace X) (K N : ℝ) : Prop :=
  M.DistortedCurvatureDimension (distortionTau K) N

/-- `CD(K, N)` is the curvature-dimension condition for the coefficients `τ_{K,N'}`. -/
theorem curvatureDimension_iff :
    M.CurvatureDimension K N ↔ M.DistortedCurvatureDimension (distortionTau K) N :=
  (Iff.rfl)

/-- The **reduced curvature-dimension condition** `CD*(K, N)` of Bacher and Sturm: the condition
`CD(K, N)` (`TauCeti.MetricMeasureSpace.CurvatureDimension`) with the distortion coefficient
`σ_{K,N'}` (`TauCeti.distortionSigma`) in place of `τ_{K,N'}`. That is, `m` has full support, and
any two laws `μ₀`, `μ₁` of bounded support, absolutely continuous with respect to `m`, admit an
optimal coupling `q` for the quadratic cost and a `W₂`-geodesic `(μ_t)` of such laws along which
`S_{N'}(μ_t | m) ≤ T_{σ_{K,N'}}^{(t)}(q | m)` for every `t ∈ [0, 1]` and every `N' ≥ N`.

The condition is meant for `N ≥ 1`, where the coefficients carry their geometric meaning. -/
def ReducedCurvatureDimension (M : MetricMeasureSpace X) (K N : ℝ) : Prop :=
  M.DistortedCurvatureDimension (distortionSigma K) N

/-- `CD*(K, N)` is the curvature-dimension condition for the coefficients `σ_{K,N'}`. -/
theorem reducedCurvatureDimension_iff :
    M.ReducedCurvatureDimension K N ↔ M.DistortedCurvatureDimension (distortionSigma K) N :=
  (Iff.rfl)

/-- The condition for the coefficients `β` implies the condition for `N ≤ N'` and any smaller
coefficients `β' ≤ β` on the times `[0, 1]`. -/
theorem DistortedCurvatureDimension.mono (h : M.DistortedCurvatureDimension β N) (hN : N ≤ N')
    (hβ : ∀ N'' ≥ N', ∀ s ∈ Icc (0 : ℝ) 1, ∀ θ, β' N'' s θ ≤ β N'' s θ) :
    M.DistortedCurvatureDimension β' N' := by
  refine ⟨h.support_eq_univ, fun μ₀ μ₁ hb₀ h₀ hb₁ h₁ ↦ ?_⟩
  obtain ⟨q, hq, γ, hγ, hle⟩ := h.exists_isOptimalCoupling_isGeodesicSegment hb₀ h₀ hb₁ h₁
  refine ⟨q, hq, γ, hγ, fun t ht ↦ ⟨(hle t ht).1, (hle t ht).2.1, fun N'' hN'' ↦ ?_⟩⟩
  exact ((hle t ht).2.2 N'' (hN.trans hN'')).trans (distortedRenyiEntropy_anti
    (hβ N'' hN'' _ ⟨sub_nonneg.2 ht.2, sub_le_self _ ht.1⟩) (hβ N'' hN'' t ht))

/-- `CD(K, N)` implies `CD(K', N')` for `K' ≤ K` and `N ≤ N'`. -/
theorem CurvatureDimension.mono (h : M.CurvatureDimension K N) (hK : K' ≤ K) (hN : N ≤ N') :
    M.CurvatureDimension K' N' :=
  DistortedCurvatureDimension.mono h hN fun _ _ _ hs _ ↦ distortionTau_left_monotone hs.1 hs.2 hK

/-- `CD*(K, N)` implies `CD*(K', N')` for `K' ≤ K` and `0 ≤ N ≤ N'`. -/
theorem ReducedCurvatureDimension.mono (h : M.ReducedCurvatureDimension K N) (hK : K' ≤ K)
    (hN : N ≤ N') (hN₀ : 0 ≤ N) : M.ReducedCurvatureDimension K' N' :=
  DistortedCurvatureDimension.mono h hN fun _ hN'' _ hs _ ↦
    distortionSigma_left_monotone hs.1 hs.2 (hN₀.trans (hN.trans hN'')) hK

/-- **The Bonnet–Myers mechanism.** Let `β_N^{(1)}(θ) = ∞` for every distance `θ > D`. Under the
curvature-dimension condition for the coefficients `β`, any two points are at distance at most `D`:
otherwise the uniform laws on two small balls about them would violate the inequality at time `0`,
since `T_{β_N}^{(0)}(q | m) = -∞` for every coupling `q` while their Rényi entropy is finite. -/
theorem DistortedCurvatureDimension.dist_le (h : M.DistortedCurvatureDimension β N) (hN : 0 < N)
    (hβ : ∀ θ, D < θ → β N 1 θ = ⊤) (x y : X) : dist x y ≤ D := by
  by_contra! hlt
  set r := (dist x y - D) / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  set m := M.reference
  -- Balls of positive radius have positive, finite measure, and their uniform laws are absolutely
  -- continuous with bounded support.
  have hball : ∀ z, m (ball z r) ≠ 0 ∧ m (ball z r) ≠ ∞ := fun z ↦
    ⟨((M.mem_support_iff z).1 (h.support_eq_univ ▸ mem_univ z) _ (ball_mem_nhds z hr)).ne',
      (M.finite_bounded _ isBounded_ball).ne⟩
  obtain ⟨hpos, hm⟩ := hball x
  obtain ⟨μ₀, hμ₀, hb₀, hac₀⟩ :=
    WassersteinSpace.exists_coe_eq_cond (p := 2) measurableSet_ball isBounded_ball hpos hm
  obtain ⟨μ₁, hμ₁, hb₁, hac₁⟩ := WassersteinSpace.exists_coe_eq_cond (p := 2) measurableSet_ball
    isBounded_ball (hball y).1 (hball y).2
  obtain ⟨q, hq, γ, hγ, hle⟩ :=
    h.exists_isOptimalCoupling_isGeodesicSegment hb₀ hac₀ hb₁ hac₁
  replace hq := hq.toIsCoupling
  replace hle : renyiEntropy N m ((μ₀ : ProbabilityMeasure X) : Measure X) ≤
      distortedRenyiEntropy (β N) N m q 0 := by
    simpa only [hγ.source] using (hle 0 (left_mem_Icc.2 zero_le_one)).2.2 N le_rfl
  have : IsProbabilityMeasure q := hq.isProbabilityMeasure
  -- Almost every pair of `q` is beyond the distance `D` and has a finite first density; there the
  -- integrand is infinite.
  have hae : ∀ᵐ z ∂q, β N (1 - 0) (dist z.1 z.2) * q.fst.rnDeriv m z.1 ^ (-N⁻¹) +
      β N 0 (dist z.1 z.2) * q.snd.rnDeriv m z.2 ^ (-N⁻¹) = ⊤ := by
    have hD := hq.ae_lt_dist (hμ₀ ▸ ae_cond_mem measurableSet_ball)
      (hμ₁ ▸ ae_cond_mem measurableSet_ball) (by linarith : D + r + r ≤ dist x y)
    have hρ : ∀ᵐ x' ∂((μ₀ : ProbabilityMeasure X) : Measure X),
        ((μ₀ : ProbabilityMeasure X) : Measure X).rnDeriv m x' < ∞ :=
      hac₀.ae_le (Measure.rnDeriv_lt_top _ _)
    rw [hq.fst_eq]
    filter_upwards [hq.measurePreserving_fst.quasiMeasurePreserving.ae hρ, hD] with z hzρ hzD
    have hne : ((μ₀ : ProbabilityMeasure X) : Measure X).rnDeriv m z.1 ^ (-N⁻¹) ≠ 0 := by
      rw [Ne, ENNReal.rpow_eq_zero_iff]
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith [inv_pos.2 hN]
      · exact hzρ.ne h
    rw [sub_zero, hβ _ hzD, ENNReal.top_mul hne, top_add]
  rw [distortedRenyiEntropy_eq_bot_of_ae (IsProbabilityMeasure.ne_zero q) hae, le_bot_iff] at hle
  exact (hμ₀ ▸ renyiEntropy_cond_ne_bot hN measurableSet_ball) hle

/-- **The Bonnet–Myers diameter bound** for the coefficients `β`: if `β_N^{(1)}(θ) = ∞` for every
distance `θ > D ≥ 0`, the space has diameter at most `D`. -/
theorem DistortedCurvatureDimension.diam_univ_le (h : M.DistortedCurvatureDimension β N)
    (hN : 0 < N) (hD : 0 ≤ D) (hβ : ∀ θ, D < θ → β N 1 θ = ⊤) : diam (univ : Set X) ≤ D :=
  diam_le_of_forall_dist_le hD fun x _ y _ ↦ h.dist_le hN hβ x y

/-- **The Bonnet–Myers diameter bound under `CD(K, N)`.** If `M` satisfies `CD(K, N)` with `K > 0`
and `N > 0`, any two points are at distance at most `π √((N - 1) / K)`. -/
theorem CurvatureDimension.dist_le (h : M.CurvatureDimension K N) (hK : 0 < K) (hN : 0 < N)
    (x y : X) : dist x y ≤ π * √((N - 1) / K) :=
  DistortedCurvatureDimension.dist_le h hN (fun _ hθ ↦ distortionTau_eq_top_of_lt hK hθ) x y

/-- **The Bonnet–Myers diameter bound under `CD(K, N)`**, for `K > 0` and `N > 0`: the space has
diameter at most `π √((N - 1) / K)`. -/
theorem CurvatureDimension.diam_univ_le (h : M.CurvatureDimension K N) (hK : 0 < K)
    (hN : 0 < N) : diam (univ : Set X) ≤ π * √((N - 1) / K) :=
  DistortedCurvatureDimension.diam_univ_le h hN (by positivity)
    fun _ hθ ↦ distortionTau_eq_top_of_lt hK hθ

/-- **The diameter bound under `CD*(K, N)`.** If `M` satisfies `CD*(K, N)` with `K > 0` and
`N > 0`, any two points are at distance at most `π √(N / K)`. -/
theorem ReducedCurvatureDimension.dist_le (h : M.ReducedCurvatureDimension K N) (hK : 0 < K)
    (hN : 0 < N) (x y : X) : dist x y ≤ π * √(N / K) :=
  DistortedCurvatureDimension.dist_le h hN (fun _ hθ ↦ distortionSigma_eq_top_of_lt hK hN hθ) x y

/-- **The diameter bound under `CD*(K, N)`**, for `K > 0` and `N > 0`: the space has diameter at
most `π √(N / K)`. -/
theorem ReducedCurvatureDimension.diam_univ_le (h : M.ReducedCurvatureDimension K N)
    (hK : 0 < K) (hN : 0 < N) : diam (univ : Set X) ≤ π * √(N / K) :=
  DistortedCurvatureDimension.diam_univ_le h hN (by positivity)
    fun _ hθ ↦ distortionSigma_eq_top_of_lt hK hN hθ

end MetricMeasureSpace

end TauCeti

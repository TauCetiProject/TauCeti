/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.Basic
public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.DistortionCoefficient
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.RenyiEntropy

/-!
# The curvature-dimension conditions `CD(K, ∞)` and `CD(K, N)`

Let `M` be a metric-measure space (`TauCeti.MetricMeasureSpace`): a complete separable metric
space `X` with its Borel structure and a reference measure `m` finite on bounded sets. Following
Sturm and Lott–Villani, `M` satisfies the *curvature-dimension condition* `CD(K, ∞)`, for `K : ℝ`,
when `m` has full support and the Boltzmann entropy `μ ↦ Ent_m(μ)` relative to `m` is weakly
`K`-convex on the quadratic Wasserstein space `P₂(X)`: any two laws `μ₀`, `μ₁` of finite second
moment with `Ent_m(μᵢ) < ∞` are joined by a `W₂`-geodesic `(μ_t)` along which

`Ent_m(μ_t) ≤ (1 - t) Ent_m(μ₀) + t Ent_m(μ₁) - (K / 2) t (1 - t) W₂(μ₀, μ₁)²`.

This is the synthetic form of the lower Ricci bound `Ric ≥ K`: on a smooth Riemannian manifold
with its volume measure the two are equivalent, by a theorem of von Renesse and Sturm. As in
Sturm's definition, the endpoints range over the laws with `Ent_m(μᵢ) < ∞`, the effective domain
of the entropy, and the inequality is read in `[-∞, ∞]`. The entropy may be `⊥` when `m` is
infinite and grows fast at infinity, and such laws are endpoints too. In the usual setting, where
`m` satisfies a growth bound such as `∫ exp (-c d(x₀, x)²) dm(x) < ∞` (for instance when `m` is
finite), the entropy is never `⊥` on `P₂(X)`, so the endpoints are the laws of finite entropy.
Given full support, the condition is `TauCeti.GeodesicallyConvex` for the energy
`TauCeti.boltzmannEntropy m` on `TauCeti.WassersteinSpace 2 X`
(`TauCeti.MetricMeasureSpace.curvatureDimensionInfinity_iff_geodesicallyConvex`), and the slope
formula and the rest of the theory of geodesically convex energies apply to it.

Full support is part of the condition, following the standing convention `supp m = X` of the
metric-measure theory of curvature bounds. A reference measure without full support is handled
by passing to its support, `TauCeti.MetricMeasureSpace.supportSpace`. In particular `CD(K, ∞)`
fails for `m = 0` on a nonempty space.

The condition constrains the geometry of `X`:

* every Dirac mass at a point of the support of a locally finite `m` is a `W_p`-limit of laws of
  finite entropy
  (`TauCeti.exists_boltzmannEntropy_ne_top_and_ne_bot_and_wassersteinEDist_dirac_le`);
* consequently, under `CD(K, ∞)`, any two points `x₀`, `x₁` have approximate midpoints: points
  `z` with `d(x₀, z)² + d(z, x₁)² ≤ d(x₀, x₁)² / 2 + ε` for every `ε > 0`
  (`TauCeti.MetricMeasureSpace.CurvatureDimensionInfinity.exists_dist_sq_add_dist_sq_le`). In any
  metric space `d(x₀, z)² + d(z, x₁)² ≥ d(x₀, x₁)² / 2`, with equality exactly at midpoints, so
  this says that the infimum of the left side is the midpoint value;
* in particular, a reference measure whose support consists of two distinct points never
  satisfies `CD(K, ∞)`, whatever `K` is
  (`TauCeti.MetricMeasureSpace.not_curvatureDimensionInfinity_of_support_eq_pair`).

## The finite-dimensional condition `CD(K, N)`

For a dimension bound `N ≥ 1`, Sturm's condition `CD(K, N)`
(`TauCeti.MetricMeasureSpace.CurvatureDimension M K N`) replaces the Boltzmann entropy by the
Rényi entropies `S_{N'}(· | m)` (`TauCeti.renyiEntropy`) for `N' ≥ N`, and the term
`(K / 2) t (1 - t) W₂²` by the distortion coefficients `τ_{K,N'}` (`TauCeti.distortionTau`). Write
`P_∞(m)` for the laws absolutely continuous with respect to `m` with bounded support. Any
`μ₀ = ρ₀ m` and `μ₁ = ρ₁ m` in `P_∞(m)` admit a quadratically optimal coupling `q` and a
`W₂`-geodesic `(μ_t)` in `P_∞(m)` from `μ₀` to `μ₁` with

`S_{N'}(μ_t | m) ≤ -∫ (τ₀ ρ₀(x₀)^{-1/N'} + τ₁ ρ₁(x₁)^{-1/N'}) dq(x₀, x₁)`,

where `τ₀ = τ_{K,N'}^{(1-t)}(d(x₀, x₁))` and `τ₁ = τ_{K,N'}^{(t)}(d(x₀, x₁))`, for every
`t ∈ [0, 1]` and every `N' ≥ N`. Here `ρ₀` and `ρ₁` are Radon–Nikodym derivatives with respect to
`m`. As in Sturm's definition, the geodesic need not be induced by `q`, and full support of `m` is
not part of the condition, as for the measure-contraction property
`TauCeti.MetricMeasureSpace.MeasureContraction`.

Following Sturm, the coefficient `τ_{K,N'}^{(s)}(θ)` is infinite at every time `s`, including
`s = 1`, once `K > 0` and `θ` exceeds the Bonnet–Myers distance `π √((N' - 1) / K)`. Hence the
condition at `t = 0` already forces the **generalised Bonnet–Myers theorem**: under `CD(K, N)`
with `K > 0` and `N ≥ 1`, the support of `m` has diameter at most `π √((N - 1) / K)`
(`TauCeti.MetricMeasureSpace.CurvatureDimension.dist_le`).

## Main definitions

* `TauCeti.MetricMeasureSpace.CurvatureDimensionInfinity M K`: the condition `CD(K, ∞)` for the
  metric-measure space `M`.
* `TauCeti.MetricMeasureSpace.CurvatureDimension M K N`: the condition `CD(K, N)` for the
  metric-measure space `M`.

## Main statements

* `TauCeti.MetricMeasureSpace.CurvatureDimensionInfinity.mono`: `CD(K, ∞)` implies `CD(K', ∞)`
  for `K' ≤ K`.
* `TauCeti.MetricMeasureSpace.curvatureDimensionInfinity_iff_geodesicallyConvex`: for a reference
  measure of full support, `CD(K, ∞)` is the `K`-geodesic convexity of the entropy.
* `TauCeti.MetricMeasureSpace.CurvatureDimensionInfinity.exists_dist_sq_add_dist_sq_le`: under
  `CD(K, ∞)`, any two points have approximate midpoints.
* `TauCeti.MetricMeasureSpace.not_curvatureDimensionInfinity_of_support_eq_pair`: a reference
  measure supported on two points satisfies `CD(K, ∞)` for no `K`.
* `TauCeti.MetricMeasureSpace.CurvatureDimension.mono`,
  `TauCeti.MetricMeasureSpace.CurvatureDimension.mono_dimension`: `CD(K, N)` implies `CD(K', N')`
  for `K' ≤ K` and `N ≤ N'`.
* `TauCeti.MetricMeasureSpace.CurvatureDimension.dist_le`,
  `TauCeti.MetricMeasureSpace.CurvatureDimension.diam_support_le`: the Bonnet–Myers diameter bound
  `diam (supp m) ≤ π √((N - 1) / K)` under `CD(K, N)` with `K > 0` and `N ≥ 1`.

## References

* K.-T. Sturm, *On the geometry of metric measure spaces. I*, Acta Math. 196 (2006), 65–131.
* K.-T. Sturm, *On the geometry of metric measure spaces. II*, Acta Math. 196 (2006), 133–177,
  Definition 1.3 and Corollary 2.6.
* M.-K. von Renesse and K.-T. Sturm, *Transport inequalities, gradient estimates, entropy, and
  Ricci curvature*, Comm. Pure Appl. Math. 58 (2005), 923–940.
* J. Lott and C. Villani, *Ricci curvature for metric-measure spaces via optimal transport*,
  Ann. of Math. 169 (2009), 903–991.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapters 29–30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {m : Measure X}

section FiniteEntropy

/-- **Dirac masses on the support are limits of laws of finite entropy.** If `m` is locally
finite and `x` lies in the support of `m`, then for every `r > 0` some law `μ` of finite
`p`-moment and finite entropy, `Ent_m(μ) ∉ {⊥, ⊤}`, is within `W_p`-distance `r` of `δ_x`. One can
take `μ` to be the normalised restriction of `m` to a small ball about `x`. -/
theorem exists_boltzmannEntropy_ne_top_and_ne_bot_and_wassersteinEDist_dirac_le
    [IsLocallyFiniteMeasure m] {p : ℝ≥0∞} {x : X} (hx : x ∈ m.support) {r : ℝ} (hr : 0 < r) :
    ∃ μ : WassersteinSpace p X, boltzmannEntropy m ((μ : ProbabilityMeasure X) : Measure X) ≠ ⊤ ∧
      boltzmannEntropy m ((μ : ProbabilityMeasure X) : Measure X) ≠ ⊥ ∧
      wassersteinEDist p (Measure.dirac x) ((μ : ProbabilityMeasure X) : Measure X) ≤
        ENNReal.ofReal r := by
  -- A ball about `x` of radius at most `r` and of finite, positive `m`-measure.
  obtain ⟨U, hxU, hU, hmU⟩ := m.exists_isOpen_measure_lt_top x
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU x hxU
  set s := ball x (min r ρ)
  have hs : MeasurableSet s := measurableSet_ball
  have hs0 : m s ≠ 0 :=
    ((Measure.mem_support_iff_forall x).1 hx s (ball_mem_nhds x (lt_min hr hρ))).ne'
  have hstop : m s ≠ ∞ :=
    ((measure_mono ((ball_subset_ball (min_le_right r ρ)).trans hρU)).trans_lt hmU).ne
  -- The normalised restriction `m[|s]`, with its constant density `(m s)⁻¹` on `s`.
  set c : ℝ≥0 := ((m s)⁻¹).toNNReal
  have hc : (c : ℝ≥0∞) = (m s)⁻¹ := ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 hs0)
  have hdens : m[|s] = m.withDensity fun y ↦ ((s.indicator (fun _ ↦ c) y : ℝ≥0) : ℝ≥0∞) := by
    simp_rw [ENNReal.coe_indicator, withDensity_indicator hs, withDensity_const, hc]
    rw [ProbabilityTheory.cond]
  obtain ⟨μ, hμ, -, -⟩ := WassersteinSpace.exists_coe_eq_cond (p := p) hs isBounded_ball hs0 hstop
  have hW : wassersteinEDist p (Measure.dirac x) ((μ : ProbabilityMeasure X) : Measure X) ≤
      ENNReal.ofReal r := by
    have hbound : ∀ᵐ y ∂((μ : ProbabilityMeasure X) : Measure X),
        ‖edist x y‖ₑ ≤ ENNReal.ofReal r :=
      hμ ▸ (ae_cond_mem hs).mono fun y hy ↦ by
        rw [enorm_eq_self, edist_comm, edist_dist]
        exact ENNReal.ofReal_le_ofReal ((mem_ball.1 hy).le.trans (min_le_left r ρ))
    calc wassersteinEDist p (Measure.dirac x) ((μ : ProbabilityMeasure X) : Measure X)
        ≤ ENNReal.ofReal r • ((μ : ProbabilityMeasure X) : Measure X) univ ^ p.toReal⁻¹ := by
          rw [wassersteinEDist_dirac_left measurable_edist]
          exact eLpNorm_le_of_ae_enorm_bound (by fun_prop) hbound
      _ = ENNReal.ofReal r := by simp
  -- The entropy is `c log c * m s`, the integral of a constant over `s`.
  have hV : (fun y ↦ ((s.indicator (fun _ ↦ c) y : ℝ≥0) : ℝ) *
      Real.log (s.indicator (fun _ ↦ c) y : ℝ≥0)) =
      s.indicator fun _ ↦ (c : ℝ) * Real.log c := by
    ext y
    by_cases hy : y ∈ s <;> simp [hy]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, boltzmannEntropy m m[|s] = E := by
    rw [hdens, boltzmannEntropy_withDensity (measurable_const.indicator hs).aemeasurable, hV,
      potentialEnergy_of_integrable ((integrableOn_const hstop).integrable_indicator hs)]
    exact ⟨_, rfl⟩
  refine ⟨μ, ?_, ?_, hW⟩ <;> rw [hμ, hE]
  exacts [EReal.coe_ne_top E, EReal.coe_ne_bot E]

end FiniteEntropy

section CurvatureDimension

namespace MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] {M : MetricMeasureSpace X} {K K' : ℝ}

/-- The **curvature-dimension condition** `CD(K, ∞)` of Sturm and Lott–Villani for the
metric-measure space `M`: the reference measure has full support, and the Boltzmann entropy
relative to it is `K`-geodesically convex on the quadratic Wasserstein space `P₂(X)`. That is, any
two laws of finite second moment with `Ent_m(μᵢ) < ∞` (the entropy may be `⊥`) are joined by a
`W₂`-geodesic `(μ_t)` along which
`Ent_m(μ_t) ≤ (1 - t) Ent_m(μ₀) + t Ent_m(μ₁) - (K / 2) t (1 - t) W₂(μ₀, μ₁)²`.

The carrier is complete and separable and the reference measure is finite on bounded sets, as
`TauCeti.MetricMeasureSpace` requires. For a reference measure without full support, apply the
condition to the support reduction `TauCeti.MetricMeasureSpace.supportSpace`. -/
structure CurvatureDimensionInfinity (M : MetricMeasureSpace X) (K : ℝ) : Prop where
  /-- The reference measure has full support. -/
  support_eq_univ : M.support = univ
  /-- Any two laws of finite second moment and entropy `< ∞` are joined by a `W₂`-geodesic
  along which the entropy is `K`-convex. -/
  exists_isGeodesicSegment_convexAlong : ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
    boltzmannEntropy M.reference ((μ₀ : ProbabilityMeasure X) : Measure X) ≠ ⊤ →
    boltzmannEntropy M.reference ((μ₁ : ProbabilityMeasure X) : Measure X) ≠ ⊤ →
    ∃ γ : ℝ → WassersteinSpace 2 X, IsGeodesicSegment γ μ₀ μ₁ ∧
      ConvexAlong K (fun μ : WassersteinSpace 2 X ↦
        boltzmannEntropy M.reference ((μ : ProbabilityMeasure X) : Measure X)) γ

/-- For a reference measure of full support, `CD(K, ∞)` is the `K`-geodesic convexity of the
Boltzmann entropy. -/
theorem curvatureDimensionInfinity_iff_geodesicallyConvex (hM : M.support = univ) :
    M.CurvatureDimensionInfinity K ↔ GeodesicallyConvex K fun μ : WassersteinSpace 2 X ↦
      boltzmannEntropy M.reference ((μ : ProbabilityMeasure X) : Measure X) :=
  ⟨fun h ↦ geodesicallyConvex_def.2 h.exists_isGeodesicSegment_convexAlong,
    fun h ↦ ⟨hM, geodesicallyConvex_def.1 h⟩⟩

/-- `CD(K, ∞)` implies `CD(K', ∞)` for every `K' ≤ K`. -/
theorem CurvatureDimensionInfinity.mono (h : M.CurvatureDimensionInfinity K) (hK : K' ≤ K) :
    M.CurvatureDimensionInfinity K' :=
  ⟨h.support_eq_univ, fun _ _ h₀ h₁ ↦
    (h.exists_isGeodesicSegment_convexAlong h₀ h₁).imp fun _ hγ ↦
      ⟨hγ.1, hγ.2.mono hK⟩⟩

/-- **Approximate midpoints under `CD(K, ∞)`.** If `M` satisfies `CD(K, ∞)`, any two points
`x₀`, `x₁` have approximate midpoints: for every `ε > 0` some `z` has
`d(x₀, z)² + d(z, x₁)² ≤ d(x₀, x₁)² / 2 + ε`. The left side is at least `d(x₀, x₁)² / 2` for every
`z`, with equality exactly at midpoints. -/
theorem CurvatureDimensionInfinity.exists_dist_sq_add_dist_sq_le
    (h : M.CurvatureDimensionInfinity K) (x₀ x₁ : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ z, dist x₀ z ^ 2 + dist z x₁ ^ 2 ≤ dist x₀ x₁ ^ 2 / 2 + ε := by
  set d := dist x₀ x₁
  -- Choose `r > 0` with `2 (d / 2 + 2 r)² ≤ d² / 2 + ε`.
  set r := min 1 (ε / (4 * d + 8))
  have hd : 0 ≤ d := dist_nonneg
  have hr : 0 < r := lt_min one_pos (by positivity)
  have hrε : 4 * d * r + 8 * r ^ 2 ≤ ε := by
    have h1 : r ≤ 1 := min_le_left _ _
    have h2 : r * (4 * d + 8) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith
  -- Laws of finite entropy concentrated near `x₀` and `x₁`, and a `W₂`-midpoint between them.
  have hsupp (x : X) : x ∈ M.reference.support := by
    rw [← M.support_def, h.support_eq_univ]
    exact mem_univ x
  obtain ⟨μ₀, hE₀, -, hW₀⟩ :=
    exists_boltzmannEntropy_ne_top_and_ne_bot_and_wassersteinEDist_dirac_le (hsupp x₀) hr
  obtain ⟨μ₁, hE₁, -, hW₁⟩ :=
    exists_boltzmannEntropy_ne_top_and_ne_bot_and_wassersteinEDist_dirac_le (hsupp x₁) hr
  obtain ⟨γ, hγ, -⟩ := h.exists_isGeodesicSegment_convexAlong hE₀ hE₁
  have ht : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set ν := ((γ (1 / 2) : ProbabilityMeasure X) : Measure X)
  -- `W₂(μ₀, μ₁) ≤ d + 2 r`, so the midpoint is within `d / 2 + 2 r` of both `δ_{x₀}` and `δ_{x₁}`.
  have hW : dist μ₀ μ₁ ≤ d + 2 * r := by
    rw [← edist_le_ofReal (by positivity), WassersteinSpace.edist_def]
    calc wassersteinEDist 2 ((μ₀ : ProbabilityMeasure X) : Measure X) (μ₁ : ProbabilityMeasure X)
        ≤ wassersteinEDist 2 ((μ₀ : ProbabilityMeasure X) : Measure X) (Measure.dirac x₀) +
          (wassersteinEDist 2 (Measure.dirac x₀) (Measure.dirac x₁) +
            wassersteinEDist 2 (Measure.dirac x₁) ((μ₁ : ProbabilityMeasure X) : Measure X)) :=
          (wassersteinEDist_triangle measurable_edist one_le_two _ _ _).trans
            (add_le_add le_rfl (wassersteinEDist_triangle measurable_edist one_le_two _ _ _))
      _ ≤ ENNReal.ofReal r + (ENNReal.ofReal d + ENNReal.ofReal r) := by
          rw [wassersteinEDist_comm measurable_edist, wassersteinEDist_dirac_dirac two_ne_zero,
            edist_dist]
          gcongr
      _ = ENNReal.ofReal (d + 2 * r) := by
          rw [← ENNReal.ofReal_add hd hr.le, ← ENNReal.ofReal_add hr.le (by positivity)]
          ring_nf
  have hmid (x : X) (μ : WassersteinSpace 2 X)
      (hx : wassersteinEDist 2 (Measure.dirac x) ((μ : ProbabilityMeasure X) : Measure X) ≤
        ENNReal.ofReal r) (hμ : dist μ (γ (1 / 2)) = 1 / 2 * dist μ₀ μ₁) :
      wassersteinEDist 2 (Measure.dirac x) ν ≤ ENNReal.ofReal (d / 2 + 2 * r) := by
    have hμν : wassersteinEDist 2 ((μ : ProbabilityMeasure X) : Measure X) ν ≤
        ENNReal.ofReal ((d + 2 * r) / 2) := by
      rw [← WassersteinSpace.edist_def, edist_le_ofReal (by positivity), hμ]
      linarith
    calc wassersteinEDist 2 (Measure.dirac x) ν
        ≤ ENNReal.ofReal r + ENNReal.ofReal ((d + 2 * r) / 2) :=
          (wassersteinEDist_triangle measurable_edist one_le_two _ _ _).trans (add_le_add hx hμν)
      _ = ENNReal.ofReal (d / 2 + 2 * r) := by
          rw [← ENNReal.ofReal_add hr.le (by positivity)]
          ring_nf
  have hν₀ := hmid x₀ μ₀ hW₀ (hγ.dist_source_apply ht)
  have hν₁ := hmid x₁ μ₁ hW₁ (by rw [dist_comm, hγ.dist_apply_target ht]; norm_num)
  obtain ⟨z, -, hle⟩ :=
    exists_notMem_dist_sq_add_dist_sq_le_of_wassersteinEDist_le measurable_edist ν
      measure_empty (by positivity) hν₀ hν₁
  exact ⟨z, hle.trans (by nlinarith)⟩

/-- **Two-point supports violate `CD(K, ∞)`.** A metric-measure space whose reference measure is
supported on two distinct points satisfies `CD(K, ∞)` for no `K`: neither point is an approximate
midpoint of the two. -/
theorem not_curvatureDimensionInfinity_of_support_eq_pair {x₀ x₁ : X} (hne : x₀ ≠ x₁)
    (hM : M.support = {x₀, x₁}) (K : ℝ) : ¬ M.CurvatureDimensionInfinity K := by
  intro h
  have hd : 0 < dist x₀ x₁ := dist_pos.2 hne
  obtain ⟨z, hle⟩ := h.exists_dist_sq_add_dist_sq_le x₀ x₁ (ε := dist x₀ x₁ ^ 2 / 4)
    (by positivity)
  have hz : z ∈ M.support := h.support_eq_univ ▸ mem_univ z
  rw [hM] at hz
  rcases hz with rfl | rfl <;>
  · simp only [dist_self] at hle
    nlinarith

/-! ### The finite-dimensional condition `CD(K, N)` -/

variable {N N' : ℝ}

/-- The **curvature-dimension condition** `CD(K, N)` of Sturm for the metric-measure space `M`
with reference measure `m`. Write `P_∞(m)` for the laws absolutely continuous with respect to `m`
with bounded support. Any two laws `μ₀ = ρ₀ m` and `μ₁ = ρ₁ m` in `P_∞(m)` admit a coupling `q`
that is optimal for the quadratic cost and a `W₂`-geodesic `(μ_t)` from `μ₀` to `μ₁` running in
`P_∞(m)` such that, for every `t ∈ [0, 1]` and every `N' ≥ N`,

`S_{N'}(μ_t | m) ≤ -∫ (τ₀ ρ₀(x₀)^{-1/N'} + τ₁ ρ₁(x₁)^{-1/N'}) dq(x₀, x₁)`,

where `τ₀ = τ_{K,N'}^{(1-t)}(d(x₀, x₁))` and `τ₁ = τ_{K,N'}^{(t)}(d(x₀, x₁))`.

Here `S_{N'}` is the Rényi entropy `TauCeti.renyiEntropy`, `τ_{K,N'}` is the distortion
coefficient `TauCeti.distortionTau` and `ρᵢ` is the Radon–Nikodym derivative of `μᵢ` with respect
to `m`. Laws of bounded support have finite second moment, so the laws involved are points of
`TauCeti.WassersteinSpace 2 X`. As in Sturm's definition, the geodesic need not be induced by `q`,
and `m` need not have full support. The condition is meaningful for `N ≥ 1`. -/
def CurvatureDimension (M : MetricMeasureSpace X) (K N : ℝ) : Prop :=
  ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
    ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    Bornology.IsBounded ((μ₀ : ProbabilityMeasure X) : Measure X).support →
    Bornology.IsBounded ((μ₁ : ProbabilityMeasure X) : Measure X).support →
    ∃ q : Measure (X × X),
      IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ (2 : ℝ)) q
        ((μ₀ : ProbabilityMeasure X) : Measure X) ((μ₁ : ProbabilityMeasure X) : Measure X) ∧
      ∃ γ : ℝ → WassersteinSpace 2 X, IsGeodesicSegment γ μ₀ μ₁ ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ((γ t : ProbabilityMeasure X) : Measure X) ≪ M.reference ∧
          Bornology.IsBounded ((γ t : ProbabilityMeasure X) : Measure X).support ∧
          ∀ N' ≥ N, renyiEntropy N' M.reference ((γ t : ProbabilityMeasure X) : Measure X) ≤
            -((∫⁻ z, (distortionTau K N' (1 - t) (dist z.1 z.2) *
                ((μ₀ : ProbabilityMeasure X) : Measure X).rnDeriv M.reference z.1 ^ (-N'⁻¹) +
              distortionTau K N' t (dist z.1 z.2) *
                ((μ₁ : ProbabilityMeasure X) : Measure X).rnDeriv M.reference z.2 ^ (-N'⁻¹)) ∂q :
                  ℝ≥0∞) : EReal)

/-- The curvature-dimension condition `CD(K, N)`, unfolded. -/
theorem curvatureDimension_iff : M.CurvatureDimension K N ↔
    ∀ ⦃μ₀ μ₁ : WassersteinSpace 2 X⦄,
      ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
      ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
      Bornology.IsBounded ((μ₀ : ProbabilityMeasure X) : Measure X).support →
      Bornology.IsBounded ((μ₁ : ProbabilityMeasure X) : Measure X).support →
      ∃ q : Measure (X × X),
        IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ (2 : ℝ)) q
          ((μ₀ : ProbabilityMeasure X) : Measure X) ((μ₁ : ProbabilityMeasure X) : Measure X) ∧
        ∃ γ : ℝ → WassersteinSpace 2 X, IsGeodesicSegment γ μ₀ μ₁ ∧
          ∀ t ∈ Icc (0 : ℝ) 1, ((γ t : ProbabilityMeasure X) : Measure X) ≪ M.reference ∧
            Bornology.IsBounded ((γ t : ProbabilityMeasure X) : Measure X).support ∧
            ∀ N' ≥ N, renyiEntropy N' M.reference ((γ t : ProbabilityMeasure X) : Measure X) ≤
              -((∫⁻ z, (distortionTau K N' (1 - t) (dist z.1 z.2) *
                  ((μ₀ : ProbabilityMeasure X) : Measure X).rnDeriv M.reference z.1 ^ (-N'⁻¹) +
                distortionTau K N' t (dist z.1 z.2) *
                  ((μ₁ : ProbabilityMeasure X) : Measure X).rnDeriv M.reference z.2 ^ (-N'⁻¹)) ∂q :
                    ℝ≥0∞) : EReal) :=
  Iff.rfl

/-- `CD(K, N)` implies `CD(K', N)` for every `K' ≤ K`: the distortion coefficient increases with
the curvature bound. -/
theorem CurvatureDimension.mono (h : M.CurvatureDimension K N) (hK : K' ≤ K) :
    M.CurvatureDimension K' N := by
  intro μ₀ μ₁ hac₀ hac₁ hb₀ hb₁
  obtain ⟨q, hq, γ, hγ, hall⟩ := h hac₀ hac₁ hb₀ hb₁
  refine ⟨q, hq, γ, hγ, fun t ht ↦ ?_⟩
  obtain ⟨hac, hb, hS⟩ := hall t ht
  refine ⟨hac, hb, fun N' hN' ↦ (hS N' hN').trans ?_⟩
  rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine lintegral_mono fun z ↦ add_le_add (mul_le_mul_left ?_ _) (mul_le_mul_left ?_ _)
  · exact distortionTau_left_monotone (sub_nonneg.2 ht.2) (sub_le_self _ ht.1) hK
  · exact distortionTau_left_monotone ht.1 ht.2 hK

/-- `CD(K, N)` implies `CD(K, N')` for every `N' ≥ N`: the defining inequality is required for
every dimension bound above `N`. -/
theorem CurvatureDimension.mono_dimension (h : M.CurvatureDimension K N) (hN : N ≤ N') :
    M.CurvatureDimension K N' := by
  intro μ₀ μ₁ hac₀ hac₁ hb₀ hb₁
  obtain ⟨q, hq, γ, hγ, hall⟩ := h hac₀ hac₁ hb₀ hb₁
  exact ⟨q, hq, γ, hγ, fun t ht ↦ (hall t ht).imp_right fun h' ↦
    h'.imp_right fun hS N'' hN'' ↦ hS N'' (hN.trans hN'')⟩

open scoped Real in
/-- **The generalised Bonnet–Myers theorem under `CD(K, N)`.** If `M` satisfies `CD(K, N)` with
`K > 0` and `N ≥ 1`, any two points of the support of the reference measure are at distance at
most `π √((N - 1) / K)`. -/
theorem CurvatureDimension.dist_le (h : M.CurvatureDimension K N) (hK : 0 < K) (hN : 1 ≤ N)
    {x y : X} (hx : x ∈ M.support) (hy : y ∈ M.support) : dist x y ≤ π * √((N - 1) / K) := by
  by_contra! hlt
  -- Uniform laws on small balls about `x` and `y`: all pairs of their points are beyond the
  -- Bonnet–Myers distance.
  set r := (dist x y - π * √((N - 1) / K)) / 2 with hr_def
  have hr : 0 < r := by linarith
  have hball (z : X) : ∀ᵐ w ∂M.reference[|ball z r], w ∈ ball z r := ae_cond_mem measurableSet_ball
  have hbdd (z : X) : Bornology.IsBounded (M.reference[|ball z r]).support :=
    isBounded_closedBall.subset (Measure.support_subset_of_isClosed isClosed_closedBall
      ((hball z).mono fun _ hw ↦ ball_subset_closedBall hw))
  have hpos {z : X} (hz : z ∈ M.support) : M.reference (ball z r) ≠ 0 :=
    ((M.mem_support_iff z).1 hz _ (ball_mem_nhds z hr)).ne'
  obtain ⟨μ₀, hμ₀, -, -⟩ := WassersteinSpace.exists_coe_eq_cond (p := 2) measurableSet_ball
    isBounded_ball (hpos hx) (M.finite_bounded _ isBounded_ball).ne
  obtain ⟨μ₁, hμ₁, -, -⟩ := WassersteinSpace.exists_coe_eq_cond (p := 2) measurableSet_ball
    isBounded_ball (hpos hy) (M.finite_bounded _ isBounded_ball).ne
  have hac₀ : ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference :=
    hμ₀ ▸ cond_absolutelyContinuous
  obtain ⟨q, hq, γ, hγ, hall⟩ := h hac₀ (hμ₁ ▸ cond_absolutelyContinuous) (hμ₀ ▸ hbdd x)
    (hμ₁ ▸ hbdd y)
  have hS := (hall 0 (left_mem_Icc.2 zero_le_one)).2.2 N le_rfl
  rw [hγ.source] at hS
  have : IsProbabilityMeasure q := hq.toIsCoupling.isProbabilityMeasure
  -- The entropy of `μ₀` is finite, since `μ₀` is carried by a ball of finite mass.
  refine renyiEntropy_ne_bot_of_measure_compl_eq_zero hN (A := ball x r)
    (by rw [hμ₀]; exact mem_ae_iff.1 (hball x)) (M.finite_bounded _ isBounded_ball).ne
    (le_bot_iff.1 (hS.trans_eq ?_))
  -- The right side at time `0` is `-∞`: the distortion coefficient is infinite `q`-a.e.
  rw [EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
  have h₀ : ∀ᵐ z ∂q, z.1 ∈ ball x r ∧
      ((μ₀ : ProbabilityMeasure X) : Measure X).rnDeriv M.reference z.1 ≠ ∞ :=
    hq.toIsCoupling.measurePreserving_fst.quasiMeasurePreserving.ae
      (((hμ₀ ▸ hball x : ∀ᵐ w ∂((μ₀ : ProbabilityMeasure X) : Measure X), w ∈ ball x r)).and
        (hac₀.ae_le (Measure.rnDeriv_ne_top _ _)))
  have h₁ : ∀ᵐ z ∂q, z.2 ∈ ball y r :=
    hq.toIsCoupling.measurePreserving_snd.quasiMeasurePreserving.ae (hμ₁ ▸ hball y)
  rw [lintegral_congr_ae (g := fun _ ↦ ∞) ?_, lintegral_const, measure_univ, mul_one]
  filter_upwards [h₀, h₁] with z ⟨hz₁, hρ⟩ hz₂
  rw [mem_ball] at hz₁ hz₂
  have hd : π * √((N - 1) / K) < dist z.1 z.2 := by
    linarith [dist_triangle4 x z.1 z.2 y, dist_comm x z.1]
  have hne : ((μ₀ : ProbabilityMeasure X) : Measure X).rnDeriv M.reference z.1 ^ (-N⁻¹) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hρ, zero_le_one.trans hN]
  rw [distortionTau_eq_top_of_lt hK hd, ENNReal.top_mul hne, top_add]

open scoped Real in
/-- **The Bonnet–Myers diameter bound under `CD(K, N)`**, for `K > 0` and `N ≥ 1`: the support of
the reference measure has diameter at most `π √((N - 1) / K)`. -/
theorem CurvatureDimension.diam_support_le (h : M.CurvatureDimension K N) (hK : 0 < K)
    (hN : 1 ≤ N) : diam M.support ≤ π * √((N - 1) / K) :=
  diam_le_of_forall_dist_le (by positivity) fun _ hx _ hy ↦ h.dist_le hK hN hx hy

open scoped Real in
/-- Under `CD(K, N)` with `K > 0` and `N ≥ 1`, the support of the reference measure is bounded. -/
theorem CurvatureDimension.isBounded_support (h : M.CurvatureDimension K N) (hK : 0 < K)
    (hN : 1 ≤ N) : Bornology.IsBounded M.support :=
  isBounded_iff.2 ⟨_, fun _ hx _ hy ↦ h.dist_le hK hN hx hy⟩

end MetricMeasureSpace

end CurvatureDimension

end TauCeti

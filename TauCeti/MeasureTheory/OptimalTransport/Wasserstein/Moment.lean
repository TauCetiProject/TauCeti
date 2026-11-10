/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FiniteMeasure.UniformIntegrable
public import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
public import TauCeti.MeasureTheory.OptimalTransport.Cost.WeakConvergence
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence
public import TauCeti.Topology.MetricSpace.DisplacementTail

/-!
# Wasserstein convergence and convergence of moments

For a finite exponent `1 ≤ p < ∞`, convergence in the `p`-Wasserstein distance is weak convergence
of probability measures together with convergence of the `p`-moments. This file proves both
halves of this classical characterization and assembles them on the finite-moment Wasserstein
space `TauCeti.WassersteinSpace p X` over a separable Borel pseudometric space.

The moment of a law about a basepoint `x` is its Wasserstein distance from the Dirac law at `x`
(`TauCeti.wassersteinEDist_dirac_left`), so the triangle inequality makes it a continuous
function on the Wasserstein space; this holds for every exponent, including `p = ∞`, in its
`eLpNorm` form. Together with `TauCeti.WassersteinSpace.continuous_toProbabilityMeasure`, which
gives weak convergence, this is the necessity half. Uniform integrability of the tails then follows
from the general criterion `TauCeti.exists_setLIntegral_le_of_tendsto_lintegral` for integrals of
unbounded continuous functions along weakly convergent families.

For the sufficiency half, a displacement larger than `2 R` forces one of the two endpoints to lie
at distance at least `R` from the basepoint, and then the displacement is at most twice that
distance. The `p`-th power of the displacement is therefore at most its truncation at `2 R` plus
`2 ^ p` times the `p`-moment tails beyond `R` of the two marginals
(`TauCeti.edist_rpow_le_min_add_indicator`). The tails are uniformly small
by the uniform integrability just described, and the transport cost of the bounded truncated cost
tends to `0` along weak convergence by
`TauCeti.tendsto_transportCost_of_tendsto_probabilityMeasure`.

## Main statements

* `TauCeti.WassersteinSpace.continuous_eLpNorm_edist` — the `L^p` norm of the distance to a
  basepoint is continuous on the Wasserstein space;
* `TauCeti.WassersteinSpace.continuous_lintegral_edist_rpow` — so is the `p`-moment
  `∫⁻ y, edist x y ^ p` (constantly `1` for `p = ∞`, where `p.toReal = 0`);
* `TauCeti.WassersteinSpace.continuous_integral_dist_rpow` — the same for the real-valued
  `p`-moment `∫ y, dist y x ^ p`, which is integrable by
  `TauCeti.WassersteinSpace.integrable_dist_rpow`;
* `TauCeti.exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral` — along a weakly convergent
  family whose `p`-moments converge to a finite limit, the `p`-moments have uniformly small tails;
* `TauCeti.WassersteinSpace.exists_setLIntegral_edist_rpow_le` — in particular, the `p`-moments
  have uniformly small tails along a `W_p`-convergent family;
* `TauCeti.tendsto_wassersteinEDist_of_tendsto_probabilityMeasure_of_tendsto_lintegral` — on a
  separable pseudometric space, weak convergence together with convergence of the `p`-moments to
  a finite limit gives convergence in the `p`-Wasserstein distance, for every finite nonzero
  exponent;
* `TauCeti.WassersteinSpace.tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral` — the
  characterization of convergence in the Wasserstein space.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Definition 6.8
  and Theorem 6.9.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, Proposition 7.1.5.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Tails

variable {X : Type*} [PseudoMetricSpace X]

variable [MeasurableSpace X] [OpensMeasurableSpace X]
  {p : ℝ≥0∞} {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}

/-- The mass of the closed region at distance at least `n` from a basepoint tends to `0` as `n`
tends to infinity. -/
theorem tendsto_measure_nndist_ge_atTop (μ : Measure X) [IsFiniteMeasure μ] (x : X) :
    Tendsto (fun n : ℕ ↦ μ {y | (n : ℝ≥0) ≤ nndist x y}) atTop (𝓝 0) := by
  have := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun n : ℕ ↦ {y | (n : ℝ≥0) ≤ nndist x y})
    (fun n ↦ (isClosed_le continuous_const
      (continuous_const.nndist continuous_id)).measurableSet.nullMeasurableSet)
    (fun m n hmn y hy ↦ (Nat.cast_le.2 hmn).trans hy) ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n : ℕ, {y | (n : ℝ≥0) ≤ nndist x y}) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (nndist x y)
    exact (not_le.2 hn) (mem_iInter.1 hy n)
  simpa [hempty, Function.comp_def] using this

/-- **Tightness of a weakly convergent family around a point.** Along a weakly convergent family
of probability measures, for every `ε > 0` there is a radius `R` such that eventually the mass
outside the ball of radius `R` about a basepoint is at most `ε`. -/
theorem exists_measure_nndist_ge_le_of_tendsto (h : Tendsto μs L (𝓝 μ)) (x : X) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, (μs i : Measure X) {y | R ≤ nndist x y} ≤ ε := by
  have hS (r : ℝ≥0) : IsClosed {y | r ≤ nndist x y} :=
    isClosed_le continuous_const (continuous_const.nndist continuous_id)
  obtain ⟨n, hn⟩ := ((tendsto_measure_nndist_ge_atTop (μ : Measure X) x).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨n, ?_⟩
  have hlt := lt_of_le_of_lt
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h (hS n)) hn
  filter_upwards [Filter.eventually_lt_of_limsup_lt hlt] with i hi using hi.le

/-- **Uniformly small moment tails.** Along a weakly convergent family of probability measures
whose `p`-moments about a basepoint converge to the finite `p`-moment of the limit, the
`p`-moments have uniformly small tails: for every `ε > 0` there is a radius `R` such that
eventually the part of the `p`-moment coming from distance at least `R` is at most `ε`. For
`p = 0` and `p = ∞`, where `p.toReal = 0`, it says that eventually the measures put mass at most
`ε` outside some ball about `x`. -/
theorem exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral
    (h : Tendsto μs L (𝓝 μ)) (x : X) (hμ : ∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X) ≠ ∞)
    (hlim : Tendsto (fun i ↦ ∫⁻ y, edist x y ^ p.toReal ∂(μs i : Measure X)) L
      (𝓝 (∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X)))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂(μs i : Measure X) ≤ ε := by
  by_cases hq : 0 < p.toReal
  swap
  · -- For `p = 0` and `p = ∞` the integrand is `1`, and the claim is a tail bound for the measures.
    have h0 : p.toReal = 0 := le_antisymm (not_lt.1 hq) ENNReal.toReal_nonneg
    simp only [h0, ENNReal.rpow_zero, lintegral_const, one_mul, Measure.restrict_apply_univ]
    exact exists_measure_nndist_ge_le_of_tendsto h x hε
  set g : X → ℝ≥0 := fun y ↦ nndist x y ^ p.toReal
  have hg : Continuous g := continuous_nndist_rpow_const hq.le x
  have hcoe (y : X) : (g y : ℝ≥0∞) = edist x y ^ p.toReal :=
    coe_nndist_rpow hq.le x y
  obtain ⟨R, hR⟩ := exists_setLIntegral_le_of_tendsto_lintegral hg
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).1 h)
    (by simpa [hcoe] using hμ) (by simpa [hcoe] using hlim) hε
  refine ⟨R ^ p.toReal⁻¹, hR.mono fun i hi ↦ ?_⟩
  have hset : {y | R ^ p.toReal⁻¹ ≤ nndist x y} = {y | R ≤ g y} := by
    ext y
    exact NNReal.rpow_inv_le_iff hq
  simpa [hset, hcoe] using hi

/-- The part of a moment coming from the open region beyond a radius is a weakly lower
semicontinuous function of the law, its integrand being lower semicontinuous. -/
theorem lowerSemicontinuous_setLIntegral_edist_rpow {q : ℝ} (x : X) (r : ℝ≥0) :
    LowerSemicontinuous fun ν : ProbabilityMeasure X ↦
      ∫⁻ y in {y | r < nndist x y}, edist x y ^ q ∂(ν : Measure X) := by
  have hU : IsOpen {y | r < nndist x y} :=
    isOpen_lt continuous_const (continuous_const.nndist continuous_id)
  have hG : Continuous fun y ↦ edist x y ^ q :=
    ENNReal.continuous_rpow_const.comp (continuous_const.edist continuous_id)
  simp_rw [← lintegral_indicator hU.measurableSet]
  refine lowerSemicontinuous_lintegral_probabilityMeasure <|
    lowerSemicontinuous_iff_isOpen_preimage.2 fun a ↦ ?_
  convert hU.inter ((isOpen_Ioi (a := a)).preimage hG) using 1
  ext y
  by_cases hy : r < nndist x y <;> simp [hy]

omit [OpensMeasurableSpace X] in
/-- A moment of a probability measure is at most the `q`-th power of a radius plus the part of
the moment coming from the open region beyond that radius. -/
theorem lintegral_edist_rpow_le_add {q : ℝ} (hq : 0 ≤ q) (ν : Measure X)
    [IsProbabilityMeasure ν] (x : X) (r : ℝ≥0) :
    ∫⁻ y, edist x y ^ q ∂ν ≤ (r : ℝ≥0∞) ^ q +
      ∫⁻ y in {y | r < nndist x y}, edist x y ^ q ∂ν := by
  calc ∫⁻ y, edist x y ^ q ∂ν
      ≤ ∫⁻ y, (r : ℝ≥0∞) ^ q +
          {y | r < nndist x y}.indicator (fun y ↦ edist x y ^ q) y ∂ν := by
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : r < nndist x y
        · simp [hy]
        · rw [indicator_of_notMem (s := {y | r < nndist x y}) hy, add_zero, edist_nndist]
          gcongr
          exact_mod_cast not_lt.1 hy
    _ ≤ (r : ℝ≥0∞) ^ q + ∫⁻ y in {y | r < nndist x y}, edist x y ^ q ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        exact add_le_add le_rfl (lintegral_indicator_le _ _)

/-- Along a weakly convergent family of laws whose `q`-moments have uniformly small tails over the
open regions beyond some radii, the `q`-moments converge to the `q`-moment of the limit. -/
theorem tendsto_lintegral_edist_rpow {q : ℝ} (hq : 0 < q) {γ : Type*} {L : Filter γ}
    {μs : γ → ProbabilityMeasure X} {μ : ProbabilityMeasure X} (h : Tendsto μs L (𝓝 μ)) (x : X)
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ r : ℝ≥0, ∀ᶠ i in L,
      ∫⁻ y in {y | r < nndist x y}, edist x y ^ q ∂(μs i : Measure X) ≤ ε) :
    Tendsto (fun i ↦ ∫⁻ y, edist x y ^ q ∂(μs i : Measure X)) L
      (𝓝 (∫⁻ y, edist x y ^ q ∂(μ : Measure X))) := by
  simp_rw [← coe_nndist_rpow hq.le x]
  refine tendsto_lintegral_of_forall_exists_setLIntegral_le
    (continuous_nndist_rpow_const hq.le x)
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).1 h) fun ε hε ↦ ?_
  obtain ⟨r, hr⟩ := htail ε hε
  refine ⟨(r + 1) ^ q, hr.mono fun i hi ↦ ?_⟩
  have hsub : {y | (r + 1) ^ q ≤ nndist x y ^ q} ⊆ {y | r < nndist x y} :=
    fun y hy ↦ (lt_add_one r).trans_le ((NNReal.rpow_le_rpow_iff hq).1 hy)
  simp_rw [coe_nndist_rpow hq.le x]
  exact (lintegral_mono_set hsub).trans hi

end Tails

namespace WassersteinSpace

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- The `L^p` norm of the distance to a basepoint, that is the `p`-th root of the `p`-moment
about that basepoint, is continuous on the Wasserstein space: it is the Wasserstein distance from
the Dirac law at the basepoint. -/
theorem continuous_eLpNorm_edist (x : X) :
    Continuous fun μ : WassersteinSpace p X ↦
      eLpNorm (fun y ↦ edist x y) p ((μ : ProbabilityMeasure X) : Measure X) := by
  refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun μ ν ↦ ?_
  rw [one_mul, edist_comm, edist_def, ← wassersteinEDist_dirac_left measurable_edist,
    ← wassersteinEDist_dirac_left measurable_edist]
  exact wassersteinEDist_triangle measurable_edist Fact.out _ _ _

/-- The `p`-moment `∫⁻ y, edist x y ^ p.toReal` about a basepoint is a continuous function on the
`p`-Wasserstein space. For `p = ∞` it is the constant `1`, since `p.toReal = 0`. -/
theorem continuous_lintegral_edist_rpow (x : X) :
    Continuous fun μ : WassersteinSpace p X ↦
      ∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) := by
  by_cases hp : p = ∞
  · subst hp
    simp only [ENNReal.toReal_top, ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one]
    exact continuous_const
  -- The measure varies, so the measurability side condition of `eLpNorm_rpow_eq_lintegral` has
  -- to be supplied once per measure rather than left to `simp_rw` to instantiate.
  have h : ∀ μ : WassersteinSpace p X,
      ∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X)
        = eLpNorm (fun y ↦ edist x y) p ((μ : ProbabilityMeasure X) : Measure X) ^ p.toReal :=
    fun _ ↦ (eLpNorm_rpow_eq_lintegral (zero_lt_one.trans_le Fact.out).ne' hp
      (measurable_const.edist measurable_id).aemeasurable).symm
  simp_rw [h]
  exact (ENNReal.continuous_rpow_const).comp (continuous_eLpNorm_edist x)

omit [SecondCountableTopology X] [StandardBorelSpace X] in
/-- The `p`-moment of a finite-moment law about any basepoint is finite. For `p = ∞` it is the
constant `1`, since `p.toReal = 0`. -/
private theorem lintegral_edist_rpow_ne_top (μ : WassersteinSpace p X) (x : X) :
    ∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) ≠ ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · simp
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  exact hasFiniteMoment_iff_lintegral_edist_rpow_ne_top hp0 hp x _ |>.1 (hasFiniteMoment μ)

omit [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)] in
/-- The `p`-th power of the distance to a basepoint is integrable against every law with finite
`p`-moment. For `p = 0` and `p = ∞`, where `p.toReal = 0`, it is the constant `1`. -/
theorem integrable_dist_rpow (μ : WassersteinSpace p X) (x : X) :
    Integrable (fun y ↦ dist y x ^ p.toReal) ((μ : ProbabilityMeasure X) : Measure X) := by
  by_cases hq : p.toReal = 0
  · simp only [hq, Real.rpow_zero]
    exact integrable_const _
  have hp0 : p ≠ 0 := fun h ↦ hq (by simp [h])
  have hp : p ≠ ∞ := fun h ↦ hq (by simp [h])
  simpa only [Real.norm_eq_abs, abs_dist] using
    (memLp_dist_iff_memLp_edist.2 ((hasFiniteMoment μ).memLp
      measurable_edist_right.aestronglyMeasurable)).integrable_norm_rpow hp0 hp

/-- The integral `∫ d(y, x)^p dμ(y)` of the `p`-th power of the distance to a basepoint is a
continuous real function on the `p`-Wasserstein space. For `p = ∞` it is the constant `1`, since
`p.toReal = 0`. -/
theorem continuous_integral_dist_rpow (x : X) :
    Continuous fun μ : WassersteinSpace p X ↦
      ∫ y, dist y x ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) := by
  have h : ∀ μ : WassersteinSpace p X,
      ∫ y, dist y x ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) =
        (∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X)).toReal := by
    intro μ
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ by positivity)
      (integrable_dist_rpow μ x).aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun y ↦ ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg ENNReal.toReal_nonneg, edist_dist,
      dist_comm]
  simp_rw [h]
  exact ENNReal.continuousOn_toReal.comp_continuous (continuous_lintegral_edist_rpow x)
    fun μ ↦ lintegral_edist_rpow_ne_top μ x

/-- **Uniform integrability of moments along a `W_p`-convergent family.** For a finite exponent
`1 ≤ p < ∞`, along a family converging in the `p`-Wasserstein distance the `p`-moments about any
basepoint have uniformly small tails: for every `ε > 0` there is a radius `R` such that eventually
the part of the `p`-moment coming from distance at least `R` is at most `ε`. -/
theorem exists_setLIntegral_edist_rpow_le {γ : Type*} {L : Filter γ}
    {μs : γ → WassersteinSpace p X} {μ : WassersteinSpace p X} (h : Tendsto μs L (𝓝 μ)) (x : X)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂((μs i : ProbabilityMeasure X) : Measure X) ≤ ε :=
  exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral
    ((continuous_toProbabilityMeasure.tendsto μ).comp h) x (lintegral_edist_rpow_ne_top μ x)
    (((continuous_lintegral_edist_rpow x).tendsto μ).comp h) hε

end WassersteinSpace

section Sufficiency

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {p : ℝ≥0∞} {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}

/-- The `2 ^ q`-multiple of the `q`-moment of `ν` beyond radius `R` is at most `2 ^ q * τ`, if the
`q`-moment of `ν` beyond some smaller radius `R'` is at most `τ`. -/
private theorem lintegral_const_mul_indicator_edist_rpow_le {q : ℝ} (hq : 0 ≤ q) (x : X)
    {R R' : ℝ≥0} (hR' : R' ≤ R) {ν : Measure X} {τ : ℝ≥0∞}
    (hν : ∫⁻ y in {y | R' ≤ nndist x y}, edist x y ^ q ∂ν ≤ τ) :
    ∫⁻ y, 2 ^ q * {w | R ≤ nndist x w}.indicator (fun w ↦ edist x w ^ q) y ∂ν ≤ 2 ^ q * τ := by
  have hS : MeasurableSet {w | R ≤ nndist x w} :=
    measurableSet_le measurable_const (continuous_const.nndist continuous_id).measurable
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofNat_ne_top),
    lintegral_indicator hS]
  gcongr
  exact (lintegral_mono_set (s := {y | R ≤ nndist x y}) (t := {y | R' ≤ nndist x y})
    fun y (hy : R ≤ nndist x y) ↦ hR'.trans hy).trans hν

/-- **Weak convergence and convergence of moments give Wasserstein convergence.** On a separable
pseudometric space, let probability measures `μᵢ` converge weakly to `μ`, and let their
`p`-moments about a basepoint `x` converge to the finite `p`-moment of `μ`. Then for every finite
nonzero exponent `p` the `p`-Wasserstein distance from `μᵢ` to `μ` tends to `0`. -/
theorem tendsto_wassersteinEDist_of_tendsto_probabilityMeasure_of_tendsto_lintegral
    [TopologicalSpace.SeparableSpace X] (hp0 : p ≠ 0) (hp : p ≠ ∞) (h : Tendsto μs L (𝓝 μ)) (x : X)
    (hμ : ∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X) ≠ ∞)
    (hlim : Tendsto (fun i ↦ ∫⁻ y, edist x y ^ p.toReal ∂(μs i : Measure X)) L
      (𝓝 (∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X)))) :
    Tendsto (fun i ↦ wassersteinEDist p (μs i : Measure X) (μ : Measure X)) L (𝓝 0) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- It suffices that the transport cost of `edist ^ p` tends to `0`.
  suffices hc : Tendsto (fun i ↦ transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal)
      (μs i : Measure X) (μ : Measure X)) L (𝓝 0) by
    simp_rw [wassersteinEDist_eq_transportCost_rpow measurable_edist hp0 hp]
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.2 hq)] using
      ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp hc
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have h2q : (2 : ℝ≥0∞) ^ p.toReal ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofNat_ne_top
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- The tails beyond a common radius `R` are at most `τ` for the family and for the limit.
  obtain ⟨τ, hτ, hτε⟩ : ∃ τ > 0, 2 ^ p.toReal * τ + 2 ^ p.toReal * τ ≤ ε / 2 := by
    refine ⟨ε / 2 / 2 / 2 ^ p.toReal, ENNReal.div_pos (ENNReal.half_pos hε2.ne').ne' h2q, ?_⟩
    calc 2 ^ p.toReal * (ε / 2 / 2 / 2 ^ p.toReal) + 2 ^ p.toReal * (ε / 2 / 2 / 2 ^ p.toReal)
        ≤ ε / 2 / 2 + ε / 2 / 2 := add_le_add ENNReal.mul_div_le ENNReal.mul_div_le
      _ = ε / 2 := ENNReal.add_halves _
  obtain ⟨R₁, hR₁⟩ :=
    exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral h x hμ hlim hτ
  obtain ⟨R₂, hR₂⟩ :=
    exists_setLIntegral_edist_rpow_le_of_tendsto_lintegral (L := (⊤ : Filter Unit))
    (μs := fun _ ↦ μ) tendsto_const_nhds x hμ tendsto_const_nhds hτ
  set R : ℝ≥0 := max R₁ R₂
  set S : Set X := {w | R ≤ nndist x w}
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const (continuous_const.nndist continuous_id).measurable
  have hf : Measurable fun w ↦ 2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) w :=
    (((continuous_const.edist continuous_id).measurable.pow_const _).indicator hS).const_mul _
  have hcore := tendsto_transportCost_min_edist_rpow_of_tendsto_probabilityMeasure hp0 hp (2 * R) h
  filter_upwards [hcore.eventually (ge_mem_nhds hε2), hR₁] with i hi hRi
  calc transportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) (μs i : Measure X) μ
      ≤ transportCost (fun z : X × X ↦ min (edist z.1 z.2) (2 * R) ^ p.toReal +
          2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) z.1 +
          2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) z.2)
          (μs i : Measure X) μ :=
        transportCost_mono fun z ↦ edist_rpow_le_min_add_indicator x R z.1 z.2
    _ = transportCost (fun z : X × X ↦ min (edist z.1 z.2) (2 * R) ^ p.toReal)
          (μs i : Measure X) μ +
          ∫⁻ y, 2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) y ∂(μs i : Measure X) +
          ∫⁻ y, 2 ^ p.toReal * S.indicator (fun w ↦ edist x w ^ p.toReal) y ∂(μ : Measure X) :=
        transportCost_add_split hf hf
    _ ≤ ε / 2 + 2 ^ p.toReal * τ + 2 ^ p.toReal * τ :=
        add_le_add (add_le_add hi
          (lintegral_const_mul_indicator_edist_rpow_le hq.le x (le_max_left _ _) hRi))
          (lintegral_const_mul_indicator_edist_rpow_le hq.le x (le_max_right _ _)
            (eventually_top.1 hR₂ ()))
    _ ≤ ε / 2 + ε / 2 := by
        rw [add_assoc]
        exact add_le_add le_rfl hτε
    _ = ε := ENNReal.add_halves ε

end Sufficiency

namespace WassersteinSpace

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- **Convergence in the Wasserstein space.** For a finite exponent `1 ≤ p < ∞` and any
basepoint `x`, a family of finite-moment laws converges in the `p`-Wasserstein distance exactly
when it converges weakly and its `p`-moments about `x` converge to the `p`-moment of the limit. -/
theorem tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral (hp : p ≠ ∞) {γ : Type*}
    {L : Filter γ} {μs : γ → WassersteinSpace p X} {μ : WassersteinSpace p X} (x : X) :
    Tendsto μs L (𝓝 μ) ↔
      Tendsto (fun i ↦ (μs i : ProbabilityMeasure X)) L (𝓝 (μ : ProbabilityMeasure X)) ∧
        Tendsto (fun i ↦ ∫⁻ y, edist x y ^ p.toReal ∂((μs i : ProbabilityMeasure X) : Measure X))
          L (𝓝 (∫⁻ y, edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X))) := by
  refine ⟨fun h ↦ ⟨(continuous_toProbabilityMeasure.tendsto μ).comp h,
    ((continuous_lintegral_edist_rpow x).tendsto μ).comp h⟩, fun ⟨hw, hm⟩ ↦ ?_⟩
  rw [tendsto_iff_edist_tendsto_0]
  simpa only [edist_def] using
    tendsto_wassersteinEDist_of_tendsto_probabilityMeasure_of_tendsto_lintegral
      (zero_lt_one.trans_le Fact.out).ne' hp hw x
      (lintegral_edist_rpow_ne_top μ x) hm

end WassersteinSpace

end TauCeti

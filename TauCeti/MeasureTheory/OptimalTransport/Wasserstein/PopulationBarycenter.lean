/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Barycenter
import TauCeti.Data.ENNReal.Weights
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.FrechetMean.Selection
import TauCeti.MeasureTheory.Measure.FrechetMean.Stability
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Compactness
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FiniteSupport
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Kernel.Basic
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Kernel.Moment
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Separable
import TauCeti.Probability.Kernel.ProbabilityMeasure

/-!
# Existence of population Wasserstein barycenters

Let `X` be a proper metric space and `1 ≤ p < ∞`. A law `P` on the Wasserstein space `P_p(X)` with
finite `p`-th moment has a `p`-Fréchet barycenter in `P_p(X)`, a minimizer of
`ν ↦ ∫ W_p(ν, μ) ^ p dP(μ)`. This is the existence theorem of Le Gouic and Loubes. Its proof
approximates `P` in `W_p` by finitely supported laws `P n`, which have barycenters `b n` by
`TauCeti.WassersteinSpace.exists_isFrechetBarycenter_sum_smul_dirac`. The space `P_p(X)` is not
proper, so the barycenters `b n` need not cluster for free; the main step is that they do.

The reason is a tail estimate. Let `ν` be a barycenter of `∑ j, w j • δ_{μ j}`. By
`TauCeti.WassersteinSpace.exists_ae_isFrechetBarycenter_sum_smul_dirac`, almost every point `y`
of `ν` is a barycenter of a weighted configuration `∑ j, w j • δ_{x j}`, where the configurations
`x` are distributed as a multi-coupling of the laws `μ j`. Such a point satisfies
`d(z, y) ≤ 2 (∑ j, w j * d(z, x j) ^ p) ^ (1 / p)` for every `z`. So the part of the `p`-th moment
of `ν` beyond distance `4 R` from `z` is at most `2 ^ (p + 1)` times the part of the `p`-th moment
of the mixture `∑ j, w j • μ j` beyond distance `R`. When `P n → P`, the mixtures converge in
`P_p(X)` by `TauCeti.wassersteinEDist_comp_le_mul`, so their `p`-th moments are uniformly
integrable. Hence so are those of the barycenters `b n`, which are therefore relatively compact in
`P_p(X)`, and every limit point is a barycenter of `P` by the stability theorem
`TauCeti.isFrechetBarycenter_of_mapClusterPt`.

## Main statements

* `TauCeti.WassersteinSpace.setLIntegral_edist_rpow_le_of_isFrechetBarycenter_sum_smul_dirac` —
  the tails of the `p`-th moment of a barycenter of `∑ j, w j • δ_{μ j}` are dominated by those of
  the laws `μ j`.
* `TauCeti.WassersteinSpace.isCompact_closure_range_of_isFrechetBarycenter` — barycenters of
  finitely supported laws converging in `W_p` form a relatively compact sequence in `P_p(X)`.
* `TauCeti.WassersteinSpace.exists_isFrechetBarycenter_tendsto_comp` — some subsequence of such
  barycenters converges to a barycenter of the limit law.
* `TauCeti.WassersteinSpace.exists_isFrechetBarycenter` — every law of finite `p`-th moment on
  `P_p(X)` has a `p`-Fréchet barycenter.

## References

* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Relat. Fields 168 (2017), 901--917, for the existence of population barycenters
  by approximation with finitely supported laws.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {p : ℝ≥0∞}

omit [ProperSpace X] in
/-- A `p`-Fréchet barycenter `y` of the weighted law `∑ j, w j • δ_{x j}` lies within twice its
Fréchet radius from any point `z`. So if `d(z, y) ≥ 4 R`, then `d(z, y) ^ p` is at most
`2 * 2 ^ p` times the weighted sum of the `d(z, x j) ^ p` with `d(z, x j) ≥ R`. -/
private theorem indicator_edist_rpow_le_of_isFrechetBarycenter {J : Type*} [Fintype J]
    {w : J → ℝ≥0} (hp : 1 ≤ p) (hp_top : p ≠ ∞) (hw : ∑ j, w j = 1) {x : J → X} {y : X}
    (hy : IsFrechetBarycenter p (∑ j, w j • Measure.dirac (x j)) y) (z : X) (R : ℝ≥0) :
    {u | 4 * R ≤ nndist z u}.indicator (fun u ↦ edist z u ^ p.toReal) y ≤
      2 * 2 ^ p.toReal * ∑ j, (w j : ℝ≥0∞) *
        {u | R ≤ nndist z u}.indicator (fun u ↦ edist z u ^ p.toReal) (x j) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  set f : X → ℝ≥0∞ := fun u ↦ edist z u ^ p.toReal
  by_cases hy₄ : y ∈ {u : X | 4 * R ≤ nndist z u}
  swap
  · simp [indicator_of_notMem hy₄]
  rw [indicator_of_mem hy₄]
  set m := ∑ j, w j • Measure.dirac (x j)
  have := isProbabilityMeasure_sum_smul_dirac hw x
  -- `H` is the weighted cost of `z` against the configuration `x`.
  set H := ∑ j, (w j : ℝ≥0∞) * f (x j)
  have hH : frechetRadius p m z ^ p.toReal = H := by
    rw [frechetRadius_rpow_eq_frechetPower hp0 hp_top
      (continuous_const.edist continuous_id).measurable.aemeasurable,
      frechetPower_sum_smul_dirac]
    simp only [ENNReal.smul_def, smul_eq_mul, H, f]
  -- The barycenter `y` of `m` is within twice the Fréchet radius of `z`.
  have hD : f y ≤ 2 ^ p.toReal * H := by
    calc f y ≤ (2 * frechetRadius p m z) ^ p.toReal :=
          ENNReal.rpow_le_rpow (hy.edist_le_two_mul_frechetRadius hp z) hpos.le
      _ = 2 ^ p.toReal * H := by rw [ENNReal.mul_rpow_of_nonneg _ _ hpos.le, hH]
  -- Since `d(z, y) ≥ 4 R`, the weighted cost is at least `2 R ^ p`.
  have h₂ : 2 * (R : ℝ≥0∞) ^ p.toReal ≤ H := by
    have h22 : (2 : ℝ≥0∞) ≤ 2 ^ p.toReal := by
      have h1p : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
      simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le one_le_two h1p
    have h4 : ((4 * R : ℝ≥0) : ℝ≥0∞) ^ p.toReal ≤ f y :=
      ENNReal.rpow_le_rpow (by rw [edist_nndist]; exact_mod_cast hy₄) hpos.le
    refine (ENNReal.mul_le_mul_iff_right (show (2 : ℝ≥0∞) ^ p.toReal ≠ 0 by positivity)
      (by finiteness)).1 ?_
    calc 2 ^ p.toReal * (2 * (R : ℝ≥0∞) ^ p.toReal)
        ≤ 2 ^ p.toReal * (2 ^ p.toReal * (R : ℝ≥0∞) ^ p.toReal) := by gcongr
      _ = ((4 * R : ℝ≥0) : ℝ≥0∞) ^ p.toReal := by
          rw [ENNReal.coe_mul, show ((4 : ℝ≥0) : ℝ≥0∞) = 2 * 2 by norm_num,
            ENNReal.mul_rpow_of_nonneg _ _ hpos.le, ENNReal.mul_rpow_of_nonneg _ _ hpos.le,
            mul_assoc]
      _ ≤ 2 ^ p.toReal * H := h4.trans hD
  -- So `H` is at most twice its part over the points at distance at least `R` from `z`.
  have hRf (u : X) : u ∈ {u : X | R ≤ nndist z u} ↔ (R : ℝ≥0∞) ^ p.toReal ≤ f u := by
    rw [mem_ofPred_eq, ENNReal.rpow_le_rpow_iff hpos, edist_nndist, ENNReal.coe_le_coe]
  calc f y ≤ 2 ^ p.toReal * H := hD
    _ ≤ 2 ^ p.toReal * (2 * ∑ j, (w j : ℝ≥0∞) *
        if (R : ℝ≥0∞) ^ p.toReal ≤ f (x j) then f (x j) else 0) := by
      gcongr
      exact sum_mul_le_two_mul_sum_mul_ite hw (fun j ↦ f (x j))
        (ENNReal.rpow_ne_top_of_nonneg hpos.le ENNReal.coe_ne_top) h₂
    _ = 2 * 2 ^ p.toReal * ∑ j, (w j : ℝ≥0∞) * {u | R ≤ nndist z u}.indicator f (x j) := by
      simp only [indicator_apply, hRf]
      ring

namespace WassersteinSpace

/-- **Barycenters have dominated moment tails.** On a proper metric space, for `1 ≤ p < ∞` and
weights summing to `1`, let `ν` be a `p`-Fréchet barycenter in `P_p(X)` of the finitely supported
law `∑ j, w j • δ_{μ j}`. Then for every point `x` and radius `R`, the part of the `p`-th moment of
`ν` about `x` coming from distance at least `4 R` is at most `2 * 2 ^ p` times the weighted sum of
the parts of the `p`-th moments of the laws `μ j` coming from distance at least `R`. -/
theorem setLIntegral_edist_rpow_le_of_isFrechetBarycenter_sum_smul_dirac {J : Type*} [Fintype J]
    {w : J → ℝ≥0} [Fact (1 ≤ p)] (hp_top : p ≠ ∞) (hw : ∑ j, w j = 1)
    {μ : J → WassersteinSpace p X} {ν : WassersteinSpace p X}
    (hν : IsFrechetBarycenter p (∑ j, w j • Measure.dirac (μ j)) ν) (x : X) (R : ℝ≥0) :
    ∫⁻ y in {y | 4 * R ≤ nndist x y}, edist x y ^ p.toReal
        ∂((ν : ProbabilityMeasure X) : Measure X) ≤
      2 * 2 ^ p.toReal * ∑ j, (w j : ℝ≥0∞) * ∫⁻ y in {y | R ≤ nndist x y},
        edist x y ^ p.toReal ∂((μ j : ProbabilityMeasure X) : Measure X) := by
  -- Almost every point of `ν` is a barycenter of a configuration distributed as a multi-coupling
  -- of the laws `μ j`; integrate the pointwise bound against that joint law `Γ`.
  obtain ⟨Γ, hΓfst, hΓ, hae⟩ := exists_ae_isFrechetBarycenter_sum_smul_dirac hp_top hw hν
  set f : X → ℝ≥0∞ := fun y ↦ edist x y ^ p.toReal
  have hA (r : ℝ≥0) : MeasurableSet {y : X | r ≤ nndist x y} :=
    measurableSet_le measurable_const (continuous_const.nndist continuous_id).measurable
  have hfind (r : ℝ≥0) : Measurable ({y | r ≤ nndist x y}.indicator f) :=
    (measurable_edist_right.pow_const _).indicator (hA r)
  have hm (j : J) : Measurable fun q : X × (J → X) ↦ {y | R ≤ nndist x y}.indicator f (q.2 j) :=
    (hfind R).comp ((measurable_pi_apply j).comp measurable_snd)
  have hmarg (j : J) : ∫⁻ q, {y | R ≤ nndist x y}.indicator f (q.2 j) ∂Γ =
      ∫⁻ y in {y | R ≤ nndist x y}, f y ∂((μ j : ProbabilityMeasure X) : Measure X) := by
    rw [← lintegral_indicator (hA R), ← hΓ.marginal_eq j, Measure.snd,
      Measure.map_map (measurable_pi_apply j) measurable_snd,
      lintegral_map (hfind R) ((measurable_pi_apply j).comp measurable_snd)]
    rfl
  calc ∫⁻ y in {y | 4 * R ≤ nndist x y}, f y ∂((ν : ProbabilityMeasure X) : Measure X)
      = ∫⁻ q, {y | 4 * R ≤ nndist x y}.indicator f q.1 ∂Γ := by
        rw [← lintegral_indicator (hA _), ← hΓfst, Measure.fst,
          lintegral_map (hfind _) measurable_fst]
    _ ≤ ∫⁻ q, 2 * 2 ^ p.toReal * ∑ j, (w j : ℝ≥0∞) *
          {y | R ≤ nndist x y}.indicator f (q.2 j) ∂Γ :=
        lintegral_mono_ae (hae.mono fun q hq ↦
          indicator_edist_rpow_le_of_isFrechetBarycenter Fact.out hp_top hw hq x R)
    _ = 2 * 2 ^ p.toReal * ∑ j, (w j : ℝ≥0∞) *
          ∫⁻ y in {y | R ≤ nndist x y}, f y ∂((μ j : ProbabilityMeasure X) : Measure X) := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ ↦ (hm j).const_mul _),
          lintegral_finsetSum _ fun j _ ↦ (hm j).const_mul _]
        simp only [lintegral_const_mul _ (hm _), hmarg]

/-- If laws `P n` on `P_p(X)` of finite `p`-th moment converge in `W_p` to a probability law,
then the `p`-th moment tails of the laws they charge are uniformly small on average: the averaged
tail is that of the mixture `∫ μ dP n(μ)` on `X`, and these mixtures converge in `P_p(X)`, since
mixing is `1`-Lipschitz for `W_p`. -/
private theorem exists_lintegral_setLIntegral_edist_rpow_le [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    {P : ℕ → Measure (WassersteinSpace p X)} [∀ n, IsProbabilityMeasure (P n)]
    (hPmom : ∀ n, HasFiniteMoment p (P n)) {Q : Measure (WassersteinSpace p X)}
    [IsProbabilityMeasure Q] (hPQ : Tendsto (fun n ↦ wassersteinEDist p (P n) Q) atTop (𝓝 0))
    (x : X) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ n, ∫⁻ μ, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂((μ : ProbabilityMeasure X) : Measure X) ∂P n ≤ ε := by
  have hp : 1 ≤ p := Fact.out
  have : Fact (p ≠ ∞) := ⟨hp_top⟩
  obtain ⟨μ₀⟩ : Nonempty (WassersteinSpace p X) := nonempty_of_isProbabilityMeasure (P 0)
  -- The mixture kernel sends a law on `P_p(X)` to its mean law on `X`; it is `1`-Lipschitz.
  set κ : Kernel (WassersteinSpace p X) X := (Probability.samplingKernel X).comap
    (fun μ ↦ (μ : ProbabilityMeasure X)) measurable_toProbabilityMeasure
  have hκ (μ : WassersteinSpace p X) : κ μ = ((μ : ProbabilityMeasure X) : Measure X) := by
    simp [κ]
  have hκL (μ ν : WassersteinSpace p X) :
      wassersteinEDist p (κ μ) (κ ν) ≤ ((1 : ℝ≥0) : ℝ≥0∞) * edist μ ν := by
    rw [hκ, hκ, ENNReal.coe_one, one_mul, edist_def]
  have hmom (R : Measure (WassersteinSpace p X)) [IsProbabilityMeasure R]
      (hR : HasFiniteMoment p R) : HasFiniteMoment p (κ ∘ₘ R) :=
    hR.comp_kernel hp hp_top (x₀ := μ₀) (.of_forall fun μ ↦ hκL μ₀ μ)
      (by rw [hκ]; exact μ₀.hasFiniteMoment)
  have hQmom : HasFiniteMoment p Q := by
    obtain ⟨n, hn⟩ := (hPQ.eventually (gt_mem_nhds zero_lt_one)).exists
    exact (hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist
      (hPmom n)).2 hn.ne_top
  -- The mixtures of the laws `P n` converge in `P_p(X)` to the mixture of `Q`.
  set m : ℕ → WassersteinSpace p X := fun n ↦ mk ⟨κ ∘ₘ P n, inferInstance⟩ (hmom _ (hPmom n))
  set m₀ : WassersteinSpace p X := mk ⟨κ ∘ₘ Q, inferInstance⟩ (hmom _ hQmom)
  have hmcoe (n : ℕ) : ((m n : ProbabilityMeasure X) : Measure X) = κ ∘ₘ P n :=
    congrArg ProbabilityMeasure.toMeasure (coe_mk _ _)
  have hm₀coe : ((m₀ : ProbabilityMeasure X) : Measure X) = κ ∘ₘ Q :=
    congrArg ProbabilityMeasure.toMeasure (coe_mk _ _)
  have hm : Tendsto m atTop (𝓝 m₀) := by
    refine tendsto_iff_edist_tendsto_0.2 (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hPQ (fun _ ↦ bot_le) fun n ↦ ?_)
    rw [edist_def, hmcoe, hm₀coe]
    simpa using wassersteinEDist_comp_le_mul hp hp_top (hmom _ (hPmom n)) (hmom _ hQmom) hκL
  -- They form a compact set, so their moment tails are uniformly small.
  have hK := hm.isCompact_insert_range
  obtain ⟨R, hR⟩ := exists_setLIntegral_edist_rpow_le_of_isCompact_closure hp_top
    (hK.isClosed.closure_eq.symm ▸ hK) x hε
  refine ⟨R, fun n ↦ ?_⟩
  have hA : MeasurableSet {y : X | R ≤ nndist x y} :=
    measurableSet_le measurable_const (continuous_const.nndist continuous_id).measurable
  have hf : Measurable ({y : X | R ≤ nndist x y}.indicator fun y ↦ edist x y ^ p.toReal) :=
    (measurable_edist_right.pow_const _).indicator hA
  have hn := hR (m n) (mem_insert_of_mem _ (mem_range_self n))
  rw [hmcoe, ← lintegral_indicator hA, Measure.lintegral_bind κ.aemeasurable hf.aemeasurable]
    at hn
  simpa only [hκ, lintegral_indicator hA] using hn

/-- **Barycenters of converging finitely supported laws are relatively compact.** On a proper
metric space and for `1 ≤ p < ∞`, let laws `P n` on `P_p(X)`, each carried by a finite set,
converge in `W_p` to a probability law `Q`, and let `b n` be a `p`-Fréchet barycenter of `P n`.
Then the sequence `b` is relatively compact in `P_p(X)`. -/
theorem isCompact_closure_range_of_isFrechetBarycenter [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    {P : ℕ → Measure (WassersteinSpace p X)} [∀ n, IsProbabilityMeasure (P n)]
    (hfin : ∀ n, ∃ s : Finset (WassersteinSpace p X), ∀ᵐ μ ∂P n, μ ∈ s)
    {Q : Measure (WassersteinSpace p X)} [IsProbabilityMeasure Q]
    (hPQ : Tendsto (fun n ↦ wassersteinEDist p (P n) Q) atTop (𝓝 0))
    {b : ℕ → WassersteinSpace p X} (hb : ∀ n, IsFrechetBarycenter p (P n) (b n)) :
    IsCompact (closure (range b)) := by
  have : Fact (p ≠ ∞) := ⟨hp_top⟩
  obtain ⟨μ₀⟩ : Nonempty (WassersteinSpace p X) := nonempty_of_isProbabilityMeasure (P 0)
  obtain ⟨x⟩ : Nonempty X :=
    nonempty_of_isProbabilityMeasure ((μ₀ : ProbabilityMeasure X) : Measure X)
  have hPmom (n : ℕ) : HasFiniteMoment p (P n) := by
    obtain ⟨s, hs⟩ := hfin n
    exact hasFiniteMoment_of_ae_mem_finset μ₀ hs
  -- The moment tails of the barycenters are dominated by the averaged tails of the laws charged
  -- by the `P n`, which are uniformly small.
  refine (isCompact_closure_iff_exists_setLIntegral_edist_rpow_le hp_top x).2 fun ε hε ↦ ?_
  set C : ℝ≥0∞ := 2 * 2 ^ p.toReal
  have hC0 : C ≠ 0 := by positivity
  have hCtop : C ≠ ∞ := by finiteness
  obtain ⟨R, hR⟩ := exists_lintegral_setLIntegral_edist_rpow_le hp_top hPmom hPQ x
    (ENNReal.div_pos hε.ne' hCtop)
  refine ⟨4 * R, ?_⟩
  rintro _ ⟨n, rfl⟩
  obtain ⟨s, hs⟩ := hfin n
  obtain ⟨w, hw, hPn⟩ := exists_eq_sum_smul_dirac_of_ae_mem_finset hs
  have hbn := hb n
  have hRn := hR n
  rw [hPn] at hbn hRn
  simp only [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
    ENNReal.smul_def, smul_eq_mul] at hRn
  calc ∫⁻ y in {y | 4 * R ≤ nndist x y}, edist x y ^ p.toReal
        ∂((b n : ProbabilityMeasure X) : Measure X)
      ≤ C * ∑ j, (w j : ℝ≥0∞) * ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
          ∂(((j : WassersteinSpace p X) : ProbabilityMeasure X) : Measure X) :=
        setLIntegral_edist_rpow_le_of_isFrechetBarycenter_sum_smul_dirac hp_top hw hbn x R
    _ ≤ C * (ε / C) := by gcongr
    _ = ε := ENNReal.mul_div_cancel hC0 hCtop

/-- **Barycenters of converging finitely supported laws converge along a subsequence.** On a
proper metric space and for `1 ≤ p < ∞`, let laws `P n` on `P_p(X)`, each carried by a finite set,
converge in `W_p` to a probability law `Q`, and let `b n` be a `p`-Fréchet barycenter of `P n`.
Then some subsequence of `b` converges in `P_p(X)` to a `p`-Fréchet barycenter of `Q`. -/
theorem exists_isFrechetBarycenter_tendsto_comp [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    {P : ℕ → Measure (WassersteinSpace p X)} [∀ n, IsProbabilityMeasure (P n)]
    (hfin : ∀ n, ∃ s : Finset (WassersteinSpace p X), ∀ᵐ μ ∂P n, μ ∈ s)
    {Q : Measure (WassersteinSpace p X)} [IsProbabilityMeasure Q]
    (hPQ : Tendsto (fun n ↦ wassersteinEDist p (P n) Q) atTop (𝓝 0))
    {b : ℕ → WassersteinSpace p X} (hb : ∀ n, IsFrechetBarycenter p (P n) (b n)) :
    ∃ c, IsFrechetBarycenter p Q c ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (b ∘ φ) atTop (𝓝 c) := by
  have : Fact (p ≠ ∞) := ⟨hp_top⟩
  obtain ⟨c, -, φ, hφ, hlim⟩ := (isCompact_closure_range_of_isFrechetBarycenter hp_top hfin hPQ
    hb).tendsto_subseq fun n ↦ subset_closure (mem_range_self n)
  exact ⟨c, isFrechetBarycenter_of_mapClusterPt Fact.out hPQ (.of_forall hb)
    (hlim.mapClusterPt.of_comp hφ.tendsto_atTop), φ, hφ, hlim⟩

/-- **Existence of population Wasserstein barycenters** (Le Gouic–Loubes). On a proper metric
space and for `1 ≤ p < ∞`, every probability law `P` on the Wasserstein space `P_p(X)` with finite
`p`-th moment has a `p`-Fréchet barycenter in `P_p(X)`: a minimizer over `P_p(X)` of
`ν ↦ ∫ W_p(ν, μ) ^ p dP(μ)` at which this value is finite. -/
theorem exists_isFrechetBarycenter [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (P : Measure (WassersteinSpace p X)) [IsProbabilityMeasure P] (hP : HasFiniteMoment p P) :
    ∃ ν : WassersteinSpace p X, IsFrechetBarycenter p P ν := by
  have : Fact (p ≠ ∞) := ⟨hp_top⟩
  -- `P` is a limit in `W_p` of finitely supported laws.
  obtain ⟨Ps, hPs, hlim⟩ := mem_closure_iff_seq_limit.1
    (dense_setOfPred_ae_mem_finset (X := WassersteinSpace p X) hp_top (mk ⟨P, ‹_›⟩ hP))
  set P' : ℕ → Measure (WassersteinSpace p X) :=
    fun n ↦ ((Ps n : ProbabilityMeasure (WassersteinSpace p X)) : Measure (WassersteinSpace p X))
  have hfin (n : ℕ) : ∃ s : Finset (WassersteinSpace p X), ∀ᵐ μ ∂P' n, μ ∈ s := by
    obtain ⟨s, hs⟩ := hPs n
    exact ⟨s, ae_iff.2 hs⟩
  have hPQ : Tendsto (fun n ↦ wassersteinEDist p (P' n) P) atTop (𝓝 0) := by
    have hPcoe : ((mk ⟨P, ‹_›⟩ hP : ProbabilityMeasure (WassersteinSpace p X)) :
        Measure (WassersteinSpace p X)) = P := congrArg ProbabilityMeasure.toMeasure (coe_mk _ _)
    have h := tendsto_iff_edist_tendsto_0.1 hlim
    simp only [edist_def, hPcoe] at h
    exact h
  -- Each approximating law has a barycenter, and these cluster at a barycenter of `P`.
  have hb (n : ℕ) : ∃ ν : WassersteinSpace p X, IsFrechetBarycenter p (P' n) ν := by
    obtain ⟨s, hs⟩ := hfin n
    obtain ⟨w, hw, hPn⟩ := exists_eq_sum_smul_dirac_of_ae_mem_finset hs
    rw [hPn]
    exact exists_isFrechetBarycenter_sum_smul_dirac hp_top hw _
  choose b hb using hb
  obtain ⟨c, hc, -⟩ := exists_isFrechetBarycenter_tendsto_comp hp_top hfin hPQ hb
  exact ⟨c, hc⟩

end WassersteinSpace

end TauCeti

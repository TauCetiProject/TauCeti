/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Moment

import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.LowerSemicontinuous

/-!
# Relatively compact sets of the Wasserstein space

For a finite exponent `1 ≤ p < ∞` and a complete separable metric ground space `X`, a set `S` of
laws with finite `p`-moment is relatively compact in the Wasserstein space
`TauCeti.WassersteinSpace p X` exactly when

* it is tight, and
* its `p`-moments about a basepoint `x` have uniformly small tails: for every `ε > 0` there is a
  radius `R` with `∫⁻ y in {y | R ≤ dist x y}, dist x y ^ p ∂μ ≤ ε` for every `μ ∈ S`.

It is compact exactly when it is moreover closed. This is the compactness half of the description
of the `W_p` topology as weak convergence together with uniform integrability of `p`-moments, whose
convergence half is
`TauCeti.WassersteinSpace.tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral`. The criterion
does not depend on the basepoint, since the equivalence holds for each one.

The corresponding weak compactness criterion is Mathlib's Prokhorov theorem, stated in
`MeasureTheory.isTightMeasureSet_of_isCompact_closure` and
`MeasureTheory.isCompact_closure_of_isTightMeasureSet`.

Bounded sets of `P_p (X)` need not be relatively compact, even when `X = ℝ`, but they keep a
narrow form of compactness. By Markov's inequality, bounded sets are tight on a proper space. By
Prokhorov's theorem, a bounded tight sequence has a narrowly convergent subsequence, whose narrow
limit still has finite `p`-moment by narrow lower semicontinuity of the Wasserstein distance. This
is the compactness used by the direct method in the Wasserstein space.

## Main statements

All the following declarations are in the `TauCeti` namespace.

* `WassersteinSpace.isCompact_closure_of_isTightMeasureSet_of_exists_setLIntegral_edist_rpow_le`
  — a tight set with uniformly small `p`-moment tails is relatively compact, on a separable metric
  space;
* `WassersteinSpace.isTightMeasureSet_of_isCompact_closure` — a relatively compact set is
  tight, on a complete separable pseudometric space;
* `WassersteinSpace.exists_setLIntegral_edist_rpow_le_of_isCompact_closure` — a relatively
  compact set has uniformly small `p`-moment tails about every basepoint;
* `WassersteinSpace.isCompact_closure_iff_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le`,
  `WassersteinSpace.isCompact_iff_isClosed_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le`
  — the resulting characterizations of relatively compact and of compact sets;
* `ofReal_mul_measure_compl_closedBall_le_wassersteinEDist` — Markov's inequality for the
  Wasserstein distance from a Dirac law;
* `WassersteinSpace.isTightMeasureSet_of_isBounded` — on a proper space, bounded sets of `P_p (X)`
  are tight;
* `WassersteinSpace.hasFiniteMoment_of_isBounded_of_tendsto` — a narrow limit of a bounded family
  of `P_p (X)` has finite `p`-moment;
* `WassersteinSpace.exists_strictMono_tendsto_of_isBounded_of_isTightMeasureSet` — a bounded tight
  sequence of `P_p (X)` has a subsequence converging narrowly to a law of `P_p (X)`.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, §7.1.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Tail

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **Markov's inequality for the Wasserstein distance from a Dirac law.** For a probability
measure `μ` and a radius `r`, the mass of `μ` outside the closed ball of radius `r` about `x`,
multiplied by `r`, is at most `W_p (δ_x, μ)`, for every exponent `1 ≤ p`. -/
theorem ofReal_mul_measure_compl_closedBall_le_wassersteinEDist (x : X) (μ : ProbabilityMeasure X)
    (r : ℝ) :
    ENNReal.ofReal r * (μ : Measure X) (Metric.closedBall x r)ᶜ ≤
      wassersteinEDist p (Measure.dirac x) μ := by
  have hsub : (Metric.closedBall x r)ᶜ ⊆ {y | ENNReal.ofReal r ≤ ‖edist x y‖ₑ} := fun y hy ↦ by
    rw [mem_compl_iff, Metric.mem_closedBall, not_le, dist_comm] at hy
    rw [mem_ofPred_eq, enorm_eq_self, edist_dist]
    exact ENNReal.ofReal_le_ofReal hy.le
  calc ENNReal.ofReal r * (μ : Measure X) (Metric.closedBall x r)ᶜ
      ≤ ENNReal.ofReal r ^ (1 : ℝ≥0∞).toReal *
          (μ : Measure X) {y | ENNReal.ofReal r ≤ ‖edist x y‖ₑ} := by
        rw [ENNReal.toReal_one, ENNReal.rpow_one]
        gcongr
    _ ≤ eLpNorm (fun y ↦ edist x y) 1 μ ^ (1 : ℝ≥0∞).toReal :=
        mul_meas_ge_le_pow_eLpNorm' _ one_ne_zero ENNReal.one_ne_top _
    _ ≤ eLpNorm (fun y ↦ edist x y) p μ := by
        rw [ENNReal.toReal_one, ENNReal.rpow_one]
        exact eLpNorm_le_eLpNorm_of_exponent_le Fact.out
    _ = wassersteinEDist p (Measure.dirac x) μ :=
        (wassersteinEDist_dirac_left measurable_edist p x μ).symm

end Tail

namespace WassersteinSpace

private theorem coe_measure_set_eq {X : Type*} {p : ℝ≥0∞} [MeasurableSpace X]
    [PseudoMetricSpace X] {S : Set (WassersteinSpace p X)} :
    {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} =
      {((ν : ProbabilityMeasure X) : Measure X) |
        ν ∈ ((↑) '' S : Set (ProbabilityMeasure X))} := by
  ext
  simp

section Necessity

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- **A relatively compact set of the Wasserstein space is tight.** On a complete separable
pseudometric space, the laws of a relatively compact set of `P_p (X)` form a tight family. -/
theorem isTightMeasureSet_of_isCompact_closure [CompleteSpace X] {S : Set (WassersteinSpace p X)}
    (hS : IsCompact (closure S)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} := by
  have hS' : IsCompact (closure ((↑) '' S : Set (ProbabilityMeasure X))) :=
    (hS.image continuous_toProbabilityMeasure).closure_of_subset (image_mono subset_closure)
  rw [coe_measure_set_eq]
  exact MeasureTheory.isTightMeasureSet_of_isCompact_closure hS'

/-- **A relatively compact set of the Wasserstein space has uniformly integrable moments.** For a
finite exponent `1 ≤ p < ∞`, the `p`-moments about any basepoint of the laws of a relatively
compact set of `P_p (X)` have uniformly small tails: for every `ε > 0` there is a radius `R` such
that, for every law of the set, the part of its `p`-moment coming from distance at least `R` is at
most `ε`. -/
theorem exists_setLIntegral_edist_rpow_le_of_isCompact_closure (hp : p ≠ ∞)
    {S : Set (WassersteinSpace p X)} (hS : IsCompact (closure S)) (x : X) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ μ ∈ S, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε := by
  by_contra! h
  -- Laws of `S` whose tails beyond radius `n` exceed `ε` have a convergent subsequence, along
  -- which the tails beyond some fixed radius are eventually at most `ε`.
  choose μ hμS hμ using fun n : ℕ ↦ h n
  obtain ⟨ν, -, φ, hφ, hlim⟩ := hS.tendsto_subseq fun n ↦ subset_closure (hμS n)
  obtain ⟨R, hR⟩ := exists_setLIntegral_edist_rpow_le hp hlim x hε
  obtain ⟨n, hn, hRn⟩ := (hR.and (hφ.tendsto_atTop.eventually_ge_atTop ⌈R⌉₊)).exists
  refine (hμ (φ n)).not_ge ((lintegral_mono_set fun y hy ↦ ?_).trans hn)
  exact (Nat.le_ceil R).trans ((Nat.cast_le.2 hRn).trans hy)

end Necessity

section Sufficiency

variable {X : Type*} {p : ℝ≥0∞} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- **Tightness and uniformly integrable moments give relative compactness.** On a separable
metric space and for a finite exponent `1 ≤ p < ∞`, a set of laws of finite `p`-moment is
relatively compact in `P_p (X)` as soon as it is tight and its `p`-moments about a basepoint `x`
have uniformly small tails: for every `ε > 0` there is a radius `R` such that, for every law of the
set, the part of its `p`-moment coming from distance at least `R` is at most `ε`. -/
theorem isCompact_closure_of_isTightMeasureSet_of_exists_setLIntegral_edist_rpow_le
    (hp : p ≠ ∞) (x : X)
    {S : Set (WassersteinSpace p X)}
    (hT : IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S})
    (hU : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0, ∀ μ ∈ S, ∫⁻ y in {y | R ≤ nndist x y}, edist x y ^ p.toReal
      ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε) :
    IsCompact (closure S) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  choose R hR using hU
  have hK : IsCompact (closure ((↑) '' S : Set (ProbabilityMeasure X))) :=
    _root_.isCompact_closure_of_isTightMeasureSet <| by
    rw [← coe_measure_set_eq]
    exact hT
  set S' : Set (ProbabilityMeasure X) := (↑) '' S
  -- `S` lies in the set `T` of laws in the weak closure of `S` whose tails over the open regions
  -- beyond the radii `R ε` are at most `ε`; it suffices to show that `T` is compact.
  set T : Set (WassersteinSpace p X) := {μ | (μ : ProbabilityMeasure X) ∈ closure S' ∧
    ∀ ε (hε : 0 < ε), ∫⁻ y in {y | R ε hε < nndist x y}, edist x y ^ p.toReal
      ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε}
  refine exists_isCompact_superset_iff.1 ⟨T, isCompact_iff_ultrafilter_le_nhds.2 fun F hF ↦ ?_,
    fun μ hμ ↦ ⟨subset_closure (mem_image_of_mem _ hμ), fun ε hε ↦
      (lintegral_mono_set fun y hy ↦ le_of_lt (α := ℝ≥0) hy).trans (hR ε hε μ hμ)⟩⟩
  have hFT : ∀ᶠ μ in (F : Filter (WassersteinSpace p X)), μ ∈ T := le_principal_iff.1 hF
  -- By Prokhorov's theorem the ultrafilter converges weakly, to a law whose tails obey the same
  -- bounds by lower semicontinuity.
  obtain ⟨ν, hνK, hν⟩ := hK.ultrafilter_le_nhds (F.map (↑)) <| by
    rw [Ultrafilter.coe_map, le_principal_iff]
    exact hFT.mono fun μ hμ ↦ hμ.1
  have hlim : Tendsto (fun μ : WassersteinSpace p X ↦ (μ : ProbabilityMeasure X)) F (𝓝 ν) := by
    rwa [Tendsto, ← Ultrafilter.coe_map]
  have hνT (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∫⁻ y in {y | R ε hε < nndist x y}, edist x y ^ p.toReal ∂(ν : Measure X) ≤ ε :=
    ((lowerSemicontinuous_setLIntegral_edist_rpow (q := p.toReal) x (R ε hε)).isClosed_preimage
      ε).mem_of_tendsto hlim (hFT.mono fun μ hμ ↦ hμ.2 ε hε)
  -- The limit has finite `p`-moment, so it is a point of the Wasserstein space.
  have hνmem : HasFiniteMoment p (ν : Measure X) := by
    apply (hasFiniteMoment_iff_lintegral_edist_rpow_ne_top hp0 hp x _).2
    exact (lintegral_edist_rpow_le_add (q := p.toReal) ENNReal.toReal_nonneg _ x
      (R 1 one_pos)).trans_lt
      (ENNReal.add_lt_top.2 ⟨by finiteness, (hνT 1 one_pos).trans_lt ENNReal.one_lt_top⟩) |>.ne
  refine ⟨mk ν hνmem, ⟨by simpa using hνK, fun ε hε ↦ by simpa using hνT ε hε⟩, ?_⟩
  -- Weak convergence and convergence of the `p`-moments give convergence in `W_p`.
  have hmoment := tendsto_lintegral_edist_rpow (q := p.toReal) (ENNReal.toReal_pos hp0 hp) hlim x
    fun ε hε ↦ ⟨R ε hε, hFT.mono fun μ hμ ↦ hμ.2 ε hε⟩
  exact Filter.tendsto_id'.1 <|
    (tendsto_iff_tendsto_toProbabilityMeasure_and_lintegral hp x (μs := id)).2
      ⟨by simpa using hlim, by simpa using hmoment⟩

end Sufficiency

section Characterization

variable {X : Type*} {p : ℝ≥0∞} [MetricSpace X] [CompleteSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **Relatively compact sets of the Wasserstein space.** On a complete separable metric space and
for a finite exponent `1 ≤ p < ∞`, a set of laws of finite `p`-moment is relatively compact in
`P_p (X)` exactly when it is tight and its `p`-moments about a basepoint `x` have uniformly small
tails. -/
theorem isCompact_closure_iff_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le
    (hp : p ≠ ∞) (x : X)
    {S : Set (WassersteinSpace p X)} :
    IsCompact (closure S) ↔
      IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} ∧
        ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0, ∀ μ ∈ S, ∫⁻ y in {y | R ≤ nndist x y},
          edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε :=
  ⟨fun h ↦ ⟨isTightMeasureSet_of_isCompact_closure h,
      fun _ hε ↦ exists_setLIntegral_edist_rpow_le_of_isCompact_closure hp h x hε⟩,
    fun h ↦ isCompact_closure_of_isTightMeasureSet_of_exists_setLIntegral_edist_rpow_le hp x h.1
      h.2⟩

/-- **Compact sets of the Wasserstein space.** On a complete separable metric space and for a
finite exponent `1 ≤ p < ∞`, a set of laws of finite `p`-moment is compact in `P_p (X)` exactly
when it is closed, tight, and its `p`-moments about a basepoint `x` have uniformly small tails. -/
theorem isCompact_iff_isClosed_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le
    (hp : p ≠ ∞) (x : X)
    {S : Set (WassersteinSpace p X)} :
    IsCompact S ↔ IsClosed S ∧
      IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} ∧
        ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0, ∀ μ ∈ S, ∫⁻ y in {y | R ≤ nndist x y},
          edist x y ^ p.toReal ∂((μ : ProbabilityMeasure X) : Measure X) ≤ ε := by
  rw [← isCompact_closure_iff_isTightMeasureSet_and_exists_setLIntegral_edist_rpow_le hp x]
  exact ⟨fun h ↦ ⟨h.isClosed, h.closure⟩,
    fun ⟨hc, h⟩ ↦ hc.closure_eq ▸ h⟩

end Characterization

section Tight

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **Bounded sets of the Wasserstein space are tight on a proper space.** On a proper
pseudometric space, the laws of a bounded set of `P_p (X)` form a tight family: by Markov's
inequality, the mass of a law `μ` outside the closed ball of radius `r > 0` about `x` is at most
`W_p (δ_x, μ) / r`. Bounded sets of `P_p (X)` need not be relatively compact in `P_p (X)`, whose
compact sets also have uniformly integrable `p`-moments. -/
theorem isTightMeasureSet_of_isBounded [StandardBorelSpace X] [ProperSpace X]
    {S : Set (WassersteinSpace p X)} (hS : Bornology.IsBounded S) :
    IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ S} := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨μ₀, hμ₀⟩
  · simp only [IsTightMeasureSet, mem_empty_iff_false, false_and, exists_false, ofPred_false,
      iSup_false, iSup_bot]
    exact (tendsto_const_nhds : Tendsto (fun _ : Set X ↦ (0 : ℝ≥0∞)) _ _)
  obtain ⟨x⟩ : Nonempty X := nonempty_of_isProbabilityMeasure (μ₀ : ProbabilityMeasure X)
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hS
  -- Every law of `S` is within `M` of `δ_x`.
  set M : ℝ≥0∞ := wassersteinEDist p (Measure.dirac x) (μ₀ : ProbabilityMeasure X) +
    ENNReal.ofReal C
  have hM : M ≠ ∞ := ENNReal.add_ne_top.2 ⟨(hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top
    measurable_edist x _).1 μ₀.hasFiniteMoment, ENNReal.ofReal_ne_top⟩
  have hbound : ∀ μ ∈ S, wassersteinEDist p (Measure.dirac x) (μ : ProbabilityMeasure X) ≤ M :=
    fun μ hμ ↦ (wassersteinEDist_triangle measurable_edist Fact.out _ _ _).trans <|
      add_le_add le_rfl ((edist_def μ₀ μ).symm.trans_le
        ((edist_le_ofReal (dist_nonneg.trans (hC hμ₀ hμ))).2 (hC hμ₀ hμ)))
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := x) ?_
  have hlim : Tendsto (fun r : ℝ ↦ M / ENNReal.ofReal r) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_div ENNReal.tendsto_ofReal_atTop (Or.inr hM)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) ((eventually_gt_atTop 0).mono fun r hr ↦ ?_)
  refine iSup₂_le fun ν ⟨μ, hμ, hν⟩ ↦ hν ▸ ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hr)) (Or.inl ENNReal.ofReal_ne_top),
    mul_comm]
  exact (ofReal_mul_measure_compl_closedBall_le_wassersteinEDist x _ r).trans (hbound μ hμ)

end Tight


section Narrow

variable {X : Type*} {p : ℝ≥0∞} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] [Fact (1 ≤ p)]

/-- **Narrow limits of bounded families have finite moment.** On a complete separable metric
space, if a bounded family of laws of `P_p (X)` converges narrowly to a probability measure `ν`,
then `ν` has finite `p`-moment: its Wasserstein distance from any law of the family is at most the
diameter of the family, by narrow lower semicontinuity of the Wasserstein distance. -/
theorem hasFiniteMoment_of_isBounded_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {v : ι → WassersteinSpace p X} (hv : Bornology.IsBounded (range v)) {ν : ProbabilityMeasure X}
    (h : Tendsto (fun i ↦ (v i : ProbabilityMeasure X)) l (𝓝 ν)) :
    HasFiniteMoment p (ν : Measure X) := by
  obtain ⟨i₀⟩ : Nonempty ι := l.nonempty_of_neBot
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hv
  refine (hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist
    (v i₀).hasFiniteMoment).2 (ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) ?_)
  refine (wassersteinEDist_le_liminf tendsto_const_nhds h p).trans <|
    liminf_le_of_frequently_le' (Frequently.of_forall fun i ↦ ?_)
  have hdist := hC (mem_range_self i₀) (mem_range_self i)
  exact (edist_def (v i₀) (v i)).symm.trans_le
    ((edist_le_ofReal (dist_nonneg.trans hdist)).2 hdist)

/-- **Narrow compactness of bounded tight sequences.** On a complete separable metric space, a
bounded sequence of `P_p (X)` whose laws form a tight family has a subsequence that converges
narrowly to a law of `P_p (X)`. Prokhorov's theorem gives the narrow limit and
`TauCeti.WassersteinSpace.hasFiniteMoment_of_isBounded_of_tendsto` its finite moment. The
subsequence need not converge in `P_p (X)`. -/
theorem exists_strictMono_tendsto_of_isBounded_of_isTightMeasureSet {v : ℕ → WassersteinSpace p X}
    (hv : Bornology.IsBounded (range v))
    (htight : IsTightMeasureSet {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ range v}) :
    ∃ ν : WassersteinSpace p X, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun n ↦ (v (ψ n) : ProbabilityMeasure X)) atTop (𝓝 ν) := by
  have hK : IsCompact (closure (range fun n ↦ (v n : ProbabilityMeasure X))) :=
    isCompact_closure_of_isTightMeasureSet (by simpa [range_comp] using htight)
  obtain ⟨ν, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq fun n ↦ subset_closure (mem_range_self n)
  have hv' : Bornology.IsBounded (range (v ∘ ψ)) := hv.subset (range_comp_subset_range ψ v)
  exact ⟨mk ν (hasFiniteMoment_of_isBounded_of_tendsto hv' hlim), ψ, hψ, by
    rw [coe_mk]
    exact hlim⟩

end Narrow

end WassersteinSpace

end TauCeti

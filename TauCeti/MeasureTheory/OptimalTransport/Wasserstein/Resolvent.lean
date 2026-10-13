/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PotentialEnergy
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import TauCeti.Analysis.GradientFlow.MoreauYosida.Existence
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.LowerSemicontinuous

/-!
# Existence of the Jordan–Kinderlehrer–Otto step

Let `φ` be an energy on the Wasserstein space `P_p(X)` of a complete separable metric space `X`,
and `τ > 0` a time step. One step of the *Jordan–Kinderlehrer–Otto scheme* (JKO scheme) for the
Wasserstein gradient flow of `φ`, started at a law `μ`, chooses a minimizer of

`ν ↦ φ ν + W_p (μ, ν) ^ 2 / (2τ)`,

that is, a point of the resolvent `TauCeti.moreauYosidaResolvent φ τ μ` of the metric theory of
gradient flows (for the quadratic scheme, `p = 2`). This file proves that such a step exists, and
hence that the JKO scheme can be run from every law, by the direct method of the calculus of
variations (`TauCeti.moreauYosidaResolvent_nonempty`).

The direct method cannot use the topology of `W_p` itself: bounded sets of `P_p(X)` are not
relatively compact, even when `X = ℝ`. It uses narrow convergence instead, that is, convergence
of the underlying probability measures against bounded continuous functions, for which the
following hold.

* The Wasserstein distance is narrowly lower semicontinuous
  (`TauCeti.wassersteinEDist_le_liminf`), so a narrow limit of a bounded sequence of `P_p(X)` still
  has finite `p`-moment (`TauCeti.WassersteinSpace.hasFiniteMoment_of_isBounded_of_tendsto`).
* A bounded tight sequence of `P_p(X)` has a narrowly convergent subsequence, by Prokhorov's
  theorem (`TauCeti.WassersteinSpace.exists_strictMono_tendsto_of_isBounded`).
* On a proper space, every bounded set of `P_p(X)` is tight, by Markov's inequality
  (`TauCeti.WassersteinSpace.isTightMeasureSet_of_isBounded`). This is the case of `X = ℝⁿ`.

The hypotheses on the energy are those of Ambrosio–Gigli–Savaré for the narrow topology: `φ` is
narrowly lower semicontinuous along bounded sequences, its bounded sublevels are tight (automatic
on a proper space), and it is coercive, `φ_{τ₀}(μ₀) > -∞` for some time step `τ₀` and law `μ₀`.
Then the resolvent is nonempty for every `0 < τ < τ₀` and every law
(`TauCeti.WassersteinSpace.moreauYosidaResolvent_nonempty`), and every law starts a JKO sequence
(`TauCeti.WassersteinSpace.exists_forall_mem_moreauYosidaResolvent`). Uniqueness of the step is a
separate matter, settled by convexity along generalized geodesics
(`TauCeti.GeneralizedGeodesicallyConvex.subsingleton_moreauYosidaResolvent`).

The potential energy `ν ↦ ∫ V dν` of a lower semicontinuous potential `V` bounded below meets
these hypotheses on a proper space, so its JKO step exists for every time step
(`TauCeti.WassersteinSpace.moreauYosidaResolvent_potentialEnergy_nonempty`).

## Main results

* `TauCeti.WassersteinSpace.isTightMeasureSet_of_isBounded`: on a proper space, bounded sets of
  `P_p(X)` are tight.
* `TauCeti.WassersteinSpace.hasFiniteMoment_of_isBounded_of_tendsto`: a narrow limit of a bounded
  family of `P_p(X)` has finite `p`-moment.
* `TauCeti.WassersteinSpace.exists_strictMono_tendsto_of_isBounded`: a bounded tight sequence of
  `P_p(X)` has a subsequence converging narrowly to a law of `P_p(X)`.
* `TauCeti.WassersteinSpace.moreauYosidaResolvent_nonempty`: existence of the JKO step for a
  narrowly lower semicontinuous coercive energy with tight bounded sublevels.
* `TauCeti.WassersteinSpace.exists_forall_mem_moreauYosidaResolvent`: existence of JKO sequences.
* `TauCeti.WassersteinSpace.moreauYosidaResolvent_nonempty_of_properSpace`: on a proper space,
  existence of the JKO step for a narrowly lower semicontinuous coercive energy.
* `TauCeti.WassersteinSpace.moreauYosidaResolvent_potentialEnergy_nonempty`: existence of the JKO
  step for the potential energy of a lower semicontinuous potential bounded below.

## References

* R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation of the Fokker–Planck
  equation*, SIAM J. Math. Anal. 29 (1998), 1–17.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, Assumption 2.1, Corollary 2.2.2 and
  Chapter 11.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace WassersteinSpace

section Tight

variable {X : Type*} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Fact (1 ≤ p)]

/-- **Markov's inequality for the Wasserstein distance from a Dirac law.** For a probability
measure `μ` and a radius `r`, the mass of `μ` outside the closed ball of radius `r` about `x`,
multiplied by `r`, is at most `W_p (δ_x, μ)`, for every exponent `1 ≤ p`. -/
private theorem ofReal_mul_measure_compl_closedBall_le (x : X) (μ : ProbabilityMeasure X) (r : ℝ) :
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
  exact (ofReal_mul_measure_compl_closedBall_le x _ r).trans (hbound μ hμ)

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
theorem exists_strictMono_tendsto_of_isBounded {v : ℕ → WassersteinSpace p X}
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

/-- The Wasserstein distance from a fixed law is lower semicontinuous along narrow convergence. -/
private theorem edist_le_liminf {μ ν : WassersteinSpace p X} {v : ℕ → WassersteinSpace p X}
    (h : Tendsto (fun n ↦ (v n : ProbabilityMeasure X)) atTop (𝓝 ν)) :
    edist μ ν ≤ liminf (fun n ↦ edist μ (v n)) atTop := by
  simp only [edist_def]
  exact wassersteinEDist_le_liminf tendsto_const_nhds h p

/-- A bounded sequence along which an energy with tight bounded sublevels is bounded above has a
narrowly convergent subsequence, in the form consumed by the abstract direct method. -/
private theorem exists_strictMono_tendsto_comap {φ : WassersteinSpace p X → EReal}
    (htight : ∀ (c : ℝ) ⦃S : Set (WassersteinSpace p X)⦄, Bornology.IsBounded S →
      (∀ ν ∈ S, φ ν ≤ c) → IsTightMeasureSet {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ S})
    (c : ℝ) ⦃v : ℕ → WassersteinSpace p X⦄ (hv : Metric.ediam (range v) ≠ ⊤)
    (hc : ∀ n, φ (v n) ≤ c) :
    ∃ ν : WassersteinSpace p X, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (v ∘ ψ) atTop (comap (↑) (𝓝 (ν : ProbabilityMeasure X))) := by
  have hv' := Metric.isBounded_iff_ediam_ne_top.2 hv
  obtain ⟨ν, ψ, hψ, hlim⟩ := exists_strictMono_tendsto_of_isBounded hv'
    (htight c hv' (forall_mem_range.2 hc))
  exact ⟨ν, ψ, hψ, tendsto_comap_iff.2 hlim⟩

/-- **Existence of the Jordan–Kinderlehrer–Otto step.** Let `X` be a complete separable metric
space, `1 ≤ p`, and `φ` an energy on `P_p (X)` such that

* `φ` is narrowly lower semicontinuous along bounded sequences: if a bounded sequence `v` of
  `P_p (X)` converges narrowly to `ν`, then `φ ν ≤ liminf φ (v n)`;
* the bounded sublevels of `φ` are tight;
* `φ` is coercive: `φ_{τ₀}(μ₀) > -∞` for some time step `τ₀` and law `μ₀`.

Then for every time step `0 < τ < τ₀` and every law `μ` of `P_p (X)`, some law `ν` minimizes
`φ ν + W_p (μ, ν) ^ 2 / (2τ)`. -/
theorem moreauYosidaResolvent_nonempty {φ : WassersteinSpace p X → EReal} {τ τ₀ : ℝ≥0}
    {μ₀ : WassersteinSpace p X}
    (hφ : ∀ ⦃v : ℕ → WassersteinSpace p X⦄ ⦃ν : WassersteinSpace p X⦄,
      Bornology.IsBounded (range v) →
      Tendsto (fun n ↦ (v n : ProbabilityMeasure X)) atTop (𝓝 ν) →
      φ ν ≤ liminf (fun n ↦ φ (v n)) atTop)
    (htight : ∀ (c : ℝ) ⦃S : Set (WassersteinSpace p X)⦄, Bornology.IsBounded S →
      (∀ ν ∈ S, φ ν ≤ c) → IsTightMeasureSet {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ S})
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) (h₀ : moreauYosida φ τ₀ μ₀ ≠ ⊥) (μ : WassersteinSpace p X) :
    (moreauYosidaResolvent φ τ μ).Nonempty :=
  TauCeti.moreauYosidaResolvent_nonempty (l := fun ν ↦ comap (↑) (𝓝 (ν : ProbabilityMeasure X)))
    (fun _ _ h ↦ edist_le_liminf (tendsto_comap_iff.1 h))
    (fun _ _ hv h ↦ hφ (Metric.isBounded_iff_ediam_ne_top.2 hv) (tendsto_comap_iff.1 h))
    (exists_strictMono_tendsto_comap htight) hτ hττ₀ (edist_ne_top μ μ₀) h₀

/-- **Existence of Jordan–Kinderlehrer–Otto sequences.** Under the hypotheses of
`TauCeti.WassersteinSpace.moreauYosidaResolvent_nonempty`, every law `μ` of `P_p (X)` starts a
sequence `u` with `u 0 = μ` in which each `u (n + 1)` is a JKO step of time step `τ` from
`u n`. -/
theorem exists_forall_mem_moreauYosidaResolvent {φ : WassersteinSpace p X → EReal}
    {τ τ₀ : ℝ≥0} {μ₀ : WassersteinSpace p X}
    (hφ : ∀ ⦃v : ℕ → WassersteinSpace p X⦄ ⦃ν : WassersteinSpace p X⦄,
      Bornology.IsBounded (range v) →
      Tendsto (fun n ↦ (v n : ProbabilityMeasure X)) atTop (𝓝 ν) →
      φ ν ≤ liminf (fun n ↦ φ (v n)) atTop)
    (htight : ∀ (c : ℝ) ⦃S : Set (WassersteinSpace p X)⦄, Bornology.IsBounded S →
      (∀ ν ∈ S, φ ν ≤ c) → IsTightMeasureSet {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ S})
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) (h₀ : moreauYosida φ τ₀ μ₀ ≠ ⊥) (μ : WassersteinSpace p X) :
    ∃ u : ℕ → WassersteinSpace p X, u 0 = μ ∧
      ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n) :=
  TauCeti.exists_forall_mem_moreauYosidaResolvent
    (l := fun ν ↦ comap (↑) (𝓝 (ν : ProbabilityMeasure X)))
    (fun _ _ _ h ↦ edist_le_liminf (tendsto_comap_iff.1 h))
    (fun _ _ hv h ↦ hφ (Metric.isBounded_iff_ediam_ne_top.2 hv) (tendsto_comap_iff.1 h))
    (exists_strictMono_tendsto_comap htight) hτ hττ₀ (edist_ne_top μ μ₀) h₀

/-- **Existence of the Jordan–Kinderlehrer–Otto step on a proper space.** On a proper metric
space, such as `ℝⁿ`, bounded sets of `P_p (X)` are tight, so the JKO step exists for every energy
that is narrowly lower semicontinuous along bounded sequences and coercive,
`φ_{τ₀}(μ₀) > -∞`: for every time step `0 < τ < τ₀` and every law `μ`, some law `ν` minimizes
`φ ν + W_p (μ, ν) ^ 2 / (2τ)`. -/
theorem moreauYosidaResolvent_nonempty_of_properSpace [ProperSpace X]
    {φ : WassersteinSpace p X → EReal} {τ τ₀ : ℝ≥0} {μ₀ : WassersteinSpace p X}
    (hφ : ∀ ⦃v : ℕ → WassersteinSpace p X⦄ ⦃ν : WassersteinSpace p X⦄,
      Bornology.IsBounded (range v) →
      Tendsto (fun n ↦ (v n : ProbabilityMeasure X)) atTop (𝓝 ν) →
      φ ν ≤ liminf (fun n ↦ φ (v n)) atTop)
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) (h₀ : moreauYosida φ τ₀ μ₀ ≠ ⊥) (μ : WassersteinSpace p X) :
    (moreauYosidaResolvent φ τ μ).Nonempty :=
  moreauYosidaResolvent_nonempty hφ (fun _ _ hS _ ↦ isTightMeasureSet_of_isBounded hS) hτ hττ₀ h₀ μ

/-- **The JKO step for a potential energy.** On a proper complete separable metric space, let `V`
be a lower semicontinuous potential bounded below. Then for every time step `τ > 0` and every law
`μ` of `P_p (X)`, some law `ν` of `P_p (X)` minimizes `∫ V dν + W_p (μ, ν) ^ 2 / (2τ)`. -/
theorem moreauYosidaResolvent_potentialEnergy_nonempty [ProperSpace X] {V : X → ℝ}
    (hV : LowerSemicontinuous V) (hb : BddBelow (range V)) {τ : ℝ≥0} (hτ : 0 < τ)
    (μ : WassersteinSpace p X) :
    (moreauYosidaResolvent
      (fun ν : WassersteinSpace p X ↦ potentialEnergy V ((ν : ProbabilityMeasure X) : Measure X))
      τ μ).Nonempty := by
  have hlsc := lowerSemicontinuous_potentialEnergy hV hb
  obtain ⟨c, hc⟩ := hb
  -- The energy is bounded below by `c`, so its Moreau–Yosida approximations are too.
  have hge : ∀ ν : WassersteinSpace p X,
      (c : EReal) ≤ potentialEnergy V ((ν : ProbabilityMeasure X) : Measure X) := fun ν ↦ by
    calc (c : EReal) = potentialEnergy (fun _ ↦ c) ((ν : ProbabilityMeasure X) : Measure X) := by
          rw [potentialEnergy_of_integrable (integrable_const c), integral_const, probReal_univ,
            one_smul]
      _ ≤ _ := potentialEnergy_mono (.of_forall fun x ↦ hc (mem_range_self x))
  refine moreauYosidaResolvent_nonempty_of_properSpace (τ₀ := τ + 1) (μ₀ := μ)
    (fun v ν _ h ↦ (hlsc.le_liminf _).trans h.liminf_le_liminf_comp) hτ
    (lt_add_of_pos_right τ one_pos) (ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) ?_) μ
  exact le_moreauYosida_iff.2 fun ν _ ↦
    (hge ν).trans (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))

end Narrow

end WassersteinSpace

end TauCeti

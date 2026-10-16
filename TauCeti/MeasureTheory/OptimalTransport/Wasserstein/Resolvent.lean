/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PotentialEnergy
import TauCeti.Analysis.GradientFlow.MoreauYosida.Existence
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Compactness
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
following hold (see `TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Compactness`).

* The Wasserstein distance is narrowly lower semicontinuous
  (`TauCeti.wassersteinEDist_le_liminf`), so a narrow limit of a bounded sequence of `P_p(X)` still
  has finite `p`-moment (`TauCeti.WassersteinSpace.hasFiniteMoment_of_isBounded_of_tendsto`).
* A bounded tight sequence of `P_p(X)` has a narrowly convergent subsequence, by Prokhorov's
  theorem
  (`TauCeti.WassersteinSpace.exists_strictMono_tendsto_of_isBounded_of_isTightMeasureSet`).
* On a proper space, every bounded set of `P_p(X)` is tight, by Markov's inequality
  (`TauCeti.WassersteinSpace.isTightMeasureSet_of_isBounded`). This is the case of `X = ℝⁿ`.

The hypotheses on the energy are those of Ambrosio–Gigli–Savaré for the narrow topology: `φ` is
narrowly lower semicontinuous along bounded sequences, bounded sequences along which it is bounded
above are tight (automatic on a proper space), and it is coercive, `φ_{τ₀}(μ₀) > -∞` for some time
step `τ₀` and law `μ₀`. Then the resolvent is nonempty for every `0 < τ < τ₀` and every law
(`TauCeti.WassersteinSpace.moreauYosidaResolvent_nonempty`), and every law starts a JKO sequence
(`TauCeti.WassersteinSpace.exists_forall_mem_moreauYosidaResolvent`). Uniqueness of the step is a
separate matter, settled by convexity along generalized geodesics
(`TauCeti.GeneralizedGeodesicallyConvex.subsingleton_moreauYosidaResolvent`).

The potential energy `ν ↦ ∫ V dν` of a lower semicontinuous potential `V` bounded below meets
these hypotheses on a proper space, so its JKO step exists for every time step
(`TauCeti.WassersteinSpace.moreauYosidaResolvent_potentialEnergy_nonempty`).

## Main results

* `TauCeti.WassersteinSpace.moreauYosidaResolvent_nonempty`: existence of the JKO step for a
  narrowly lower semicontinuous coercive energy whose bounded sequences with bounded energy are
  tight.
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

section Narrow

variable {X : Type*} {p : ℝ≥0∞} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] [Fact (1 ≤ p)]

/-- A bounded sequence along which an energy is bounded above has a narrowly convergent
subsequence, provided such sequences are tight, in the form consumed by the abstract direct
method. -/
private theorem exists_strictMono_tendsto_comap {φ : WassersteinSpace p X → EReal}
    (htight : ∀ (c : ℝ) ⦃v : ℕ → WassersteinSpace p X⦄, Bornology.IsBounded (range v) →
      (∀ n, φ (v n) ≤ c) →
      IsTightMeasureSet {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ range v})
    (c : ℝ) ⦃v : ℕ → WassersteinSpace p X⦄ (hv : Metric.ediam (range v) ≠ ⊤)
    (hc : ∀ n, φ (v n) ≤ c) :
    ∃ ν : WassersteinSpace p X, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (v ∘ ψ) atTop (comap (↑) (𝓝 (ν : ProbabilityMeasure X))) := by
  have hv' := Metric.isBounded_iff_ediam_ne_top.2 hv
  obtain ⟨ν, ψ, hψ, hlim⟩ := exists_strictMono_tendsto_of_isBounded_of_isTightMeasureSet hv'
    (htight c hv' hc)
  exact ⟨ν, ψ, hψ, tendsto_comap_iff.2 hlim⟩

/-- **Existence of the Jordan–Kinderlehrer–Otto step.** Let `X` be a complete separable metric
space, `1 ≤ p`, and `φ` an energy on `P_p (X)` such that

* `φ` is narrowly lower semicontinuous along bounded sequences: if a bounded sequence `v` of
  `P_p (X)` converges narrowly to `ν`, then `φ ν ≤ liminf φ (v n)`;
* bounded sequences of `P_p (X)` along which `φ` is bounded above are tight;
* `φ` is coercive: `φ_{τ₀}(μ₀) > -∞` for some time step `τ₀` and law `μ₀`.

Then for every time step `0 < τ < τ₀` and every law `μ` of `P_p (X)`, some law `ν` minimizes
`φ ν + W_p (μ, ν) ^ 2 / (2τ)`. -/
theorem moreauYosidaResolvent_nonempty {φ : WassersteinSpace p X → EReal} {τ τ₀ : ℝ≥0}
    {μ₀ : WassersteinSpace p X}
    (hφ : ∀ ⦃v : ℕ → WassersteinSpace p X⦄ ⦃ν : WassersteinSpace p X⦄,
      Bornology.IsBounded (range v) →
      Tendsto (fun n ↦ (v n : ProbabilityMeasure X)) atTop (𝓝 ν) →
      φ ν ≤ liminf (fun n ↦ φ (v n)) atTop)
    (htight : ∀ (c : ℝ) ⦃v : ℕ → WassersteinSpace p X⦄, Bornology.IsBounded (range v) →
      (∀ n, φ (v n) ≤ c) →
      IsTightMeasureSet {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ range v})
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
    (htight : ∀ (c : ℝ) ⦃v : ℕ → WassersteinSpace p X⦄, Bornology.IsBounded (range v) →
      (∀ n, φ (v n) ≤ c) →
      IsTightMeasureSet {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ range v})
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) (h₀ : moreauYosida φ τ₀ μ₀ ≠ ⊥) (μ : WassersteinSpace p X) :
    ∃ u : ℕ → WassersteinSpace p X, u 0 = μ ∧
      ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n) :=
  TauCeti.exists_forall_mem_moreauYosidaResolvent
    (l := fun ν ↦ comap (↑) (𝓝 (ν : ProbabilityMeasure X)))
    (fun _ _ _ h ↦ edist_le_liminf (tendsto_comap_iff.1 h))
    (fun _ _ hv h ↦ hφ (Metric.isBounded_iff_ediam_ne_top.2 hv) (tendsto_comap_iff.1 h))
    (exists_strictMono_tendsto_comap htight) hτ hττ₀ (edist_ne_top μ μ₀) h₀

end Narrow

section Proper

variable {X : Type*} {p : ℝ≥0∞} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [ProperSpace X] [Fact (1 ≤ p)]

/-- **Existence of the Jordan–Kinderlehrer–Otto step on a proper space.** On a proper metric
space, such as `ℝⁿ`, bounded sets of `P_p (X)` are tight, so the JKO step exists for every energy
that is narrowly lower semicontinuous along bounded sequences and coercive,
`φ_{τ₀}(μ₀) > -∞`: for every time step `0 < τ < τ₀` and every law `μ`, some law `ν` minimizes
`φ ν + W_p (μ, ν) ^ 2 / (2τ)`. -/
theorem moreauYosidaResolvent_nonempty_of_properSpace {φ : WassersteinSpace p X → EReal}
    {τ τ₀ : ℝ≥0} {μ₀ : WassersteinSpace p X}
    (hφ : ∀ ⦃v : ℕ → WassersteinSpace p X⦄ ⦃ν : WassersteinSpace p X⦄,
      Bornology.IsBounded (range v) →
      Tendsto (fun n ↦ (v n : ProbabilityMeasure X)) atTop (𝓝 ν) →
      φ ν ≤ liminf (fun n ↦ φ (v n)) atTop)
    (hτ : 0 < τ) (hττ₀ : τ < τ₀) (h₀ : moreauYosida φ τ₀ μ₀ ≠ ⊥) (μ : WassersteinSpace p X) :
    (moreauYosidaResolvent φ τ μ).Nonempty :=
  moreauYosidaResolvent_nonempty hφ (fun _ _ hv _ ↦ isTightMeasureSet_of_isBounded hv) hτ hττ₀ h₀ μ

/-- **The JKO step for a potential energy.** On a proper complete separable metric space, let `V`
be a lower semicontinuous potential bounded below. Then for every time step `τ > 0` and every law
`μ` of `P_p (X)`, some law `ν` of `P_p (X)` minimizes `∫ V dν + W_p (μ, ν) ^ 2 / (2τ)`. -/
theorem moreauYosidaResolvent_potentialEnergy_nonempty {V : X → ℝ}
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

end Proper

end WassersteinSpace

end TauCeti

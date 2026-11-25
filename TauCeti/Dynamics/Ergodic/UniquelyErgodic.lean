/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.InvariantProbabilities
public import Mathlib.Dynamics.Ergodic.EmpiricalMeasure
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.UniformConvergence
import TauCeti.Dynamics.BirkhoffSum.Integrable
import TauCeti.Dynamics.Ergodic.EmpiricalMeasure
import Mathlib.Topology.Metrizable.Basic

/-!
# Unique ergodicity and uniform convergence of Birkhoff averages

For a continuous map `T` of a nonempty compact metrizable space `X`, `T` is uniquely ergodic if
and only if, for every continuous `f : C(X, ℝ)`, the Birkhoff averages `birkhoffAverage ℝ T f n`
converge uniformly to a constant; the constant is then `∫ x, f x ∂μ` for the unique invariant
probability `μ`.

The forward direction takes, for a hypothetical bad sequence of points, a cluster point of the
corresponding orbit empirical measures in the compact space of probability measures: it is
invariant, as in Mathlib's proof of the Krylov–Bogolyubov theorem, hence equal to `μ`. The
converse integrates the Birkhoff averages against an invariant probability.

## Main results

* `TauCeti.UniquelyErgodic.tendstoUniformly_birkhoffAverage`: for a uniquely ergodic continuous
  map with invariant probability `μ`, the Birkhoff averages of `f` converge uniformly to
  `∫ x, f x ∂μ`.
* `TauCeti.uniquelyErgodic_of_tendstoUniformly_birkhoffAverage`: uniform convergence of the
  Birkhoff averages of every `f : C(X, ℝ)` to a constant implies unique ergodicity.
* `TauCeti.uniquelyErgodic_iff_tendstoUniformly_birkhoffAverage`: the equivalence.

## References

* M. Hochman, *Notes on ergodic theory*, 2012 course notes, Proposition 4.5.2, p. 41,
  https://math.huji.ac.il/~mhochman/courses/ergodic-theory-2012/notes.final.pdf
-/

public section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped BoundedContinuousFunction

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {T : X → X}

/-- The integral of an integrable function against an invariant probability is a limit of the
integrals of its Birkhoff averages; if these converge uniformly to `c`, the integral is `c`. -/
theorem integral_eq_of_tendstoUniformly_birkhoffAverage {ν : ProbabilityMeasure X}
    (hν : ν ∈ invariantProbabilities T) {f : X → ℝ} (hfi : Integrable f (ν : Measure X)) {c : ℝ}
    (hc : TendstoUniformly (fun n ↦ birkhoffAverage ℝ T f n) (fun _ ↦ c) atTop) :
    ∫ x, f x ∂ν = c := by
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformly_iff.mp hc ε hε).and
    (eventually_ge_atTop 1)).exists
  have hA : Integrable (birkhoffAverage ℝ T f n) (ν : Measure X) :=
    integrable_birkhoffAverage (mem_invariantProbabilities.mp hν) hfi
  rw [← (mem_invariantProbabilities.mp hν).integral_birkhoffAverage hfi
    (Nat.one_le_iff_ne_zero.mp hn.2), dist_comm, dist_eq_norm,
    ← (by simp : ∫ _, c ∂(ν : Measure X) = c), ← integral_sub (integrable_const c) hA]
  refine (norm_integral_le_of_norm_le_const (C := ε) (Eventually.of_forall fun x ↦ ?_)).trans
    (by simp)
  rw [← dist_eq_norm]
  exact (hn.1 x).le

variable [TopologicalSpace X] [BorelSpace X]

/-- **Uniform convergence implies unique ergodicity.** If the Birkhoff averages of every
continuous function on a nonempty compact metrizable space converge uniformly to a constant, then
the continuous map `T` is uniquely ergodic. -/
theorem uniquelyErgodic_of_tendstoUniformly_birkhoffAverage [MetrizableSpace X] [CompactSpace X]
    [Nonempty X] (hT : Continuous T)
    (h : ∀ f : C(X, ℝ), ∃ c : ℝ,
      TendstoUniformly (fun n ↦ birkhoffAverage ℝ T f n) (fun _ ↦ c) atTop) :
    UniquelyErgodic T := by
  refine uniquelyErgodic_iff.mpr ⟨invariantProbabilities_nonempty hT, fun ν₁ h₁ ν₂ h₂ ↦ ?_⟩
  refine ProbabilityMeasure.toMeasure_injective
    (ext_of_forall_integral_eq_of_IsFiniteMeasure fun g ↦ ?_)
  obtain ⟨c, hc⟩ := h g.toContinuousMap
  exact (integral_eq_of_tendstoUniformly_birkhoffAverage h₁ (g.integrable _) hc).trans
    (integral_eq_of_tendstoUniformly_birkhoffAverage h₂ (g.integrable _) hc).symm

/-- **Unique ergodicity implies uniform convergence.** For a continuous uniquely ergodic map `T`
of a compact metrizable space with invariant probability `μ`, the Birkhoff averages of every
`f : C(X, ℝ)` converge uniformly to `∫ x, f x ∂μ`. -/
theorem UniquelyErgodic.tendstoUniformly_birkhoffAverage [MetrizableSpace X] [CompactSpace X]
    (hT : Continuous T) (h : UniquelyErgodic T) {μ : ProbabilityMeasure X}
    (hμ : μ ∈ invariantProbabilities T) (f : C(X, ℝ)) :
    TendstoUniformly (fun n ↦ birkhoffAverage ℝ T f n) (fun _ ↦ ∫ x, f x ∂μ) atTop := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure (μ : Measure X)
  set c := ∫ x, f x ∂μ
  refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
  -- Otherwise infinitely many lengths `n + 1` have a point `x n` with an `ε`-far average.
  by_contra hne
  rw [not_eventually] at hne
  set S : Set ℕ := {n | ∃ x, ¬ dist c (birkhoffAverage ℝ T f (n + 1) x) < ε}
  have hS : ∃ᶠ n in atTop, n ∈ S := by
    refine (tendsto_sub_atTop_nat 1).frequently
      ((hne.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, h1⟩ ↦ ?_)
    obtain ⟨x, hx⟩ := not_forall.mp hn
    exact ⟨x, by rwa [Nat.sub_add_cancel h1]⟩
  have hF : (atTop ⊓ 𝓟 S).NeBot := frequently_iff_neBot.mp hS
  choose! x hx using fun n (hn : n ∈ S) ↦ hn
  -- A cluster point `ν` of the empirical measures along these orbits.
  let u : ℕ → ProbabilityMeasure X := fun n ↦ ⟨empiricalMeasure T (x n) n, inferInstance⟩
  have hu : ∀ n, (u n : Measure X) = empiricalMeasure T (x n) n := fun n ↦
    ProbabilityMeasure.coe_mk _ _
  obtain ⟨ν, -, hν⟩ := isCompact_univ.exists_mapClusterPt (f := atTop ⊓ 𝓟 S) (u := u) (by simp)
  have hνinv : ν ∈ invariantProbabilities T := by
    refine (mem_invariantProbabilities_iff_map_eq hT.measurable).mpr
      (ProbabilityMeasure.toMeasure_injective ?_)
    rw [ProbabilityMeasure.toMeasure_map]
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g ↦ ?_
    rw [integral_map hT.aemeasurable g.continuous.aestronglyMeasurable]
    refine ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt hT hν ?_
    have h0 : Tendsto (fun n : ℕ ↦ 2 * ‖g‖ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      refine ((tendsto_const_div_atTop_nhds_zero_nat (2 * ‖g‖)).comp
        (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
      simp
    simp only [hu]
    exact (squeeze_zero_norm (fun n ↦ norm_integral_comp_sub_integral_empiricalMeasure_le T
      g.norm_coe_le_norm (x n) n) h0).mono_left inf_le_left
  have hνμ : ν = μ := h.eq_of_mem hνinv hμ
  -- Along an ultrafilter the integrals of `f` converge to `c`, but stay `ε`-far on `S`.
  obtain ⟨U, hUF, hU⟩ := mapClusterPt_iff_ultrafilter.mp hν
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hU
    (BoundedContinuousFunction.mkOfCompact f)
  rw [hνμ] at hint
  have h1 := Metric.tendsto_nhds.mp hint ε hε
  have h2 : ∀ᶠ n in (U : Filter ℕ), n ∈ S := hUF (mem_inf_of_right (mem_principal_self S))
  obtain ⟨n, h1n, h2n⟩ := (h1.and h2).exists
  refine hx n h2n ?_
  have he : ∫ y, f y ∂(u n : Measure X) = birkhoffAverage ℝ T f (n + 1) (x n) := by
    rw [hu, ← birkhoffAverage_apply_congr_ring (R := NNReal) ℝ]
    exact integral_empiricalMeasure_eq_birkhoffaverage T (x n) f n
  simpa [dist_comm, he, c] using h1n

/-- **Unique ergodicity and uniform convergence.** A continuous map of a nonempty compact
metrizable space is uniquely ergodic if and only if the Birkhoff averages of every continuous
real function converge uniformly to a constant. -/
theorem uniquelyErgodic_iff_tendstoUniformly_birkhoffAverage [MetrizableSpace X] [CompactSpace X]
    [Nonempty X] (hT : Continuous T) :
    UniquelyErgodic T ↔ ∀ f : C(X, ℝ), ∃ c : ℝ,
      TendstoUniformly (fun n ↦ birkhoffAverage ℝ T f n) (fun _ ↦ c) atTop := by
  refine ⟨fun h f ↦ ?_, uniquelyErgodic_of_tendstoUniformly_birkhoffAverage hT⟩
  obtain ⟨μ, hμ⟩ := h.nonempty
  exact ⟨_, h.tendstoUniformly_birkhoffAverage hT hμ f⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.UniformOn
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Space
import TauCeti.MeasureTheory.Constructions.UnitInterval.GridApproximation
import TauCeti.MeasureTheory.Measure.UnitIntervalMap
import TauCeti.Probability.Distributions.Uniform.Finite.Basic

/-!
# Finite uniform kernels and separability of the Gromov–Wasserstein space

A *finite uniform kernel* is a measured kernel on `n` equally weighted points: the carrier
`Fin n` with the uniform probability measure and an arbitrary kernel `ω : Fin n × Fin n → Z`. This
file shows that for a finite exponent these kernels are dense among all finite-`p` measured
kernels, with kernel values in any prescribed dense subset of the target `Z`. Consequently, when
`Z` is separable and `1 ≤ p < ∞`, so are the presentations and the Gromov–Wasserstein space
`GromovWassersteinSpace p Z`.

The density proof parametrizes a standard Borel probability space `(X, μ)` by a
measure-preserving map `g : I → X` from the unit interval
(`MeasureTheory.Measure.exists_measurePreserving_from_unitInterval`) and approximates the
pulled-back kernel `ω ∘ (g × g)` on the unit square by a grid step function
(`TauCeti.unitInterval.exists_eLpNorm_edist_comp_prodMap_cellFin_lt`). A grid step function on
`n` equal cells is the pullback of a finite uniform kernel along the cell index map, which is
measure preserving onto the uniform measure, so the common-parametrization bound
`TauCeti.gromovWassersteinEDist_le_eLpNorm` turns the `Lᵖ` estimate into a
Gromov–Wasserstein estimate.

Density of finite kernels needs a finite exponent. At `p = ∞`, take the kernel
`(x, y) ↦ if x < y then 1 else 0` on `([0, 1], volume)` and a coupling `π` of `volume` with a law
on finitely many points. Some point `y` of the finite carrier has `π ([0, 1] × {y}) > 0`, and the
slice measure `π (· × {y}) ≤ volume` is atomless, so `π ⊗ π` gives positive measure both to the
pairs `((x, y), (x', y))` with `x < x'` and to those with `x > x'`. The first kernel takes the
values `1` and `0` there and the finite kernel the single value at `(y, y)`, so the distortion is at
least `1 / 2`.

## Main definitions

* `TauCeti.GromovWassersteinPresentation.finiteUniform n ω`: the presentation of the measured
  kernel on `n` equally weighted points with kernel `ω`, its carrier lifted to the carrier
  universe.

## Main statements

* `TauCeti.exists_gromovWassersteinEDist_uniformOn_lt`: for `p ≠ ∞`, every finite-`p` measured
  kernel on a standard Borel probability space is within any positive Gromov–Wasserstein distance
  of a finite uniform kernel with values in a given dense set.
* `TauCeti.GromovWassersteinPresentation.areWeaklyIsomorphicKernels_finiteUniform`,
  `TauCeti.GromovWassersteinPresentation.gromovWassersteinEDist_finiteUniform_left` and
  `TauCeti.GromovWassersteinPresentation.gromovWassersteinEDist_finiteUniform_right`: the
  presentation `finiteUniform n ω` is weakly isomorphic to the uniform law on `Fin n` with kernel
  `ω`, and has the same Gromov–Wasserstein distances.
* `TauCeti.GromovWassersteinPresentation.exists_edist_finiteUniform_lt`: every presentation is
  within any positive distance of a finite uniform kernel with values in a given dense set.
* `TauCeti.GromovWassersteinSpace.dense_finiteUniform`: the classes of these kernels are dense in
  the Gromov–Wasserstein space.
* `TauCeti.GromovWassersteinPresentation.separableSpace` and
  `TauCeti.GromovWassersteinSpace.separableSpace`: over a separable target and for `p ≠ ∞`, the
  presentations and the Gromov–Wasserstein space are separable. The instances
  `instSeparableSpace` read `p ≠ ∞` off a `Fact`.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Propositions 36 and 38, for density of finite kernels and
  separability over a separable target. The proof here goes through the unit interval instead.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal unitInterval

namespace TauCeti

universe u v w

/-- **Density of finite uniform kernels** (compare Bauer–Mémoli–Needham–Nishino, Propositions 36
and 38). For a finite exponent `p`, every measured kernel `(X, μ, ω)` on a standard Borel
probability space, with finite `p`-th moment about some point, is within any positive
Gromov–Wasserstein distance of the uniform law on some `Fin n` with a kernel whose values lie in a
prescribed dense subset `D` of the target. The target need not be separable or complete. -/
theorem exists_gromovWassersteinEDist_uniformOn_lt {X Z : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] [PseudoMetricSpace Z] {p : ℝ≥0∞} (hp : p ≠ ∞) (μ : Measure X)
    [IsProbabilityMeasure μ] {ω : X × X → Z} (hω : AEStronglyMeasurable ω (μ.prod μ)) {z₀ : Z}
    (hz₀ : MemLp (fun q ↦ edist (ω q) z₀) p (μ.prod μ)) {D : Set Z} (hD : Dense D) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (ω' : Fin n × Fin n → Z), (∀ ij, ω' ij ∈ D) ∧
      gromovWassersteinEDist p μ ω (ProbabilityTheory.uniformOn univ) ω' < ε := by
  obtain ⟨g, hg⟩ := Measure.exists_measurePreserving_from_unitInterval μ
  have hgg : MeasurePreserving (Prod.map g g) volume (μ.prod μ) := hg.prod hg
  obtain ⟨n, hn, ω', hωD, hlt⟩ := unitInterval.exists_eLpNorm_edist_comp_prodMap_cellFin_lt hp
    (hω.comp_measurePreserving hgg) (hz₀.comp_measurePreserving hgg) hD hε
  refine ⟨n, hn, ω', hωD, (gromovWassersteinEDist_le_eLpNorm hg
    unitInterval.measurePreserving_cellFin hω
    StronglyMeasurable.of_discrete.aestronglyMeasurable p).trans_lt ?_⟩
  rwa [← Measure.volume_eq_prod]

namespace GromovWassersteinPresentation

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z]

/-- The **finite uniform kernel** with kernel `ω`: the carrier `Fin n`, lifted to the carrier
universe, with the uniform probability measure and the kernel `ω`. -/
-- Implicit reduction lets the projected carrier and measurable structure elaborate together.
@[implicit_reducible]
def finiteUniform (n : ℕ) [NeZero n] (ω : Fin n × Fin n → Z) :
    GromovWassersteinPresentation.{u} p Z where
  Carrier := ULift.{u} (Fin n)
  measure := ProbabilityTheory.uniformOn univ
  kernel q := ω (q.1.down, q.2.down)
  aestronglyMeasurable_kernel := StronglyMeasurable.of_discrete.aestronglyMeasurable
  finite_moment := ⟨ω (0, 0), by
    simpa [Real.eNorm_of_nonneg dist_nonneg, ← edist_dist] using
      (MemLp.of_discrete (f := fun q : ULift.{u} (Fin n) × ULift.{u} (Fin n) ↦
        dist (ω (q.1.down, q.2.down)) (ω (0, 0))) (p := p)
        (μ := (ProbabilityTheory.uniformOn univ).prod (ProbabilityTheory.uniformOn univ))).eNorm⟩

section FiniteUniform

variable (n : ℕ) [NeZero n] (ω : Fin n × Fin n → Z)

/-- A finite uniform kernel is weakly isomorphic to the uniform law on `Fin n` with kernel `ω`. -/
theorem areWeaklyIsomorphicKernels_finiteUniform :
    AreWeaklyIsomorphicKernels (finiteUniform.{u} (p := p) n ω).measure
      (finiteUniform.{u} (p := p) n ω).kernel (ProbabilityTheory.uniformOn univ) ω :=
  areWeaklyIsomorphicKernels_comp_prodMap (f := ULift.down.{u})
    ⟨measurable_down, Equiv.ulift.map_uniformOn_univ⟩
    StronglyMeasurable.of_discrete.aestronglyMeasurable

/-- The Gromov–Wasserstein distance from a finite uniform kernel is the distance from the uniform
law on `Fin n` with kernel `ω`. -/
@[simp]
theorem gromovWassersteinEDist_finiteUniform_left (K : GromovWassersteinPresentation.{w} p Z) :
    gromovWassersteinEDist p (finiteUniform.{u} (p := p) n ω).measure
      (finiteUniform.{u} (p := p) n ω).kernel K.measure K.kernel =
      gromovWassersteinEDist p (ProbabilityTheory.uniformOn univ) ω K.measure K.kernel :=
  (areWeaklyIsomorphicKernels_finiteUniform n ω).gromovWassersteinEDist_congr_left
    (finiteUniform n ω).aestronglyMeasurable_kernel
    StronglyMeasurable.of_discrete.aestronglyMeasurable K.aestronglyMeasurable_kernel

/-- The Gromov–Wasserstein distance to a finite uniform kernel is the distance to the uniform law
on `Fin n` with kernel `ω`. -/
@[simp]
theorem gromovWassersteinEDist_finiteUniform_right (K : GromovWassersteinPresentation.{w} p Z) :
    gromovWassersteinEDist p K.measure K.kernel (finiteUniform.{u} (p := p) n ω).measure
      (finiteUniform.{u} (p := p) n ω).kernel =
      gromovWassersteinEDist p K.measure K.kernel (ProbabilityTheory.uniformOn univ) ω :=
  (areWeaklyIsomorphicKernels_finiteUniform n ω).gromovWassersteinEDist_congr_right
    (finiteUniform n ω).aestronglyMeasurable_kernel
    StronglyMeasurable.of_discrete.aestronglyMeasurable K.aestronglyMeasurable_kernel

end FiniteUniform

/-- **Density of finite uniform kernels** (compare Bauer–Mémoli–Needham–Nishino, Propositions 36
and 38). For a finite exponent `1 ≤ p < ∞`, every finite-`p` presentation is within any positive
Gromov–Wasserstein distance of a finite uniform kernel whose values lie in a prescribed dense
subset `D` of the target. The target need not be separable or complete. -/
theorem exists_edist_finiteUniform_lt [Fact (1 ≤ p)] (hp : p ≠ ∞) {D : Set Z} (hD : Dense D)
    (K : GromovWassersteinPresentation.{u} p Z) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (ω : Fin n × Fin n → Z), (∀ ij, ω ij ∈ D) ∧
      edist K (finiteUniform n ω) < ε := by
  obtain ⟨z₀, hz₀⟩ := K.finite_moment
  obtain ⟨n, hn, ω, hωD, hlt⟩ := exists_gromovWassersteinEDist_uniformOn_lt hp K.measure
    K.aestronglyMeasurable_kernel hz₀ hD hε
  exact ⟨n, hn, ω, hωD, by rwa [edist_eq, gromovWassersteinEDist_finiteUniform_right]⟩

/-- **Separability of measured kernels** (compare Bauer–Mémoli–Needham–Nishino, Propositions 36
and 38). Over a separable target and for a finite exponent `1 ≤ p < ∞`, the finite-`p`
presentations form a separable pseudometric space. -/
theorem separableSpace [Fact (1 ≤ p)] [SeparableSpace Z] (hp : p ≠ ∞) :
    SeparableSpace (GromovWassersteinPresentation.{u} p Z) := by
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense Z
  have : Countable D := hDc.to_subtype
  refine ⟨⟨range fun x : Σ n : ℕ, Fin (n + 1) × Fin (n + 1) → D ↦
    finiteUniform (n := x.1 + 1) fun ij ↦ (x.2 ij : Z), countable_range _, ?_⟩⟩
  refine EMetric.dense_iff.2 fun K ε hε ↦ ?_
  obtain ⟨n, hn, ω, hωD, hlt⟩ := exists_edist_finiteUniform_lt hp hD K hε
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.out
  exact ⟨_, by rw [Metric.mem_eball, edist_comm]; exact hlt,
    ⟨⟨m, fun ij ↦ ⟨ω ij, hωD ij⟩⟩, by simp⟩⟩

/-- The separability of presentations as an instance, reading the finiteness of the exponent off
a `Fact`, as the pseudometric reads off `Fact (1 ≤ p)`. -/
instance instSeparableSpace [Fact (1 ≤ p)] [Fact (p ≠ ∞)] [SeparableSpace Z] :
    SeparableSpace (GromovWassersteinPresentation.{u} p Z) :=
  separableSpace Fact.out

end GromovWassersteinPresentation

namespace GromovWassersteinSpace

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [Fact (1 ≤ p)]

/-- **Density of finite uniform kernels in the Gromov–Wasserstein space.** For a finite exponent,
the classes of finite uniform kernels with values in a dense subset `D` of the target are dense in
`GromovWassersteinSpace p Z`. -/
theorem dense_finiteUniform (hp : p ≠ ∞) {D : Set Z} (hD : Dense D) :
    Dense {x : GromovWassersteinSpace.{u} p Z | ∃ (n : ℕ) (_ : NeZero n)
      (ω : Fin n × Fin n → Z), (∀ ij, ω ij ∈ D) ∧
        mk (GromovWassersteinPresentation.finiteUniform n ω) = x} := by
  refine EMetric.dense_iff.2 fun x ε hε ↦ ?_
  obtain ⟨K, rfl⟩ := mk_surjective x
  obtain ⟨n, hn, ω, hωD, hlt⟩ :=
    GromovWassersteinPresentation.exists_edist_finiteUniform_lt hp hD K hε
  refine ⟨_, ?_, n, hn, ω, hωD, rfl⟩
  rw [Metric.mem_eball, edist_comm]
  exact (isometry_mk.edist_eq K _).trans_lt hlt

/-- **Separability of the Gromov–Wasserstein space** (compare Bauer–Mémoli–Needham–Nishino,
Propositions 36 and 38). Over a separable target and for a finite exponent `1 ≤ p < ∞`, the
Gromov–Wasserstein space is separable. -/
theorem separableSpace [SeparableSpace Z] (hp : p ≠ ∞) :
    SeparableSpace (GromovWassersteinSpace.{u} p Z) :=
  have := GromovWassersteinPresentation.separableSpace.{u} (Z := Z) hp
  mk_surjective.denseRange.separableSpace isometry_mk.continuous

/-- The separability of the Gromov–Wasserstein space as an instance, reading the finiteness of the
exponent off a `Fact`. -/
instance instSeparableSpace [Fact (p ≠ ∞)] [SeparableSpace Z] :
    SeparableSpace (GromovWassersteinSpace.{u} p Z) :=
  separableSpace Fact.out

end GromovWassersteinSpace

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.UnitInterval.GridApproximation
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Space
import TauCeti.MeasureTheory.Measure.UnitIntervalMap

/-!
# Finite uniform kernels and separability of the Gromov–Wasserstein space

A *finite uniform kernel* is a measured kernel on `n` equally weighted points: the carrier
`Fin n` (lifted to the carrier universe) with the uniform probability measure and an arbitrary
kernel `ω : Fin n × Fin n → Z`. This file shows that for a finite exponent `1 ≤ p < ∞` these
kernels are dense among all finite-`p` measured kernels, with kernel values in any prescribed
dense subset of the target `Z`. Consequently, when `Z` is separable, so are the presentations and
the Gromov–Wasserstein space `GromovWassersteinSpace p Z`.

The density proof parametrizes a presentation `(X, μ, ω)` by a measure-preserving map
`g : I → X` from the unit interval
(`MeasureTheory.Measure.exists_measurePreserving_from_unitInterval`) and approximates the
pulled-back kernel `ω ∘ (g × g)` on the unit square by a grid step function
(`TauCeti.unitInterval.exists_eLpNorm_edist_comp_cellFin_lt`). A grid step function on `n`
equal cells is the pullback of a finite uniform kernel along the cell index map, which is
measure preserving onto the uniform measure, so the common-parametrization bound
`TauCeti.GromovWassersteinPresentation.edist_le_eLpNorm` turns the `Lᵖ` estimate into a
Gromov–Wasserstein estimate.

The exponent must be finite. At `p = ∞`, take the kernel `(x, y) ↦ if x < y then 1 else 0` on
`([0, 1], volume)`. A coupling with a kernel on finitely many points sends a set `A` of positive
measure to a single point, and `1` and `0` are both taken on parts of `A × A` of positive measure,
so the distortion is at least `1 / 2`.

## Main definitions

* `TauCeti.GromovWassersteinPresentation.finiteUniform n ω`: the measured kernel on `n` equally
  weighted points with kernel `ω`.

## Main statements

* `TauCeti.GromovWassersteinPresentation.exists_finiteUniform_edist_lt`: every presentation is
  within any positive distance of a finite uniform kernel with values in a given dense set.
* `TauCeti.GromovWassersteinSpace.dense_finiteUniform`: the classes of these kernels are dense in
  the Gromov–Wasserstein space.
* `TauCeti.GromovWassersteinPresentation.separableSpace` and
  `TauCeti.GromovWassersteinSpace.separableSpace`: over a separable target and for `p ≠ ∞`, the
  presentations and the Gromov–Wasserstein space are separable.

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

universe u v

namespace GromovWassersteinPresentation

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z]

/-- The **finite uniform kernel** with kernel `ω`: the carrier `Fin n`, lifted to the carrier
universe, with the uniform probability measure and the kernel `ω`. -/
-- The body is exposed so that maps into the carrier `ULift (Fin n)` typecheck downstream;
-- implicit reduction lets the projected carrier and measurable structure elaborate together.
@[expose, implicit_reducible]
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

section Simp

variable (n : ℕ) [NeZero n] (ω : Fin n × Fin n → Z)

/-- The law of a finite uniform kernel is the uniform measure on its carrier. -/
@[simp]
theorem finiteUniform_measure :
    (finiteUniform.{u} (p := p) n ω).measure = ProbabilityTheory.uniformOn univ := (rfl)

/-- The kernel of a finite uniform kernel reads `ω` on the lifted indices. -/
@[simp]
theorem finiteUniform_kernel (q : ULift.{u} (Fin n) × ULift.{u} (Fin n)) :
    (finiteUniform.{u} (p := p) n ω).kernel q = ω (q.1.down, q.2.down) := (rfl)

end Simp

/-- **Density of finite uniform kernels** (compare Bauer–Mémoli–Needham–Nishino, Propositions 36
and 38). For a finite exponent `1 ≤ p < ∞`, every finite-`p` presentation is within any positive
Gromov–Wasserstein distance of a finite uniform kernel whose values lie in a prescribed dense
subset `D` of the target. The target need not be separable or complete. -/
theorem exists_finiteUniform_edist_lt [Fact (1 ≤ p)] (hp : p ≠ ∞) {D : Set Z} (hD : Dense D)
    (K : GromovWassersteinPresentation.{u} p Z) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (ω : Fin n × Fin n → Z), (∀ ij, ω ij ∈ D) ∧
      edist K (finiteUniform n ω) < ε := by
  obtain ⟨g, hg⟩ := Measure.exists_measurePreserving_from_unitInterval K.measure
  obtain ⟨z₀, hz₀⟩ := K.finite_moment
  have hgg : MeasurePreserving (Prod.map g g) volume (K.measure.prod K.measure) := hg.prod hg
  obtain ⟨n, hn, ω, hωD, hlt⟩ := unitInterval.exists_eLpNorm_edist_comp_cellFin_lt hp
    (K.aestronglyMeasurable_kernel.comp_measurePreserving hgg)
    (hz₀.comp_measurePreserving hgg) hD hε
  refine ⟨n, hn, ω, hωD, (edist_le_eLpNorm (L := finiteUniform n ω) hg
    (TauCeti.unitInterval.measurePreserving_up_cellFin n)).trans_lt ?_⟩
  rwa [← Measure.volume_eq_prod]

/-- **Separability of measured kernels** (compare Bauer–Mémoli–Needham–Nishino, Propositions 36
and 38). Over a separable target and for a finite exponent `1 ≤ p < ∞`, the finite-`p`
presentations form a separable pseudometric space: finite uniform kernels with values in a
countable dense subset of the target are dense. -/
theorem separableSpace [Fact (1 ≤ p)] [SeparableSpace Z] (hp : p ≠ ∞) :
    SeparableSpace (GromovWassersteinPresentation.{u} p Z) := by
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense Z
  have : Countable D := hDc.to_subtype
  refine ⟨⟨range fun x : Σ n : ℕ, Fin (n + 1) × Fin (n + 1) → D ↦
    finiteUniform (n := x.1 + 1) fun ij ↦ (x.2 ij : Z), countable_range _, ?_⟩⟩
  refine EMetric.dense_iff.2 fun K ε hε ↦ ?_
  obtain ⟨n, hn, ω, hωD, hlt⟩ := exists_finiteUniform_edist_lt hp hD K hε
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.out
  exact ⟨_, by rw [Metric.mem_eball, edist_comm]; exact hlt,
    ⟨⟨m, fun ij ↦ ⟨ω ij, hωD ij⟩⟩, rfl⟩⟩

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
    GromovWassersteinPresentation.exists_finiteUniform_edist_lt hp hD K hε
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

end GromovWassersteinSpace

end TauCeti

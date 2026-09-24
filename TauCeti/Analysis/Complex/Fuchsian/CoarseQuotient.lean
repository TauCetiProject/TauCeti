/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic
public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# The coarse quotient of a Fuchsian group is a Riemann surface

Let `Γ ≤ PSL(2, ℝ)` act properly discontinuously on the upper half-plane, as every discrete
subgroup does. This file puts complex charts on the whole orbit space `Γ \ ℍ`, elliptic orbits
included, and proves that they make it a Riemann surface with a holomorphic orbit projection.

The atlas consists of the charts `Subgroup.stabilizerBallQuotientChart` at every point of the
upper half-plane and every admissible radius; the chart at an orbit is the chart at a chosen
representative with the radius `Subgroup.chartRadius`, which exists because the local orbit space
of a small enough disc embeds openly into `Γ \ ℍ`. The transition maps between these charts are
holomorphic (`Subgroup.differentiableOn_stabilizerBallQuotientChart_symm_trans`), so the atlas is
analytic, and the local formula for a chart along the orbit projection makes the projection
`ℍ → Γ \ ℍ` holomorphic.

The chart centred at an orbit of stabilizer order `m` is the cyclic quotient model `u ↦ u ^ m`:
near a point of the disc about the centre, the chart composed with the orbit projection is the
`m`-th power of the disc coordinate
(`Subgroup.exists_stabilizerBallQuotientChart_quotientMk_eventuallyEq`). At a free orbit `m = 1`,
so the chart centred there is a disc coordinate pushed forward along the orbit projection.

## Main declarations

* `Subgroup.chartRadius`: a positive radius at which the chart at the orbit of `z` exists.
* `Subgroup.instChartedSpaceOrbitRelQuotient`: the atlas of all charts
  `Subgroup.stabilizerBallQuotientChart` on `Γ \ ℍ`, with `Subgroup.chartAt_eq`,
  `Subgroup.mem_atlas_orbitRelQuotient_iff` and `Subgroup.stabilizerBallQuotientChart_mem_atlas`
  describing it.
* `Subgroup.instIsManifoldOrbitRelQuotient`: this atlas is analytic, so `Γ \ ℍ` is a Riemann
  surface. It is Hausdorff and second countable by
  `t2Space_of_properlyDiscontinuousSMul_of_t2Space` and
  `Subgroup.instSecondCountableTopologyOrbitRelQuotient`.
* `Subgroup.mdifferentiable_quotientMk`: the orbit projection is holomorphic.

## References

* Hershel Farkas and Irwin Kra, *Riemann Surfaces*, Graduate Texts in Mathematics 71, Springer,
  second edition, 1992, Chapter I §§4–5.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §§3–4.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.4.
-/

public noncomputable section

open Filter MulAction Set Topology UpperHalfPlane

open scoped ContDiff Manifold MatrixGroups

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- For a properly discontinuous action there is a positive radius whose local orbit space embeds
openly into `Γ \ ℍ`, so the chart at the orbit of `z` exists. -/
theorem exists_pos_isOpenEmbedding_stabilizerBallQuotientToQuotient (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε) :=
  (eventually_mem_nhdsWithin.and
    (eventually_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z)).exists

/-- A positive radius at which the chart `Subgroup.stabilizerBallQuotientChart` at the orbit of `z`
exists. -/
def chartRadius (z : ℍ) : ℝ :=
  (exists_pos_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z).choose

theorem chartRadius_pos (z : ℍ) : 0 < chartRadius Γ z :=
  (exists_pos_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z).choose_spec.1

theorem isOpenEmbedding_stabilizerBallQuotientToQuotient_chartRadius (z : ℍ) :
    IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z (chartRadius Γ z)) :=
  (exists_pos_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z).choose_spec.2

/-- **The atlas of `Γ \ ℍ`.** It consists of the charts `Subgroup.stabilizerBallQuotientChart` at
every point and every admissible radius; the chart at an orbit is the chart at a chosen
representative with the radius `Subgroup.chartRadius`. -/
instance instChartedSpaceOrbitRelQuotient : ChartedSpace ℂ (orbitRel.Quotient Γ ℍ) where
  atlas := {e | ∃ (z : ℍ) (ε : ℝ) (hε : 0 < ε)
    (hopen : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε)),
    stabilizerBallQuotientChart hε hopen = e}
  chartAt q := stabilizerBallQuotientChart (chartRadius_pos Γ q.out)
    (isOpenEmbedding_stabilizerBallQuotientToQuotient_chartRadius Γ q.out)
  mem_chart_source q := by
    have := (mem_stabilizerBallQuotientChart_source_iff (τ := q.out) (chartRadius_pos Γ q.out)
      (isOpenEmbedding_stabilizerBallQuotientToQuotient_chartRadius Γ q.out)).2
      ⟨(1 : Γ), by simpa using chartRadius_pos Γ q.out⟩
    rwa [Quotient.out_eq] at this
  chart_mem_atlas _ := ⟨_, _, _, _, rfl⟩

theorem chartAt_eq (q : orbitRel.Quotient Γ ℍ) :
    chartAt ℂ q = stabilizerBallQuotientChart (chartRadius_pos Γ q.out)
      (isOpenEmbedding_stabilizerBallQuotientToQuotient_chartRadius Γ q.out) :=
  (rfl)

/-- A chart of `Γ \ ℍ` belongs to the atlas exactly when it is the chart
`Subgroup.stabilizerBallQuotientChart` at some point and some admissible radius. -/
theorem mem_atlas_orbitRelQuotient_iff (e : OpenPartialHomeomorph (orbitRel.Quotient Γ ℍ) ℂ) :
    e ∈ atlas ℂ (orbitRel.Quotient Γ ℍ) ↔ ∃ (z : ℍ) (ε : ℝ) (hε : 0 < ε)
      (hopen : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε)),
      stabilizerBallQuotientChart hε hopen = e :=
  Iff.rfl

theorem stabilizerBallQuotientChart_mem_atlas {z : ℍ} {ε : ℝ} (hε : 0 < ε)
    (hopen : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε)) :
    stabilizerBallQuotientChart hε hopen ∈ atlas ℂ (orbitRel.Quotient Γ ℍ) :=
  (mem_atlas_orbitRelQuotient_iff Γ _).2 ⟨_, _, _, _, rfl⟩

/-- The coarse orbit quotient `Γ \ ℍ` is second countable, as the orbit space of a second
countable space under a continuous group action. -/
instance instSecondCountableTopologyOrbitRelQuotient :
    SecondCountableTopology (orbitRel.Quotient Γ ℍ) :=
  ContinuousConstSMul.secondCountableTopology

-- The coarse quotient is Hausdorff by Mathlib's instance for properly discontinuous actions.
example : T2Space (orbitRel.Quotient Γ ℍ) := inferInstance

/-- **The coarse quotient of a Fuchsian group is a Riemann surface**: the transition maps between
the charts of the atlas are holomorphic. -/
instance instIsManifoldOrbitRelQuotient : IsManifold 𝓘(ℂ) ω (orbitRel.Quotient Γ ℍ) := by
  refine isManifold_of_contDiffOn 𝓘(ℂ) ω _ fun e e' he he' ↦ ?_
  obtain ⟨z, ε, hε, hopen, rfl⟩ := (mem_atlas_orbitRelQuotient_iff Γ e).1 he
  obtain ⟨z', ε', hε', hopen', rfl⟩ := (mem_atlas_orbitRelQuotient_iff Γ e').1 he'
  simp only [mfld_simps]
  exact (differentiableOn_stabilizerBallQuotientChart_symm_trans hε hopen hε' hopen').contDiffOn
    (OpenPartialHomeomorph.open_source _)

example : IsManifold 𝓘(ℂ) ∞ (orbitRel.Quotient Γ ℍ) := inferInstance

/-- **The orbit projection is holomorphic.** In the chart at the orbit of `τ` it is a power of a
disc coordinate. -/
theorem mdifferentiable_quotientMk :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Quotient.mk (orbitRel Γ ℍ)) := fun τ ↦ by
  rw [mdifferentiableAt_iff_target]
  refine ⟨continuous_quotient_mk'.continuousAt, ?_⟩
  simp only [mfld_simps]
  exact mdifferentiableAt_stabilizerBallQuotientChart_comp_quotientMk _ _ (mem_chart_source ℂ _)

end Subgroup

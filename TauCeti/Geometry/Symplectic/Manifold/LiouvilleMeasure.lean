/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure
public import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow
public import TauCeti.Geometry.Symplectic.Manifold.Volume

/-!
# The Liouville measure of a symplectic manifold

Let `σ` be a smooth two-form on a manifold `M` modelled on a space of dimension `2 * n`. The
**Liouville measure** of `σ` (`TauCeti.SmoothTwoForm.liouvilleMeasure σ n`) is the measure
`|σⁿ / n!|` of its symplectic volume form: in each chart it is Lebesgue measure weighted by the
absolute value of the coefficient of `σⁿ / n!`
(`TauCeti.SmoothTwoForm.liouvilleMeasure_apply_of_subset`), where `σⁿ / n!` is normalized to take
the value `1` on Darboux bases. The measure is built on the Borel `σ`-algebra of any Lindelöf
manifold, uses no orientation and no Riemannian metric, and allows boundary and corners.

The Liouville measure is locally finite, so it is a finite measure on a compact manifold. When `σ`
is nondegenerate, the volume form vanishes nowhere and every nonempty open set has positive
Liouville measure. If a differentiable homeomorphism `Φ` satisfies `Φ^* τ = σ`, then `Φ` carries
the Liouville measure of `σ` to that of `τ`; in particular symplectomorphisms preserve the
Liouville measure. Since Hamiltonian flows preserve a symplectic form, this gives
**Liouville's theorem**: the time-`t` maps of a complete Hamiltonian flow preserve the Liouville
measure
(`TauCeti.SmoothTwoForm.IsSymplectic.measurePreserving_globalFlowDiffeomorph_liouvilleMeasure`).

## Main definitions

* `TauCeti.SmoothTwoForm.liouvilleMeasure σ n`: the Liouville measure `|σⁿ / n!|`.

## Main results

* `TauCeti.SmoothTwoForm.liouvilleMeasure_apply_of_subset`: the Liouville measure in a chart.
* `TauCeti.SmoothTwoForm.isLocallyFiniteMeasure_liouvilleMeasure`: it is locally finite.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isOpenPosMeasure_liouvilleMeasure`: for nondegenerate
  `σ` it is positive on nonempty open sets.
* `Homeomorph.measurePreserving_liouvilleMeasure`: maps pulling `τ` back to `σ` carry the
  Liouville measure of `σ` to that of `τ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.measurePreserving_globalFlowDiffeomorph_liouvilleMeasure`:
  Liouville's theorem, Hamiltonian flows preserve the Liouville measure.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 16 (Liouville's theorem).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 3 (the volume form `ωⁿ / n!` of a symplectic manifold).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped ContDiff ENNReal Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {n : ℕ} [hn : Fact (finrank ℝ E = 2 * n)]

attribute [local instance] TauCeti.extChartAtMeasurableSpaceE TauCeti.extChartAtBorelSpaceE

namespace TauCeti

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I M}

variable (σ n) in
/-- The **Liouville measure** of a two-form `σ` on a manifold modelled on a space of dimension
`2 * n`: the measure `|σⁿ / n!|` of its symplectic volume form. For a symplectic form this is the
canonical volume of the symplectic manifold. -/
def liouvilleMeasure : Measure M :=
  RoughForm.measure (σ.volumeForm n).1

variable (σ n) in
/-- The Liouville measure is the measure of the symplectic volume form. -/
theorem liouvilleMeasure_def : σ.liouvilleMeasure n = RoughForm.measure (σ.volumeForm n).1 :=
  (rfl)

/-- **The Liouville measure in coordinates.** The Liouville measure of a measurable subset of a
chart source is the integral over its coordinate image of the absolute value of the coefficient of
`σⁿ / n!` in that chart. -/
theorem liouvilleMeasure_apply_of_subset {α : M} {s : Set M} (hs : MeasurableSet s)
    (hsub : s ⊆ (extChartAt I α).source) :
    σ.liouvilleMeasure n s =
      ∫⁻ y in (extChartAt I α) '' s,
        ENNReal.ofReal |RoughForm.inChartAt (σ.volumeForm n).1 α y (finBasisOfFinrankEq ℝ E hn.out)|
          ∂(finBasisOfFinrankEq ℝ E hn.out).addHaar :=
  RoughForm.measure_apply_of_subset _ hs hsub

/-- The Liouville measure is locally finite. In particular it is a finite measure on a compact
manifold. -/
instance isLocallyFiniteMeasure_liouvilleMeasure : IsLocallyFiniteMeasure (σ.liouvilleMeasure n) :=
  RoughForm.isLocallyFiniteMeasure_measure ((σ.volumeForm n).isSmoothForm.of_le bot_le)

/-- The Liouville measure of a nondegenerate two-form is positive on nonempty open sets. -/
theorem IsNondegenerate.isOpenPosMeasure_liouvilleMeasure (h : σ.IsNondegenerate) :
    (σ.liouvilleMeasure n).IsOpenPosMeasure :=
  RoughForm.isOpenPosMeasure_measure ((σ.volumeForm n).isSmoothForm.of_le bot_le)
    (h.volumeForm_apply_ne_zero hn.out)

end SmoothTwoForm

end TauCeti

namespace Homeomorph

open TauCeti

variable {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J ∞ N] [MeasurableSpace N] [BorelSpace N] [LindelofSpace N]

/-- **Maps pulling back the two-form preserve the Liouville measure.** A differentiable
homeomorphism `Φ : M → N` with `Φ^* τ = σ` carries the Liouville measure of `σ` to that of `τ`. In
particular a symplectomorphism preserves the Liouville measure. -/
theorem measurePreserving_liouvilleMeasure {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (Φ : M ≃ₜ N) (hΦ : MDifferentiable I J Φ) (h : mpullback I J Φ τ.1 = σ.1) :
    MeasurePreserving Φ (σ.liouvilleMeasure n) (τ.liouvilleMeasure n) := by
  rw [SmoothTwoForm.liouvilleMeasure_def, SmoothTwoForm.liouvilleMeasure_def,
    ← SmoothTwoForm.mpullback_volumeForm h]
  exact Φ.measurePreserving_measure_mpullback hΦ _

end Homeomorph

namespace TauCeti.SmoothTwoForm.IsSymplectic

variable [T2Space M] [I.Boundaryless] {σ : SmoothTwoForm I M} {f : M → ℝ}

/-- **Liouville's theorem.** For a symplectic form `σ` and a smooth function `f` with complete
Hamiltonian vector field, every time-`t` map of the Hamiltonian flow of `f` preserves the Liouville
measure. -/
theorem measurePreserving_globalFlowDiffeomorph_liouvilleMeasure (hσ : σ.IsSymplectic)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (σ.hamiltonianVectorField f)) (t : ℝ) :
    MeasurePreserving (globalFlowDiffeomorph hc le_top
      (hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl (by simpa using hf)) t)
      (σ.liouvilleMeasure n) (σ.liouvilleMeasure n) := by
  have hv : ContMDiff I I.tangent (⊤ : ℕ∞)
      (fun y ↦ (⟨y, σ.hamiltonianVectorField f y⟩ : TangentBundle I M)) :=
    hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl (by simpa using hf)
  set ψ := globalFlowDiffeomorph hc le_top hv t
  refine ψ.toHomeomorph.measurePreserving_liouvilleMeasure (ψ.mdifferentiable (by simp)) ?_
  have h := congrArg Subtype.val (hσ.mpullback_globalFlowDiffeomorph hf hc hv t)
  rw [SmoothForm.coe_mpullback] at h
  rwa [Diffeomorph.coe_toHomeomorph]

end TauCeti.SmoothTwoForm.IsSymplectic

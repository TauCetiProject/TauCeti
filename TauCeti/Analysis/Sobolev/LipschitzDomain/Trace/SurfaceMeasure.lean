/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.SurfaceMeasure
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Basic

/-!
# Local Sobolev traces and surface measure

For `1 ≤ p < ∞`, the localized Sobolev trace in a Lipschitz boundary chart is constructed as an
`Lᵖ` function on the tangential parameter space. Surface measure on the chart graph and
tangential Lebesgue measure have the same null sets. Consequently, the chart trace can also be
read almost everywhere on the frontier by evaluating it at the tangential coordinate of each
boundary point.

For a Sobolev function represented by a function continuous up to the boundary, this
surface-measure interpretation agrees almost everywhere with the classical boundary value of the
localized function. This is the compatibility needed to patch the local chart traces into a global
trace on the frontier.

## Main declaration

* `TauCeti.W1p.lipschitzChartTrace_comp_snd_ae_of_continuousOn`: the localized chart trace of a
  continuous Sobolev representative agrees with its classical value almost everywhere for
  normalized Euclidean Hausdorff measure on the frontier patch.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 1.
* J. Nečas, *Direct Methods in the Theory of Elliptic Equations*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Omega : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {phi : E → ℝ} {a b : ℝ}
  {psi : WithLp 2 (ℝ × E) → ℝ} {M : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The local trace agrees with classical boundary values in surface measure.** Let
`1 ≤ p < ∞`. If `u ∈ W^{1,p}(Ω)` agrees almost everywhere with a function `f` continuous on
`closure Ω`, then the localized trace through a Lipschitz boundary chart, read at the tangential
coordinate of a boundary point, equals `ψ * f` almost everywhere on the part of the frontier in
that chart. -/
theorem W1p.lipschitzChartTrace_comp_snd_ae_of_continuousOn (hp : p ≠ (∞ : ℝ≥0∞))
    (h : (Omega : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e phi a b)
    (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (hs : tsupport psi ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Omega p}
    {f : WithLp 2 (ℝ × E) → ℝ}
    (hf : ContinuousOn f (closure (Omega : Set (WithLp 2 (ℝ × E)))))
    (hu : W1p.value u =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))] f) :
    ∀ᵐ x ∂(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Omega : Set (WithLp 2 (ℝ × E))) ∩ e ⁻¹' normalCylinder a b),
      W1p.lipschitzChartTrace hp h psi hpsi hM hpsiM hgM hs u (e x).snd = psi x * f x := by
  let bad : Set E := {y |
    W1p.lipschitzChartTrace hp h psi hpsi hM hpsiM hgM hs u y ≠
      psi (e.symm (normalGraphEmbedding phi y)) * f (e.symm (normalGraphEmbedding phi y))}
  have hparameter : volume bad = 0 := by
    rw [← ae_iff]
    simpa only [bad, mem_ofPred_eq, not_not] using
      W1p.lipschitzChartTrace_apply_ae_of_continuousOn hp h hpsi hM hpsiM hgM hs hf hu
  have hsurface :
      μHE[finrank ℝ E]
          ((fun y ↦ e.symm (normalGraphEmbedding phi y)) '' bad) = 0 :=
    (h.euclideanHausdorffMeasure_image_boundaryParametrization_eq_zero_iff bad).2 hparameter
  refine (ae_restrict_iff' (measurableSet_frontier_inter_preimage_normalCylinder _ e a b)).2 ?_
  rw [ae_iff]
  apply measure_mono_null ?_ hsurface
  intro x hx
  simp only [mem_ofPred_eq, not_imp] at hx
  have hximage : x ∈ (fun y ↦ e.symm (normalGraphEmbedding phi y)) ''
      (normalGraphEmbedding phi ⁻¹' normalCylinder a b) := by
    rw [h.image_boundaryParametrization]
    exact hx.1
  obtain ⟨y, hy, rfl⟩ := hximage
  refine ⟨y, ?_, rfl⟩
  simpa only [bad, mem_ofPred_eq, e.apply_symm_apply, normalGraphEmbedding_snd] using hx.2

end TauCeti

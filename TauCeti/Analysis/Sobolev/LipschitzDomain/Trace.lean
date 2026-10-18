/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Localization
public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Local Sobolev traces in Lipschitz boundary charts

A smooth cutoff supported inside a Lipschitz boundary chart lets a Sobolev function be
transported to the whole epigraph of the chart's graph. Its epigraph trace is the localized
boundary trace, parametrized by `y ↦ e.symm (φ y, y)` and measured using Lebesgue measure on
the tangential space `E`. This is not yet a trace valued in Hausdorff surface measure on the
frontier of the original domain.

`W1p.lipschitzChartLocalizeL` performs the cutoff, zero extension past the artificial chart
boundary, and rigid coordinate change. It has norm at most `2 M`. Composing with the graph
trace gives `W1p.lipschitzChartTrace`, of norm at most `2 M (1 + L)`. Functions in `H¹₀` have
zero local trace. Equality of the cutoff products suffices for equality of local traces.
These are the local operators used when assembling a boundary trace by a partition of unity.

Unlike reflection extension, taking a trace requires no shortening of the chart cylinder:
the support need only lie inside the original cylinder.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 1.
* J. Nečas, *Direct Methods in the Theory of Elliptic Equations*, Chapter 2
  (traces on Lipschitz domains by local flattening).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}
  {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The localized `H¹` trace through a Lipschitz boundary chart. The result is in `L²(E)`
with respect to tangential Lebesgue measure, not surface measure on `frontier Ω`. -/
def W1p.lipschitzChartTrace
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (ψ : WithLp 2 (ℝ × E) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) :
    W1p volume Ω 2 →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  (W1p.normalEpigraphTrace (φ := ⟨φ, h.lipschitzWith.continuous⟩) h.lipschitzWith).comp
    (W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs)

/-- The local chart trace is the epigraph trace of the localized function in chart coordinates. -/
theorem W1p.lipschitzChartTrace_apply
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) (u : W1p volume Ω 2) :
    W1p.lipschitzChartTrace h ψ hψ hM hψM hgM hs u =
      W1p.normalEpigraphTrace h.lipschitzWith
        (W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u) := (rfl)

/-- The local trace estimate, with explicit cutoff and graph constants. -/
theorem W1p.norm_lipschitzChartTrace_le
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) (u : W1p volume Ω 2) :
    ‖W1p.lipschitzChartTrace h ψ hψ hM hψM hgM hs u‖ ≤ 2 * M * (1 + L) * ‖u‖ := by
  rw [W1p.lipschitzChartTrace_apply]
  calc
    _ ≤ (1 + L) * ‖W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u‖ :=
      W1p.norm_normalEpigraphTrace_le _ _
    _ ≤ (1 + L) * (2 * M * ‖u‖) := by
      gcongr
      exact W1p.norm_lipschitzChartLocalizeL_le h hψ hM hψM hgM hs u
    _ = _ := by ring

/-- The local trace has operator norm at most `2 M (1 + L)`. -/
theorem W1p.opNorm_lipschitzChartTrace_le
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) :
    ‖W1p.lipschitzChartTrace h ψ hψ hM hψM hgM hs‖ ≤ 2 * M * (1 + L) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (W1p.norm_lipschitzChartTrace_le h hψ hM hψM hgM hs)

/-- A function with zero Sobolev boundary values has zero trace in every localized chart. -/
theorem W1p.lipschitzChartTrace_eq_zero_of_mem_w1p0Submodule
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω 2}
    (hu : u ∈ w1p0Submodule volume Ω 2) :
    W1p.lipschitzChartTrace h ψ hψ hM hψM hgM hs u = 0 := by
  rw [W1p.lipschitzChartTrace_apply]
  exact (W1p.mem_w1p0Submodule_iff_normalEpigraphTrace_eq_zero _ _).1
    (W1p.lipschitzChartLocalizeL_mem_w1p0Submodule ENNReal.ofNat_ne_top
      h hψ hM hψM hgM hs hu)

/-- The local trace depends only on the cutoff product on the original domain. In particular,
values outside the support of the cutoff have no effect on it. -/
theorem W1p.lipschitzChartTrace_eq_of_smul_value_ae_eq
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u v : W1p volume Ω 2}
    (huv : (fun x => ψ x • W1p.value u x) =ᵐ[volume.restrict Ω]
      fun x => ψ x • W1p.value v x) :
    W1p.lipschitzChartTrace h ψ hψ hM hψM hgM hs u =
      W1p.lipschitzChartTrace h ψ hψ hM hψM hgM hs v := by
  rw [W1p.lipschitzChartTrace_apply, W1p.lipschitzChartTrace_apply]
  congr 1
  apply W1p.ext_value
  apply Lp.ext
  have hi := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).1 huv
  filter_upwards [W1p.value_lipschitzChartLocalizeL_ae h hψ hM hψM hgM hs u,
    W1p.value_lipschitzChartLocalizeL_ae h hψ hM hψM hgM hs v,
    ae_restrict_of_ae (e.symm.measurePreserving.quasiMeasurePreserving.ae hi)] with z hu hv hz
  rw [hu, hv, hz]

end TauCeti

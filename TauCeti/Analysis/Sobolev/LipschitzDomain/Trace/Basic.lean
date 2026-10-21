/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Localization
public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic
import TauCeti.Analysis.Sobolev.Trace.Continuous
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
zero local trace. Equality of the cutoff products suffices for equality of local traces. For a
function continuous up to the boundary, the local trace is the classical boundary value of the
cutoff product at the graph point (`W1p.lipschitzChartTrace_apply_ae_of_continuousOn`).
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

open MeasureTheory Set TopologicalSpace Filter Topology
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

/-- **The local trace of a function continuous up to the boundary.** If `u ∈ H¹(Ω)` agrees almost
everywhere with a function `f` continuous on `closure Ω`, then its local chart trace is the
classical boundary value of the cutoff product `ψ f` at the graph point `e.symm (φ y, y)`, for
almost every `y`. -/
theorem W1p.lipschitzChartTrace_apply_ae_of_continuousOn
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω 2}
    {f : WithLp 2 (ℝ × E) → ℝ} (hf : ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))))
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.lipschitzChartTrace h ψ hψ hM hψM hgM hs u y =
        ψ (e.symm (normalGraphEmbedding φ y)) * f (e.symm (normalGraphEmbedding φ y)) := by
  let G : WithLp 2 (ℝ × E) → ℝ := fun z => ψ (e.symm z) * f (e.symm z)
  -- Inside the chart cylinder, the closed region above the graph is the closure of `Ω`.
  have hcl : ∀ z ∈ normalCylinder a b, φ z.snd ≤ z.fst →
      e.symm z ∈ closure (Ω : Set (WithLp 2 (ℝ × E))) := by
    intro z hz hle
    obtain ⟨x, hx, rfl⟩ :=
      (h.toIsLipschitzChart.image_closure_inter_normalCylinder.superset ⟨hle, hz⟩).1
    simpa using hx
  have hG : ContinuousOn G {z | φ z.snd ≤ z.fst} := by
    intro z hz
    by_cases hzs : e.symm z ∈ tsupport ψ
    · have hzC : z ∈ normalCylinder a b := by simpa using hs hzs
      rw [← continuousWithinAt_inter ((isOpen_normalCylinder a b).mem_nhds hzC)]
      exact (hψ.continuous.comp e.symm.continuous).continuousWithinAt.mul
        ((hf (e.symm z) (hcl z hzC hz)).comp e.symm.continuous.continuousWithinAt
          fun w hw => hcl w hw.2 hw.1)
    · have hzero : G =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [((isClosed_tsupport ψ).isOpen_compl.preimage e.symm.continuous).mem_nhds
          hzs] with w hw
        simp [G, image_eq_zero_of_notMem_tsupport hw]
      exact (continuousAt_const.congr hzero.symm).continuousWithinAt
  have hu' := e.symm.measurePreserving.quasiMeasurePreserving.ae
    ((ae_restrict_iff' Ω.isOpen.measurableSet).1 hu)
  have hv : W1p.value (W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u) =ᵐ[volume.restrict
      (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩ : Set (WithLp 2 (ℝ × E)))] G := by
    filter_upwards [W1p.value_lipschitzChartLocalizeL_ae h hψ hM hψM hgM hs u,
      ae_restrict_of_ae hu',
      ae_restrict_mem (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩).isOpen.measurableSet]
      with z hz hfz hzE
    rw [hz]
    by_cases hzΩ : e.symm z ∈ Ω
    · rw [indicator_of_mem hzΩ, hfz hzΩ, smul_eq_mul]
    · have hzs : e.symm z ∉ tsupport ψ := fun hzs => hzΩ
        (chartEpigraph_inter_tsupport_subset h hs
          ⟨mem_chartEpigraph.2 (by simpa using hzE), hzs⟩)
      rw [indicator_of_notMem hzΩ]
      simp only [G, image_eq_zero_of_notMem_tsupport hzs, zero_mul]
  filter_upwards [W1p.normalEpigraphTrace_apply_ae_of_continuousOn h.lipschitzWith
    (f := G) (by simpa using hG) hv] with y hy
  rw [W1p.lipschitzChartTrace_apply, hy]
  simp only [G, ContinuousMap.coe_mk]

end TauCeti

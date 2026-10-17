/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic
public import TauCeti.Analysis.Sobolev.W1p.Localization
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

/-- Cut off a Sobolev function inside a Lipschitz boundary chart, extend by zero along the
artificial chart boundary, and express it in the rigid chart coordinates. The resulting
function is defined on the whole epigraph of the chart graph. -/
def W1p.lipschitzChartLocalizeL
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (ψ : WithLp 2 (ℝ × E) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) :
    W1p volume Ω p →L[ℝ] W1p volume (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩) p :=
  let V := Opens.comap ⟨e, e.continuous⟩ (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩)
  (W1p.compAffineIsometryEquivL e.symm (by ext z; simp [V])).comp <|
    (W1p.localizeL (inf_le_right : Ω ⊓ V ≤ V) ψ hψ hM
      (fun x hx => hψM x hx.1) (fun x hx => hgM x hx.1)
      (fun _ hx => ⟨(h.mem_iff (hs hx.2)).2 ((mem_normalEpigraph ..).1 hx.1),
        hx.1⟩)).comp
      (W1p.restrictL inf_le_left)

/-- In chart coordinates, localization is the cutoff product, set to zero outside the original
domain. This formula characterizes the localized Sobolev function by its value. -/
theorem W1p.value_lipschitzChartLocalizeL_ae
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) (u : W1p volume Ω p) :
    W1p.value (W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u) =ᵐ[
      volume.restrict (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩)] fun z =>
        (Ω : Set _).indicator (fun x => ψ x • W1p.value u x) (e.symm z) := by
  let V := Opens.comap ⟨e, e.continuous⟩ (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩)
  have hsub : (V : Set _) ∩ tsupport ψ ⊆ (Ω ⊓ V : Opens _) :=
    fun _ hx => ⟨(h.mem_iff (hs hx.2)).2 ((mem_normalEpigraph ..).1 hx.1), hx.1⟩
  let v := W1p.localizeL (inf_le_right : Ω ⊓ V ≤ V) ψ hψ hM
    (fun x hx => hψM x hx.1) (fun x hx => hgM x hx.1) hsub
    (W1p.restrictL (p := p) inf_le_left u)
  have hv := (ae_restrict_iff' V.isOpen.measurableSet).1
    (W1p.value_localizeL_ae (μ := volume) inf_le_right hψ hM
      (fun x hx => hψM x hx.1) (fun x hx => hgM x hx.1) hsub
      (W1p.restrictL (p := p) inf_le_left u))
  have hu := (ae_restrict_iff' (Ω ⊓ V).isOpen.measurableSet).1
    (W1p.value_restrictL_ae (p := p) (inf_le_left : Ω ⊓ V ≤ Ω) u)
  have hcoord : ((normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩ : Opens _) : Set _) =
      e.symm ⁻¹' V := by ext z; simp [V]
  rw [W1p.lipschitzChartLocalizeL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  filter_upwards [W1p.value_compAffineIsometryEquivL_ae e.symm hcoord v,
    ae_restrict_of_ae (e.symm.measurePreserving.quasiMeasurePreserving.ae hv),
    ae_restrict_of_ae (e.symm.measurePreserving.quasiMeasurePreserving.ae hu),
    ae_restrict_mem (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩).isOpen.measurableSet]
    with z hz hvz huz hzG
  have hzV : e.symm z ∈ V := by simpa [V] using hzG
  rw [hz, hvz hzV]
  by_cases hzΩ : e.symm z ∈ Ω
  · have hzU : e.symm z ∈ (Ω ⊓ V : Opens (WithLp 2 (ℝ × E))) := ⟨hzΩ, hzV⟩
    rw [indicator_of_mem hzU, indicator_of_mem hzΩ, huz hzU]
  · have hzU : e.symm z ∉ (Ω ⊓ V : Opens (WithLp 2 (ℝ × E))) := fun hx => hzΩ hx.1
    rw [indicator_of_notMem hzU, indicator_of_notMem hzΩ]

/-- Chart localization multiplies the Sobolev norm by at most `2 M`, independently of the
Lipschitz constant of the graph. -/
theorem W1p.norm_lipschitzChartLocalizeL_le
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) (u : W1p volume Ω p) :
    ‖W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u‖ ≤ 2 * M * ‖u‖ := by
  rw [W1p.lipschitzChartLocalizeL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  exact (W1p.norm_compAffineIsometryEquivL_le _ _ _).trans
    ((W1p.norm_localizeL_le _ _ _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (W1p.norm_restrictL_le inf_le_left u) (by positivity)))

/-- Chart localization preserves zero boundary values for finite Sobolev exponent. -/
theorem W1p.lipschitzChartLocalizeL_mem_w1p0Submodule (hp : p ≠ (∞ : ℝ≥0∞))
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω p}
    (hu : u ∈ w1p0Submodule volume Ω p) :
    W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u ∈
      w1p0Submodule volume (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩) p := by
  simp only [W1p.lipschitzChartLocalizeL, ContinuousLinearMap.comp_apply]
  apply W1p.compAffineIsometryEquivL_mem_w1p0Submodule hp
  exact W1p.localizeL_restrictL_mem_w1p0Submodule
    (V := Opens.comap ⟨e, e.continuous⟩ (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩))
    hp hψ hM hψM hgM
    (fun _ hx => (h.mem_iff (hs hx.2)).2 ((mem_normalEpigraph ..).1 hx.1))
    (fun x hx => (mem_normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩ (e x)).2
      ((h.mem_iff (hs hx.2)).1 hx.1)) hu

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

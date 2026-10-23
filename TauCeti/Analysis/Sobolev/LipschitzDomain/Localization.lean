/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
public import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Sobolev localization in Lipschitz boundary charts

`W1p.lipschitzChartLocalizeL` cuts off a Sobolev function, extends it by zero past the artificial
chart boundary, and transports it to the whole epigraph of the chart graph. Its norm is at most
`2 M`, for every `1 ≤ p ≤ ∞`; it preserves zero boundary values for finite exponents.
This is the common localization step for chart trace and reflection extension operators.
The support need only lie in the original chart cylinder.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §§5.4–5.5.
* J. Nečas, *Direct Methods in the Theory of Elliptic Equations*, Chapter 2.
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
  let V := chartEpigraph e h.lipschitzWith.continuous
  (W1p.compAffineIsometryEquivL e.symm
    (coe_normalEpigraph_eq_preimage e h.lipschitzWith.continuous)).comp <|
    (W1p.localizeL (inf_le_right : Ω ⊓ V ≤ V) ψ hψ hM
      (fun x hx => hψM x hx.1) (fun x hx => hgM x hx.1)
      (fun _ hx => ⟨chartEpigraph_inter_tsupport_subset h hs hx, hx.1⟩)).comp
      (W1p.restrictL inf_le_left)

/-- Chart localization is restriction, localization on the chart epigraph, and rigid transport. -/
theorem W1p.lipschitzChartLocalizeL_apply
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) (u : W1p volume Ω p) :
    let V := chartEpigraph e h.lipschitzWith.continuous
    W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u =
      W1p.compAffineIsometryEquivL e.symm
        (coe_normalEpigraph_eq_preimage e h.lipschitzWith.continuous)
        (W1p.localizeL (inf_le_right : Ω ⊓ V ≤ V) ψ hψ hM
          (fun x hx => hψM x hx.1) (fun x hx => hgM x hx.1)
          (fun _ hx => ⟨chartEpigraph_inter_tsupport_subset h hs hx, hx.1⟩)
          (W1p.restrictL inf_le_left u)) := (rfl)

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
  let V := chartEpigraph e h.lipschitzWith.continuous
  have hsub : (V : Set _) ∩ tsupport ψ ⊆ (Ω ⊓ V : Opens _) :=
    fun _ hx => ⟨chartEpigraph_inter_tsupport_subset h hs hx, hx.1⟩
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
      e.symm ⁻¹' V := coe_normalEpigraph_eq_preimage e h.lipschitzWith.continuous
  rw [W1p.lipschitzChartLocalizeL_apply]
  filter_upwards [W1p.value_compAffineIsometryEquivL_ae e.symm hcoord v,
    ae_restrict_of_ae (e.symm.measurePreserving.quasiMeasurePreserving.ae hv),
    ae_restrict_of_ae (e.symm.measurePreserving.quasiMeasurePreserving.ae hu),
    ae_restrict_mem (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩).isOpen.measurableSet]
    with z hz hvz huz hzG
  have hzV : e.symm z ∈ V := hcoord.subset hzG
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
  rw [W1p.lipschitzChartLocalizeL_apply]
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
  rw [W1p.lipschitzChartLocalizeL_apply]
  apply W1p.compAffineIsometryEquivL_mem_w1p0Submodule hp
  exact W1p.localizeL_restrictL_mem_w1p0Submodule
    (V := chartEpigraph e h.lipschitzWith.continuous)
    hp hψ hM hψM hgM
    (chartEpigraph_inter_tsupport_subset h hs)
    (inter_tsupport_subset_chartEpigraph h hs) hu

end TauCeti

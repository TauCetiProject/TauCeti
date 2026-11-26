/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.AdmissibleBoundaryPart
public import TauCeti.Analysis.Sobolev.LipschitzDomain.BoundaryPart
public import TauCeti.Analysis.Sobolev.Trace.Epigraph.AdmissibleBoundaryPart
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.InnerProductSpace.OfLinearIsometry
import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables
import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.Localization
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The trace characterization of `W^{1,p}_Γ(Ω)` for admissible boundary parts

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain, `σ` normalized `dim E`-dimensional Euclidean
Hausdorff measure on `frontier Ω`, `T : W^{1,p}(Ω) → Lᵖ(frontier Ω, σ)` the trace operator
(`TauCeti.W1p.frontierTrace`) and `1 ≤ p < ∞`. For an admissible boundary part `Γ`
(`Set.IsAdmissibleBoundaryPart`), this file proves the **trace characterization** of the space
`W^{1,p}_Γ(Ω)` of Sobolev functions vanishing on `Γ` (`TauCeti.w1pVanishingOnSubmodule`):
`u ∈ W^{1,p}_Γ(Ω)` exactly when `T u = 0` holds `σ`-almost everywhere on `Γ`
(`TauCeti.W1p.mem_w1pVanishingOnSubmodule_iff_frontierTrace_ae_eq_zero`). This identifies the
closure of the smooth functions vanishing near `Γ`, the energy space of the mixed boundary value
problem, with the space defined by the Dirichlet condition on `Γ` in the sense of traces. At
`Γ = frontier Ω` it is the kernel theorem `TauCeti.W1p.mem_w1p0Submodule_iff_frontierTrace_eq_zero`.

## The argument

Membership in `W^{1,p}_Γ(Ω)` is local, and the zero trace on `Γ` already gives it away from the
points where `closure Γ` meets `closure (frontier Ω \ Γ)`
(`TauCeti.W1p.mem_w1pVanishingOnSubmodule_of_frontierTrace_ae_eq_zero_of_forall_mem_closure_inter`).
At every frontier point, admissibility supplies a Lipschitz boundary chart `e` in which `Γ` is,
inside the chart cylinder, the part of the graph of `φ` lying over an admissible base region `B`.
It remains to show `ψ u ∈ W^{1,p}_Γ(Ω)` for cutoffs `ψ` supported in that cylinder.

* The local chart trace of `u` (`TauCeti.W1p.lipschitzChartTrace`), read at the tangential
  coordinate, is the trace of `ψ u` on the frontier patch of the chart
  (`TauCeti.W1p.lipschitzChartFrontierTrace_eq_frontierTrace_comp`), and surface measure on the
  patch corresponds to Lebesgue measure on the parameters
  (`Set.IsLipschitzChartWith.ae_restrict_frontier_inter_iff`). So it vanishes almost everywhere
  on `B` (`TauCeti.W1p.lipschitzChartTrace_ae_eq_zero_of_frontierTrace_ae_eq_zero`).
* The localized function in chart coordinates, defined above the graph of `φ`, then lies in
  `W^{1,p}` vanishing on the part of the graph over `B`, by the model characterization
  `W1p.mem_w1pVanishingOnSubmodule_iff_normalEpigraphTrace_ae_eq_zero_of_isAdmissibleBaseRegion`.
* Pulling it back along `e` and localizing it to `Ω` with a second cutoff, equal to one on the
  support of `ψ` and supported in the cylinder, recovers `ψ u`; inside the cylinder `Ω` agrees with
  the region above the graph and `Γ` with the part of the graph over `B`, so vanishing on the
  boundary part is preserved (`TauCeti.W1p.localizeL_restrictL_mem_w1pVanishingOnSubmodule`).

## Main declarations

* `TauCeti.W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartLocalizeL_mem`: a cutoff
  product whose chart localization vanishes on a set of chart coordinates containing the image of
  `Γ` lies in `W^{1,p}_Γ(Ω)`.
* `TauCeti.W1p.lipschitzChartTrace_ae_eq_zero_of_frontierTrace_ae_eq_zero`: zero trace on `Γ`
  gives zero local chart trace on every base region whose graph points lie in `Γ`.
* `TauCeti.W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartTrace_ae_eq_zero`: a cutoff
  product with zero local chart trace on an admissible base region lies in `W^{1,p}_Γ(Ω)`.
* `TauCeti.W1p.mem_w1pVanishingOnSubmodule_iff_frontierTrace_ae_eq_zero`: the trace
  characterization.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. **48** (2016), 2912–2943, §2.1
  (strong Lipschitz pairs), Lemma 3.1 and Appendix A (the trace characterization for `p = 2` in
  dimension three, by localization and flattening).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 2 (functions of zero
  trace).
-/

public section

noncomputable section

open Filter MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Gradient Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {Γ : Set (WithLp 2 (ℝ × E))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Cutoff products in one boundary chart -/

section Chart

variable {L : ℝ≥0} {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}
  {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ}

/-- **Vanishing on a boundary part, read in a chart.** Let `ψ` be a cutoff supported in the
cylinder of a Lipschitz boundary chart `e` of `Ω`, and let `Γ₀` be a set of chart coordinates
containing the image under `e` of every point of `Γ` in the cylinder. If the localization of
`u ∈ W^{1,p}(Ω)` to the region above the chart graph (`TauCeti.W1p.lipschitzChartLocalizeL`) lies in
`W^{1,p}_{Γ₀}` of that region, then `ψ u ∈ W^{1,p}_Γ(Ω)`. -/
theorem W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartLocalizeL_mem
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    {Γ₀ : Set (WithLp 2 (ℝ × E))} (hΓ : Γ ∩ e ⁻¹' normalCylinder a b ⊆ e ⁻¹' Γ₀)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω p}
    (hu : W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u ∈
      w1pVanishingOnSubmodule volume (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩) p Γ₀) :
    W1p.contDiffSMul ψ hψ hM hψM hgM u ∈ w1pVanishingOnSubmodule volume Ω p Γ := by
  let V := chartEpigraph e h.lipschitzWith.continuous
  -- Return to the original coordinates, on the chart epigraph `V`.
  have hVG := coe_chartEpigraph e h.lipschitzWith.continuous
  have hw' : W1p.compAffineIsometryEquivL e hVG (W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u)
      ∈ w1pVanishingOnSubmodule volume V p (e ⁻¹' Γ₀) :=
    W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule e hVG hu
  -- A cutoff `χ`, equal to one near `tsupport ψ` and supported in the chart cylinder `C`.
  have hC : IsOpen (e ⁻¹' normalCylinder a b) :=
    (isOpen_normalCylinder (E := E) a b).preimage e.continuous
  have hK : IsCompact (tsupport ψ) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport ψ)
      ((e.antilipschitzWith.isBounded_preimage (isBounded_normalCylinder a b)).subset hs)
  obtain ⟨χ, N, hχ, -, hχ1, -, hχs, hN, hχN, hgN⟩ := hK.exists_contDiff_cutoff_with_bounds hC hs
  -- Inside `C`, the closure of `Γ` lies in the closure of `e⁻¹' Γ₀`.
  have hΓχ : closure Γ ∩ tsupport χ ⊆ closure (e ⁻¹' Γ₀) := fun x hx =>
    closure_mono (fun y (hy : y ∈ e ⁻¹' normalCylinder a b ∩ Γ) => hΓ ⟨hy.2, hy.1⟩)
      (hC.inter_closure ⟨hχs hx.2, hx.1⟩)
  -- Inside `C`, `Ω` and `V` agree, so `χ` carries the pullback back to `ψ u`, in `W^{1,p}_Γ(Ω)`.
  rw [← W1p.localizeL_restrictL_compAffineIsometryEquivL_lipschitzChartLocalizeL h hψ hM hψM hgM
    hs hχ hN hχN hgN hχs (fun x hx => interior_subset (hχ1 hx)) u]
  exact W1p.localizeL_restrictL_mem_w1pVanishingOnSubmodule (Omega := V) (V := Ω)
    hχ hN (fun x _ => hχN x) (fun x _ => hgN x) (inter_tsupport_subset_chartEpigraph h hχs) hΓχ hw'

/-- In chart coordinates, the localization of `u` vanishes on the part of the graph over an
admissible base region `B` on which its local trace vanishes. This is the trace characterization
above a Lipschitz graph, which models interfaces on an inner product space. -/
private theorem W1p.lipschitzChartLocalizeL_mem_w1pVanishingOnSubmodule_of_ae_eq_zero
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [MeasurableSpace E']
    [BorelSpace E'] (hp : p ≠ (∞ : ℝ≥0∞))
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b) {B : Set E}
    (hB : B.IsAdmissibleBaseRegion E') (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω p}
    (hu : ∀ᵐ y ∂(volume : Measure E), y ∈ B →
      W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u y = 0) :
    W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u ∈
      w1pVanishingOnSubmodule volume (normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩) p
        {z | z.fst = φ z.snd ∧ z.snd ∈ B} := by
  have hmodel :=
    W1p.mem_w1pVanishingOnSubmodule_iff_normalEpigraphTrace_ae_eq_zero_of_isAdmissibleBaseRegion
      (φ := ⟨φ, h.lipschitzWith.continuous⟩) hp h.lipschitzWith hB
      (W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u)
  exact hmodel.2 (by simpa only [W1p.lipschitzChartTrace_apply] using hu)

/-- **Zero local trace on an admissible base region.** Let `1 ≤ p < ∞`, let `ψ` be a cutoff
supported in the cylinder of a Lipschitz boundary chart `e` of `Ω` with graph `φ`, and let `B` be an
admissible base region such that every point of `Γ` in the cylinder lies, in chart coordinates, on
the part of the graph over `B`. If the local trace of `u ∈ W^{1,p}(Ω)` through the chart
(`TauCeti.W1p.lipschitzChartTrace`) vanishes almost everywhere on `B`, then
`ψ u ∈ W^{1,p}_Γ(Ω)`. -/
theorem W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartTrace_ae_eq_zero
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (hp : p ≠ (∞ : ℝ≥0∞))
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b) {B : Set E}
    (hB : B.IsAdmissibleBaseRegion E')
    (hΓ : Γ ∩ e ⁻¹' normalCylinder a b ⊆ e ⁻¹' {z | z.fst = φ z.snd ∧ z.snd ∈ B})
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω p}
    (hu : ∀ᵐ y ∂(volume : Measure E), y ∈ B →
      W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u y = 0) :
    W1p.contDiffSMul ψ hψ hM hψM hgM u ∈ w1pVanishingOnSubmodule volume Ω p Γ := by
  refine W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartLocalizeL_mem h hΓ hψ hM
    hψM hgM hs ?_
  -- Model the interfaces on an inner product space: `E` itself when `B` has no interface, and
  -- otherwise `E'` with the inner product of its isometric image in `E`.
  obtain rfl | rfl | ⟨f, β, K, hβ, rfl⟩ := isAdmissibleBaseRegion_iff.1 hB
  · exact W1p.lipschitzChartLocalizeL_mem_w1pVanishingOnSubmodule_of_ae_eq_zero (E' := E) hp h
      isAdmissibleBaseRegion_univ hψ hM hψM hgM hs hu
  · exact W1p.lipschitzChartLocalizeL_mem_w1pVanishingOnSubmodule_of_ae_eq_zero (E' := E) hp h
      isAdmissibleBaseRegion_empty hψ hM hψM hgM hs hu
  · let _ : InnerProductSpace ℝ E' := .ofLinearIsometry f.symmInr
    let _ : MeasurableSpace E' := borel E'
    have _ : BorelSpace E' := ⟨rfl⟩
    exact W1p.lipschitzChartLocalizeL_mem_w1pVanishingOnSubmodule_of_ae_eq_zero hp h
      (isAdmissibleBaseRegion_preimage_setOf_lt_fst f hβ) hψ hM hψM hgM hs hu

/-- **Zero trace on `Γ` gives zero local chart traces on the base.** On a bounded Lipschitz domain
and for `1 ≤ p < ∞`, let the trace of `u ∈ W^{1,p}(Ω)` vanish almost everywhere on `Γ`, and let
`B` be a measurable set of tangential parameters whose graph points in the cylinder of a Lipschitz
boundary chart `e` of `Ω` correspond to points of `Γ`. Then the local trace of `u` through the
chart vanishes almost everywhere on `B`. -/
theorem W1p.lipschitzChartTrace_ae_eq_zero_of_frontierTrace_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    {L' : ℝ≥0} (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L')
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b) {B : Set E}
    (hBm : MeasurableSet B)
    (hΓ : ∀ y ∈ B, normalGraphEmbedding φ y ∈ normalCylinder a b →
      e.symm (normalGraphEmbedding φ y) ∈ Γ)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω p}
    (hu : W1p.frontierTrace hp hΩ hb u =ᵐ[((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))).restrict Γ] 0) :
    ∀ᵐ y ∂(volume : Measure E), y ∈ B →
      W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u y = 0 := by
  let σ := (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
    (frontier (Ω : Set (WithLp 2 (ℝ × E))))
  let P := frontier (Ω : Set (WithLp 2 (ℝ × E))) ∩ e ⁻¹' normalCylinder a b
  have hPm : MeasurableSet P := measurableSet_frontier_inter_preimage_normalCylinder _ e a b
  -- The frontier points of the chart patch with tangential coordinate in `B` lie in `Γ`.
  have hS : P ∩ (fun x => (e x).snd) ⁻¹' B ⊆ Γ := by
    rintro x ⟨⟨hxF, hxC⟩, hxB⟩
    -- Inside the cylinder, the frontier point `e x` is the graph point over its base coordinate.
    obtain ⟨y, hy⟩ : e x ∈ range (normalGraphEmbedding φ) := by
      rw [range_normalGraphEmbedding]
      exact h.toIsLipschitzChart.fst_apply_eq_of_mem_frontier hxF hxC
    have hyx : y = (e x).snd := by rw [← hy, normalGraphEmbedding_snd]
    simpa [hy] using hΓ y (hyx ▸ hxB) (hy ▸ hxC)
  have hSm : MeasurableSet (P ∩ (fun x => (e x).snd) ⁻¹' B) :=
    hPm.inter (e.measurable_snd_apply hBm)
  -- The frontier version of the local trace is the trace of `ψ u`, which vanishes on `Γ`.
  have hF : W1p.lipschitzChartFrontierTrace hp h ψ hψ hM hψM hgM hs u =ᵐ[σ.restrict Γ] 0 := by
    rw [W1p.lipschitzChartFrontierTrace_eq_frontierTrace_comp hp hΩ hb,
      ContinuousLinearMap.comp_apply, W1p.contDiffSMulL_apply]
    filter_upwards [ae_restrict_of_ae (W1p.frontierTrace_contDiffSMul_ae hp hΩ hb hψ hM hψM hgM u),
      hu] with x hx h0
    rw [hx, h0, Pi.zero_apply, mul_zero]
  -- On the patch it is the local trace at the tangential coordinate, so the local trace
  -- vanishes at almost every point of the patch whose tangential coordinate lies in `B`.
  have hpatch : ∀ᵐ x ∂(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict P,
      (e x).snd ∈ B → W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u (e x).snd = 0 := by
    have h0 : ∀ᵐ x ∂σ.restrict Γ,
        P.indicator (fun x => W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u (e x).snd) x =
          0 := by
      filter_upwards [ae_restrict_of_ae
        (W1p.lipschitzChartFrontierTrace_ae_eq hp h hψ hM hψM hgM hs u), hF] with x hx h0
      rw [← hx, h0, Pi.zero_apply]
    have h1 := (ae_restrict_iff' hSm).1 (ae_restrict_of_ae_restrict_of_subset hS h0)
    have h2 : ∀ᵐ x ∂(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))), x ∈ frontier
        (Ω : Set (WithLp 2 (ℝ × E))) → x ∈ P ∩ (fun x => (e x).snd) ⁻¹' B →
          P.indicator (fun x => W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u (e x).snd) x =
            0 :=
      (ae_restrict_iff' isClosed_frontier.measurableSet).1 h1
    filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hPm] with x hx hxP hxB
    simpa [indicator_of_mem hxP] using hx hxP.1 ⟨hxP, hxB⟩
  -- Pass to tangential parameters; graph points outside the cylinder carry no local trace.
  filter_upwards [(ae_restrict_iff' h.measurableSet_normalGraphEmbedding_preimage_normalCylinder).1
      ((h.ae_restrict_frontier_inter_iff (P := fun y => y ∈ B →
        W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u y = 0)).1 hpatch),
    W1p.lipschitzChartTrace_ae_eq_zero_of_notMem hp hΩ hb h hψ hM hψM hgM hs u] with y hy hy'
  exact fun hyB => (em _).elim (fun hyC => hy hyC hyB) hy'

end Chart

/-! ### The trace characterization -/

/-- **The trace characterization of `W^{1,p}_Γ(Ω)`.** Let `Ω ⊆ ℝ × E` be a bounded Lipschitz
domain, `1 ≤ p < ∞`, and `Γ` an admissible boundary part of `Ω`, with interfaces in the base
modelled on `E'`. Then `u ∈ W^{1,p}(Ω)` lies in `W^{1,p}_Γ(Ω)`, the closure
of the restrictions of test functions vanishing near `Γ`, exactly when its trace vanishes almost
everywhere on `Γ` for surface measure on the frontier. -/
theorem W1p.mem_w1pVanishingOnSubmodule_iff_frontierTrace_ae_eq_zero
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (hp : p ≠ (∞ : ℝ≥0∞)) {L : ℝ≥0}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hΓ : (Ω : Set (WithLp 2 (ℝ × E))).IsAdmissibleBoundaryPart Γ E E') (u : W1p volume Ω p) :
    u ∈ w1pVanishingOnSubmodule volume Ω p Γ ↔
      W1p.frontierTrace hp hΩ hb u =ᵐ[((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))).restrict Γ] 0 := by
  refine ⟨W1p.frontierTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule hp hΩ hb, fun hu => ?_⟩
  have hΓΩ : Disjoint Γ (Ω : Set (WithLp 2 (ℝ × E))) :=
    (disjoint_frontier_iff_isOpen.2 Ω.isOpen).mono_left hΓ.subset_frontier
  refine W1p.mem_w1pVanishingOnSubmodule_of_frontierTrace_ae_eq_zero_of_forall_mem_closure_inter
    hp hΩ hb hΓΩ hu fun x hx => ?_
  -- A boundary-part chart centred at `x`, with admissible base region `B`.
  have hxF : x ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))) :=
    closure_minimal hΓ.subset_frontier isClosed_frontier hx.1
  obtain ⟨e, γ, K, h, r, B, hc, hB, hex⟩ := hΓ.exists_isBoundaryPartChart x hxF
  have hxC : e x ∈ normalCylinder h r :=
    hex ▸ zero_mem_normalCylinder hc.isLipschitzChart.height_pos hc.isLipschitzChart.radius_pos
  have hγ : γ 0 = 0 := by
    simpa [hex] using (hc.isLipschitzChart.fst_apply_eq_of_mem_frontier hxF hxC).symm
  have hch := hc.isLipschitzChart.isLipschitzChartWith hγ
  refine ⟨e ⁻¹' normalCylinder h r, hc.isLipschitzChart.preimage_normalCylinder_mem_nhds hex,
    fun ψ hψ M hM hψM hgM hs => ?_⟩
  refine W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartTrace_ae_eq_zero hp hch hB
    (fun z hz => (hc.mem_iff hz.2).1 hz.1) hψ hM hψM hgM hs
    (W1p.lipschitzChartTrace_ae_eq_zero_of_frontierTrace_ae_eq_zero hp hΩ hb hch
      hB.isOpen.measurableSet (fun y hyB hyC => ?_) hψ hM hψM hgM hs hu)
  -- A graph point over `B` inside the cylinder corresponds to a point of `Γ`.
  refine (hc.mem_iff (by simpa using hyC)).2 ?_
  simpa [normalGraphEmbedding_apply] using hyB

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.AdmissibleBoundaryPart
public import TauCeti.Analysis.Sobolev.LipschitzDomain.BoundaryPart
public import TauCeti.Analysis.Sobolev.Trace.Epigraph.AdmissibleBoundaryPart
import TauCeti.Analysis.InnerProductSpace.OfLinearIsometry
import TauCeti.Analysis.Sobolev.LipschitzDomain.Localization

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

* Zero trace on `Γ` gives zero local chart trace (`TauCeti.W1p.lipschitzChartTrace`) almost
  everywhere on `B` (`TauCeti.W1p.lipschitzChartTrace_ae_eq_zero_of_isBoundaryPartChart`).
* The localized function in chart coordinates, defined above the graph of `φ`, then lies in
  `W^{1,p}` vanishing on the part of the graph over `B`, by the model characterization
  `W1p.mem_w1pVanishingOnSubmodule_iff_normalEpigraphTrace_ae_eq_zero_of_isAdmissibleBaseRegion`.
* Undoing the chart localization carries this back to `ψ u ∈ W^{1,p}_Γ(Ω)`
  (`TauCeti.W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartLocalizeL_mem`).

## Main declarations

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
  refine W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartLocalizeL_mem h hψ hM hψM
    hgM hs hΓ ?_
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
  exact W1p.contDiffSMul_mem_w1pVanishingOnSubmodule_of_lipschitzChartTrace_ae_eq_zero hp hch hB
    hc.inter_preimage_normalCylinder_subset hψ hM hψM hgM hs
    (W1p.lipschitzChartTrace_ae_eq_zero_of_isBoundaryPartChart hp hΩ hb hc hγ hψ hM hψM hgM hs hu)

end TauCeti

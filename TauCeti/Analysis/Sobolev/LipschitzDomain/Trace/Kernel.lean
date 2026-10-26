/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.PartitionOfUnity
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Functions of zero trace on a Lipschitz domain

Let `Ω ⊆ ℝ × E` be open and `1 ≤ p < ∞`. Functions in `W^{1,p}_0(Ω)` have zero local trace in
every Lipschitz boundary chart (`TauCeti.W1p.lipschitzChartTrace_eq_zero_of_mem_w1p0Submodule`).
This file proves the converse: zero local traces in the charts of a partition of unity force zero
boundary values.

The key step is local. If the trace of `u ∈ W^{1,p}(Ω)` through one chart, localized by a cutoff
`ψ`, vanishes, then `ψ u ∈ W^{1,p}_0(Ω)`. In chart coordinates the localized function lies above a
Lipschitz graph and has zero graph trace, so it lies in `W^{1,p}_0` of the epigraph
(`TauCeti.W1p.mem_w1p0Submodule_iff_normalEpigraphTrace_eq_zero`). A second cutoff, equal to one
near the support of `ψ` and supported in the chart cylinder, carries it back to `W^{1,p}_0(Ω)`,
because `Ω` and the epigraph agree inside the cylinder. Writing `u = ψ₀ u + ∑ ψᵢ u` with `ψ₀`
compactly supported in `Ω` then gives `u ∈ W^{1,p}_0(Ω)` whenever every chart trace vanishes.

Every bounded Lipschitz domain carries such a partition of unity
(`Set.IsLipschitzDomainWith.exists_contDiff_partitionOfUnity`). Hence on a bounded Lipschitz
domain, `W^{1,p}_0(Ω)` is the common kernel of finitely many local chart traces
`W^{1,p}(Ω) → Lᵖ(E)`. These traces are measured by tangential Lebesgue measure in each chart; no
surface measure on `frontier Ω` is involved.

## Main declarations

* `TauCeti.W1p.contDiffSMul_mem_w1p0Submodule_of_lipschitzChartTrace_eq_zero`: a cutoff product
  with zero local chart trace lies in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.mem_w1p0Submodule_iff_forall_lipschitzChartTrace_eq_zero` and
  `TauCeti.W1p.iInf_ker_lipschitzChartTrace`: for the charts of a partition of unity,
  `W^{1,p}_0(Ω)` is the common kernel of the local traces.
* `TauCeti.W1p.exists_iInf_ker_lipschitzChartTrace_eq_of_isLipschitzDomainWith`: on a bounded
  Lipschitz domain, `W^{1,p}_0(Ω)` is the common kernel of finitely many local chart traces.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 2.
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
  {Ω : Opens (WithLp 2 (ℝ × E))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

section Chart

variable {L : ℝ≥0} {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}
  {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ}

/-- **Zero local trace gives zero boundary values.** Let `1 ≤ p < ∞`. If the trace of
`u ∈ W^{1,p}(Ω)` through a Lipschitz boundary chart, localized by the cutoff `ψ`, vanishes, then
`ψ u ∈ W^{1,p}_0(Ω)`. -/
theorem W1p.contDiffSMul_mem_w1p0Submodule_of_lipschitzChartTrace_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω p}
    (hu : W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u = 0) :
    W1p.contDiffSMul ψ hψ hM hψM hgM u ∈ w1p0Submodule volume Ω p := by
  let V := chartEpigraph e h.lipschitzWith.continuous
  let G := normalEpigraph ⟨φ, h.lipschitzWith.continuous⟩
  let w := W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM hs u
  -- In chart coordinates the localized function has zero graph trace, so it lies in `W^{1,p}_0`.
  have hw : w ∈ w1p0Submodule volume G p :=
    (W1p.mem_w1p0Submodule_iff_normalEpigraphTrace_eq_zero hp _ _).2
      (by rwa [W1p.lipschitzChartTrace_apply] at hu)
  -- Return to the original coordinates, on the chart epigraph `V = e⁻¹' G`.
  have hVG : (V : Set (WithLp 2 (ℝ × E))) = e ⁻¹' (G : Set (WithLp 2 (ℝ × E))) := by
    ext x
    simp [V, G, coe_normalEpigraph_eq_preimage e h.lipschitzWith.continuous]
  let w' := W1p.compAffineIsometryEquivL e hVG w
  have hw' : w' ∈ w1p0Submodule volume V p :=
    W1p.compAffineIsometryEquivL_mem_w1p0Submodule hp e hVG hw
  -- A cutoff `χ`, equal to one near `tsupport ψ` and supported in the chart cylinder.
  have hcyl : IsOpen (e ⁻¹' normalCylinder (E := E) a b) :=
    (isOpen_normalCylinder a b).preimage e.continuous
  have hK : IsCompact (tsupport ψ) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport ψ)
      ((e.antilipschitzWith.isBounded_preimage (isBounded_normalCylinder a b)).subset hs)
  obtain ⟨χ, N, hχ, -, hχ1, -, hχs, hN, hχN, hgN⟩ :=
    hK.exists_contDiff_cutoff_with_bounds hcyl hs
  -- Inside the cylinder `Ω` and `V` agree, so `χ` carries `w'` from `W^{1,p}_0(V)` to
  -- `W^{1,p}_0(Ω)`.
  have hmem := W1p.localizeL_restrictL_mem_w1p0Submodule (Ω := V) (V := Ω)
    hp hχ hN (fun x _ => hχN x) (fun x _ => hgN x)
    (inter_tsupport_subset_chartEpigraph h hχs) (chartEpigraph_inter_tsupport_subset h hχs) hw'
  convert hmem using 1
  -- Both sides are `ψ u` on `Ω`.
  apply W1p.ext_value
  apply Lp.ext
  have hwG := (ae_restrict_iff' G.isOpen.measurableSet).1
    (W1p.value_lipschitzChartLocalizeL_ae h hψ hM hψM hgM hs u)
  have hwV : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))), x ∈ V →
      W1p.value w (e x) = (Ω : Set _).indicator (fun y => ψ y • W1p.value u y) x := by
    filter_upwards [e.measurePreserving.quasiMeasurePreserving.ae hwG] with x hx hxV
    simpa using hx (hVG.subset hxV)
  have hw'V := (ae_restrict_iff' V.isOpen.measurableSet).1
    (W1p.value_compAffineIsometryEquivL_ae e hVG w)
  have hres := (ae_restrict_iff' (V ⊓ Ω).isOpen.measurableSet).1
    (W1p.value_restrictL_ae (inf_le_left : V ⊓ Ω ≤ V) w')
  filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM hgM u,
    W1p.value_localizeL_ae (inf_le_right : V ⊓ Ω ≤ Ω) hχ hN (fun x _ => hχN x)
      (fun x _ => hgN x) (fun _ hx => ⟨inter_tsupport_subset_chartEpigraph h hχs hx, hx.1⟩)
      (W1p.restrictL inf_le_left w'),
    ae_restrict_of_ae hwV, ae_restrict_of_ae hw'V, ae_restrict_of_ae hres,
    ae_restrict_mem Ω.isOpen.measurableSet] with x hx hloc hwx hw'x hresx hxΩ
  rw [hx, hloc]
  by_cases hxV : x ∈ V
  · have hxVΩ : x ∈ ((V ⊓ Ω : Opens _) : Set (WithLp 2 (ℝ × E))) := ⟨hxV, hxΩ⟩
    rw [indicator_of_mem hxVΩ, hresx hxVΩ, hw'x hxV, hwx hxV, indicator_of_mem hxΩ]
    by_cases hxψ : x ∈ tsupport ψ
    · rw [interior_subset (hχ1 hxψ), one_smul]
    · simp [image_eq_zero_of_notMem_tsupport hxψ]
  · have hxψ : x ∉ tsupport ψ := fun hxψ =>
      hxV (inter_tsupport_subset_chartEpigraph h hs ⟨hxΩ, hxψ⟩)
    have hxVΩ : x ∉ ((V ⊓ Ω : Opens _) : Set (WithLp 2 (ℝ × E))) := fun hx => hxV hx.1
    rw [indicator_of_notMem hxVΩ, image_eq_zero_of_notMem_tsupport hxψ, zero_smul]

end Chart

section Partition

variable {ι : Type*} [Fintype ι] {L : ι → ℝ≥0} {e : ι → WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)}
  {φ : ι → E → ℝ} {a b : ι → ℝ} {ψ₀ : WithLp 2 (ℝ × E) → ℝ}
  {ψ : ι → WithLp 2 (ℝ × E) → ℝ} {M : ι → ℝ}

/-- **The functions of zero trace on a chart-covered domain are those of `W^{1,p}_0`.** Let
`1 ≤ p < ∞`, let `ψ₀` be a smooth cutoff compactly supported in `Ω`, and let each `ψ i` be
supported in the cylinder of a Lipschitz boundary chart, with `ψ₀ + ∑ i, ψ i = 1` on `Ω`. Then
`u ∈ W^{1,p}(Ω)` lies in `W^{1,p}_0(Ω)` if and only if all of its local chart traces vanish. -/
theorem W1p.mem_w1p0Submodule_iff_forall_lipschitzChartTrace_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    (h : ∀ i, (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith (L i) (e i) (φ i) (a i) (b i))
    (hψ₀ : ContDiff ℝ ∞ ψ₀) (hψ₀c : HasCompactSupport ψ₀) (hψ₀Ω : tsupport ψ₀ ⊆ Ω)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hM : ∀ i, 0 ≤ M i)
    (hψM : ∀ i, ∀ x ∈ Ω, |ψ i x| ≤ M i) (hgM : ∀ i, ∀ x ∈ Ω, ‖∇ (ψ i) x‖ ≤ M i)
    (hs : ∀ i, tsupport (ψ i) ⊆ e i ⁻¹' normalCylinder (a i) (b i))
    (hsum : ∀ x ∈ Ω, ψ₀ x + ∑ i, ψ i x = 1) (u : W1p volume Ω p) :
    u ∈ w1p0Submodule volume Ω p ↔
      ∀ i, W1p.lipschitzChartTrace hp (h i) (ψ i) (hψ i) (hM i) (hψM i) (hgM i) (hs i) u = 0 := by
  refine ⟨fun hu i => W1p.lipschitzChartTrace_eq_zero_of_mem_w1p0Submodule hp (h i) (hψ i) (hM i)
    (hψM i) (hgM i) (hs i) hu, fun hu => ?_⟩
  obtain ⟨M₀, hM₀, hψ₀M, hgM₀⟩ :=
    (hψ₀.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψ₀c
  -- Split `u` by the partition of unity; every piece has zero boundary values.
  have hsplit : u = W1p.contDiffSMul ψ₀ hψ₀ hM₀ (fun x _ => hψ₀M x) (fun x _ => hgM₀ x) u +
      ∑ i, W1p.contDiffSMul (ψ i) (hψ i) (hM i) (hψM i) (hgM i) u := by
    apply W1p.ext_value
    apply Lp.ext
    filter_upwards [W1p.value_add_ae
        (W1p.contDiffSMul ψ₀ hψ₀ hM₀ (fun x _ => hψ₀M x) (fun x _ => hgM₀ x) u)
        (∑ i, W1p.contDiffSMul (ψ i) (hψ i) (hM i) (hψM i) (hgM i) u),
      W1p.value_contDiffSMul_ae hψ₀ hM₀ (fun x _ => hψ₀M x) (fun x _ => hgM₀ x) u,
      W1p.value_finsetSum_ae Finset.univ
        (fun i => W1p.contDiffSMul (ψ i) (hψ i) (hM i) (hψM i) (hgM i) u),
      ae_all_iff.2 fun i => W1p.value_contDiffSMul_ae (hψ i) (hM i) (hψM i) (hgM i) u,
      ae_restrict_mem Ω.isOpen.measurableSet] with x hadd h₀ hsumx hi hxΩ
    rw [hadd, Pi.add_apply, h₀, hsumx]
    simp only [hi, smul_eq_mul, ← Finset.sum_mul, ← add_mul, hsum x hxΩ, one_mul]
  rw [hsplit]
  exact add_mem (W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport hp
    hψ₀ hM₀ _ _ hψ₀c hψ₀Ω u) (Submodule.sum_mem _ fun i _ =>
      W1p.contDiffSMul_mem_w1p0Submodule_of_lipschitzChartTrace_eq_zero hp (h i) (hψ i) (hM i)
        (hψM i) (hgM i) (hs i) (hu i))

/-- **The common kernel of the local traces is `W^{1,p}_0`.** For `1 ≤ p < ∞` and the charts of
a partition of unity as in `TauCeti.W1p.mem_w1p0Submodule_iff_forall_lipschitzChartTrace_eq_zero`,
the local traces `W^{1,p}(Ω) → Lᵖ(E)` vanish simultaneously exactly on `W^{1,p}_0(Ω)`. -/
theorem W1p.iInf_ker_lipschitzChartTrace (hp : p ≠ (∞ : ℝ≥0∞))
    (h : ∀ i, (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith (L i) (e i) (φ i) (a i) (b i))
    (hψ₀ : ContDiff ℝ ∞ ψ₀) (hψ₀c : HasCompactSupport ψ₀) (hψ₀Ω : tsupport ψ₀ ⊆ Ω)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hM : ∀ i, 0 ≤ M i)
    (hψM : ∀ i, ∀ x ∈ Ω, |ψ i x| ≤ M i) (hgM : ∀ i, ∀ x ∈ Ω, ‖∇ (ψ i) x‖ ≤ M i)
    (hs : ∀ i, tsupport (ψ i) ⊆ e i ⁻¹' normalCylinder (a i) (b i))
    (hsum : ∀ x ∈ Ω, ψ₀ x + ∑ i, ψ i x = 1) :
    ⨅ i, LinearMap.ker
        (W1p.lipschitzChartTrace hp (h i) (ψ i) (hψ i) (hM i) (hψM i) (hgM i)
          (hs i)).toLinearMap =
      w1p0Submodule volume Ω p := by
  ext u
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  exact (W1p.mem_w1p0Submodule_iff_forall_lipschitzChartTrace_eq_zero hp h hψ₀ hψ₀c hψ₀Ω hψ hM
    hψM hgM hs hsum u).symm

end Partition

/-- **Zero trace on a bounded Lipschitz domain.** A bounded Lipschitz domain has finitely many
boundary charts with cutoffs such that, for every `1 ≤ p < ∞`, the local traces
`W^{1,p}(Ω) → Lᵖ(E)` vanish simultaneously exactly on `W^{1,p}_0(Ω)`. -/
theorem W1p.exists_iInf_ker_lipschitzChartTrace_eq_of_isLipschitzDomainWith {L : ℝ≥0}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ (t : Finset (WithLp 2 (ℝ × E))) (e : t → WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
      (φ : t → E → ℝ) (a b : t → ℝ)
      (h : ∀ i, (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L (e i) (φ i) (a i) (b i))
      (ψ : t → WithLp 2 (ℝ × E) → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (M : t → ℝ)
      (hM : ∀ i, 0 ≤ M i) (hψM : ∀ i, ∀ x ∈ Ω, |ψ i x| ≤ M i)
      (hgM : ∀ i, ∀ x ∈ Ω, ‖∇ (ψ i) x‖ ≤ M i)
      (hs : ∀ i, tsupport (ψ i) ⊆ e i ⁻¹' normalCylinder (a i) (b i)),
      ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ (∞ : ℝ≥0∞)),
        ⨅ i, LinearMap.ker
            (W1p.lipschitzChartTrace hq (h i) (ψ i) (hψ i) (hM i) (hψM i) (hgM i)
              (hs i)).toLinearMap =
          w1p0Submodule volume Ω q := by
  obtain ⟨t, e, φ, a, b, ψ₀, ψ, M, hchart, ⟨hψ₀, hψ₀c, hψ₀Ω⟩, hψ, hsum⟩ :=
    hΩ.exists_lipschitzChart_cutoffs hb
  choose hψ hM hψM hgM hs using hψ
  refine ⟨t, e, φ, a, b, hchart, ψ, hψ, M, hM, fun i x _ => hψM i x, fun i x _ => hgM i x, hs,
    fun q _ hq => ?_⟩
  exact W1p.iInf_ker_lipschitzChartTrace hq _ hψ₀ hψ₀c hψ₀Ω _ _ _ _ _
    fun x hx => hsum x (subset_closure hx)

end TauCeti

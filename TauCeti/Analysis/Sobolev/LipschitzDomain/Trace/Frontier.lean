/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.SurfaceMeasure
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Kernel

/-!
# The boundary trace of a bounded Lipschitz domain

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain and let `σ` be normalized `dim E`-dimensional
Euclidean Hausdorff measure restricted to `frontier Ω`. For `1 ≤ p < ∞`, this file constructs
the trace operator

`TauCeti.W1p.frontierTrace : W^{1,p}(Ω) →L[ℝ] Lᵖ(frontier Ω, σ)`,

the unique bounded linear operator that sends every `u ∈ W^{1,p}(Ω)` represented by a function `f`
continuous on `closure Ω` to the restriction of `f` to the frontier.

The construction glues the local chart traces. In one Lipschitz boundary chart, the local trace
is an `Lᵖ` function of the tangential parameter. Reading it at the tangential coordinate of each
boundary point transports it to `Lᵖ` of surface measure on the frontier patch; this is bounded
because surface measure pushes forward to at most `(L + 1) ^ dim E` times tangential Lebesgue
measure (`Set.IsLipschitzChartWith.map_snd_euclideanHausdorffMeasure_frontier_inter_le`).
Extension by zero gives `TauCeti.W1p.lipschitzChartFrontierTrace`. Summing over the charts of a
partition of unity, whose interior cutoff vanishes on the frontier, produces an operator with the
required boundary values. Uniqueness, and hence independence of all choices, follows because
restrictions of test functions are dense in `W^{1,p}(Ω)`
(`TauCeti.W1p.denseRange_restrictL_ofTestFunctionₗ_top`).

The same density argument shows that the trace commutes with multiplication by smooth bounded
functions, and that the frontier version of each local chart trace is the trace of the cutoff
product. Hence a function of zero trace has zero local trace in every chart, and the chart
characterization of `W^{1,p}_0(Ω)`
(`TauCeti.W1p.mem_w1p0Submodule_iff_forall_lipschitzChartTrace_eq_zero`) identifies the kernel
of the trace with `W^{1,p}_0(Ω)`.

## Main declarations

* `TauCeti.W1p.lipschitzChartFrontierTrace`: a local chart trace as an `Lᵖ` function on the
  frontier for surface measure.
* `TauCeti.W1p.frontierTrace`: the trace operator of a bounded Lipschitz domain.
* `TauCeti.W1p.frontierTrace_ae_eq_of_continuousOn`: the trace of a function continuous up to
  the boundary is its restriction to the frontier.
* `TauCeti.W1p.eq_frontierTrace`: any bounded operator with these boundary values is the trace.
* `TauCeti.W1p.w1p0Submodule_le_ker_frontierTrace`: functions in `W^{1,p}_0(Ω)` have zero trace.
* `TauCeti.W1p.frontierTrace_contDiffSMul_ae`: the trace of `ψ u` is `ψ` times the trace of `u`.
* `TauCeti.W1p.mem_w1p0Submodule_iff_frontierTrace_eq_zero` and `TauCeti.W1p.ker_frontierTrace`:
  the kernel of the trace is `W^{1,p}_0(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorems 1 and 2.
* J. Nečas, *Direct Methods in the Theory of Elliptic Equations*, Chapter 2, §4
  (traces on Lipschitz domains by local flattening).
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Gradient Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {a b : ℝ}
  {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Local chart traces on the frontier -/

/-- **A local chart trace on the frontier.** The localized `W^{1,p}` trace through a Lipschitz
boundary chart, read at the tangential coordinate `(e x).snd` of each point `x` of the frontier
patch inside the chart cylinder, and extended by zero to the rest of the frontier. The result is
in `Lᵖ` for normalized Euclidean Hausdorff measure on `frontier Ω`. -/
def W1p.lipschitzChartFrontierTrace (hp : p ≠ (∞ : ℝ≥0∞))
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (ψ : WithLp 2 (ℝ × E) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) :
    W1p volume Ω p →L[ℝ] Lp ℝ p ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))) :=
  (extendByZeroLpₗᵢ ℝ (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E)))
      (measurableSet_frontier_inter_preimage_normalCylinder _ e a b)
      inter_subset_left).toContinuousLinearMap.comp <|
    ((Lp.compMeasurePreservingₗᵢ ℝ (fun x => (e x).snd)
        (e.measurable_snd_apply.measurePreserving _)).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul (by simp)
        h.map_snd_euclideanHausdorffMeasure_frontier_inter_le)).comp
    (W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs)

/-- The frontier version of a local chart trace is the local trace evaluated at the tangential
coordinate on the frontier patch of the chart, and zero elsewhere on the frontier. -/
theorem W1p.lipschitzChartFrontierTrace_ae_eq (hp : p ≠ (∞ : ℝ≥0∞))
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) (u : W1p volume Ω p) :
    W1p.lipschitzChartFrontierTrace hp h ψ hψ hM hψM hgM hs u =ᵐ[
      (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))]
      (frontier (Ω : Set (WithLp 2 (ℝ × E))) ∩ e ⁻¹' normalCylinder a b).indicator
        fun x =>
          W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u (e x).snd := by
  have hpatch := measurableSet_frontier_inter_preimage_normalCylinder (Ω : Set _) e a b
  have hm := e.measurable_snd_apply
  set g := W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u
  set g' := Lp.LpToLpOfMeasureLeSMul (by simp)
    h.map_snd_euclideanHausdorffMeasure_frontier_inter_le g
  -- On the patch, the transported class is represented by `g ∘ (snd ∘ e)`.
  have hcomp : (Lp.compMeasurePreservingₗᵢ ℝ (fun x => (e x).snd) (hm.measurePreserving _) g' :
        WithLp 2 (ℝ × E) → ℝ) =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
          (frontier (Ω : Set (WithLp 2 (ℝ × E))) ∩ e ⁻¹' normalCylinder a b)]
        fun x => g (e x).snd := by
    filter_upwards [Lp.coeFn_compMeasurePreserving g' (hm.measurePreserving _),
      ae_of_ae_map hm.aemeasurable (Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
        h.map_snd_euclideanHausdorffMeasure_frontier_inter_le g)] with x hx hx'
    rw [Lp.compMeasurePreservingₗᵢ_apply]
    exact hx.trans hx'
  refine (coeFn_extendByZeroLpₗᵢ ℝ hpatch inter_subset_left _).trans ?_
  exact ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq hpatch).1 hcomp)

/-- **A local chart trace on the frontier of a function continuous up to the boundary.** If
`u ∈ W^{1,p}(Ω)` agrees almost everywhere with a function `f` continuous on `closure Ω`, then the
frontier version of its local chart trace is `ψ f` almost everywhere on the frontier. -/
theorem W1p.lipschitzChartFrontierTrace_ae_eq_of_continuousOn (hp : p ≠ (∞ : ℝ≥0∞))
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω p}
    {f : WithLp 2 (ℝ × E) → ℝ} (hf : ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))))
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) :
    W1p.lipschitzChartFrontierTrace hp h ψ hψ hM hψM hgM hs u =ᵐ[
      (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))] fun x => ψ x * f x := by
  have hpatch := measurableSet_frontier_inter_preimage_normalCylinder (Ω : Set _) e a b
  filter_upwards [W1p.lipschitzChartFrontierTrace_ae_eq hp h hψ hM hψM hgM hs u,
    ae_restrict_of_ae ((ae_restrict_iff' hpatch).1
      (W1p.lipschitzChartTrace_comp_snd_ae_of_continuousOn hp h hψ hM hψM hgM
        hs hf hu)),
    ae_restrict_mem isClosed_frontier.measurableSet] with x hx hpx hxF
  rw [hx]
  by_cases hxp : x ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))) ∩ e ⁻¹' normalCylinder a b
  · rw [indicator_of_mem hxp, hpx hxp]
  · -- Off the chart cylinder, the cutoff vanishes.
    have hxs : x ∉ tsupport ψ := fun hxs => hxp ⟨hxF, hs hxs⟩
    rw [indicator_of_notMem hxp, image_eq_zero_of_notMem_tsupport hxs, zero_mul]

/-- **Gluing local chart traces.** If the cutoffs `ψ i` of finitely many Lipschitz boundary
charts sum to one on the frontier, then the sum of the frontier versions of the local traces
of a function continuous up to the boundary is its restriction to the frontier. -/
theorem W1p.sum_lipschitzChartFrontierTrace_ae_eq_of_continuousOn {ι : Type*} [Fintype ι]
    {L : ι → ℝ≥0} {e : ι → WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : ι → E → ℝ}
    {a b : ι → ℝ} {ψ : ι → WithLp 2 (ℝ × E) → ℝ} {M : ι → ℝ} (hp : p ≠ (∞ : ℝ≥0∞))
    (h : ∀ i, (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith (L i) (e i) (φ i) (a i) (b i))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hM : ∀ i, 0 ≤ M i)
    (hψM : ∀ i, ∀ x ∈ Ω, |ψ i x| ≤ M i) (hgM : ∀ i, ∀ x ∈ Ω, ‖∇ (ψ i) x‖ ≤ M i)
    (hs : ∀ i, tsupport (ψ i) ⊆ e i ⁻¹' normalCylinder (a i) (b i))
    (hsum : ∀ x ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))), ∑ i, ψ i x = 1)
    {u : W1p volume Ω p} {f : WithLp 2 (ℝ × E) → ℝ}
    (hf : ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))))
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) :
    (∑ i, W1p.lipschitzChartFrontierTrace hp (h i) (ψ i) (hψ i) (hM i) (hψM i) (hgM i) (hs i)) u
      =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f := by
  rw [sum_apply]
  filter_upwards [Lp.coeFn_finsetSum (μ := (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))) Finset.univ fun i =>
      W1p.lipschitzChartFrontierTrace hp (h i) (ψ i) (hψ i) (hM i) (hψM i) (hgM i) (hs i) u,
    ae_all_iff.2 fun i => W1p.lipschitzChartFrontierTrace_ae_eq_of_continuousOn hp (h i) (hψ i)
      (hM i) (hψM i) (hgM i) (hs i) hf hu,
    ae_restrict_mem isClosed_frontier.measurableSet] with x hx hi hxF
  rw [hx, Finset.sum_apply]
  simp only [hi, ← Finset.sum_mul, hsum x hxF, one_mul]

/-! ### The trace operator -/

/-- **Existence of the trace on a bounded Lipschitz domain.** There is a bounded linear operator
`W^{1,p}(Ω) → Lᵖ(frontier Ω)`, for `p < ∞` and normalized Euclidean Hausdorff measure on the
frontier, sending every function continuous up to the boundary to its restriction to the
frontier. -/
theorem W1p.exists_frontierTrace (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : W1p volume Ω p →L[ℝ] Lp ℝ p ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))),
      ∀ (u : W1p volume Ω p) (f : WithLp 2 (ℝ × E) → ℝ),
        ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))) →
        W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f →
        T u =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
          (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f := by
  obtain ⟨t, e, φ, a, b, ψ₀, ψ, M, hchart, ⟨-, -, hψ₀Ω⟩, hψ, hsum⟩ :=
    hΩ.exists_lipschitzChart_cutoffs hb
  choose hψ hM hψM hgM hs using hψ
  -- The interior cutoff `ψ₀` vanishes on the frontier, so the boundary cutoffs sum to one there.
  have hsumF : ∀ x ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))), ∑ i, ψ i x = 1 := by
    intro x hx
    have hx₀ : ψ₀ x = 0 := image_eq_zero_of_notMem_tsupport fun hxs =>
      (Ω.isOpen.frontier_eq ▸ hx).2 (hψ₀Ω hxs)
    rw [← hsum x (frontier_subset_closure hx), hx₀, zero_add]
  exact ⟨∑ i, W1p.lipschitzChartFrontierTrace hp (hchart i) (ψ i) (hψ i) (hM i)
      (fun x _ => hψM i x) (fun x _ => hgM i x) (hs i),
    fun u f hf hu => W1p.sum_lipschitzChartFrontierTrace_ae_eq_of_continuousOn hp _ _ _ _ _ _
      hsumF hf hu⟩

/-- **The trace operator of a bounded Lipschitz domain**, `W^{1,p}(Ω) → Lᵖ(frontier Ω)` for
`p < ∞` and normalized `dim E`-dimensional Euclidean Hausdorff measure on the frontier. It is
characterized by `TauCeti.W1p.frontierTrace_ae_eq_of_continuousOn` and
`TauCeti.W1p.eq_frontierTrace`: it is the unique bounded linear operator sending every function
continuous up to the boundary to its restriction to the frontier. -/
def W1p.frontierTrace (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    W1p volume Ω p →L[ℝ] Lp ℝ p ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))) :=
  (W1p.exists_frontierTrace hp hΩ hb).choose

/-- **The trace of a function continuous up to the boundary is its boundary restriction.** If
`u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function `f` continuous on `closure Ω`, then
the trace of `u` is `f` almost everywhere on the frontier for surface measure. -/
theorem W1p.frontierTrace_ae_eq_of_continuousOn (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω p}
    {f : WithLp 2 (ℝ × E) → ℝ} (hf : ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))))
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) :
    W1p.frontierTrace hp hΩ hb u =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f :=
  (W1p.exists_frontierTrace hp hΩ hb).choose_spec u f hf hu

/-- **Uniqueness of the trace.** A bounded linear operator `W^{1,p}(Ω) → Lᵖ(frontier Ω)` that sends
the restriction to `Ω` of every test function on the whole space to its restriction to the
frontier is the trace operator. -/
theorem W1p.eq_frontierTrace (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (T : W1p volume Ω p →L[ℝ] Lp ℝ p ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))))
    (hT : ∀ φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ),
      T (W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ)) =ᵐ[
        (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
          (frontier (Ω : Set (WithLp 2 (ℝ × E))))] φ) :
    T = W1p.frontierTrace hp hΩ hb := by
  refine DFunLike.coe_injective <|
    (W1p.denseRange_restrictL_ofTestFunctionₗ_top hp hΩ hb).equalizer
      T.continuous (W1p.frontierTrace hp hΩ hb).continuous (funext fun φ => ?_)
  refine Lp.ext ((hT φ).trans (W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb
    φ.continuous.continuousOn ?_).symm)
  exact (W1p.value_restrictL_ae (le_top : Ω ≤ ⊤) _).trans
    (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 le_top)
      (W1p.value_ofTestFunctionₗ_ae φ))

/-- **Functions in `W^{1,p}_0(Ω)` have zero trace.** -/
theorem W1p.w1p0Submodule_le_ker_frontierTrace (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    (w1p0Submodule volume Ω p : Submodule ℝ (W1p volume Ω p)) ≤
      LinearMap.ker (W1p.frontierTrace hp hΩ hb).toLinearMap := by
  -- The kernel is closed, so it suffices to treat test functions supported in `Ω`.
  intro u hu
  have hu' : u ∈ closure (range (W1p.ofTestFunctionₗ volume Ω p)) := by
    rw [← coe_w1p0Submodule]
    exact hu
  refine closure_minimal ?_ (W1p.frontierTrace hp hΩ hb).isClosed_ker hu'
  rintro _ ⟨φ, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine Lp.ext ((W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb φ.continuous.continuousOn
    (W1p.value_ofTestFunctionₗ_ae φ)).trans ?_)
  -- A test function supported in the open set `Ω` vanishes on its frontier.
  filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet,
    (Lp.coeFn_zero ℝ p _).symm] with x hxF hx0
  rw [← hx0]
  exact image_eq_zero_of_notMem_tsupport fun hxs =>
    (Ω.isOpen.frontier_eq ▸ hxF).2 (φ.tsupport_subset hxs)

/-! ### Localization and the kernel of the trace -/

/-- **The trace commutes with smooth bounded multiplication.** On a bounded Lipschitz domain, for
`1 ≤ p < ∞`, the trace of `ψ u` is `ψ` times the trace of `u`, for every smooth `ψ` bounded
together with its gradient on `Ω`. -/
theorem W1p.frontierTrace_contDiffSMul_ae (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M) (u : W1p volume Ω p) :
    W1p.frontierTrace hp hΩ hb (W1p.contDiffSMul ψ hψ hM hψM hgM u) =ᵐ[
      (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))]
      fun x => ψ x * W1p.frontierTrace hp hΩ hb u x := by
  set σ := (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
    (frontier (Ω : Set (WithLp 2 (ℝ × E))))
  -- The frontier lies in the closure of `Ω`, where `ψ` is still bounded by `M`.
  have hB : MemLp ψ ∞ σ := memLp_top_of_bound hψ.continuous.aestronglyMeasurable M <|
    (ae_restrict_mem isClosed_frontier.measurableSet).mono fun x hx => by
      rw [Real.norm_eq_abs]
      exact closure_minimal (t := {x | |ψ x| ≤ M}) hψM
        (isClosed_le (continuous_abs.comp hψ.continuous) continuous_const)
        (frontier_subset_closure hx)
  let T : Lp ℝ p σ →L[ℝ] Lp ℝ p σ :=
    (ContinuousLinearMap.lsmul ℝ ℝ).holderL σ ∞ p p (hB.toLp ψ)
  have hT (f : Lp ℝ p σ) : T f =ᵐ[σ] fun x => ψ x * f x := by
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder (r := p) (hB.toLp ψ) f,
      hB.coeFn_toLp] with x hx hψx
    simpa only [T, ContinuousLinearMap.holderL_apply_apply, hψx,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hx
  -- Both sides are continuous in `u`, so it suffices to check restrictions of test functions.
  have heq : W1p.frontierTrace hp hΩ hb (W1p.contDiffSMul ψ hψ hM hψM hgM u) =
      T (W1p.frontierTrace hp hΩ hb u) := by
    refine (W1p.denseRange_restrictL_ofTestFunctionₗ_top hp hΩ hb).induction_on u
      (isClosed_eq ?_ ?_) fun φ => ?_
    · simpa only [Function.comp_def, W1p.contDiffSMulL_apply] using
        (W1p.frontierTrace hp hΩ hb).continuous.comp
          (W1p.contDiffSMulL ψ hψ hM hψM hgM).continuous
    · exact T.continuous.comp (W1p.frontierTrace hp hΩ hb).continuous
    have hφ := (W1p.value_restrictL_ae (le_top : Ω ≤ ⊤) _).trans
      (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 le_top)
        (W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := p) φ))
    have hψφ : W1p.value (W1p.contDiffSMul ψ hψ hM hψM hgM
        (W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ))) =ᵐ[
          volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] fun x => ψ x * φ x := by
      filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM hgM
        (W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ)), hφ] with x hx hφx
      rw [hx, hφx, smul_eq_mul]
    apply Lp.ext
    filter_upwards [W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb
        (hψ.continuous.mul φ.continuous).continuousOn hψφ,
      hT (W1p.frontierTrace hp hΩ hb _),
      W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb φ.continuous.continuousOn hφ]
      with x h₁ h₂ h₃
    rw [h₁, h₂, h₃, Pi.mul_apply]
  rw [heq]
  exact hT _

/-- **A local chart trace on the frontier is the trace of the cutoff product.** On a bounded
Lipschitz domain, for `1 ≤ p < ∞`, the frontier version of the local trace through a Lipschitz
boundary chart with cutoff `ψ` is the trace of `ψ u`. -/
theorem W1p.lipschitzChartFrontierTrace_eq_frontierTrace_comp (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {L' : ℝ≥0}
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L' e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) :
    W1p.lipschitzChartFrontierTrace hp h ψ hψ hM hψM hgM hs =
      (W1p.frontierTrace hp hΩ hb).comp (W1p.contDiffSMulL ψ hψ hM hψM hgM) := by
  refine DFunLike.coe_injective <|
    (W1p.denseRange_restrictL_ofTestFunctionₗ_top hp hΩ hb).equalizer
      (W1p.lipschitzChartFrontierTrace hp h ψ hψ hM hψM hgM hs).continuous
      ((W1p.frontierTrace hp hΩ hb).comp (W1p.contDiffSMulL ψ hψ hM hψM hgM)).continuous
      (funext fun χ => ?_)
  have hχ := (W1p.value_restrictL_ae (le_top : Ω ≤ ⊤) _).trans
    (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 le_top)
      (W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := p) χ))
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, W1p.contDiffSMulL_apply]
  apply Lp.ext
  filter_upwards [W1p.lipschitzChartFrontierTrace_ae_eq_of_continuousOn hp h hψ hM hψM hgM hs
      χ.continuous.continuousOn hχ,
    W1p.frontierTrace_contDiffSMul_ae hp hΩ hb hψ hM hψM hgM _,
    W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb χ.continuous.continuousOn hχ]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]

/-- **A local chart trace vanishes off the chart.** On a bounded Lipschitz domain, for
`1 ≤ p < ∞`, the local trace through a Lipschitz boundary chart vanishes almost everywhere at
the tangential parameters whose graph point lies outside the chart cylinder. -/
theorem W1p.lipschitzChartTrace_ae_eq_zero_of_notMem (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {L' : ℝ≥0}
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L' e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) (u : W1p volume Ω p) :
    ∀ᵐ y ∂(volume : Measure E), normalGraphEmbedding φ y ∉ normalCylinder a b →
      W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u y = 0 := by
  set S : Set E := (normalGraphEmbedding φ ⁻¹' normalCylinder a b)ᶜ
  let R := (LpToLpRestrictCLM E ℝ ℝ (volume : Measure E) p S).comp
    (W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs)
  -- Restricted to `S`, the local trace vanishes on restrictions of test functions, hence
  -- everywhere by density.
  have hR : R = 0 := by
    refine DFunLike.coe_injective <|
      (W1p.denseRange_restrictL_ofTestFunctionₗ_top hp hΩ hb).equalizer
        R.continuous continuous_const (funext fun χ => ?_)
    have hχ := (W1p.value_restrictL_ae (le_top : Ω ≤ ⊤) _).trans
      (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 le_top)
        (W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := p) χ))
    refine Lp.ext ?_
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ S (W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs
        (W1p.restrictL (le_top : Ω ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p χ))),
      ae_restrict_of_ae (W1p.lipschitzChartTrace_apply_ae_of_continuousOn hp h hψ hM hψM hgM hs
        χ.continuous.continuousOn hχ),
      ae_restrict_mem (h.measurableSet_normalGraphEmbedding_preimage_normalCylinder.compl),
      Lp.coeFn_zero ℝ p ((volume : Measure E).restrict S)] with y hRy hy hyS h0
    simp only [R, Function.comp_apply, Pi.zero_apply, ContinuousLinearMap.comp_apply,
      zero_apply] at hRy h0 ⊢
    have hψy : ψ (e.symm (normalGraphEmbedding φ y)) = 0 :=
      image_eq_zero_of_notMem_tsupport fun hys => hyS (by simpa using hs hys)
    rw [hRy, hy, h0, hψy, zero_mul]
  have hu : LpToLpRestrictCLM E ℝ ℝ (volume : Measure E) p S
      (W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u) = 0 := by
    simpa [R] using DFunLike.congr_fun hR u
  have h0 : W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u =ᵐ[(volume : Measure E).restrict S]
      (0 : E → ℝ) := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ S (W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u),
      Lp.coeFn_zero ℝ p ((volume : Measure E).restrict S)] with y hy h0
    rw [← hy, hu, h0]
  exact (ae_restrict_iff' h.measurableSet_normalGraphEmbedding_preimage_normalCylinder.compl).1 h0

/-- **Zero trace gives zero local chart traces.** On a bounded Lipschitz domain, for
`1 ≤ p < ∞`, if the trace of `u ∈ W^{1,p}(Ω)` vanishes, then so does its local trace through
every Lipschitz boundary chart. -/
theorem W1p.lipschitzChartTrace_eq_zero_of_frontierTrace_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {L' : ℝ≥0}
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L' e φ a b)
    (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder a b) {u : W1p volume Ω p}
    (hu : W1p.frontierTrace hp hΩ hb u = 0) :
    W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u = 0 := by
  set g := W1p.lipschitzChartTrace hp h ψ hψ hM hψM hgM hs u
  -- The frontier version of the local trace is the trace of `ψ u`, which is `ψ` times zero.
  have hF : ∀ᵐ x ∂(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      x ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))) ∩ e ⁻¹' normalCylinder a b → g (e x).snd = 0 := by
    have h₁ := W1p.lipschitzChartFrontierTrace_ae_eq hp h hψ hM hψM hgM hs u
    rw [W1p.lipschitzChartFrontierTrace_eq_frontierTrace_comp hp hΩ hb,
      ContinuousLinearMap.comp_apply, W1p.contDiffSMulL_apply] at h₁
    have h₂ := (h₁.symm.trans (W1p.frontierTrace_contDiffSMul_ae hp hΩ hb hψ hM hψM hgM u))
    rw [hu] at h₂
    have h0 := Lp.coeFn_zero ℝ p ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E)))))
    filter_upwards [(ae_restrict_iff' isClosed_frontier.measurableSet).1 h₂,
      (ae_restrict_iff' isClosed_frontier.measurableSet).1 h0] with x hx h0x hxP
    have hgx := hx hxP.1
    rwa [indicator_of_mem hxP, h0x hxP.1, Pi.zero_apply, mul_zero] at hgx
  -- Hence `g` vanishes almost everywhere on the parameters of the frontier patch.
  set bad : Set E := {y | normalGraphEmbedding φ y ∈ normalCylinder a b ∧ g y ≠ 0}
  have hbad : volume bad = 0 := by
    refine (h.euclideanHausdorffMeasure_image_boundaryParametrization_eq_zero_iff bad).1 ?_
    rw [ae_iff] at hF
    refine measure_mono_null ?_ hF
    rintro _ ⟨y, hy, rfl⟩
    simp only [mem_ofPred_eq, not_imp, e.apply_symm_apply, normalGraphEmbedding_snd]
    exact ⟨h.image_boundaryParametrization.subset ⟨y, hy.1, rfl⟩, hy.2⟩
  refine Lp.ext ?_
  filter_upwards [W1p.lipschitzChartTrace_ae_eq_zero_of_notMem hp hΩ hb h hψ hM hψM hgM hs u,
    measure_eq_zero_iff_ae_notMem.1 hbad, Lp.coeFn_zero ℝ p (volume : Measure E)] with y hy hyb h0
  rw [h0]
  by_contra hne
  by_cases hyC : normalGraphEmbedding φ y ∈ normalCylinder a b
  · exact hyb ⟨hyC, hne⟩
  · exact hne (hy hyC)

/-- **The functions of zero trace on a bounded Lipschitz domain are those of `W^{1,p}_0`.** For
`1 ≤ p < ∞`, `u ∈ W^{1,p}(Ω)` lies in `W^{1,p}_0(Ω)` exactly when its trace on the frontier
vanishes. -/
theorem W1p.mem_w1p0Submodule_iff_frontierTrace_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω p) :
    u ∈ w1p0Submodule volume Ω p ↔ W1p.frontierTrace hp hΩ hb u = 0 := by
  refine ⟨fun hu => W1p.w1p0Submodule_le_ker_frontierTrace hp hΩ hb hu, fun hu => ?_⟩
  obtain ⟨t, e, φ, a, b, ψ₀, ψ, M, hchart, ⟨hψ₀, hψ₀c, hψ₀Ω⟩, hψ, hsum⟩ :=
    hΩ.exists_lipschitzChart_cutoffs hb
  choose hψ hM hψM hgM hs using hψ
  exact (W1p.mem_w1p0Submodule_iff_forall_lipschitzChartTrace_eq_zero hp hchart hψ₀ hψ₀c hψ₀Ω hψ hM
    (fun i x _ => hψM i x) (fun i x _ => hgM i x) hs (fun x hx => hsum x (subset_closure hx))
      u).2 fun i => W1p.lipschitzChartTrace_eq_zero_of_frontierTrace_eq_zero hp hΩ hb (hchart i)
        (hψ i) (hM i) _ _ (hs i) hu

/-- **The kernel of the trace on a bounded Lipschitz domain is `W^{1,p}_0`.** For `1 ≤ p < ∞`,
the trace `W^{1,p}(Ω) → Lᵖ(frontier Ω)` vanishes exactly on the closure of the test functions
supported in `Ω`. -/
theorem W1p.ker_frontierTrace (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    LinearMap.ker (W1p.frontierTrace hp hΩ hb).toLinearMap =
      (w1p0Submodule volume Ω p).toSubmodule := by
  ext u
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ClosedSubmodule.mem_toSubmodule_iff,
    W1p.mem_w1p0Submodule_iff_frontierTrace_eq_zero hp hΩ hb]

end TauCeti

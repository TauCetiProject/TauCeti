/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.SurfaceMeasure
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero

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

## Main declarations

* `TauCeti.W1p.lipschitzChartFrontierTrace`: a local chart trace as an `Lᵖ` function on the
  frontier for surface measure.
* `TauCeti.W1p.frontierTrace`: the trace operator of a bounded Lipschitz domain.
* `TauCeti.W1p.frontierTrace_ae_eq_of_continuousOn`: the trace of a function continuous up to
  the boundary is its restriction to the frontier.
* `TauCeti.W1p.eq_frontierTrace`: any bounded operator with these boundary values is the trace.
* `TauCeti.W1p.w1p0Submodule_le_ker_frontierTrace`: functions in `W^{1,p}_0(Ω)` have zero trace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 1.
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

end TauCeti

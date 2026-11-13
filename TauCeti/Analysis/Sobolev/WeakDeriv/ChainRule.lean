/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.UniformConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The weak chain rule for continuous maps

Let `u` be continuous on an open set `Ω` of a finite-dimensional space, with weak derivative `Du`
and values in a Banach space, and let `g` be `C¹` on an open set containing the image of `u`.
Then `g ∘ u` has weak derivative `x ↦ Dg(u x) ∘ Du x` on `Ω`. No integrability exponent enters:
`Du` is only locally integrable, and continuity of `u` makes `Dg ∘ u` locally bounded. The
domain-dependent form `x ↦ g(x, u x)` follows by composing with the graph map `x ↦ (x, u x)`.

Continuity of `u` is a hypothesis. Without it the statement fails in general: in the plane, the
function `u = -log |z|` has the locally integrable weak derivative `-z / |z|²` near `0`, but for
`g = exp (2 ·)` the composition `g ∘ u = |z|⁻²` is not even locally integrable there. Continuity
also matters for the `W^{1,p}` form: for `p = 4/3` the function `u = |z|^{-2/5}` lies in
`W^{1,4/3}` near `0`, but `u²` does not, since its derivative has size `|z|^{-9/5}` and
`(9/5)(4/3) > 2`.

## Proof

On an open set `V` with compact closure in `Ω`, mollify the zero extension of `u` from a slightly
larger open set. The mollifications converge to `u` uniformly on `closure V`
(`ContDiffBump.tendstoUniformlyOn_normed_convolution`), and their derivatives, the mollifications
of `Du`, converge to `Du` in `L¹(V)`. The classical chain rule applies to each mollification.
Since `u '' closure V` is compact, uniform convergence carries `g` and `Dg` along
(`IsCompact.comp_tendstoUniformlyOn`), and the compositions converge in `L¹(V)`
(`TendstoUniformlyOn.tendsto_setLIntegral_enorm_clm_comp_sub`). The weak derivatives pass to that
limit, and locality of weak derivatives returns the statement to `Ω`.

## Main declarations

* `TauCeti.HasWeakFDerivOn.contDiffOn_comp`: the weak chain rule for continuous `u`.
* `TauCeti.HasWeakFDerivOn.contDiff_comp`: the same for globally `C¹` maps `g`.
* `TauCeti.HasWeakFDerivOn.contDiffOn_comp_graph`: the weak chain rule for `x ↦ g(x, u x)`.
* `TauCeti.HasWeakFDerivOn.sq`: the check `D(u²) = 2u Du` for continuous real `u`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution ENNReal NNReal Topology

namespace TauCeti

section Core

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F} {g : F → G} {W : Set F}

/-- **Smooth approximation on a relatively compact subset.** On an open set `V` with compact
closure in `Ω`, a continuous `u` with weak derivative `Du` is the uniform limit on `closure V` of
continuous maps `uₙ` that are differentiable on `V` with continuous derivatives `Duₙ` converging
to `Du` in `L¹(V)`. The maps are mollifications of the zero extension of `u` from a neighbourhood
of `closure V`. -/
private theorem exists_smooth_approx_of_isCompact_closure (hu : HasWeakFDerivOn μ Ω u Du)
    (huc : ContinuousOn u Ω) (V : Opens E) (hVc : IsCompact (closure (V : Set E)))
    (hVΩ : closure (V : Set E) ⊆ Ω) :
    ∃ (un : ℕ → E → F) (Dn : ℕ → E → E →L[ℝ] F), (∀ n, Continuous (un n)) ∧
      (∀ n, Continuous (Dn n)) ∧ (∀ n, ∀ x ∈ (V : Set E), HasFDerivAt (un n) (Dn n x) x) ∧
      TendstoUniformlyOn un u atTop (closure (V : Set E)) ∧
      Tendsto (fun n => ∫⁻ x in V, ‖Dn n x - Du x‖ₑ ∂μ) atTop (𝓝 0) := by
  have : CompleteSpace F := hu.completeSpace
  set S := closure (V : Set E)
  -- A compact neighbourhood of `S` inside `Ω`, and an open set `Ω'` between them.
  obtain ⟨δ, hδ, hδΩ⟩ := hVc.exists_cthickening_subset_open Ω.isOpen hVΩ
  have hK : IsCompact (cthickening δ S) := hVc.cthickening
  let Ω' : Opens E := ⟨thickening δ S, isOpen_thickening⟩
  have hΩ'K : (Ω' : Set E) ⊆ cthickening δ S := thickening_subset_cthickening δ S
  have hSΩ' : S ⊆ Ω' := self_subset_thickening hδ S
  have huK : IntegrableOn u (cthickening δ S) μ :=
    hu.locallyIntegrableOn.integrableOn_compact_subset hδΩ hK
  have hDuK : IntegrableOn Du (cthickening δ S) μ :=
    hu.locallyIntegrableOn_deriv.integrableOn_compact_subset hδΩ hK
  -- Mollifiers of outer radius `δ / 2 / (n + 1) < δ`.
  let φ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking (half_pos hδ)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking (half_pos hδ)
  have hball (n : ℕ) (x : E) (hx : x ∈ S) : closedBall x (φ n).rOut ⊆ Ω' := fun y hy => by
    have hr : (φ n).rOut < δ := by
      simp only [φ, ContDiffBump.rOut_shrinking]
      exact (div_le_self (half_pos hδ).le (by linarith [n.cast_nonneg' (α := ℝ)])).trans_lt
        (half_lt_self hδ)
    exact mem_thickening_iff.2 ⟨x, hx, (mem_closedBall.1 hy).trans_lt hr⟩
  set uext := (Ω' : Set E).indicator u
  set Dext := (Ω' : Set E).indicator Du
  have huext : Integrable uext μ :=
    (huK.mono_set hΩ'K).integrable_indicator Ω'.isOpen.measurableSet
  have hDext : Integrable Dext μ :=
    (hDuK.mono_set hΩ'K).integrable_indicator Ω'.isOpen.measurableSet
  refine ⟨fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] uext,
    fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Dext,
    fun n => (φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed
      huext.locallyIntegrable,
    fun n => (φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed
      hDext.locallyIntegrable, fun n x hx => ?_, ?_, ?_⟩
  · -- The classical derivative of a mollification is the mollified weak derivative.
    have h := (hu.mono (hΩ'K.trans hδΩ)).hasFDerivAt_indicator_convolution_normed (p := 1)
      (q := 1) (memLp_one_iff_integrable.2 (huK.mono_set hΩ'K))
      (memLp_one_iff_integrable.2 (hDuK.mono_set hΩ'K)) le_rfl le_rfl (φ n) x
      (hball n x (subset_closure hx))
    simpa only [convolution_flip] using h
  · -- Uniform convergence on `S`, from uniform continuity of `u` on `cthickening δ S`.
    have hUC : UniformContinuousOn uext Ω' := by
      refine Metric.uniformContinuousOn_iff.2 fun ε hε =>
        (Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous
          (huc.mono hδΩ)) ε hε).imp fun η ⟨hη, h⟩ => ⟨hη, fun x hx y hy hxy => ?_⟩
      simpa only [uext, indicator_of_mem hx, indicator_of_mem hy] using
        h x (hΩ'K hx) y (hΩ'K hy) hxy
    refine (ContDiffBump.tendstoUniformlyOn_normed_convolution
      hφ hδ hUC huext.aestronglyMeasurable).congr_right
      fun x hx => ?_
    simp only [uext, indicator_of_mem (hSΩ' hx)]
  · -- `L¹(V)` convergence of the derivatives.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_setLIntegral_enorm_normed_convolution_sub hφ
        hDext.locallyIntegrable hVc) (fun _ => zero_le) fun n => ?_
    calc ∫⁻ x in V, ‖((φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Dext) x - Du x‖ₑ ∂μ
        = ∫⁻ x in V, ‖((φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Dext) x - Dext x‖ₑ ∂μ :=
          setLIntegral_congr_fun V.isOpen.measurableSet fun x hx => by
            simp only [Dext, indicator_of_mem (hSΩ' (subset_closure hx))]
      _ ≤ _ := lintegral_mono_set subset_closure

variable [CompleteSpace G]

/-- The classical chain rule for a continuous map `v` that is differentiable on `V` with
continuous derivative and values in `W`, read as a weak derivative on `V`. -/
private theorem hasWeakFDerivOn_comp_of_hasFDerivAt {V : Opens E} {v : E → F}
    {Dv : E → E →L[ℝ] F} (hv : Continuous v) (hDv : Continuous Dv)
    (hderiv : ∀ x ∈ (V : Set E), HasFDerivAt v (Dv x) x) (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (hmem : ∀ x ∈ (V : Set E), v x ∈ W) :
    HasWeakFDerivOn μ V (fun x => g (v x)) fun x => (fderiv ℝ g (v x)).comp (Dv x) := by
  have hcont : ContinuousOn (fun x => (fderiv ℝ g (v x)).comp (Dv x)) V :=
    ((hg.continuousOn_fderiv_of_isOpen hW le_rfl).comp hv.continuousOn hmem).clm_comp
      hDv.continuousOn
  refine hasWeakFDerivOn_iff.2 fun w => hasWeakLineDerivOn_of_hasLineDerivAt
    ((hg.continuousOn.comp hv.continuousOn hmem).locallyIntegrableOn V.isOpen.measurableSet)
    ((hcont.clm_apply continuousOn_const).locallyIntegrableOn V.isOpen.measurableSet)
    fun x hx => ?_
  exact ((((hg.differentiableOn one_ne_zero _ (hmem x hx)).differentiableAt
    (hW.mem_nhds (hmem x hx))).hasFDerivAt).comp x (hderiv x hx)).hasLineDerivAt w

/-- The weak chain rule on an open set with compact closure inside the domain. -/
private theorem hasWeakFDerivOn_comp_of_isCompact_closure
    (hu : HasWeakFDerivOn μ Ω u Du) (huc : ContinuousOn u Ω) (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (huW : MapsTo u Ω W) (V : Opens E)
    (hVc : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Ω) :
    HasWeakFDerivOn μ V (fun x => g (u x)) fun x => (fderiv ℝ g (u x)).comp (Du x) := by
  set S := closure (V : Set E)
  have hVS : (V : Set E) ⊆ S := subset_closure
  obtain ⟨un, Dn, hun, hDn, hderiv, huu, hDD⟩ :=
    exists_smooth_approx_of_isCompact_closure hu huc V hVc hVΩ
  have hDuS : IntegrableOn Du S μ :=
    hu.locallyIntegrableOn_deriv.integrableOn_compact_subset hVΩ hVc
  have hgc : ContinuousOn g W := hg.continuousOn
  have hDgc : ContinuousOn (fderiv ℝ g) W := hg.continuousOn_fderiv_of_isOpen hW le_rfl
  have huSW : u '' S ⊆ W := (huW.mono_left hVΩ).image_subset
  have huS : IsCompact (u '' S) := hVc.image_of_continuousOn (huc.mono hVΩ)
  have hDguS : ContinuousOn (fun x => fderiv ℝ g (u x)) S := hDgc.comp (huc.mono hVΩ)
    (huW.mono_left hVΩ)
  -- Eventually the approximations take values in `W` on `V`.
  obtain ⟨η, hη, hηW⟩ := huS.exists_thickening_subset_open hW huSW
  obtain ⟨N, hN⟩ := eventually_atTop.1 <| (Metric.tendstoUniformlyOn_iff.1 huu η hη).mono
    fun n hn x (hx : x ∈ (V : Set E)) => hηW <| mem_thickening_iff.2
      ⟨u x, mem_image_of_mem u (hVS hx), by rw [dist_comm]; exact hn x (hVS hx)⟩
  have happrox (n : ℕ) := hasWeakFDerivOn_comp_of_hasFDerivAt (μ := μ) (hun (n + N))
    (hDn (n + N)) (hderiv (n + N)) hW hg (hN (n + N) (Nat.le_add_left N n))
  -- `Dg ∘ u` is bounded on `S`, and `Dg(u) ∘ Du` is integrable there.
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn hDguS
  have hWint : IntegrableOn (fun x => (fderiv ℝ g (u x)).comp (Du x)) V μ :=
    IntegrableOn.mono_set (memLp_one_iff_integrable.1 <| (memLp_one_iff_integrable.2 hDuS)
      |>.clm_comp_of_continuousOn hDguS hVc isClosed_closure.measurableSet subset_rfl) hVS
  have hgAt : ∀ y ∈ u '' S, ContinuousAt g y := fun y hy =>
    hgc.continuousAt (hW.mem_nhds (huSW hy))
  have hDgAt : ∀ y ∈ u '' S, ContinuousAt (fderiv ℝ g) y := fun y hy =>
    hDgc.continuousAt (hW.mem_nhds (huSW hy))
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    ((hgc.comp (huc.mono (hVS.trans hVΩ)) (huW.mono_left (hVS.trans hVΩ))).locallyIntegrableOn
      V.isOpen.measurableSet)
    (fun v => IntegrableOn.locallyIntegrableOn
      ((ContinuousLinearMap.apply ℝ G v).integrable_comp hWint))
    happrox ?_ ?_
  · refine (tendsto_add_atTop_iff_nat
      (f := fun n => ∫⁻ x in V, ‖g (un n x) - g (u x)‖ₑ ∂μ) N).2 ?_
    exact ((huS.comp_tendstoUniformlyOn hgAt huu).mono hVS).tendsto_setLIntegral_enorm_sub
      ((measure_mono hVS).trans_lt hVc.measure_lt_top).ne
  · refine (tendsto_add_atTop_iff_nat (f := fun n => ∫⁻ x in V,
      ‖(fderiv ℝ g (un n x)).comp (Dn n x) - (fderiv ℝ g (u x)).comp (Du x)‖ₑ ∂μ) N).2 ?_
    have hDgu := (huS.comp_tendstoUniformlyOn hDgAt huu).mono hVS
    refine hDgu.tendsto_setLIntegral_enorm_clm_comp_sub V.isOpen.measurableSet (C := C.toNNReal)
      (fun x hx => ?_) (fun n => (hDn n).aestronglyMeasurable)
      (hDuS.mono_set hVS).aestronglyMeasurable hDD (hDuS.mono_set hVS).hasFiniteIntegral.ne
    rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact (hC x (hVS hx)).trans (Real.le_coe_toNNReal C)

/-- **The weak chain rule for continuous maps.** If `u` is continuous on `Ω` with weak derivative
`Du`, and `g` is `C¹` on an open set `W` containing `u '' Ω`, then `g ∘ u` has weak derivative
`x ↦ Dg(u x) ∘ Du x` on `Ω`. No integrability exponent enters: `Du` is only locally integrable.
Continuity of `u` cannot simply be dropped, since `g ∘ u` and `Dg(u) ∘ Du` need not be locally
integrable otherwise. -/
theorem HasWeakFDerivOn.contDiffOn_comp (hu : HasWeakFDerivOn μ Ω u Du)
    (huc : ContinuousOn u Ω) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (huW : MapsTo u Ω W) :
    HasWeakFDerivOn μ Ω (fun x => g (u x)) fun x => (fderiv ℝ g (u x)).comp (Du x) :=
  hasWeakFDerivOn_iff_forall_isCompact_closure.2 fun V hVc hVΩ =>
    hasWeakFDerivOn_comp_of_isCompact_closure hu huc hW hg huW V hVc hVΩ

/-- **The weak chain rule for continuous maps and globally `C¹` functions.** -/
theorem HasWeakFDerivOn.contDiff_comp (hu : HasWeakFDerivOn μ Ω u Du)
    (huc : ContinuousOn u Ω) (hg : ContDiff ℝ 1 g) :
    HasWeakFDerivOn μ Ω (fun x => g (u x)) fun x => (fderiv ℝ g (u x)).comp (Du x) :=
  hu.contDiffOn_comp huc isOpen_univ hg.contDiffOn (mapsTo_univ _ _)

end Core

section Pair

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] [CompleteSpace H]

/-- **The weak chain rule with domain dependence.** If `u` is continuous on `Ω` with weak
derivative `Du`, and `g` is `C¹` on an open set `W` containing the graph of `u` over `Ω`, then
`x ↦ g (x, u x)` has weak derivative `x ↦ Dg(x, u x) ∘ (id, Du x)` on `Ω`. -/
theorem HasWeakFDerivOn.contDiffOn_comp_graph {u : E → F}
    {Du : E → E →L[ℝ] F} {g : E × F → H} {W : Set (E × F)} (hu : HasWeakFDerivOn μ Ω u Du)
    (huc : ContinuousOn u Ω) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (huW : ∀ x ∈ (Ω : Set E), (x, u x) ∈ W) :
    HasWeakFDerivOn μ Ω (fun x => g (x, u x))
      fun x => (fderiv ℝ g (x, u x)).comp ((ContinuousLinearMap.id ℝ E).prod (Du x)) := by
  have : CompleteSpace F := hu.completeSpace
  have hid : HasWeakFDerivOn μ Ω (fun x => x) fun _ => ContinuousLinearMap.id ℝ E := by
    have hD : fderiv ℝ (fun x : E => x) = fun _ => ContinuousLinearMap.id ℝ E :=
      funext fun _ => fderiv_id
    have h := hasWeakFDerivOn_of_differentiableOn (μ := μ) (Ω := Ω) (u := fun x : E => x)
      (by rw [hD]; exact locallyIntegrableOn_const _) fun x _ => differentiableAt_id
    rwa [hD] at h
  exact (hid.prodMk hu).contDiffOn_comp (continuousOn_id.prodMk huc) hW hg huW

end Pair

/-! ### Check: the square of a continuous function -/

section Square

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ} {Du : E → E →L[ℝ] ℝ}

/-- **The square of a continuous weakly differentiable function.** For continuous `u` with weak
derivative `Du`, the square `u²` has weak derivative `2u Du`. Continuity makes `2u Du` locally
integrable; for `u = |z|^{-2/5}` and `p = 4/3` the analogous statement in `W^{1,p}` fails. -/
theorem HasWeakFDerivOn.sq (hu : HasWeakFDerivOn μ Ω u Du) (huc : ContinuousOn u Ω) :
    HasWeakFDerivOn μ Ω (fun x => u x ^ 2) fun x => (2 * u x) • Du x := by
  have h := hu.contDiff_comp huc (g := fun t : ℝ => t ^ 2) (contDiff_id.pow 2)
  convert h using 2 with x
  ext v
  simp [mul_comm, mul_left_comm]

end Square

end TauCeti

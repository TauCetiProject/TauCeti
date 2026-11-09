/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# The chain rule for continuous local Sobolev maps

Let `u` be continuous on an open set `Ω` of a finite-dimensional space, with weak derivative `Du`,
and let `g` be `C¹` on an open set containing the image of `u`. Then `g ∘ u` has weak derivative
`z ↦ Dg(u z) ∘ Du z` on `Ω`. In particular, a continuous member of `W^{1,p}_loc` composes with a
`C¹` map to give a member of `W^{1,p}_loc`, with the local bound
`‖D(g ∘ u)‖_{Lᵖ(K)} ≤ (sup_{u(K)} ‖Dg‖) ‖Du‖_{Lᵖ(K)}` on compact sets `K`. The domain-dependent
form `z ↦ G(z, u z)` follows by composing with the graph map `z ↦ (z, u z)`.

Continuity of `u` is a hypothesis here. For `p > 2` it is automatic after changing `u` on a null
set, by Morrey's embedding; without continuity, and below that exponent, the statement fails:
for `p = 4/3` the function `u = |z|^{-2/5}` lies in `W^{1,4/3}` near `0`, but `u²` does not,
since its derivative has size `|z|^{-9/5}` and `(9/5)(4/3) > 2`.

## Proof

On an open set `V` with compact closure in `Ω`, mollify the zero extension of `u` from a slightly
larger open set. The mollifications converge to `u` uniformly on `V`, by uniform continuity of `u`
on a compact neighbourhood of `closure V`, and their derivatives, the mollifications of `Du`,
converge to `Du` in `L¹(V)`. The classical chain rule applies to each mollification. Uniform
convergence carries `g` and `Dg` along, and the weak derivatives pass to the `L¹(V)` limit.
Locality of weak derivatives returns the statement to `Ω`.

## Main declarations

* `TauCeti.HasWeakFDerivOn.comp_contDiffOn`: the weak chain rule for continuous `u`.
* `TauCeti.HasWeakFDerivOn.prodMk`: the weak derivative of a pair.
* `TauCeti.HasWeakFDerivOn.comp_graph_contDiffOn`: the weak chain rule for `z ↦ G(z, u z)`.
* `TauCeti.eLpNorm_fderiv_comp_le`: the local `Lᵖ` bound for the chain-rule derivative.
* `TauCeti.MemWkpLoc.comp_contDiffOn`: continuous `W^{1,p}_loc` maps compose with `C¹` maps.
* `TauCeti.MemWkpLoc.prodMk`: pairs of local Sobolev maps, at every order.
* `TauCeti.MemWkpLoc.comp_graph_contDiffOn`: the domain-dependent composition `z ↦ G(z, u z)`.
* `TauCeti.HasWeakFDerivOn.sq`: the check `D(u²) = 2u Du` for continuous real `u`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution ENNReal NNReal Topology

section Core

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F} {g : F → G} {W : Set F}

/-- Uniform convergence on `s` makes the supremum over `s` of the pointwise distance tend to
zero. -/
private theorem tendsto_iSup_enorm_sub_of_tendstoUniformlyOn {ι α X : Type*}
    [NormedAddCommGroup X] {l : Filter ι} {f : ι → α → X} {f₀ : α → X} {s : Set α}
    (h : TendstoUniformlyOn f f₀ l s) :
    Tendsto (fun i => ⨆ x ∈ s, ‖f i x - f₀ x‖ₑ) l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  filter_upwards [EMetric.tendstoUniformlyOn_iff.1 h ε hε] with i hi
  refine iSup₂_le fun x hx => ?_
  rw [← edist_eq_enorm_sub, edist_comm]
  exact (hi x hx).le

/-- The extended operator norm is submultiplicative under composition. -/
private theorem enorm_comp_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : F →L[ℝ] G) (B : H →L[ℝ] F) : ‖A.comp B‖ₑ ≤ ‖A‖ₑ * ‖B‖ₑ := by
  simpa only [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using
    A.opNNNorm_comp_le B

omit [μ.IsAddHaarMeasure] in
/-- The chain-rule derivative is almost everywhere strongly measurable on a measurable set where
`Dg ∘ u` is continuous. -/
private theorem aestronglyMeasurable_fderiv_comp {K : Set E} (hK : MeasurableSet K)
    (hgu : ContinuousOn (fun x => fderiv ℝ g (u x)) K)
    (hDu : AEStronglyMeasurable Du (μ.restrict K)) :
    AEStronglyMeasurable (fun x => (fderiv ℝ g (u x)).comp (Du x)) (μ.restrict K) :=
  (ContinuousLinearMap.compL ℝ E F G).continuous₂.comp_aestronglyMeasurable₂
    (hgu.aestronglyMeasurable hK) hDu

omit [μ.IsAddHaarMeasure] in
/-- **The local bound for the chain rule.** On a measurable set `K` where `Dg ∘ u` is continuous
and bounded by `C`, the `Lᵖ(K)` norm of `Dg(u) ∘ Du` is at most `C` times that of `Du`, for every
exponent. -/
theorem eLpNorm_fderiv_comp_le {K : Set E} (hK : MeasurableSet K)
    (hgu : ContinuousOn (fun x => fderiv ℝ g (u x)) K)
    (hDu : AEStronglyMeasurable Du (μ.restrict K)) {C : ℝ≥0}
    (hC : ∀ x ∈ K, ‖fderiv ℝ g (u x)‖₊ ≤ C) (p : ℝ≥0∞) :
    eLpNorm (fun x => (fderiv ℝ g (u x)).comp (Du x)) p (μ.restrict K) ≤
      C * eLpNorm Du p (μ.restrict K) := by
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (aestronglyMeasurable_fderiv_comp hK hgu hDu) ?_ p
  filter_upwards [ae_restrict_mem hK] with x hx
  exact (ContinuousLinearMap.opNNNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hC x hx) zero_le)

variable [FiniteDimensional ℝ F] [CompleteSpace G]

/-- The weak chain rule on an open set with compact closure inside the domain. -/
private theorem hasWeakFDerivOn_comp_of_isCompact_closure
    (hu : HasWeakFDerivOn μ Ω u Du) (huc : ContinuousOn u Ω) (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (huW : MapsTo u Ω W) (V : Opens E)
    (hVc : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Ω) :
    HasWeakFDerivOn μ V (fun x => g (u x)) fun x => (fderiv ℝ g (u x)).comp (Du x) := by
  have : CompleteSpace F := hu.completeSpace
  set S := closure (V : Set E)
  have hVS : (V : Set E) ⊆ S := subset_closure
  -- A compact neighbourhood `K` of `S` inside `Ω`, and an open set `Ω'` between them.
  obtain ⟨δ, hδ, hδΩ⟩ := hVc.exists_cthickening_subset_open Ω.isOpen hVΩ
  have hK : IsCompact (cthickening δ S) := hVc.cthickening
  let Ω' : Opens E := ⟨thickening δ S, isOpen_thickening⟩
  have hΩ'K : (Ω' : Set E) ⊆ cthickening δ S := thickening_subset_cthickening δ S
  have hΩ'Ω : Ω' ≤ Ω := hΩ'K.trans hδΩ
  have hVΩ' : (V : Set E) ⊆ Ω' := hVS.trans (self_subset_thickening hδ S)
  have huK : IntegrableOn u (cthickening δ S) μ :=
    hu.locallyIntegrableOn.integrableOn_compact_subset hδΩ hK
  have hDuK : IntegrableOn Du (cthickening δ S) μ :=
    hu.locallyIntegrableOn_deriv.integrableOn_compact_subset hδΩ hK
  have hDuV : IntegrableOn Du V μ := hDuK.mono_set (hVΩ'.trans hΩ'K)
  have hμV : μ V ≠ ∞ := (measure_mono hVS).trans_lt hVc.measure_lt_top |>.ne
  -- Mollifiers whose radii shrink to zero and stay below `δ`.
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    { rIn := δ / 2 / (n + 1) / 2
      rOut := δ / 2 / (n + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (δ / 2)
    simpa only [mul_zero, mul_one_div] using this
  have hφδ (n : ℕ) : (φ n).rOut < δ := by
    change δ / 2 / (n + 1) < δ
    calc δ / 2 / (n + 1) ≤ δ / 2 :=
          div_le_self (by positivity) (by linarith [n.cast_nonneg' (α := ℝ)])
      _ < δ := half_lt_self hδ
  have hball (n : ℕ) (x : E) (hx : x ∈ S) : closedBall x (φ n).rOut ⊆ Ω' := fun y hy =>
    mem_thickening_iff.2 ⟨x, hx, (mem_closedBall.1 hy).trans_lt (hφδ n)⟩
  -- The zero extensions from `Ω'` and their mollifications.
  set uext := (Ω' : Set E).indicator u
  set Dext := (Ω' : Set E).indicator Du
  have huext : Integrable uext μ :=
    (huK.mono_set hΩ'K).integrable_indicator Ω'.isOpen.measurableSet
  have hDext : Integrable Dext μ :=
    (hDuK.mono_set hΩ'K).integrable_indicator Ω'.isOpen.measurableSet
  let un : ℕ → E → F := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] uext
  let Dn : ℕ → E → E →L[ℝ] F := fun n => (φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Dext
  have hun_cont (n : ℕ) : Continuous (un n) :=
    (φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed
      huext.locallyIntegrable
  have hDn_cont (n : ℕ) : Continuous (Dn n) :=
    (φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed
      hDext.locallyIntegrable
  have hderiv (n : ℕ) (x : E) (hx : x ∈ (V : Set E)) : HasFDerivAt (un n) (Dn n x) x := by
    have h := (hu.mono hΩ'Ω).hasFDerivAt_indicator_convolution_normed (p := 1) (q := 1)
      (memLp_one_iff_integrable.2 (huK.mono_set hΩ'K))
      (memLp_one_iff_integrable.2 (hDuK.mono_set hΩ'K)) le_rfl le_rfl (φ n) x
      (hball n x (hVS hx))
    simpa only [convolution_flip] using h
  -- The mollifications converge to `u` uniformly on `V`.
  have huu : TendstoUniformlyOn un u atTop V := by
    have hUC : UniformContinuousOn u (cthickening δ S) :=
      hK.uniformContinuousOn_of_continuous (huc.mono hδΩ)
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuousOn_iff.1 hUC (ε / 2) (by positivity)
    filter_upwards [hφ.eventually (gt_mem_nhds hη)] with n hn x hx
    have hx' : x ∈ (Ω' : Set E) := hVΩ' hx
    rw [dist_comm]
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    have h := (φ n).dist_normed_convolution_le (μ := μ) (x₀ := x) (ε := ε / 2)
      huext.aestronglyMeasurable fun y hy => by
        have hy' : y ∈ (Ω' : Set E) := hball n x (hVS hx) (ball_subset_closedBall hy)
        simp only [uext, indicator_of_mem hy', indicator_of_mem hx']
        exact (hηu y (hΩ'K hy') x (hΩ'K hx') ((mem_ball.1 hy).trans hn)).le
    simpa only [uext, indicator_of_mem hx'] using h
  -- The derivatives converge to `Du` in `L¹(V)`.
  have hDD : Tendsto (fun n => ∫⁻ x in V, ‖Dn n x - Du x‖ₑ ∂μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_setLIntegral_enorm_normed_convolution_sub hφ hDext.locallyIntegrable hVc)
      (fun _ => zero_le) fun n => ?_
    calc ∫⁻ x in V, ‖Dn n x - Du x‖ₑ ∂μ = ∫⁻ x in V, ‖Dn n x - Dext x‖ₑ ∂μ :=
          setLIntegral_congr_fun V.isOpen.measurableSet fun x hx => by
            simp only [Dext, indicator_of_mem (hVΩ' hx)]
      _ ≤ ∫⁻ x in S, ‖Dn n x - Dext x‖ₑ ∂μ := lintegral_mono_set hVS
  -- A compact neighbourhood `T` of `u '' S` inside `W`, on which `g` and `Dg` are uniformly
  -- continuous, and which eventually contains the values of the mollifications on `V`.
  have huS : IsCompact (u '' S) := hVc.image_of_continuousOn (huc.mono hVΩ)
  obtain ⟨η, hη, hηW⟩ := huS.exists_cthickening_subset_open hW (huW.mono_left hVΩ).image_subset
  have hT : IsCompact (cthickening η (u '' S)) := huS.cthickening
  have hgc : ContinuousOn g W := hg.continuousOn
  have hDgc : ContinuousOn (fderiv ℝ g) W := hg.continuousOn_fderiv_of_isOpen hW le_rfl
  have huT : ∀ x ∈ (V : Set E), u x ∈ cthickening η (u '' S) := fun x hx =>
    self_subset_cthickening _ (mem_image_of_mem u (hVS hx))
  have hunT : ∀ᶠ n in atTop, ∀ x ∈ (V : Set E), un n x ∈ cthickening η (u '' S) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 huu η hη] with n hn x hx
    exact mem_cthickening_of_dist_le _ (u x) _ _ (mem_image_of_mem u (hVS hx))
      (by rw [dist_comm]; exact (hn x hx).le)
  have hgu : TendstoUniformlyOn (fun n x => g (un n x)) (fun x => g (u x)) atTop V :=
    (hT.uniformContinuousOn_of_continuous (hgc.mono hηW)).comp_tendstoUniformlyOn_eventually
      hunT huT huu
  have hDgu : TendstoUniformlyOn (fun n x => fderiv ℝ g (un n x)) (fun x => fderiv ℝ g (u x))
      atTop V :=
    (hT.uniformContinuousOn_of_continuous (hDgc.mono hηW)).comp_tendstoUniformlyOn_eventually
      hunT huT huu
  obtain ⟨N, hN⟩ := eventually_atTop.1 hunT
  -- `Dg ∘ u` is continuous and bounded on `S`.
  have hDguS : ContinuousOn (fun x => fderiv ℝ g (u x)) S :=
    hDgc.comp (huc.mono hVΩ) ((huW.mono_left hVΩ))
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn hDguS
  have hCe : ∀ x ∈ (V : Set E), ‖fderiv ℝ g (u x)‖ₑ ≤ ENNReal.ofReal C := fun x hx => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC x (hVS hx))
  -- The limit derivative is integrable on `V`.
  have hmeasW : AEStronglyMeasurable (fun x => (fderiv ℝ g (u x)).comp (Du x)) (μ.restrict V) :=
    aestronglyMeasurable_fderiv_comp V.isOpen.measurableSet (hDguS.mono hVS)
      hDuV.aestronglyMeasurable
  have hWint : IntegrableOn (fun x => (fderiv ℝ g (u x)).comp (Du x)) V μ := by
    refine Integrable.mono' (hDuV.norm.const_mul C) hmeasW ?_
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC x (hVS hx)) (norm_nonneg _))
  -- The approximating compositions have the classical chain-rule derivative.
  have happrox (n : ℕ) : HasWeakFDerivOn μ V (fun x => g (un (n + N) x))
      (fun x => (fderiv ℝ g (un (n + N) x)).comp (Dn (n + N) x)) := by
    have hmem : ∀ x ∈ (V : Set E), un (n + N) x ∈ W := fun x hx =>
      hηW (hN (n + N) (Nat.le_add_left N n) x hx)
    have hcont : ContinuousOn (fun x => (fderiv ℝ g (un (n + N) x)).comp (Dn (n + N) x)) V :=
      (hDgc.comp (hun_cont _).continuousOn hmem).clm_comp (hDn_cont _).continuousOn
    refine hasWeakFDerivOn_iff.2 fun v => hasWeakLineDerivOn_of_hasLineDerivAt
      ((hgc.comp (hun_cont _).continuousOn hmem).locallyIntegrableOn V.isOpen.measurableSet)
      ((hcont.clm_apply continuousOn_const).locallyIntegrableOn V.isOpen.measurableSet)
      fun x hx => ?_
    have hgx : HasFDerivAt g (fderiv ℝ g (un (n + N) x)) (un (n + N) x) :=
      ((hg.differentiableOn one_ne_zero _ (hmem x hx)).differentiableAt
        (hW.mem_nhds (hmem x hx))).hasFDerivAt
    exact (hgx.comp x (hderiv _ x hx)).hasLineDerivAt v
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    ((hgc.comp (huc.mono (hVΩ'.trans hΩ'Ω)) (huW.mono_left (hVΩ'.trans hΩ'Ω))).locallyIntegrableOn
      V.isOpen.measurableSet)
    (fun v => IntegrableOn.locallyIntegrableOn
      ((ContinuousLinearMap.apply ℝ G v).integrable_comp hWint))
    happrox ?_ ?_
  · -- The compositions converge uniformly, hence in `L¹(V)`.
    refine (tendsto_add_atTop_iff_nat
      (f := fun n => ∫⁻ x in V, ‖g (un n x) - g (u x)‖ₑ ∂μ) N).2 ?_
    have h0 := ENNReal.Tendsto.mul_const (b := μ V)
      (tendsto_iSup_enorm_sub_of_tendstoUniformlyOn hgu) (Or.inr hμV)
    rw [zero_mul] at h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun _ => zero_le) fun n => ?_
    calc ∫⁻ x in V, ‖g (un n x) - g (u x)‖ₑ ∂μ
        ≤ ∫⁻ _ in V, ⨆ x ∈ (V : Set E), ‖g (un n x) - g (u x)‖ₑ ∂μ :=
          setLIntegral_mono' V.isOpen.measurableSet fun x hx =>
            le_iSup₂ (f := fun x (_ : x ∈ (V : Set E)) => ‖g (un n x) - g (u x)‖ₑ) x hx
      _ = _ := setLIntegral_const _ _
  · -- The derivatives converge in `L¹(V)`: split off the uniform error of `Dg`.
    refine (tendsto_add_atTop_iff_nat (f := fun n => ∫⁻ x in V,
      ‖(fderiv ℝ g (un n x)).comp (Dn n x) - (fderiv ℝ g (u x)).comp (Du x)‖ₑ ∂μ) N).2 ?_
    set e := fun n => ⨆ x ∈ (V : Set E), ‖fderiv ℝ g (un n x) - fderiv ℝ g (u x)‖ₑ
    have he : Tendsto e atTop (𝓝 0) := tendsto_iSup_enorm_sub_of_tendstoUniformlyOn hDgu
    set J := ∫⁻ x in V, ‖Du x‖ₑ ∂μ
    have hJ : J ≠ ∞ := hDuV.hasFiniteIntegral.ne
    have hlim : Tendsto (fun n => (e n + ENNReal.ofReal C) * ∫⁻ x in V, ‖Dn n x - Du x‖ₑ ∂μ +
        e n * J) atTop (𝓝 0) := by
      have h1 := ENNReal.Tendsto.mul (he.add_const (ENNReal.ofReal C))
        (Or.inr (by simp)) hDD (Or.inr (by simp))
      have h2 := ENNReal.Tendsto.mul_const (b := J) he (Or.inr hJ)
      simpa only [zero_add, mul_zero, zero_mul, add_zero] using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun n => ?_
    have hmeas : AEMeasurable (fun x => ‖Dn n x - Du x‖ₑ) (μ.restrict V) :=
      ((hDn_cont n).aestronglyMeasurable.sub hDuV.aestronglyMeasurable).enorm
    calc ∫⁻ x in V, ‖(fderiv ℝ g (un n x)).comp (Dn n x) - (fderiv ℝ g (u x)).comp (Du x)‖ₑ ∂μ
        ≤ ∫⁻ x in V, ((e n + ENNReal.ofReal C) * ‖Dn n x - Du x‖ₑ + e n * ‖Du x‖ₑ) ∂μ := by
          refine setLIntegral_mono' V.isOpen.measurableSet fun x hx => ?_
          have hex : ‖fderiv ℝ g (un n x) - fderiv ℝ g (u x)‖ₑ ≤ e n :=
            le_iSup₂ (f := fun x (_ : x ∈ (V : Set E)) =>
              ‖fderiv ℝ g (un n x) - fderiv ℝ g (u x)‖ₑ) x hx
          have hsplit : (fderiv ℝ g (un n x)).comp (Dn n x) - (fderiv ℝ g (u x)).comp (Du x) =
              (fderiv ℝ g (un n x) - fderiv ℝ g (u x)).comp (Dn n x - Du x) +
                (fderiv ℝ g (un n x) - fderiv ℝ g (u x)).comp (Du x) +
                (fderiv ℝ g (u x)).comp (Dn n x - Du x) := by
            ext v
            simp only [add_apply, sub_apply,
              ContinuousLinearMap.coe_comp, Function.comp_apply, map_sub]
            abel
          rw [hsplit]
          calc _ ≤ ‖(fderiv ℝ g (un n x) - fderiv ℝ g (u x)).comp (Dn n x - Du x)‖ₑ +
                ‖(fderiv ℝ g (un n x) - fderiv ℝ g (u x)).comp (Du x)‖ₑ +
                ‖(fderiv ℝ g (u x)).comp (Dn n x - Du x)‖ₑ :=
                (enorm_add_le _ _).trans (add_le_add_left (enorm_add_le _ _) _)
            _ ≤ e n * ‖Dn n x - Du x‖ₑ + e n * ‖Du x‖ₑ +
                ENNReal.ofReal C * ‖Dn n x - Du x‖ₑ := by
                gcongr
                · exact (enorm_comp_le _ _).trans (mul_le_mul_left hex _)
                · exact (enorm_comp_le _ _).trans (mul_le_mul_left hex _)
                · exact (enorm_comp_le _ _).trans (mul_le_mul_left (hCe x hx) _)
            _ = _ := by ring
      _ = (e n + ENNReal.ofReal C) * ∫⁻ x in V, ‖Dn n x - Du x‖ₑ ∂μ + e n * J := by
          rw [lintegral_add_left' (hmeas.const_mul _), lintegral_const_mul'' _ hmeas,
            lintegral_const_mul'' _ hDuV.aestronglyMeasurable.enorm]

/-- **The weak chain rule for continuous maps.** If `u` is continuous on `Ω` with weak derivative
`Du`, and `g` is `C¹` on an open set `W` containing `u '' Ω`, then `g ∘ u` has weak derivative
`x ↦ Dg(u x) ∘ Du x` on `Ω`. No integrability exponent enters: `Du` is only locally integrable.
Continuity of `u` cannot simply be dropped, since `g ∘ u` and `Dg(u) ∘ Du` need not be locally
integrable otherwise. -/
theorem HasWeakFDerivOn.comp_contDiffOn (hu : HasWeakFDerivOn μ Ω u Du)
    (huc : ContinuousOn u Ω) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (huW : MapsTo u Ω W) :
    HasWeakFDerivOn μ Ω (fun x => g (u x)) fun x => (fderiv ℝ g (u x)).comp (Du x) :=
  hasWeakFDerivOn_iff_forall_isCompact_closure.2 fun V hVc hVΩ =>
    hasWeakFDerivOn_comp_of_isCompact_closure hu huc hW hg huW V hVc hVΩ

/-- **The weak chain rule for continuous maps and globally `C¹` functions.** -/
theorem HasWeakFDerivOn.comp_contDiff (hu : HasWeakFDerivOn μ Ω u Du)
    (huc : ContinuousOn u Ω) (hg : ContDiff ℝ 1 g) :
    HasWeakFDerivOn μ Ω (fun x => g (u x)) fun x => (fderiv ℝ g (u x)).comp (Du x) :=
  hu.comp_contDiffOn huc isOpen_univ hg.contDiffOn (mapsTo_univ _ _)

end Core

section Pair

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Weak derivatives of pairs.** The pair of two weakly differentiable maps is weakly
differentiable, with the paired derivative. -/
theorem HasWeakFDerivOn.prodMk {f : E → F} {g : E → G} {Df : E → E →L[ℝ] F}
    {Dg : E → E →L[ℝ] G} (hf : HasWeakFDerivOn μ Ω f Df) (hg : HasWeakFDerivOn μ Ω g Dg) :
    HasWeakFDerivOn μ Ω (fun x => (f x, g x)) fun x => (Df x).prod (Dg x) := by
  have : CompleteSpace F := hf.completeSpace
  have : CompleteSpace G := hg.completeSpace
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  · ext x <;> simp
  · ext x v <;> simp

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] [FiniteDimensional ℝ F]
  [CompleteSpace H]

/-- **The weak chain rule with domain dependence.** If `u` is continuous on `Ω` with weak
derivative `Du`, and `G` is `C¹` on an open set `W` containing the graph of `u` over `Ω`, then
`x ↦ G(x, u x)` has weak derivative `x ↦ DG(x, u x) ∘ (id, Du x)` on `Ω`. -/
theorem HasWeakFDerivOn.comp_graph_contDiffOn {u : E → F}
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
  exact (hid.prodMk hu).comp_contDiffOn (continuousOn_id.prodMk huc) hW hg huW

end Pair

/-! ### Local Sobolev classes -/

section MemWkpLoc

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] {p : ℝ≥0∞} {U : Set ℂ} {k : ℕ}

/-- **Pairs of local Sobolev maps.** Two maps in the local Sobolev class of order `k` pair to a map
in the same class, with values in the product. -/
theorem MemWkpLoc.prodMk [CompleteSpace F] [CompleteSpace G] {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (fun z => (f z, g z)) := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext z <;> simp

variable [FiniteDimensional ℝ F] [CompleteSpace G]

/-- **Composition of continuous `W^{1,p}_loc` maps with `C¹` maps.** If `u` is continuous on `U`
and belongs to `W^{1,p}_loc(U)`, and `g` is `C¹` on an open set containing `u '' U`, then
`g ∘ u` belongs to `W^{1,p}_loc(U)`. Its weak derivative on `interior U` is given by
`TauCeti.HasWeakFDerivOn.comp_contDiffOn`, and its `Lᵖ` bound on compact sets by
`TauCeti.eLpNorm_fderiv_comp_le`. -/
theorem MemWkpLoc.comp_contDiffOn {u : ℂ → F} {g : F → G} {W : Set F}
    (hu : MemWkpLoc p U 1 u) (huc : ContinuousOn u U) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (huW : MapsTo u U W) : MemWkpLoc p U 1 (fun z => g (u z)) := by
  obtain ⟨Du, hDu, hDup⟩ := hu.exists_weakFDeriv
  have hDgc : ContinuousOn (fderiv ℝ g) W := hg.continuousOn_fderiv_of_isOpen hW le_rfl
  refine memWkpLoc_succ_iff.2 ⟨(hg.continuousOn.comp huc huW).memLpLoc, _,
    hDu.comp_contDiffOn (huc.mono interior_subset) hW hg (huW.mono_left interior_subset), ?_⟩
  rw [memWkpLoc_zero_iff, memLpLoc_iff] at hDup ⊢
  intro K hKU hK
  have hgu : ContinuousOn (fun x => fderiv ℝ g (u x)) K :=
    hDgc.comp (huc.mono hKU) (huW.mono_left hKU)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgu
  have hDK : MemLp Du p (volume.restrict K) := hDup K hKU hK
  refine MemLp.of_le_mul (c := C) hDK
    (aestronglyMeasurable_fderiv_comp hK.measurableSet hgu hDK.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _))

/-- **Composition of continuous `W^{1,p}_loc` maps with globally `C¹` maps.** -/
theorem MemWkpLoc.comp_contDiff {u : ℂ → F} {g : F → G} (hu : MemWkpLoc p U 1 u)
    (huc : ContinuousOn u U) (hg : ContDiff ℝ 1 g) : MemWkpLoc p U 1 (fun z => g (u z)) :=
  hu.comp_contDiffOn huc isOpen_univ hg.contDiffOn (mapsTo_univ _ _)

variable [CompleteSpace H] in
/-- **Composition with domain dependence.** If `u` is continuous on `U` and belongs to
`W^{1,p}_loc(U)`, and `G` is `C¹` on an open set containing the graph of `u` over `U`, then
`z ↦ G(z, u z)` belongs to `W^{1,p}_loc(U)`. Its weak derivative on `interior U` is given by
`TauCeti.HasWeakFDerivOn.comp_graph_contDiffOn`. -/
theorem MemWkpLoc.comp_graph_contDiffOn {u : ℂ → F} {g : ℂ × F → H} {W : Set (ℂ × F)}
    (hu : MemWkpLoc p U 1 u) (huc : ContinuousOn u U) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (huW : ∀ z ∈ U, (z, u z) ∈ W) : MemWkpLoc p U 1 (fun z => g (z, u z)) := by
  have : CompleteSpace F := hu.completeSpace
  have hid : MemWkpLoc p U 1 (fun z : ℂ => z) :=
    (contDiff_id.contDiffOn (s := ((⊤ : Opens ℂ) : Set ℂ))).memWkpLoc (subset_univ U)
  exact (hid.prodMk hu).comp_contDiffOn (continuousOn_id.prodMk huc) hW hg huW

end MemWkpLoc

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
  have h := hu.comp_contDiff huc (g := fun t : ℝ => t ^ 2) (contDiff_id.pow 2)
  convert h using 2 with x
  ext v
  simp [mul_comm, mul_left_comm]

end Square

end TauCeti

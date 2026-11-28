/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
import Mathlib.Topology.UniformSpace.CompactConvergence
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Symplectic.Floer.Compactness.Limit
import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold.Family
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Derivative convergence for Floer solutions on a manifold

This file upgrades compact-open convergence of smooth Floer solutions on a manifold to uniform `C¹`
convergence in charts and passage of the intrinsic Floer equation `(dv - X_{K_{p₀}})^{0,1} = 0`
to the limit, assuming eventual uniform bounds on chart differentials
(`TauCeti.SmoothTwoForm.IsNondegenerate.`
`contMDiffOn_one_and_isComplexLinearMap_of_tendsto_floer_parametric`).

The proof localizes in extended charts around each point, reads `J` and `X_K` in coordinates via
`Floer.almostComplexInChartAt` and `SmoothTwoForm.hamiltonianOneFormInChartAt`, and applies the
parametric `C¹` convergence theorem
`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_stdComplexLineImag_sub_parametric`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Section 8.1 and Appendix B.4 (elliptic regularity).
-/

public section

noncomputable section

open Bundle Filter Function Metric Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]

/-- Local `C¹` convergence and passage of the chart Floer equation on a small disc around `z₀ ∈ Ω`
mapped by `v` into `(extChartAt I α).source`. -/
private theorem chart_c1_on_ball {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [I.Boundaryless] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {p : ℕ → P} {p₀ : P} {u : ℕ → ℝ × ℝ → M} {v : ℝ × ℝ → M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hvW : ∀ y ∈ Ω, (p₀, (y, v y)) ∈ W)
    (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) Ω)
    (hfl : ∀ n, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p n) y (u n y))
      (ω.perturbedMFDeriv (Ks (p n)) (Kt (p n)) (u n) y).toLinearMap)
    (hvc : ContinuousOn v Ω)
    (hlim : Tendsto (fun n ↦ (⟨Ω.domRestrict (u n), (hu n).continuousOn.domRestrict⟩ : C(Ω, M)))
      atTop (𝓝 ⟨Ω.domRestrict v, hvc.domRestrict⟩))
    (hbd : ∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω → MapsTo v C' (extChartAt I α).source →
      ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u n) y‖ ≤ M₀)
    (α : M) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) (hvz₀ : v z₀ ∈ (extChartAt I α).source) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ MapsTo v (ball z₀ r) (extChartAt I α).source ∧
      ContDiffOn ℝ 1 (extChartAt I α ∘ v) (ball z₀ r) ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop (ball z₀ r) ∧
      fderiv ℝ (extChartAt I α ∘ v) z₀ stdComplexLineImag -
          ω.hamiltonianVectorFieldInChartAt α (Kt p₀) (z₀, extChartAt I α (v z₀)) =
        Floer.almostComplexInChartAt I α (J p₀) (z₀, extChartAt I α (v z₀))
          (fderiv ℝ (extChartAt I α ∘ v) z₀ stdComplexLineReal -
            ω.hamiltonianVectorFieldInChartAt α (Ks p₀) (z₀, extChartAt I α (v z₀))) := by
  set e := extChartAt I α
  -- Step 1: Choose a small closed disc around `z₀` mapped into `e.source` with uniform `C¹` bound.
  have hU_open : IsOpen (Ω ∩ v ⁻¹' e.source) :=
    hvc.isOpen_inter_preimage hΩ (isOpen_extChartAt_source α)
  obtain ⟨r, hr, hcl_sub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (hU_open.mem_nhds ⟨hz₀, hvz₀⟩)
  have hcl_Ω : closedBall z₀ r ⊆ Ω := hcl_sub.trans inter_subset_left
  have hcl_v : MapsTo v (closedBall z₀ r) e.source := fun y hy ↦ (hcl_sub hy).2
  have hL : IsCompact (((↑) : Ω → ℝ × ℝ) ⁻¹' closedBall z₀ r) :=
    IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall z₀ r)
      (by simpa [Subtype.range_coe_subtype] using hcl_Ω)
  have hev_src : ∀ᶠ n in atTop, MapsTo (u n) (closedBall z₀ r) e.source := by
    filter_upwards [(ContinuousMap.tendsto_nhds_compactOpen.1 hlim) _ hL e.source
      (isOpen_extChartAt_source α) fun y hy ↦ hcl_v hy] with n hn z hz
    exact hn (x := ⟨z, hcl_Ω hz⟩) hz
  obtain ⟨M₀, hev_bd⟩ := hbd α (closedBall z₀ r) (isCompact_closedBall z₀ r) hcl_Ω hcl_v
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev_src.and hev_bd)
  -- Step 2: Set up the `C¹` coordinate Floer data on `ℝ × ℝ` in the chart at `α`.
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 1) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 1) (by simp) hW hKt
  let g : (P × (ℝ × ℝ)) × E → P × ((ℝ × ℝ) × E) := Equiv.prodAssoc P (ℝ × ℝ) E
  have hg : ContDiff ℝ 1 g := contDiff_prodAssoc
  set S₀ : Set (P × ((ℝ × ℝ) × E)) :=
    {q | q.2.2 ∈ e.target ∧ (q.1, (q.2.1, e.symm q.2.2)) ∈ W}
  have hS₀ : IsOpen S₀ := isOpen_preimage_prod_extChartAt_symm (I := I) α hW
  have hJ' : ContDiffOn ℝ 1
      (fun q : (P × (ℝ × ℝ)) × E ↦ Floer.almostComplexInChartAt I α (J q.1.1) (q.1.2, q.2))
      (g ⁻¹' S₀) :=
    (Floer.contDiffOn_almostComplexInChartAt_of_contMDiffOn (n := 1) (by simp) α hJ).comp
      hg.contDiffOn (mapsTo_preimage g S₀)
  have hXs' : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α (Function.uncurry Ks))
      (g ⁻¹' S₀) :=
    ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 1) (by simp) α hXsM).comp
      hg.contDiffOn (mapsTo_preimage g S₀)).congr fun q _ ↦
        ω.hamiltonianVectorFieldInChartAt_uncurry α Ks q.1.1 q.1.2 q.2
  have hXt' : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α (Function.uncurry Kt))
      (g ⁻¹' S₀) :=
    ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 1) (by simp) α hXtM).comp
      hg.contDiffOn (mapsTo_preimage g S₀)).congr fun q _ ↦
        ω.hamiltonianVectorFieldInChartAt_uncurry α Kt q.1.1 q.1.2 q.2
  have hX' : ContDiffOn ℝ 1
      (ω.hamiltonianOneFormInChartAt α (Function.uncurry Ks) (Function.uncurry Kt)) (g ⁻¹' S₀) :=
    ω.contDiffOn_hamiltonianOneFormInChartAt hXs' hXt'
  obtain ⟨hv_cd, hconv_tail, hCR_v⟩ :=
    Floer.tendstoLocallyUniformlyOn_fderiv_of_stdComplexLineImag_sub_parametric
      (J := fun q : (P × (ℝ × ℝ)) × E ↦ Floer.almostComplexInChartAt I α (J q.1.1) (q.1.2, q.2))
      (X := ω.hamiltonianOneFormInChartAt α (Function.uncurry Ks) (Function.uncurry Kt))
      (hS₀.preimage hg.continuous) hJ' hX' isOpen_ball
      (p := fun n ↦ p (n + N)) (p₀ := p₀)
      (u := fun n ↦ e ∘ u (n + N)) (v := e ∘ v)
      (hp.comp (tendsto_add_atTop_nat N))
      (fun y hy ↦ by
        have hysrc := hcl_v (ball_subset_closedBall hy)
        refine ⟨e.map_source hysrc, ?_⟩
        simpa only [g, Equiv.prodAssoc_apply, Function.comp_apply, e.left_inv hysrc] using
          hvW y (hcl_Ω (ball_subset_closedBall hy)))
      (fun n ↦ contMDiffOn_iff_contDiffOn.1 <|
        (contMDiffOn_extChartAt (n := (⊤ : ℕ∞))).comp
          ((hu (n + N)).mono (ball_subset_closedBall.trans hcl_Ω))
          fun z hz ↦ by
            rw [mem_preimage, ← extChartAt_source I]
            exact (hN (n + N) (Nat.le_add_left N n)).1 (ball_subset_closedBall hz))
      (fun n y hy w ↦ Floer.almostComplexInChartAt_apply_apply
        (e.map_source ((hN (n + N) (Nat.le_add_left N n)).1 (ball_subset_closedBall hy))) _ w)
      (fun n y hy ↦ by
        have hzcl : y ∈ closedBall z₀ r := ball_subset_closedBall hy
        have hzΩ : y ∈ Ω := hcl_Ω hzcl
        have hsrc : u (n + N) y ∈ e.source := (hN (n + N) (Nat.le_add_left N n)).1 hzcl
        have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u (n + N)) y :=
          ((hu (n + N)).mdifferentiableOn (by simp)).mdifferentiableAt (hΩ.mem_nhds hzΩ)
        simpa only [e, Function.comp_apply, SmoothTwoForm.hamiltonianOneFormInChartAt_uncurry,
          SmoothTwoForm.hamiltonianOneFormInChartAt_stdComplexLineImag,
          SmoothTwoForm.hamiltonianOneFormInChartAt_stdComplexLineReal] using
          (ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub
            hdiff hsrc).1 (hfl (n + N) y hzΩ))
      (fun C'' _ hC''U ↦ ⟨max M₀ 0, fun n y hy ↦
        ((hN (n + N) (Nat.le_add_left N n)).2 y (ball_subset_closedBall (hC''U hy))).trans
          (le_max_left _ _)⟩)
      (fun y hy ↦ by
        have hysrc := hcl_v (ball_subset_closedBall hy)
        have hyΩ : y ∈ Ω := hcl_Ω (ball_subset_closedBall hy)
        have hpt_u : Tendsto (fun n ↦ u (n + N) y) atTop (𝓝 (v y)) :=
          ((continuous_eval_const (⟨y, hyΩ⟩ : Ω)).continuousAt.tendsto.comp
            hlim).comp (tendsto_add_atTop_nat N)
        exact ((continuousOn_extChartAt α).continuousAt
          ((isOpen_extChartAt_source α).mem_nhds hysrc)).tendsto.comp hpt_u)
  -- Step 3: Reindex the derivative convergence back from `n + N` to `n`.
  have hconv_real : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (e ∘ u n))
      (fderiv ℝ (e ∘ v)) atTop (ball z₀ r) := by
    rw [← Filter.map_add_atTop_eq_nat N]
    exact tendstoLocallyUniformlyOn_map_iff.2 hconv_tail
  refine ⟨r, hr, ball_subset_closedBall.trans hcl_Ω, hcl_v.mono_left ball_subset_closedBall, hv_cd,
    hconv_real, ?_⟩
  simpa only [Function.comp_apply, SmoothTwoForm.hamiltonianOneFormInChartAt_uncurry,
    SmoothTwoForm.hamiltonianOneFormInChartAt_stdComplexLineImag,
    SmoothTwoForm.hamiltonianOneFormInChartAt_stdComplexLineReal] using
    hCR_v z₀ (mem_ball_self hr)

/-- **Global `C¹` convergence and passage of the Floer equation to the limit on a manifold.**
Let `ω` be a nondegenerate two-form on a boundaryless manifold `M` modelled on a
finite-dimensional space `E`, and let `P` be a finite-dimensional parameter space. Let `K_s, K_t`
be jointly `C²` and `J` jointly `C¹` on an open set `W ⊆ P × ((ℝ × ℝ) × M)`. Suppose `u_n` are
smooth (`C^∞`) solutions of the Floer equation on an open `Ω ⊆ ℝ × ℝ` for parameters `p_n → p₀`,
converging in `C(Ω, M)` (with the compact-open topology) to a continuous map `v : Ω → M` with
`(p₀, (y, v y)) ∈ W` on `Ω`, and suppose the chart differentials `d(extChartAt I α ∘ u_n)` are
eventually uniformly bounded on every compact `C' ⊆ Ω` with `MapsTo v C' (extChartAt I α).source`.

Then `v` is `C¹` on `Ω`, solves the intrinsic Floer equation `(dv - X_{K_{p₀}})^{0,1} = 0` for
`J_{p₀}` at every point of `Ω`, and in every chart `extChartAt I α`, the differentials
`d(extChartAt I α ∘ u_n)` converge uniformly to `d(extChartAt I α ∘ v)` on every compact
`C' ⊆ Ω` with `MapsTo v C' (extChartAt I α).source`. -/
theorem contMDiffOn_one_and_isComplexLinearMap_of_tendsto_floer_parametric
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [I.Boundaryless] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {p : ℕ → P} {p₀ : P} {u : ℕ → ℝ × ℝ → M} {v : ℝ × ℝ → M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hvW : ∀ y ∈ Ω, (p₀, (y, v y)) ∈ W)
    (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) Ω)
    (hfl : ∀ n, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p n) y (u n y))
      (ω.perturbedMFDeriv (Ks (p n)) (Kt (p n)) (u n) y).toLinearMap)
    (hvc : ContinuousOn v Ω)
    (hlim : Tendsto (fun n ↦ (⟨Ω.domRestrict (u n), (hu n).continuousOn.domRestrict⟩ : C(Ω, M)))
      atTop (𝓝 ⟨Ω.domRestrict v, hvc.domRestrict⟩))
    (hbd : ∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω → MapsTo v C' (extChartAt I α).source →
      ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u n) y‖ ≤ M₀) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v Ω ∧
      (∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p₀ y (v y))
        (ω.perturbedMFDeriv (Ks p₀) (Kt p₀) v y).toLinearMap) ∧
      ∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω → MapsTo v C' (extChartAt I α).source →
        TendstoUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n))
          (fderiv ℝ (extChartAt I α ∘ v)) atTop C' := by
  have hv_cmd : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v Ω := by
    intro z₀ hz₀
    obtain ⟨r, hr, -, -, hv_cd, -, -⟩ :=
      hω.chart_c1_on_ball hW hKs hKt hJ hΩ hp hvW hu hfl hvc hlim hbd (v z₀) hz₀
        (mem_extChartAt_source (v z₀))
    have hAt : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 1 v z₀ := by
      rw [contMDiffAt_iff]
      refine ⟨hvc.continuousAt (hΩ.mem_nhds hz₀), ?_⟩
      simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
        Function.comp_id, id_eq] using
        (hv_cd.contDiffAt (ball_mem_nhds z₀ hr)).contDiffWithinAt
    exact hAt.contMDiffWithinAt
  refine ⟨hv_cmd, ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨-, -, -, -, -, -, hCR⟩ :=
      hω.chart_c1_on_ball hW hKs hKt hJ hΩ hp hvW hu hfl hvc hlim hbd (v z₀) hz₀
        (mem_extChartAt_source (v z₀))
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v z₀ :=
      (hv_cmd.mdifferentiableOn one_ne_zero).mdifferentiableAt (hΩ.mem_nhds hz₀)
    exact (ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub
      hdiff (mem_extChartAt_source (v z₀))).2 hCR
  · intro α C' hC' hC'Ω hvα
    set U := Ω ∩ v ⁻¹' (extChartAt I α).source
    have hU : IsOpen U := hvc.isOpen_inter_preimage hΩ (isOpen_extChartAt_source α)
    have hball : ∀ z : U, ∃ r > 0, TendstoLocallyUniformlyOn
        (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n)) (fderiv ℝ (extChartAt I α ∘ v)) atTop
        (ball z.val r) := fun z ↦ by
      obtain ⟨r, hr, -, -, -, hconv, -⟩ :=
        hω.chart_c1_on_ball hW hKs hKt hJ hΩ hp hvW hu hfl hvc hlim hbd α z.property.1 z.property.2
      exact ⟨r, hr, hconv⟩
    choose r hr hconv using hball
    have hloc : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop U :=
      (tendstoLocallyUniformlyOn_iUnion (fun _ ↦ isOpen_ball) hconv).mono fun z hz ↦
        mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hr ⟨z, hz⟩)⟩
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hloc C'
      (fun y hy ↦ ⟨hC'Ω hy, hvα hy⟩) hC'

end TauCeti.SmoothTwoForm.IsNondegenerate

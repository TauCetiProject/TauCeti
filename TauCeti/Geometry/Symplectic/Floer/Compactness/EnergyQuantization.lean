/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import TauCeti.Analysis.Hofer
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Energy quantization and localization for Floer solutions on a manifold

Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M` modelled on a
finite-dimensional real normed space `E`, such as a closed symplectic manifold. Let `K_s, K_t` be
families of Hamiltonians and `J(p, z, x)` a family of `ω`-tame almost complex structures on the
tangent spaces of `M`, depending on a parameter `p` in a real inner product space `P`, a domain
point `z ∈ ℝ × ℝ` and a target point `x ∈ M`, with `(K_s, K_t)` jointly `C³` and `J` jointly `C²`
on an open neighbourhood `W` of a compact window `C × D × K`.

This file establishes the analytic localization and energy-quantization estimates needed for global
Gromov–Floer compactness on `M` (without assuming solutions stay in a single chart):

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_forall_norm_fderiv_extChartAt_comp_sq_le_and_floerEnergyDensity_le`:
  two-sided parametric comparison between the intrinsic Floer energy density `e(u)` and the chart
  derivative `‖d(extChartAt I α ∘ u)‖²` on a compact window `C × D × K_α`.
* `exists_pos_forall_pi_mul_sq_mul_floerEnergyDensity_le_inChart`:
  intrinsic chart mean-value inequality over a compact parameter window.
* `exists_opens_smoothEmbedding_norm_fderiv_sq_le`:
  smooth Euclidean embedding `eM : W_emb → ℝ^N` of a neighbourhood of `K` with a uniform global
  energy-to-derivative estimate `‖d(eM ∘ u)‖² ≤ A_e e(u) + B_e` for all Floer solutions taking
  values in `K`.
* `exists_pos_forall_eventually_le_setIntegral_ball_of_tendsto_floerEnergyDensity`:
  uniform energy quantization at blow-up points: there is `δ > 0` such that whenever `e(u_k)(z_k)
  → ∞` along `z_k → z₀ ∈ Ω`, every disc `ball z₀ ε ∩ Ω` eventually carries Floer energy at least
  `δ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Section 4.6 (bubbling off finitely many points) and Section 8.1
  (inhomogeneous equations).
* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*,
  Comm. Pure Appl. Math. **45** (1992), 583–622 (Hofer's lemma).
-/

public section

noncomputable section

open Bundle Complex ContinuousLinearMap Filter Function MeasureTheory Metric Real Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]

section ChartEstimates

variable {P : Type*} [TopologicalSpace P]

/-- **Two-sided parametric energy–derivative comparison in a chart.** On a compact parameter window
`C × D × K` in the chart at `α`, with `J` tamed by `ω` and `J`, `X_{K_s}`, `X_{K_t}` continuous in
the chart, there are uniform constants `A > 0, B ≥ 0, C₀ ≥ 0, D₀ ≥ 0` such that every solution `u`
for `p ∈ C` at `z ∈ D` with chart coordinate in `K` satisfies both
`‖d(extChartAt I α ∘ u)_z‖² ≤ A e(u)(z) + B` and
`e(u)(z) ≤ C₀ ‖∂ₛ(extChartAt I α ∘ u)(z)‖² + D₀`. -/
theorem exists_forall_norm_fderiv_extChartAt_comp_sq_le_and_floerEnergyDensity_le
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (α : M)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {C : Set P} {D : Set (ℝ × ℝ)} {K : Set E}
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hJ : ContinuousOn (fun q : P × ((ℝ × ℝ) × E) ↦ Floer.almostComplexInChartAt I α (J q.1) q.2)
      (C ×ˢ (D ×ˢ K)))
    (hXs : ContinuousOn (fun q : P × ((ℝ × ℝ) × E) ↦
      ω.hamiltonianVectorFieldInChartAt α (Ks q.1) q.2) (C ×ˢ (D ×ˢ K)))
    (hXt : ContinuousOn (fun q : P × ((ℝ × ℝ) × E) ↦
      ω.hamiltonianVectorFieldInChartAt α (Kt q.1) q.2) (C ×ˢ (D ×ˢ K)))
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ K,
      (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames (J p z ((extChartAt I α).symm y))) :
    ∃ A > 0, ∃ B ≥ 0, ∃ C₀ ≥ 0, ∃ D₀ ≥ 0, ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄,
      p ∈ C → z ∈ D → u z ∈ (extChartAt I α).source → extChartAt I α (u z) ∈ K →
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
        (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap →
      ‖fderiv ℝ (extChartAt I α ∘ u) z‖ ^ 2 ≤ A * ω.floerEnergyDensity (Ks p) (Kt p) u z + B ∧
        ω.floerEnergyDensity (Ks p) (Kt p) u z ≤
          C₀ * ‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ ^ 2 + D₀ := by
  set e := extChartAt I α with he
  set T := trivializationAt E (TangentSpace I) α with hT
  have hCDK : IsCompact (C ×ˢ (D ×ˢ K)) := hC.prod (hD.prod hK)
  have hbase {y : E} (hy : y ∈ e.target) : e.symm y ∈ T.baseSet := by
    simpa only [hT, TangentBundle.trivializationAt_baseSet, ← extChartAt_source I] using
      e.map_target hy
  -- Step 1: Uniform coercivity and upper bound for `b(p, z, y)(a, a) = ω(a, J_p(z, y) a)`.
  set b : P × ((ℝ × ℝ) × E) → E →L[ℝ] E →L[ℝ] ℝ := fun q ↦
    ((compL ℝ E E ℝ).flip (Floer.almostComplexInChartAt I α (J q.1) q.2)).comp
      (ContinuousAlternatingMap.flatL ℝ E ℝ (RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α q.2.2))
    with hb_def
  have hb : ∀ q ∈ C ×ˢ (D ×ˢ K), ∀ a, b q a a = SmoothBundleForm.eval₂ ω (e.symm q.2.2)
      (T.symmL ℝ (e.symm q.2.2) a) (J q.1 q.2.1 (e.symm q.2.2) (T.symmL ℝ (e.symm q.2.2) a)) := by
    rintro ⟨p, z, y⟩ hq a
    have hy : y ∈ e.target := hKα hq.2.2
    simp only [hb_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply, ContinuousAlternatingMap.flatL_apply_apply]
    have hS := TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) (x₀ := α)
      (by simpa only [he, extChartAt_source] using e.map_target hy)
    rw [(extChartAt I α).right_inv hy] at hS
    rw [RoughForm.inChartAt_apply, SmoothBundleForm.eval₂_apply, ← hS]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [he, extChartAt_coe_symm, Function.comp_apply]
      rfl
    · exact (congrArg (T.symmL ℝ (e.symm y)) (Floer.almostComplexInChartAt_apply z y a)).trans
        (Trivialization.symmL_continuousLinearMapAt _ (hbase hy) _)
  have hbc : ContinuousOn b (C ×ˢ (D ×ˢ K)) :=
    ((compL ℝ E E ℝ).flip.continuous.comp_continuousOn hJ).clm_comp
      ((ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.comp_continuousOn
        ((ω.isSmoothForm.continuousOn_inChartAt α).comp
          (continuousOn_snd.comp continuousOn_snd (mapsTo_univ _ _)) fun q hq ↦ hKα hq.2.2))
  obtain ⟨c, hc, hcb⟩ := hCDK.exists_pos_forall_mul_norm_sq_le hbc fun q hq a ha ↦ by
    rw [hb q hq]
    have hy : q.2.2 ∈ e.target := hKα hq.2.2
    have hSa : T.symmL ℝ (e.symm q.2.2) a ≠ 0 := fun h0 ↦ ha <| by
      rw [← Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ (hbase hy) a, h0, map_zero]
    simpa only [IsNondegenerate.symplecticFormAt_apply] using hJt q.1 hq.1 q.2.1 hq.2.1 q.2.2 hq.2.2
      _ hSa
  have hdiag : ContinuousOn (fun p : (P × ((ℝ × ℝ) × E)) × E ↦ b p.1 p.2 p.2)
      ((C ×ˢ (D ×ˢ K)) ×ˢ sphere (0 : E) 1) :=
    ((hbc.comp continuousOn_fst mapsTo_fst_prod).clm_apply continuousOn_snd).clm_apply
      continuousOn_snd
  obtain ⟨Mb, hMb⟩ := (hCDK.prod (isCompact_sphere (0 : E) 1)).exists_bound_of_continuousOn hdiag
  obtain ⟨MJ, hMJ⟩ := hCDK.exists_bound_of_continuousOn hJ
  obtain ⟨Ms, hMs⟩ := hCDK.exists_bound_of_continuousOn hXs
  obtain ⟨Mt, hMt⟩ := hCDK.exists_bound_of_continuousOn hXt
  set M_b := max Mb 0
  set M_J := max MJ 0
  set M_s := max Ms 0
  set M_t := max Mt 0
  refine ⟨4 * (1 + M_J ^ 2) / c, by positivity, 4 * (M_s ^ 2 + M_t ^ 2), by positivity,
    2 * M_b, by positivity, 2 * M_b * M_s ^ 2, by positivity, fun p u z hp hz hus huK hu hfl ↦ ?_⟩
  -- Step 2: Evaluate `b` on `a = ∂ₛ(e ∘ u) - X_{K_s}` to identify `b(a, a) = e(u)`.
  have hq : (p, (z, e (u z))) ∈ C ×ˢ (D ×ˢ K) := ⟨hp, hz, huK⟩
  have hx : e.symm (e (u z)) = u z := e.left_inv hus
  have hub : u z ∈ T.baseSet := by
    simpa only [hT, TangentBundle.trivializationAt_baseSet, ← extChartAt_source I] using hus
  set Xs := ω.hamiltonianVectorFieldInChartAt α (Ks p) (z, e (u z)) with hXs_def
  set Xt := ω.hamiltonianVectorFieldInChartAt α (Kt p) (z, e (u z))
  set a := fderiv ℝ (e ∘ u) z stdComplexLineReal - Xs with ha_def
  have hPs : T.symmL ℝ (u z) a = ω.perturbedMFDeriv (Ks p) (Kt p) u z stdComplexLineReal := by
    have hre := ω.continuousLinearMapAt_perturbedMFDeriv_apply (Ks := Ks p) (Kt := Kt p) hu hus
      stdComplexLineReal
    simp only [stdComplexLineReal_fst, stdComplexLineReal_snd, zero_smul, one_smul,
      sub_zero] at hre
    rw [ha_def, hXs_def, ← hre, Trivialization.symmL_continuousLinearMapAt _ hub]
  have hea : b (p, (z, e (u z))) a a = ω.floerEnergyDensity (Ks p) (Kt p) u z := by
    have hPt := hfl.apply_stdComplexLineImag
    simp only [ContinuousLinearMap.coe_coe] at hPt
    rw [hb _ hq]
    dsimp only
    rw [hx, hPs, floerEnergyDensity_def, hPt]
  have hca : c * ‖a‖ ^ 2 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u z := hea ▸ hcb _ hq a
  have hba : ω.floerEnergyDensity (Ks p) (Kt p) u z ≤ M_b * ‖a‖ ^ 2 := by
    rw [← hea]
    by_cases ha0 : a = 0
    · simp [ha0]
    · have ha_pos : 0 < ‖a‖ := norm_pos_iff.2 ha0
      have hunit : ‖a‖⁻¹ • a ∈ sphere (0 : E) 1 := by
        simp [norm_smul, ha_pos.ne']
      have h1 : b (p, (z, e (u z))) (‖a‖⁻¹ • a) (‖a‖⁻¹ • a) ≤ M_b := by
        have hMb' := hMb ((p, (z, e (u z))), ‖a‖⁻¹ • a) ⟨hq, hunit⟩
        rw [Real.norm_eq_abs] at hMb'
        exact (le_abs_self _).trans (hMb'.trans (le_max_left _ _))
      simp only [map_smul, smul_apply, smul_eq_mul] at h1
      have h2 : ‖a‖⁻¹ * (‖a‖⁻¹ * b (p, (z, e (u z))) a a) = b (p, (z, e (u z))) a a / ‖a‖ ^ 2 := by
        ring
      rw [h2, div_le_iff₀ (sq_pos_of_pos ha_pos)] at h1
      exact h1
  -- Step 3: Compare `‖d(e ∘ u)‖` and `‖∂ₛ(e ∘ u)‖` with `‖a‖` using the chart Floer equation.
  have hXsB : ‖Xs‖ ≤ M_s := (hMs _ hq).trans (le_max_left _ _)
  have hXtB : ‖Xt‖ ≤ M_t := (hMt _ hq).trans (le_max_left _ _)
  have hJB : ‖Floer.almostComplexInChartAt I α (J p) (z, e (u z))‖ ≤ M_J :=
    (hMJ _ hq).trans (le_max_left _ _)
  have hre_le : ‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ ≤ ‖a‖ + M_s := by
    calc ‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ = ‖a + Xs‖ := by rw [ha_def, sub_add_cancel]
      _ ≤ ‖a‖ + ‖Xs‖ := norm_add_le _ _
      _ ≤ ‖a‖ + M_s := by linarith
  have hCR := ω.fderiv_extChartAt_comp_stdComplexLineImag_sub (J := J p) (Ks := Ks p) (Kt := Kt p)
    hu hus hfl
  have him_le : ‖fderiv ℝ (e ∘ u) z stdComplexLineImag‖ ≤ M_J * ‖a‖ + M_t := by
    calc ‖fderiv ℝ (e ∘ u) z stdComplexLineImag‖
        = ‖Floer.almostComplexInChartAt I α (J p) (z, e (u z)) a + Xt‖ := by
            rw [← hCR, sub_add_cancel]
      _ ≤ ‖Floer.almostComplexInChartAt I α (J p) (z, e (u z)) a‖ + ‖Xt‖ := norm_add_le _ _
      _ ≤ M_J * ‖a‖ + M_t := by
            gcongr
            exact ((Floer.almostComplexInChartAt I α (J p) (z, e (u z))).le_opNorm a).trans
              (mul_le_mul_of_nonneg_right hJB (norm_nonneg a))
  have ha_le : ‖a‖ ≤ ‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ + M_s :=
    (norm_sub_le _ _).trans (by linarith)
  have hL : ‖fderiv ℝ (e ∘ u) z‖ ≤ ‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ +
      ‖fderiv ℝ (e ∘ u) z stdComplexLineImag‖ := by
    simpa [stdComplexLineReal, stdComplexLineImag] using
      (fderiv ℝ (e ∘ u) z).opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one
  have hdiv : ‖a‖ ^ 2 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u z / c :=
    (le_div_iff₀ hc).2 (by linarith)
  refine ⟨?_, ?_⟩
  · have hsq1 : ‖fderiv ℝ (e ∘ u) z‖ ^ 2 ≤
        2 * (‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (e ∘ u) z stdComplexLineImag‖ ^ 2) := by
      nlinarith [sq_nonneg (‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ -
        ‖fderiv ℝ (e ∘ u) z stdComplexLineImag‖), norm_nonneg (fderiv ℝ (e ∘ u) z)]
    have hsq2 : ‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * M_s ^ 2 := by
      nlinarith [sq_nonneg (‖a‖ - M_s), norm_nonneg (fderiv ℝ (e ∘ u) z stdComplexLineReal)]
    have hsq3 : ‖fderiv ℝ (e ∘ u) z stdComplexLineImag‖ ^ 2 ≤
        2 * M_J ^ 2 * ‖a‖ ^ 2 + 2 * M_t ^ 2 := by
      nlinarith [sq_nonneg (M_J * ‖a‖ - M_t), norm_nonneg (fderiv ℝ (e ∘ u) z stdComplexLineImag)]
    have h4 : 4 * (1 + M_J ^ 2) * ‖a‖ ^ 2 ≤
        4 * (1 + M_J ^ 2) / c * ω.floerEnergyDensity (Ks p) (Kt p) u z := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    linarith
  · have hsqa : ‖a‖ ^ 2 ≤ 2 * ‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ ^ 2 + 2 * M_s ^ 2 := by
      nlinarith [sq_nonneg (‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ - M_s), norm_nonneg a]
    have hM0 : 0 ≤ M_b := le_max_right _ _
    nlinarith

end ChartEstimates

section ChartMVI

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- Conjugates the chart Floer data `(J, X_{K_s}, X_{K_t})` to Euclidean space via `toEuclidean`
and `Complex.equivRealProdCLM`, obtaining the parametric Euclidean mean-value inequality on
`C × (eℂ⁻¹ D) × (L '' K_α)`. -/
private theorem exists_euclidean_chart_mvi [I.Boundaryless]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (α : M)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {Kα : Set E} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hKα : IsCompact Kα)
    (hKαt : Kα ⊆ (extChartAt I α).target)
    (hCDKW : C ×ˢ (D ×ˢ ((extChartAt I α).symm '' Kα)) ⊆ W) :
    let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
    let eℂ := Complex.equivRealProdCLM
    ∃ δ > 0, ∀ ⦃p : P⦄ ⦃w : ℂ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))⦄ ⦃y₀ : ℂ⦄ ⦃r : ℝ⦄,
      p ∈ C → 0 ≤ r → ball y₀ r ⊆ eℂ ⁻¹' D → ContDiffOn ℝ 3 w (ball y₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ w y 1) (closedBall y₀ r) →
      (∀ y ∈ ball y₀ r,
        fderiv ℝ w y Complex.I - L (ω.hamiltonianVectorFieldInChartAt α (Kt p)
          (eℂ y, L.symm (w y))) =
        L (Floer.almostComplexInChartAt I α (J p) (eℂ y, L.symm (w y))
          (L.symm (fderiv ℝ w y 1) - ω.hamiltonianVectorFieldInChartAt α (Ks p)
            (eℂ y, L.symm (w y))))) →
      MapsTo w (ball y₀ r) (L '' Kα) →
      π * r ^ 2 + ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ w y₀ 1‖ ^ 2 ≤
        7 * π * r ^ 2 + 8 * ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2 := by
  set e := extChartAt I α
  set eℂ := Complex.equivRealProdCLM
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKt
  set Wα : Set (P × ((ℝ × ℝ) × E)) :=
    {q | q.2.2 ∈ e.target ∧ (q.1, (q.2.1, e.symm q.2.2)) ∈ W}
  have hWα : IsOpen Wα :=
    (continuousOn_fst.prodMk ((continuousOn_fst.comp continuousOn_snd (mapsTo_univ _ _)).prodMk
      ((continuousOn_extChartAt_symm α).comp (continuousOn_snd.comp continuousOn_snd
        (mapsTo_univ _ _)) fun _ hq ↦ hq))).isOpen_inter_preimage
      ((isOpen_extChartAt_target α).preimage (continuous_snd.comp continuous_snd)) hW
  have hJα := Floer.contDiffOn_almostComplexInChartAt (n := 2) (by simp) α hJ
  have hXsα := ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (by simp) α hXsM
  have hXtα := ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (by simp) α hXtM
  let g : P × (ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) → P × ((ℝ × ℝ) × E) :=
    fun q ↦ (q.1, (eℂ q.2.1, L.symm q.2.2))
  have hg : ContDiff ℝ 2 g := contDiff_fst.prodMk
    ((eℂ.contDiff.comp (contDiff_fst.comp contDiff_snd)).prodMk
      (L.symm.contDiff.comp (contDiff_snd.comp contDiff_snd)))
  let J' : P → ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun p q ↦ (L.toContinuousLinearMap.comp
      (Floer.almostComplexInChartAt I α (J p) (eℂ q.1, L.symm q.2))).comp
        L.symm.toContinuousLinearMap
  let X' : P → ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      ℂ →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun p q ↦ L.toContinuousLinearMap.comp
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (ω.hamiltonianVectorFieldInChartAt α (Ks p) (eℂ q.1, L.symm q.2)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          (ω.hamiltonianVectorFieldInChartAt α (Kt p) (eℂ q.1, L.symm q.2))).comp
        eℂ.toContinuousLinearMap)
  have hJ' : ContDiffOn ℝ 2 (uncurry J') (g ⁻¹' Wα) :=
    (contDiffOn_const.clm_comp (hJα.comp hg.contDiffOn (mapsTo_preimage _ _))).clm_comp
      contDiffOn_const
  have hX' : ContDiffOn ℝ 2 (uncurry X') (g ⁻¹' Wα) :=
    contDiffOn_const.clm_comp
      (((contDiffOn_const.smulRight (hXsα.comp hg.contDiffOn (mapsTo_preimage _ _))).add
        (contDiffOn_const.smulRight (hXtα.comp hg.contDiffOn (mapsTo_preimage _ _)))).clm_comp
        contDiffOn_const)
  have hCDKW' : C ×ˢ ((eℂ ⁻¹' D) ×ˢ (L '' Kα)) ⊆ g ⁻¹' Wα := by
    rintro ⟨p, z, _⟩ ⟨hp, hz, y, hy, rfl⟩
    exact ⟨hKαt (by simp [g, hy]), hCDKW ⟨hp, hz, ⟨y, hy, by simp [g]⟩⟩⟩
  obtain ⟨δ, hδ, hmvi⟩ :=
    Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy_parametric
      (J := J') (X := X') (hWα.preimage hg.continuous) hJ' hX' hC
      (eℂ.toHomeomorph.isCompact_preimage.2 hD) (hKα.image L.continuous) hCDKW'
      fun p _ z _ x hx v ↦ by
        rcases hx with ⟨y, hy, rfl⟩
        simp [J', Floer.almostComplexInChartAt_apply_apply (hKαt hy)]
  refine ⟨δ, hδ, fun p w y₀ r hp hr hball hw hwc hCR hwK hsmall ↦ ?_⟩
  exact hmvi hp hr hball hw hwc (fun y hy ↦ by
    simpa [J', X', eℂ, equivRealProdCLM_one, equivRealProdCLM_I, map_sub] using hCR y hy)
    hwK hsmall

/-- **Intrinsic chart mean-value inequality over a compact parameter window.** For a chart at `α`
and a compact set `K_α` of chart coordinates whose image lies in `W` over `C × D`, there exist
`δ > 0`, `M₁ > 0`, `M₂ > 0`, `M₃ ≥ 0` such that any `C³` solution `u` on an open `Ω ⊆ D` for
`p ∈ C` mapping `closedBall c r ⊆ Ω` into the chart with coordinates in `K_α` and satisfying the
small-energy condition `M₁ (π r²) + M₂ ∫_{B_r(c)} e(u) < δ` obeys
`π r² e(u)(c) ≤ M₃ (π r² + ∫_{B_r(c)} e(u))`. -/
theorem exists_pos_forall_pi_mul_sq_mul_floerEnergyDensity_le_inChart
    [I.Boundaryless] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (α : M) {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {Kα : Set E} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hKα : IsCompact Kα)
    (hKαt : Kα ⊆ (extChartAt I α).target)
    (hCDKW : C ×ˢ (D ×ˢ ((extChartAt I α).symm '' Kα)) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ Kα,
      (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames (J p z ((extChartAt I α).symm y))) :
    ∃ δ > 0, ∃ M₁ > 0, ∃ M₂ > 0, ∃ M₃ ≥ 0,
      ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃c : ℝ × ℝ⦄ ⦃r : ℝ⦄,
        IsOpen Ω → Ω ⊆ D → p ∈ C → 0 ≤ r → closedBall c r ⊆ Ω →
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω →
        (∀ z ∈ closedBall c r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
          (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap) →
        MapsTo u (closedBall c r) ((extChartAt I α).source ∩ extChartAt I α ⁻¹' Kα) →
        M₁ * (π * r ^ 2) + M₂ * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z < δ →
        π * r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
          M₃ * (π * r ^ 2 + ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z) := by
  set e := extChartAt I α
  set eℂ := Complex.equivRealProdCLM
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKt
  have hCDKWα : C ×ˢ (D ×ˢ Kα) ⊆
      {q : P × ((ℝ × ℝ) × E) | q.2.2 ∈ e.target ∧ (q.1, (q.2.1, e.symm q.2.2)) ∈ W} :=
    fun q hq ↦ ⟨hKαt hq.2.2, hCDKW ⟨hq.1, hq.2.1, ⟨q.2.2, hq.2.2, rfl⟩⟩⟩
  obtain ⟨A, hA, B, hB, C₀, hC₀, D₀, hD₀, hbd⟩ :=
    hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le_and_floerEnergyDensity_le α hC hD hKα hKαt
      ((Floer.contDiffOn_almostComplexInChartAt (n := 2) (by simp) α hJ).continuousOn.mono hCDKWα)
      ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (by simp) α hXsM).continuousOn.mono
        hCDKWα)
      ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (by simp) α hXtM).continuousOn.mono
        hCDKWα)
      hJt
  obtain ⟨δ, hδ, hmvi⟩ :=
    hω.exists_euclidean_chart_mvi α hW hKs hKt hJ hC hD hKα hKαt hCDKW
  -- Translate between Euclidean `‖∂ₛ(L ∘ e ∘ u ∘ eℂ)‖²` and the intrinsic energy density `e(u)`.
  set cL := ‖(L : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ 2
  set cLs := ‖(L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖ ^ 2
  set A₁ := cL * A + 1
  set B₁ := cL * B
  set C₁ := C₀ * cLs
  refine ⟨δ, hδ, 1 + B₁, by positivity, A₁, by positivity,
    max (C₁ * (7 + 8 * B₁) + D₀) (C₁ * 8 * A₁), by positivity,
    fun Ω p u c r hΩ hΩD hp hr hcr hu hfl huK hsmall ↦ ?_⟩
  rcases hr.eq_or_lt with rfl | _
  · simp [ball_zero]
  -- Continuity and nonnegativity of `e(u)` on `closedBall c r`.
  have he_cont : ContinuousOn (ω.floerEnergyDensity (Ks p) (Kt p) u) (closedBall c r) := by
    intro z hz
    have hqW : (p, (z, u z)) ∈ W :=
      hCDKW ⟨hp, hΩD (hcr hz), ⟨e (u z), (huK hz).2, e.left_inv (huK hz).1⟩⟩
    have hslice : ContinuousAt (fun q : (ℝ × ℝ) × M ↦ (p, q)) (z, u z) :=
      continuousAt_const.prodMk continuousAt_id
    exact (ω.continuousAt_floerEnergyDensity
      ((hu.of_le (by norm_num)).contMDiffAt (hΩ.mem_nhds (hcr hz)))
      ((hXsM.continuousOn.continuousAt (hW.mem_nhds hqW)).comp hslice)
      ((hXtM.continuousOn.continuousAt (hW.mem_nhds hqW)).comp hslice)).continuousWithinAt
  have he_int : IntegrableOn (ω.floerEnergyDensity (Ks p) (Kt p) u) (ball c r) :=
    (he_cont.integrableOn_compact (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  have he_nn : ∀ z ∈ closedBall c r, 0 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u z := fun z hz ↦ by
    have ht := hJt p hp z (hΩD (hcr hz)) (e (u z)) (huK hz).2
    rw [e.left_inv (huK hz).1] at ht
    exact floerEnergyDensity_nonneg hω ht (hfl z hz)
  -- Transport `u` to `w : ℂ → ℝ^d` via `L ∘ e ∘ u ∘ eℂ` and compare derivatives and integrals.
  set y₀ := eℂ.symm c
  set w : ℂ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun y ↦ L (e (u (eℂ y)))
  have hball_sub : ball y₀ r ⊆ eℂ ⁻¹' ball c r := fun y hy ↦ by
    simpa [y₀, eℂ] using (lipschitz_equivRealProd.dist_le_mul y y₀).trans_lt (by simpa using hy)
  have hcl_sub : closedBall y₀ r ⊆ eℂ ⁻¹' closedBall c r := fun y hy ↦ by
    simpa [y₀, eℂ] using (lipschitz_equivRealProd.dist_le_mul y y₀).trans (by simpa using hy)
  have hU₀ : IsOpen (eℂ ⁻¹' (Ω ∩ u ⁻¹' e.source)) :=
    (hu.continuousOn.isOpen_inter_preimage hΩ (isOpen_extChartAt_source α)).preimage eℂ.continuous
  have hsubU : closedBall y₀ r ⊆ eℂ ⁻¹' (Ω ∩ u ⁻¹' e.source) :=
    fun y hy ↦ ⟨hcr (hcl_sub hy), (huK (hcl_sub hy)).1⟩
  have hcdU : ContDiffOn ℝ 3 w (eℂ ⁻¹' (Ω ∩ u ⁻¹' e.source)) :=
    L.contDiff.comp_contDiffOn ((contMDiffOn_iff_contDiffOn.1 <|
      (contMDiffOn_extChartAt (n := 3)).comp (hu.mono inter_subset_left)
        fun z hz ↦ by rw [mem_preimage, ← extChartAt_source I]; exact hz.2).comp
      eℂ.contDiff.contDiffOn (mapsTo_preimage _ _))
  have hw_cont : ContinuousOn (fun y ↦ fderiv ℝ w y 1) (closedBall y₀ r) :=
    ((hcdU.continuousOn_fderiv_of_isOpen hU₀ (by norm_num)).clm_apply
      continuousOn_const).mono hsubU
  have hfw (y : ℂ) : fderiv ℝ w y 1 = L (fderiv ℝ (e ∘ u) (eℂ y) stdComplexLineReal) := by
    have h1 := congrArg (fun f : ℂ →L[ℝ] _ ↦ f 1) (L.comp_fderiv (f := (e ∘ u) ∘ eℂ) (x := y))
    exact h1.trans (congrArg L (fderiv_comp_equivRealProdCLM_one (e ∘ u) y))
  have hfwI (y : ℂ) : fderiv ℝ w y Complex.I = L (fderiv ℝ (e ∘ u) (eℂ y) stdComplexLineImag) := by
    have h1 := congrArg (fun f : ℂ →L[ℝ] _ ↦ f Complex.I)
      (L.comp_fderiv (f := (e ∘ u) ∘ eℂ) (x := y))
    exact h1.trans (congrArg L (fderiv_comp_equivRealProdCLM_I (e ∘ u) y))
  have hdiff (z : ℝ × ℝ) (hz : z ∈ closedBall c r) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z :=
    (hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds (hcr hz))
  have hpt_le (y : ℂ) (hy : y ∈ closedBall y₀ r) :
      ‖fderiv ℝ w y 1‖ ^ 2 ≤ A₁ * ω.floerEnergyDensity (Ks p) (Kt p) u (eℂ y) + B₁ := by
    have hzc : eℂ y ∈ closedBall c r := hcl_sub hy
    have h1 := (hbd hp (hΩD (hcr hzc)) (huK hzc).1 (huK hzc).2 (hdiff _ hzc) (hfl _ hzc)).1
    have h2 : ‖fderiv ℝ (e ∘ u) (eℂ y) stdComplexLineReal‖ ≤ ‖fderiv ℝ (e ∘ u) (eℂ y)‖ := by
      simpa [stdComplexLineReal] using (fderiv ℝ (e ∘ u) (eℂ y)).le_opNorm stdComplexLineReal
    have h3 : ‖fderiv ℝ w y 1‖ ≤
        ‖(L : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ *
          ‖fderiv ℝ (e ∘ u) (eℂ y) stdComplexLineReal‖ := by
      rw [hfw y]; exact L.toContinuousLinearMap.le_opNorm _
    have h4 : ‖fderiv ℝ w y 1‖ ^ 2 ≤ cL * ‖fderiv ℝ (e ∘ u) (eℂ y)‖ ^ 2 := by
      have h3' : ‖fderiv ℝ w y 1‖ ≤
          ‖(L : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ *
            ‖fderiv ℝ (e ∘ u) (eℂ y)‖ :=
        h3.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      calc ‖fderiv ℝ w y 1‖ ^ 2
          ≤ (‖(L : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ *
              ‖fderiv ℝ (e ∘ u) (eℂ y)‖) ^ 2 := by gcongr
        _ = cL * ‖fderiv ℝ (e ∘ u) (eℂ y)‖ ^ 2 := by rw [mul_pow]
    have h5 := he_nn _ hzc
    have hcL_nn : 0 ≤ cL := by positivity
    dsimp only [A₁, B₁]
    nlinarith
  have hw_int : IntegrableOn (fun y ↦ ‖fderiv ℝ w y 1‖ ^ 2) (ball y₀ r) :=
    ((hw_cont.norm.pow 2).integrableOn_compact (isCompact_closedBall y₀ r)).mono_set
      ball_subset_closedBall
  have heℂ_int : IntegrableOn (fun y ↦ ω.floerEnergyDensity (Ks p) (Kt p) u (eℂ y))
      (eℂ ⁻¹' ball c r) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      equivRealProdCLM.toHomeomorph.measurableEmbedding).2 he_int
  have hint_le : ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2 ≤
      B₁ * (π * r ^ 2) + A₁ * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z := by
    have hvol : volume.real (ball y₀ r) = π * r ^ 2 := Complex.volume_real_ball y₀ hr
    calc ∫ y in ball y₀ r, ‖fderiv ℝ w y 1‖ ^ 2
        ≤ ∫ y in ball y₀ r, (A₁ * ω.floerEnergyDensity (Ks p) (Kt p) u (eℂ y) + B₁) :=
          setIntegral_mono_on hw_int
            (((heℂ_int.mono_set hball_sub).const_mul A₁).fun_add
              (integrableOn_const measure_ball_lt_top.ne))
            measurableSet_ball fun y hy ↦ hpt_le y (ball_subset_closedBall hy)
      _ = A₁ * (∫ y in ball y₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u (eℂ y)) +
            B₁ * (π * r ^ 2) := by
          rw [integral_add ((heℂ_int.mono_set hball_sub).const_mul A₁)
            (integrableOn_const measure_ball_lt_top.ne), integral_const_mul, setIntegral_const,
            smul_eq_mul, hvol, mul_comm (π * r ^ 2)]
      _ ≤ B₁ * (π * r ^ 2) +
            A₁ * ∫ y in eℂ ⁻¹' ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u (eℂ y) := by
          have hA₁_nn : 0 ≤ A₁ := by positivity
          have hmono := setIntegral_mono_set heℂ_int
            (ae_restrict_of_forall_mem (isOpen_ball.preimage eℂ.continuous).measurableSet
              fun y hy ↦ he_nn (eℂ y) (ball_subset_closedBall hy))
            hball_sub.eventuallySubset
          nlinarith
      _ = B₁ * (π * r ^ 2) + A₁ * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z :=
          congrArg (fun x ↦ B₁ * (π * r ^ 2) + A₁ * x)
            (Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
              equivRealProdCLM.toHomeomorph.measurableEmbedding _ _)
  -- Apply the Euclidean chart MVI and convert `‖∂ₛw(y₀)‖²` back to `e(u)(c)`.
  have hmvi_w := hmvi (p := p) (w := w) (y₀ := y₀) (r := r) hp hr
    (hball_sub.trans (preimage_mono (ball_subset_closedBall.trans (hcr.trans hΩD))))
    (hcdU.mono (ball_subset_closedBall.trans hsubU)) hw_cont
    (fun y hy ↦ by
      have hzc : eℂ y ∈ closedBall c r := hcl_sub (ball_subset_closedBall hy)
      have hCR := ω.fderiv_extChartAt_comp_stdComplexLineImag_sub (J := J p) (Ks := Ks p)
        (Kt := Kt p) (hdiff _ hzc) (huK hzc).1 (hfl _ hzc)
      rw [hfw y, hfwI y, show L.symm (w y) = e (u (eℂ y)) from L.symm_apply_apply _,
        L.symm_apply_apply, ← map_sub]
      exact congrArg L hCR)
    (fun y hy ↦ ⟨e (u (eℂ y)), (huK (hcl_sub (ball_subset_closedBall hy))).2, rfl⟩)
    (by linarith)
  have hc_mem : c ∈ closedBall c r := mem_closedBall_self hr
  have hup := (hbd hp (hΩD (hcr hc_mem)) (huK hc_mem).1 (huK hc_mem).2 (hdiff c hc_mem)
    (hfl c hc_mem)).2
  have hre_w : ‖fderiv ℝ (e ∘ u) c stdComplexLineReal‖ ^ 2 ≤ cLs * ‖fderiv ℝ w y₀ 1‖ ^ 2 := by
    have h1 : fderiv ℝ (e ∘ u) c stdComplexLineReal = L.symm (fderiv ℝ w y₀ 1) := by
      rw [hfw y₀]; simp [y₀, eℂ]
    have h2 : ‖fderiv ℝ (e ∘ u) c stdComplexLineReal‖ ≤
        ‖(L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖ * ‖fderiv ℝ w y₀ 1‖ := by
      rw [h1]; exact L.symm.toContinuousLinearMap.le_opNorm _
    calc ‖fderiv ℝ (e ∘ u) c stdComplexLineReal‖ ^ 2
        ≤ (‖(L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖ *
            ‖fderiv ℝ w y₀ 1‖) ^ 2 := by gcongr
      _ = cLs * ‖fderiv ℝ w y₀ 1‖ ^ 2 := by rw [mul_pow]
  have hint_nn : 0 ≤ ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z :=
    setIntegral_nonneg measurableSet_ball fun z hz ↦ he_nn z (ball_subset_closedBall hz)
  have hπr_nn : 0 ≤ π * r ^ 2 := by positivity
  have hstep1 : π * r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
      C₁ * (π * r ^ 2 * ‖fderiv ℝ w y₀ 1‖ ^ 2) + D₀ * (π * r ^ 2) := by
    have : ω.floerEnergyDensity (Ks p) (Kt p) u c ≤ C₁ * ‖fderiv ℝ w y₀ 1‖ ^ 2 + D₀ := by
      nlinarith
    nlinarith
  have hC₁_nn : 0 ≤ C₁ := by positivity
  have hstep3 : π * r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
      (C₁ * (7 + 8 * B₁) + D₀) * (π * r ^ 2) +
        (C₁ * 8 * A₁) * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z := by nlinarith
  have hle1 : C₁ * (7 + 8 * B₁) + D₀ ≤ max (C₁ * (7 + 8 * B₁) + D₀) (C₁ * 8 * A₁) := le_max_left _ _
  have hle2 : C₁ * 8 * A₁ ≤ max (C₁ * (7 + 8 * B₁) + D₀) (C₁ * 8 * A₁) := le_max_right _ _
  nlinarith

end ChartMVI

section EmbeddingCover

variable {P : Type*} [TopologicalSpace P]

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] in
/-- For a compact set `K ⊆ W_emb` with `C × D × K ⊆ W`, covers `K` by finitely many chart balls
`V_α` whose closed chart balls stay in `(extChartAt I α).target`, `W_emb`, and `W` over `C × D`. -/
private theorem exists_finset_chart_cover [I.Boundaryless]
    {W : Set (P × ((ℝ × ℝ) × M))} {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M}
    {W_emb : TopologicalSpace.Opens M} (hW : IsOpen W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hKne : K.Nonempty)
    (hKW : K ⊆ (W_emb : Set M)) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W) :
    ∃ (sK : Finset M) (r : M → ℝ), sK.Nonempty ∧ (∀ α ∈ sK, α ∈ K) ∧
      (∀ α ∈ sK, 0 < r α) ∧
      (∀ α ∈ sK, closedBall (extChartAt I α α) (r α) ⊆ (extChartAt I α).target) ∧
      (∀ α ∈ sK, (extChartAt I α).symm '' closedBall (extChartAt I α α) (r α) ⊆ (W_emb : Set M)) ∧
      (∀ α ∈ sK, C ×ˢ (D ×ˢ ((extChartAt I α).symm '' closedBall (extChartAt I α α) (r α))) ⊆ W) ∧
      K ⊆ ⋃ α ∈ sK,
        ((extChartAt I α).source ∩ extChartAt I α ⁻¹' ball (extChartAt I α α) (r α)) := by
  classical
  have hlocal : ∀ α ∈ K, ∃ r > 0,
      closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target ∧
      (extChartAt I α).symm '' closedBall (extChartAt I α α) r ⊆ (W_emb : Set M) ∧
      C ×ˢ (D ×ˢ ((extChartAt I α).symm '' closedBall (extChartAt I α α) r)) ⊆ W := by
    intro α hα
    have hW_swap : IsOpen ((fun q : (P × (ℝ × ℝ)) × M ↦ (q.1.1, (q.1.2, q.2))) ⁻¹' W) :=
      hW.preimage ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    obtain ⟨U₁, U₂, -, hU₂, hCDU₁, hαU₂, hprod⟩ :=
      generalized_tube_lemma (hC.prod hD) isCompact_singleton hW_swap (by
        rintro ⟨⟨p, z⟩, x⟩ ⟨⟨hp, hz⟩, rfl⟩
        exact hCDKW ⟨hp, hz, hα⟩)
    have hU : IsOpen ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (U₂ ∩ W_emb)) :=
      (continuousOn_extChartAt_symm α).isOpen_inter_preimage (isOpen_extChartAt_target α)
        (hU₂.inter W_emb.isOpen)
    have hmem : extChartAt I α α ∈
        (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (U₂ ∩ W_emb) :=
      ⟨mem_extChartAt_target α, by
        rw [mem_preimage, extChartAt_to_inv]
        exact ⟨hαU₂ rfl, hKW hα⟩⟩
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hmem)
    refine ⟨r, hr, fun y hy ↦ (hball hy).1, fun _ ⟨y, hy, h⟩ ↦ h ▸ (hball hy).2.2, ?_⟩
    rintro ⟨p, z, _⟩ ⟨hp, hz, y, hy, rfl⟩
    exact @hprod ((p, z), (extChartAt I α).symm y) ⟨hCDU₁ ⟨hp, hz⟩, (hball hy).2.1⟩
  choose r₀ hr_pos hr_tgt hr_emb hr_W using hlocal
  let r : M → ℝ := fun α ↦ if hα : α ∈ K then r₀ α hα else 1
  let V : M → Set M := fun α ↦
    (extChartAt I α).source ∩ extChartAt I α ⁻¹' ball (extChartAt I α α) (r α)
  have hV_open (α : M) : IsOpen (V α) :=
    (continuousOn_extChartAt α).isOpen_inter_preimage (isOpen_extChartAt_source α) isOpen_ball
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun α : K ↦ V α.1) (fun α ↦ hV_open α.1) fun α hα ↦
    mem_iUnion.2 ⟨⟨α, hα⟩, mem_extChartAt_source α, by
      simp only [mem_preimage, r, hα, ↓reduceDIte]; exact mem_ball_self (hr_pos α hα)⟩
  let sK : Finset M := t.image Subtype.val
  have hsK_sub : ∀ α ∈ sK, α ∈ K := by
    intro α hα; obtain ⟨β, -, rfl⟩ := Finset.mem_image.1 hα; exact β.2
  have hsK_cov : K ⊆ ⋃ α ∈ sK, V α := by simpa [sK] using ht
  have hsK_ne : sK.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨α, hα, -⟩ := mem_iUnion₂.1 (hsK_cov hx)
    exact ⟨α, hα⟩
  refine ⟨sK, r, hsK_ne, hsK_sub,
    fun α hα ↦ by simpa [r, hsK_sub α hα] using hr_pos α (hsK_sub α hα),
    fun α hα ↦ by simpa [r, hsK_sub α hα] using hr_tgt α (hsK_sub α hα),
    fun α hα ↦ by simpa [r, hsK_sub α hα] using hr_emb α (hsK_sub α hα),
    fun α hα ↦ by simpa [r, hsK_sub α hα] using hr_W α (hsK_sub α hα), hsK_cov⟩

/-- Local embedded derivative bound on a single chart ball `V_α`, under continuity of the Floer
data and pointwise differentiability of `u`. -/
private theorem exists_chart_embedding_bound [I.Boundaryless] [T2Space M]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M}
    (hJ : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
      (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hXs : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (Ks q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hXt : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (Kt q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x))
    {N : ℕ} {W_emb : TopologicalSpace.Opens M} {eM : M → EuclideanSpace ℝ (Fin N)}
    (heM_cmd : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) eM W_emb)
    (α : M) {r : ℝ} (hr_tgt : closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hr_emb : (extChartAt I α).symm '' closedBall (extChartAt I α α) r ⊆ (W_emb : Set M))
    (hr_W : C ×ˢ (D ×ˢ ((extChartAt I α).symm '' closedBall (extChartAt I α α) r)) ⊆ W) :
    let V := (extChartAt I α).source ∩ extChartAt I α ⁻¹' ball (extChartAt I α α) r
    ∃ A_α > 0, ∃ B_α ≥ 0,
      ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄,
        p ∈ C → z ∈ D → u z ∈ K → u z ∈ V → MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
          (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap →
        ‖fderiv ℝ (eM ∘ u) z‖ ^ 2 ≤ A_α * ω.floerEnergyDensity (Ks p) (Kt p) u z + B_α := by
  let Kα : Set E := closedBall (extChartAt I α α) r ∩ (extChartAt I α).symm ⁻¹' K
  have hKα_comp : IsCompact Kα := by
    have hcl : IsClosed Kα :=
      ((continuousOn_extChartAt_symm α).mono hr_tgt).preimage_isClosed_of_isClosed
        isClosed_closedBall hK.isClosed
    exact (isCompact_closedBall _ _).of_isClosed_subset hcl inter_subset_left
  have hKα_tgt : Kα ⊆ (extChartAt I α).target := inter_subset_left.trans hr_tgt
  have hKα_W : C ×ˢ (D ×ˢ ((extChartAt I α).symm '' Kα)) ⊆ W :=
    (prod_mono_right (prod_mono_right (image_mono inter_subset_left))).trans hr_W
  have hKα_tame : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ Kα,
      (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames (J p z ((extChartAt I α).symm y)) :=
    fun p hp z hz _ hy ↦ hJt p hp z hz _ hy.2
  set Oα := (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (W_emb : Set M)
  have hOα : IsOpen Oα := (continuousOn_extChartAt_symm α).isOpen_inter_preimage
    (isOpen_extChartAt_target α) W_emb.isOpen
  have hKαO : Kα ⊆ Oα := fun y hy ↦ ⟨hKα_tgt hy, hr_emb ⟨y, hy.1, rfl⟩⟩
  have heM_cd : ContDiffOn ℝ (⊤ : ℕ∞) (eM ∘ (extChartAt I α).symm) Oα :=
    contMDiffOn_iff_contDiffOn.1 <|
      heM_cmd.comp ((contMDiffOn_extChartAt_symm α).mono inter_subset_left) fun _ hy ↦ hy.2
  obtain ⟨Me, hMe⟩ := hKα_comp.exists_bound_of_continuousOn
    ((heM_cd.continuousOn_fderiv_of_isOpen hOα (by simp)).mono hKαO)
  set M_e := max Me 0
  have hWα_sub : C ×ˢ (D ×ˢ Kα) ⊆
      {q : P × ((ℝ × ℝ) × E) | q.2.2 ∈ (extChartAt I α).target ∧
        (q.1, (q.2.1, (extChartAt I α).symm q.2.2)) ∈ W} :=
    fun q hq ↦ ⟨hKα_tgt hq.2.2, hKα_W ⟨hq.1, hq.2.1, ⟨q.2.2, hq.2.2, rfl⟩⟩⟩
  obtain ⟨A_c, hAc, B_c, hBc, _, _, _, _, hcbd⟩ :=
    hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le_and_floerEnergyDensity_le α hC hD hKα_comp
      hKα_tgt
      ((Floer.continuousOn_almostComplexInChartAt α hJ).mono hWα_sub)
      ((ω.continuousOn_hamiltonianVectorFieldInChartAt α hXs).mono hWα_sub)
      ((ω.continuousOn_hamiltonianVectorFieldInChartAt α hXt).mono hWα_sub)
      hKα_tame
  refine ⟨M_e ^ 2 * A_c + 1, by positivity, M_e ^ 2 * B_c, by positivity,
    fun p u z hp hz huzK huzV hdiff_u hfl ↦ ?_⟩
  have huzKα : extChartAt I α (u z) ∈ Kα :=
    ⟨ball_subset_closedBall huzV.2, by
      rw [mem_preimage, (extChartAt I α).left_inv huzV.1]; exact huzK⟩
  have hcbd1 := (hcbd hp hz huzV.1 huzKα hdiff_u hfl).1
  have hev : eM ∘ u =ᶠ[𝓝 z] (eM ∘ (extChartAt I α).symm) ∘ (extChartAt I α ∘ u) := by
    filter_upwards [hdiff_u.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source α).mem_nhds huzV.1)] with y hy
    simp only [Function.comp_apply, (extChartAt I α).left_inv hy]
  have hd1 : DifferentiableAt ℝ (eM ∘ (extChartAt I α).symm) (extChartAt I α (u z)) :=
    (heM_cd.differentiableOn (by simp) _ (hKαO huzKα)).differentiableAt
      (hOα.mem_nhds (hKαO huzKα))
  have hd2 : DifferentiableAt ℝ (extChartAt I α ∘ u) z :=
    ((((contMDiffOn_extChartAt (n := 1)).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (by rw [← extChartAt_source I]; exact (isOpen_extChartAt_source α).mem_nhds huzV.1)).comp
        z hdiff_u).differentiableAt
  have hnorm : ‖fderiv ℝ (eM ∘ u) z‖ ≤ M_e * ‖fderiv ℝ (extChartAt I α ∘ u) z‖ := by
    rw [hev.fderiv_eq, fderiv_comp z hd1 hd2]
    exact (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ((hMe _ huzKα).trans (le_max_left _ _)) (norm_nonneg _))
  have he_nn : 0 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u z :=
    floerEnergyDensity_nonneg hω (hJt p hp z hz (u z) huzK) hfl
  nlinarith [sq_nonneg M_e, norm_nonneg (fderiv ℝ (eM ∘ u) z),
    norm_nonneg (fderiv ℝ (extChartAt I α ∘ u) z)]

/-- **Smooth Euclidean embedding and global energy-to-derivative estimate.** For a compact subset
`K ⊆ M` and a compact parameter window `C × D × K ⊆ W` with jointly continuous `J`, `X_{K_s}`,
`X_{K_t}` on the open set `W`, there exist an open neighbourhood `W_emb ⊇ K`, a smooth embedding
`emb : W_emb → ℝ^N` with total extension `eM : M → ℝ^N`, and constants `A_e > 0`, `B_e ≥ 0` such
that every map `u` differentiable at `z ∈ D` with `u z ∈ K` solving the Floer equation for `p ∈ C`
at `z` satisfies `‖d(eM ∘ u)_z‖² ≤ A_e e(u)(z) + B_e`. -/
theorem exists_opens_smoothEmbedding_norm_fderiv_sq_le [I.Boundaryless] [T2Space M]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M} (hW : IsOpen W)
    (hJ : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
      (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hXs : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (Ks q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hXt : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (Kt q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ (W_emb : TopologicalSpace.Opens M) (N : ℕ)
      (emb : SmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) W_emb
        (EuclideanSpace ℝ (Fin N)))
      (eM : M → EuclideanSpace ℝ (Fin N)),
      K ⊆ (W_emb : Set M) ∧
      (∀ x (hx : x ∈ (W_emb : Set M)), eM x = emb ⟨x, hx⟩) ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) eM W_emb ∧
      ∃ A_e > 0, ∃ B_e ≥ 0,
        ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄,
          p ∈ C → z ∈ D → u z ∈ K → MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
          IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
            (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap →
          ‖fderiv ℝ (eM ∘ u) z‖ ^ 2 ≤ A_e * ω.floerEnergyDensity (Ks p) (Kt p) u z + B_e := by
  classical
  obtain ⟨W_emb, hKW, -, N, ⟨emb⟩⟩ := hK.exists_opens_nonempty_smoothEmbedding_euclidean (I := I)
  let eM : M → EuclideanSpace ℝ (Fin N) :=
    fun x ↦ if hx : x ∈ (W_emb : Set M) then emb ⟨x, hx⟩ else 0
  have heM_eq (x : M) (hx : x ∈ (W_emb : Set M)) : eM x = emb ⟨x, hx⟩ := by
    simp only [eM, hx, ↓reduceDIte]
  have heM_cmd : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) eM W_emb := by
    intro x hx
    have hsub : (fun y : W_emb ↦ eM y) = emb := funext fun y ↦ heM_eq y.1 y.2
    exact (contMDiffAt_subtype_iff (U := W_emb) (x := ⟨x, hx⟩) |>.1
      (hsub ▸ emb.contMDiff.contMDiffAt)).contMDiffWithinAt
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨W_emb, N, emb, eM, empty_subset _, heM_eq, heM_cmd, 1, one_pos, 0, le_rfl,
      fun _ _ _ _ _ huzK _ _ ↦ huzK.elim⟩
  obtain ⟨sK, r, hsK_ne, -, -, hr_tgt, hr_emb, hr_W, hsK_cov⟩ :=
    exists_finset_chart_cover (I := I) hW hC hD hK hKne hKW hCDKW
  have hchart : ∀ α : {α // α ∈ sK},
      ∃ A_α > 0, ∃ B_α ≥ 0,
        ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄,
          p ∈ C → z ∈ D → u z ∈ K →
          u z ∈ (extChartAt I α.1).source ∩
            extChartAt I α.1 ⁻¹' ball (extChartAt I α.1 α.1) (r α.1) →
          MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
          IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
            (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap →
          ‖fderiv ℝ (eM ∘ u) z‖ ^ 2 ≤ A_α * ω.floerEnergyDensity (Ks p) (Kt p) u z + B_α :=
    fun α ↦ hω.exists_chart_embedding_bound hJ hXs hXt hC hD hK hJt heM_cmd α.1
      (hr_tgt α.1 α.2) (hr_emb α.1 α.2) (hr_W α.1 α.2)
  choose A_α hAα B_α hBα hbd_α using hchart
  let sK_att := sK.attach
  have hsK_att_ne : sK_att.Nonempty := Finset.attach_nonempty_iff.2 hsK_ne
  set A_e := sK_att.sup' hsK_att_ne A_α
  set B_e := sK_att.sup' hsK_att_ne B_α
  have hAe_pos : 0 < A_e := by
    obtain ⟨α, hα⟩ := hsK_att_ne; exact (hAα α).trans_le (Finset.le_sup' A_α hα)
  have hBe_nn : 0 ≤ B_e := by
    obtain ⟨α, hα⟩ := hsK_att_ne; exact (hBα α).trans (Finset.le_sup' B_α hα)
  refine ⟨W_emb, N, emb, eM, hKW, heM_eq, heM_cmd, A_e, hAe_pos, B_e, hBe_nn,
    fun p u z hp hz huzK hdiff_u hfl ↦ ?_⟩
  obtain ⟨α, hαsK, huzV⟩ := mem_iUnion₂.1 (hsK_cov huzK)
  have h1 := hbd_α ⟨α, hαsK⟩ hp hz huzK huzV hdiff_u hfl
  have he_nn : 0 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u z :=
    floerEnergyDensity_nonneg hω (hJt p hp z hz (u z) huzK) hfl
  have hA_le : A_α ⟨α, hαsK⟩ ≤ A_e := Finset.le_sup' A_α (Finset.mem_attach sK ⟨α, hαsK⟩)
  have hB_le : B_α ⟨α, hαsK⟩ ≤ B_e := Finset.le_sup' B_α (Finset.mem_attach sK ⟨α, hαsK⟩)
  nlinarith

end EmbeddingCover

section Concentration

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- **Localized intrinsic mean-value inequality relative to an embedding.** Given a smooth embedding
`emb : W_emb → ℝ^N` covering `K` with total extension `eM`, produces a Lebesgue number `η > 0` and
uniform MVI constants `(δ_mvi, M₁, M₂, M₃)` on discs whose embedded image has diameter `< η`. -/
private theorem exists_localized_mvi [I.Boundaryless] [T2Space M]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x))
    {W_emb : TopologicalSpace.Opens M} {N : ℕ}
    (emb : SmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) W_emb
      (EuclideanSpace ℝ (Fin N)))
    {eM : M → EuclideanSpace ℝ (Fin N)} (hKW : K ⊆ (W_emb : Set M))
    (heM_eq : ∀ x (hx : x ∈ (W_emb : Set M)), eM x = emb ⟨x, hx⟩)
    (heM_cmd : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) eM W_emb) :
    ∃ η > 0, ∃ δ_mvi > 0, ∃ M₁ > 0, ∃ M₂ > 0, ∃ M₃ ≥ 0,
      ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃c : ℝ × ℝ⦄ ⦃r : ℝ⦄,
        IsOpen Ω → Ω ⊆ D → p ∈ C → 0 ≤ r → closedBall c r ⊆ Ω →
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω → MapsTo u Ω K →
        (∀ z ∈ closedBall c r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
          (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap) →
        (∀ z ∈ closedBall c r, dist (eM (u z)) (eM (u c)) < η) →
        M₁ * (π * r ^ 2) + M₂ * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z <
          δ_mvi →
        π * r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
          M₃ * (π * r ^ 2 + ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, 1, one_pos, 1, one_pos, 1, one_pos, 0, le_rfl,
      fun _ _ _ _ _ _ _ _ hr hcr _ huK _ _ _ ↦ (huK (hcr (mem_closedBall_self hr))).elim⟩
  obtain ⟨sK, r, hsK_ne, -, -, hr_tgt, -, hr_W, hsK_cov⟩ :=
    exists_finset_chart_cover (I := I) hW hC hD hK hKne hKW hCDKW
  let V : M → Set M := fun α ↦
    (extChartAt I α).source ∩ extChartAt I α ⁻¹' ball (extChartAt I α α) (r α)
  have hV_open (α : M) : IsOpen (V α) :=
    (continuousOn_extChartAt α).isOpen_inter_preimage (isOpen_extChartAt_source α) isOpen_ball
  have hchart : ∀ α : {α // α ∈ sK},
      ∃ δ_α > 0, ∃ M₁_α > 0, ∃ M₂_α > 0, ∃ M₃_α ≥ 0,
        ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃c : ℝ × ℝ⦄ ⦃r' : ℝ⦄,
          IsOpen Ω → Ω ⊆ D → p ∈ C → 0 ≤ r' → closedBall c r' ⊆ Ω →
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω → MapsTo u Ω K → MapsTo u (closedBall c r') (V α.1) →
          (∀ z ∈ closedBall c r',
            IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
              (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap) →
          M₁_α * (π * r' ^ 2) + M₂_α * ∫ z in ball c r', ω.floerEnergyDensity (Ks p) (Kt p) u z <
            δ_α →
          π * r' ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
            M₃_α * (π * r' ^ 2 + ∫ z in ball c r', ω.floerEnergyDensity (Ks p) (Kt p) u z) := by
    intro α
    let Kα : Set E := closedBall (extChartAt I α.1 α.1) (r α.1) ∩ (extChartAt I α.1).symm ⁻¹' K
    have hKα_comp : IsCompact Kα := by
      have hcl : IsClosed Kα :=
        ((continuousOn_extChartAt_symm α.1).mono (hr_tgt α.1 α.2)).preimage_isClosed_of_isClosed
          isClosed_closedBall hK.isClosed
      exact (isCompact_closedBall _ _).of_isClosed_subset hcl inter_subset_left
    have hKα_tgt : Kα ⊆ (extChartAt I α.1).target := inter_subset_left.trans (hr_tgt α.1 α.2)
    have hKα_W : C ×ˢ (D ×ˢ ((extChartAt I α.1).symm '' Kα)) ⊆ W :=
      (prod_mono_right (prod_mono_right (image_mono inter_subset_left))).trans (hr_W α.1 α.2)
    have hKα_tame : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ Kα,
        (hω.symplecticFormAt ((extChartAt I α.1).symm y)).Tames
          (J p z ((extChartAt I α.1).symm y)) :=
      fun p hp z hz _ hy ↦ hJt p hp z hz _ hy.2
    obtain ⟨δ_α, hδα, M₁_α, hM₁α, M₂_α, hM₂α, M₃_α, hM₃α, hmvi_α⟩ :=
      hω.exists_pos_forall_pi_mul_sq_mul_floerEnergyDensity_le_inChart α.1 hW hKs hKt hJ hC hD
        hKα_comp hKα_tgt hKα_W hKα_tame
    refine ⟨δ_α, hδα, M₁_α, hM₁α, M₂_α, hM₂α, M₃_α, hM₃α,
      fun Ω p u c r' hΩ hΩD hp hr' hcr hu huK huV hfl hsmall ↦ ?_⟩
    refine hmvi_α hΩ hΩD hp hr' hcr hu hfl (fun z hz ↦ ?_) hsmall
    have hzV := huV hz
    exact ⟨hzV.1, ball_subset_closedBall hzV.2, by
      rw [mem_preimage, (extChartAt I α.1).left_inv hzV.1]; exact huK (hcr hz)⟩
  choose δ_α hδα M₁_α hM₁α M₂_α hM₂α M₃_α hM₃α hmvi_α using hchart
  let sK_att := sK.attach
  have hsK_att_ne : sK_att.Nonempty := Finset.attach_nonempty_iff.2 hsK_ne
  set δ_mvi := sK_att.inf' hsK_att_ne δ_α
  set M₁ := sK_att.sup' hsK_att_ne M₁_α
  set M₂ := sK_att.sup' hsK_att_ne M₂_α
  set M₃ := sK_att.sup' hsK_att_ne M₃_α
  have hδmvi_pos : 0 < δ_mvi := (Finset.lt_inf'_iff hsK_att_ne).2 fun α _ ↦ hδα α
  have hM₁_pos : 0 < M₁ := by
    obtain ⟨α, hα⟩ := hsK_att_ne; exact (hM₁α α).trans_le (Finset.le_sup' M₁_α hα)
  have hM₂_pos : 0 < M₂ := by
    obtain ⟨α, hα⟩ := hsK_att_ne; exact (hM₂α α).trans_le (Finset.le_sup' M₂_α hα)
  have hM₃_nn : 0 ≤ M₃ := by
    obtain ⟨α, hα⟩ := hsK_att_ne; exact (hM₃α α).trans (Finset.le_sup' M₃_α hα)
  have hO_ex : ∀ α : {α // α ∈ sK}, ∃ O : Set (EuclideanSpace ℝ (Fin N)),
      IsOpen O ∧ emb ⁻¹' O = ((↑) : W_emb → M) ⁻¹' V α.1 := fun α ↦
    emb.isEmbedding.isInducing.isOpen_iff.1 ((hV_open α.1).preimage continuous_subtype_val)
  choose O hO_open hO_eq using hO_ex
  have heMK_comp : IsCompact (eM '' K) := hK.image_of_continuousOn (heM_cmd.continuousOn.mono hKW)
  have heMK_cov : eM '' K ⊆ ⋃ α : {α // α ∈ sK}, O α := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨α, hαsK, hxV⟩ := mem_iUnion₂.1 (hsK_cov hx)
    refine mem_iUnion.2 ⟨⟨α, hαsK⟩, ?_⟩
    rw [heM_eq x (hKW hx)]
    exact (Set.ext_iff.1 (hO_eq ⟨α, hαsK⟩) ⟨x, hKW hx⟩).2 hxV
  obtain ⟨η, hη, hLeb⟩ := lebesgue_number_lemma_of_metric heMK_comp hO_open heMK_cov
  refine ⟨η, hη, δ_mvi, hδmvi_pos, M₁, hM₁_pos, M₂, hM₂_pos, M₃, hM₃_nn,
    fun Ω p u c r' hΩ hΩD hp hr' hcr hu huK hfl hdist hsmall ↦ ?_⟩
  obtain ⟨α, hballO⟩ := hLeb (eM (u c)) ⟨u c, huK (hcr (mem_closedBall_self hr')), rfl⟩
  have huV : MapsTo u (closedBall c r') (V α.1) := by
    intro z hz
    have hzO : eM (u z) ∈ O α := hballO (hdist z hz)
    rw [heM_eq (u z) (hKW (huK (hcr hz)))] at hzO
    exact (Set.ext_iff.1 (hO_eq α) ⟨u z, hKW (huK (hcr hz))⟩).1 hzO
  have hint_nn : 0 ≤ ∫ z in ball c r', ω.floerEnergyDensity (Ks p) (Kt p) u z :=
    setIntegral_nonneg measurableSet_ball fun z hz ↦
      floerEnergyDensity_nonneg hω
        (hJt p hp z (hΩD (hcr (ball_subset_closedBall hz))) (u z)
          (huK (hcr (ball_subset_closedBall hz))))
        (hfl z (ball_subset_closedBall hz))
  have hπr_nn : 0 ≤ π * r' ^ 2 := by positivity
  have hδ_le : δ_mvi ≤ δ_α α := Finset.inf'_le δ_α (Finset.mem_attach sK α)
  have hM₁_le : M₁_α α ≤ M₁ := Finset.le_sup' M₁_α (Finset.mem_attach sK α)
  have hM₂_le : M₂_α α ≤ M₂ := Finset.le_sup' M₂_α (Finset.mem_attach sK α)
  have hM₃_le : M₃_α α ≤ M₃ := Finset.le_sup' M₃_α (Finset.mem_attach sK α)
  have hres := hmvi_α α hΩ hΩD hp hr' hcr hu huK huV hfl (by nlinarith)
  nlinarith

/-- **Energy quantization at blow-up points on a manifold.** Let `ω` be a nondegenerate two-form
on a Hausdorff boundaryless manifold `M` modelled on a finite-dimensional space `E`. Let `K_s, K_t`
be jointly `C³` and `J` jointly `C²` on an open set `W ⊆ P × ((ℝ × ℝ) × M)` containing `C × D × K`
for compact `C ⊆ P`, `D ⊆ ℝ × ℝ` and `K ⊆ M`, with `J(p, z, x)` tamed by `ω` on `C × D × K`.
There is a quantum `δ > 0` such that whenever `C³` Floer solutions `u_k` on an open `Ω ⊆ D` for
parameters `p_k ∈ C`, with values in `K`, have energy densities `e(u_k)(z_k) → ∞` along points
`z_k → z₀ ∈ Ω`, every disc `ball z₀ ε ∩ Ω` eventually carries Floer energy at least `δ`. -/
theorem exists_pos_forall_eventually_le_setIntegral_ball_of_tendsto_floerEnergyDensity
    [I.Boundaryless] [T2Space M] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃z : ℕ → ℝ × ℝ⦄ ⦃z₀ : ℝ × ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) y (u k y))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) y).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      z₀ ∈ Ω → Tendsto z atTop (𝓝 z₀) →
      Tendsto (fun k ↦ ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) (z k)) atTop atTop →
      ∀ ε > 0, ∀ᶠ k in atTop,
        δ ≤ ∫ y in ball z₀ ε ∩ Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) y := by
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKt
  obtain ⟨W_emb, N, emb, eM, hKW, heM_eq, heM_cmd, A_e, hAe, B_e, hBe, hbd_e⟩ :=
    hω.exists_opens_smoothEmbedding_norm_fderiv_sq_le hW hJ.continuousOn hXsM.continuousOn
      hXtM.continuousOn hC hD hK hCDKW hJt
  obtain ⟨η, hη, δ_mvi, hδmvi, M₁, -, M₂, hM₂, M₃, hM₃, hmvi⟩ :=
    hω.exists_localized_mvi hW hKs hKt hJ hC hD hK hCDKW hJt emb hKW heM_eq heM_cmd
  set c₀ := η / (4 * √A_e)
  have hc₀ : 0 < c₀ := by positivity
  set δ := min (δ_mvi / (2 * M₂)) ((π * c₀ ^ 2) / (2 * (M₃ + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, fun Ω p u z z₀ hΩ hΩD hpC hu hfl huK hint hz₀ hz hblow ε hε ↦ ?_⟩
  -- Step 1: Continuity and nonnegativity of `e_k`, then apply Hofer's lemma to `√(e_k)`.
  set e : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)
  have he_nn (k : ℕ) {y : ℝ × ℝ} (hy : y ∈ Ω) : 0 ≤ e k y :=
    floerEnergyDensity_nonneg hω (hJt (p k) (hpC k) y (hΩD hy) (u k y) (huK k hy)) (hfl k y hy)
  have he_cont (k : ℕ) : ContinuousOn (e k) Ω := by
    intro y hy
    have hqW : (p k, (y, u k y)) ∈ W := hCDKW ⟨hpC k, hΩD hy, huK k hy⟩
    have hslice : ContinuousAt (fun q : (ℝ × ℝ) × M ↦ (p k, q)) (y, u k y) :=
      continuousAt_const.prodMk continuousAt_id
    exact (ω.continuousAt_floerEnergyDensity
      (((hu k).of_le (by norm_num)).contMDiffAt (hΩ.mem_nhds hy))
      ((hXsM.continuousOn.continuousAt (hW.mem_nhds hqW)).comp hslice)
      ((hXtM.continuousOn.continuousAt (hW.mem_nhds hqW)).comp hslice)).continuousWithinAt
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    ((isOpen_ball.inter hΩ).mem_nhds ⟨mem_ball_self hε, hz₀⟩)
  obtain ⟨c, ρ, -, hc, -, hρl, hhof⟩ := exists_tendsto_hofer hr
    (fun k ↦ (he_cont k).mono (hrsub.trans inter_subset_right) |>.sqrt)
    (fun _ _ _ ↦ Real.sqrt_nonneg _) hz (Real.tendsto_sqrt_atTop.comp hblow)
  -- Step 2: Choose scales `s_k = c₀ / √(e_k(c_k)) → 0` so `eM ∘ u_k` stays within `< η` on
  -- `closedBall (c k) (s k)` and area terms become negligible.
  set lam : ℕ → ℝ := fun k ↦ √(e k (c k))
  have hlam : Tendsto lam atTop atTop :=
    tendsto_atTop_mono' atTop (hhof.mono fun k hk ↦ hk.1) (Real.tendsto_sqrt_atTop.comp hblow)
  set s : ℕ → ℝ := fun k ↦ c₀ / lam k
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlam
  have hsc_in : ∀ᶠ k in atTop, closedBall (c k) (s k) ⊆ ball z₀ ε ∩ Ω := by
    have hsum : Tendsto (fun k ↦ s k + dist (c k) z₀) atTop (𝓝 0) := by
      simpa using hs0.add (tendsto_iff_dist_tendsto_zero.1 hc)
    filter_upwards [hsum.eventually (gt_mem_nhds hr)] with k hk
    exact (closedBall_subset_closedBall' hk.le).trans hrsub
  have hs_le_ρ : ∀ᶠ k in atTop, s k ≤ ρ k := by
    filter_upwards [hlam.eventually_gt_atTop 0, hρl.eventually_ge_atTop c₀] with k hlk hrl
    exact (div_le_iff₀ hlk).2 (by linarith)
  have hB_small : ∀ᶠ k in atTop, √B_e * c₀ / lam k < η / 2 :=
    (tendsto_const_nhds.div_atTop hlam).eventually (gt_mem_nhds (half_pos hη))
  have hM₁_small : ∀ᶠ k in atTop, M₁ * (π * s k ^ 2) < δ_mvi / 2 := by
    have hlim : Tendsto (fun k ↦ M₁ * (π * s k ^ 2)) atTop (𝓝 0) := by
      simpa using (hs0.pow 2).const_mul π |>.const_mul M₁
    exact hlim.eventually (gt_mem_nhds (half_pos hδmvi))
  have hM₃_small : ∀ᶠ k in atTop, M₃ * (π * s k ^ 2) < (π * c₀ ^ 2) / 2 := by
    have hlim : Tendsto (fun k ↦ M₃ * (π * s k ^ 2)) atTop (𝓝 0) := by
      simpa using (hs0.pow 2).const_mul π |>.const_mul M₃
    exact hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hhof, hlam.eventually_gt_atTop 0, hsc_in, hs_le_ρ, hB_small, hM₁_small,
    hM₃_small] with k hk hlk hsc hsr hBs hM₁s hM₃s
  have hsk_nn : 0 ≤ s k := by positivity
  -- Step 3: Use the mean-value theorem on `eM ∘ u_k` to keep `closedBall (c k) (s k)` within `< η`.
  have hdist : ∀ y ∈ closedBall (c k) (s k), dist (eM (u k y)) (eM (u k (c k))) < η := by
    intro y hy
    have heM_diff : ∀ w ∈ closedBall (c k) (s k), DifferentiableAt ℝ (eM ∘ u k) w := fun w hw ↦ by
      have hwΩ : w ∈ Ω := (hsc hw).2
      have hcd : ContDiffOn ℝ 3 (eM ∘ u k) Ω := contMDiffOn_iff_contDiffOn.1 <|
        (heM_cmd.of_le (by simp)).comp (hu k) ((huK k).mono_right hKW)
      exact (hcd.differentiableOn (by norm_num) w hwΩ).differentiableAt (hΩ.mem_nhds hwΩ)
    have hfd_le : ∀ w ∈ closedBall (c k) (s k),
        ‖fderiv ℝ (eM ∘ u k) w‖ ≤ 2 * √A_e * lam k + √B_e := by
      intro w hw
      have hwΩ : w ∈ Ω := (hsc hw).2
      have h1 : ‖fderiv ℝ (eM ∘ u k) w‖ ^ 2 ≤ A_e * e k w + B_e :=
        hbd_e (hpC k) (hΩD hwΩ) (huK k hwΩ)
          (((hu k).mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds hwΩ))
          (hfl k w hwΩ)
      have h2 : √(e k w) ≤ 2 * lam k := hk.2 w ((mem_closedBall'.1 hw).trans hsr)
      have h3 : e k w ≤ 4 * lam k ^ 2 := by
        have := Real.sq_sqrt (he_nn k hwΩ)
        nlinarith [Real.sqrt_nonneg (e k w)]
      have h4 : ‖fderiv ℝ (eM ∘ u k) w‖ ^ 2 ≤ (2 * √A_e * lam k + √B_e) ^ 2 := by
        have hAeq : (√A_e) ^ 2 = A_e := Real.sq_sqrt hAe.le
        have hBeq : (√B_e) ^ 2 = B_e := Real.sq_sqrt hBe
        have hcross : 0 ≤ √A_e * lam k * √B_e := by positivity
        nlinarith
      have hrhs_nn : 0 ≤ 2 * √A_e * lam k + √B_e := by positivity
      nlinarith [norm_nonneg (fderiv ℝ (eM ∘ u k) w)]
    have hmv := (convex_closedBall (c k) (s k)).norm_image_sub_le_of_norm_fderiv_le heM_diff hfd_le
      (mem_closedBall_self hsk_nn) hy
    rw [← dist_eq_norm] at hmv
    have hdy : ‖y - c k‖ ≤ s k := by simpa [dist_eq_norm] using mem_closedBall.1 hy
    have hprod : (2 * √A_e * lam k + √B_e) * s k = η / 2 + √B_e * c₀ / lam k := by
      have hsq : √A_e ≠ 0 := (Real.sqrt_pos.2 hAe).ne'
      simp only [s, c₀]
      field_simp [hlk.ne', hsq]
      ring
    have hle : dist (eM (u k y)) (eM (u k (c k))) ≤ (2 * √A_e * lam k + √B_e) * s k :=
      hmv.trans (mul_le_mul_of_nonneg_left hdy (by positivity))
    linarith
  -- Step 4: Contradict energy `< δ` via the localized mean-value inequality.
  by_contra hlt
  push Not at hlt
  have hint_ball : ∫ y in ball (c k) (s k), e k y ≤ ∫ y in ball z₀ ε ∩ Ω, e k y :=
    setIntegral_mono_set ((hint k).mono_set inter_subset_right)
      (ae_restrict_of_forall_mem (measurableSet_ball.inter hΩ.measurableSet)
        fun y hy ↦ he_nn k hy.2)
      (ball_subset_closedBall.trans hsc).eventuallySubset
  have hsmall : M₁ * (π * s k ^ 2) + M₂ * ∫ y in ball (c k) (s k), e k y < δ_mvi := by
    have hδ1 : δ ≤ δ_mvi / (2 * M₂) := min_le_left _ _
    have hM₂δ : M₂ * δ ≤ δ_mvi / 2 := by rw [le_div_iff₀ (by positivity)] at hδ1; linarith
    nlinarith
  have hmvi_k := hmvi hΩ hΩD (hpC k) hsk_nn (hsc.trans inter_subset_right) (hu k) (huK k)
    (fun y hy ↦ hfl k y (hsc hy).2) hdist hsmall
  have hlhs : π * s k ^ 2 * e k (c k) = π * c₀ ^ 2 := by
    have hsq : lam k ^ 2 = e k (c k) := Real.sq_sqrt (he_nn k (hsc (mem_closedBall_self hsk_nn)).2)
    rw [← hsq]; simp only [s]; field_simp [hlk.ne']
  have hδ2 : δ ≤ (π * c₀ ^ 2) / (2 * (M₃ + 1)) := min_le_right _ _
  have hM₃δ : M₃ * δ ≤ (π * c₀ ^ 2) / 2 := by rw [le_div_iff₀ (by positivity)] at hδ2; nlinarith
  nlinarith

end Concentration

end TauCeti.SmoothTwoForm.IsNondegenerate

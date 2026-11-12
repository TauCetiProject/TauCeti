/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
public import TauCeti.Analysis.Sobolev.Morrey
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.MetricSpace.Equicontinuity
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.RCLike.OperatorNorm

/-!
# Second-derivative estimates for variable-coefficient Cauchy–Riemann equations

Let `F` be a complex Hilbert space and let `u : ℂ → F` be smooth on an open set `U ⊆ ℂ` and solve

`∂ₛu + A(z) ∂ₜu = f(z)`

there, where each `A(z)` is a real-linear map on `F` within `δ` of multiplication by `i` and `A`,
`f` are differentiable. This is the form taken by a nonlinear Cauchy–Riemann equation
`∂ₛu + J(z, u) ∂ₜu = h(z, u)` along a given solution, with `A(z) = J(z, u z)` and
`f(z) = h(z, u z)`, in coordinates in which `J` is close to the standard complex structure.

* **The differentiated equation.** For every direction `e`, the directional derivative
  `ξ = ∂ₑu` solves the same equation with right-hand side `∂ₑf - (∂ₑA) ∂ₜu`
  (`TauCeti.fderiv_fderiv_apply_add_eq_of_forall_fderiv_add_eq`). Only the symmetry of the second
  derivative of `u` is used.
* **The interior `W^{2,p}` estimate.** For `1 < p < ∞`, applying the interior `Lᵖ` estimate for
  the variable-coefficient operator (`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_I_smul_le`) to
  `ξ` bounds `‖Dξ‖_{Lᵖ(K)}` on a compact `K ⊆ U` by a constant depending only on `U`, `K`, `p`,
  `F` and bounds `M` for `‖DA‖`, `‖Df‖` and `L` for `‖Du‖` on `U`
  (`TauCeti.exists_eLpNorm_fderiv_fderiv_apply_le`). So uniform `C¹` bounds on solutions and
  coefficients give uniform bounds on second derivatives.
* **Equicontinuity of the derivatives.** For `p = 4 > 2 = dim ℂ`, Morrey's inequality on small
  balls (`TauCeti.enorm_sub_le_of_mem_ball_of_finrank_lt`) turns these `L⁴` bounds into a common
  Hölder modulus for the first derivatives. Hence a family of solutions whose first derivatives,
  and those of its coefficients, are bounded on compact sets has equicontinuous derivatives
  (`TauCeti.exists_pos_forall_equicontinuousOn_fderiv`). With the Arzelà–Ascoli theorem in `C¹`
  (`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`) this is the step from `C⁰` to
  `C¹` convergence in compactness arguments for pseudoholomorphic curves and Floer solutions.

In the interior estimate the threshold `δ` depends only on `p` and `F`, through the
Calderón–Zygmund constant; in the equicontinuity result, where `p = 4`, it depends only on `F`.
The estimates are stated for smooth `u`, the regularity required by the interior `Lᵖ` estimate.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix B.4 (elliptic bootstrapping) and Section 4.1.
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal ContDiff

namespace TauCeti

section Differentiated

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The differentiated Cauchy–Riemann equation.** If a `C²` map `u` solves
`∂ₛu + A(z) ∂ₜu = f(z)` on an open set `U`, with `A` differentiable, then for every direction `e`
its directional derivative `ξ = ∂ₑu` solves `∂ₛξ + A(z) ∂ₜξ = ∂ₑf - (∂ₑA) ∂ₜu` on `U`. -/
theorem fderiv_fderiv_apply_add_eq_of_forall_fderiv_add_eq {U : Set ℂ} (hU : IsOpen U)
    {u f : ℂ → F} {A : ℂ → F →L[ℝ] F} (hu : ContDiffOn ℝ 2 u U)
    (hA : DifferentiableOn ℝ A U) (h : ∀ z ∈ U, fderiv ℝ u z 1 + A z (fderiv ℝ u z I) = f z)
    {z : ℂ} (hz : z ∈ U) (e : ℂ) :
    fderiv ℝ (fun w ↦ fderiv ℝ u w e) z 1 + A z (fderiv ℝ (fun w ↦ fderiv ℝ u w e) z I) =
      fderiv ℝ f z e - fderiv ℝ A z e (fderiv ℝ u z I) := by
  have hzU : U ∈ 𝓝 z := hU.mem_nhds hz
  have hu2 : ContDiffAt ℝ 2 u z := hu.contDiffAt hzU
  have hsymm : IsSymmSndFDerivAt ℝ u z := hu2.isSymmSndFDerivAt (by simp)
  have hξ : ∀ e', HasFDerivAt (fun w ↦ fderiv ℝ u w e')
      ((fderiv ℝ (fderiv ℝ u) z).flip e') z := hu2.hasFDerivAt_fderiv_apply le_rfl
  have hlhs := (hξ 1).add ((hA.differentiableAt hzU).hasFDerivAt.clm_apply (hξ I))
  have heq : (fun w ↦ fderiv ℝ u w 1 + A w (fderiv ℝ u w I)) =ᶠ[𝓝 z] f :=
    Filter.eventually_of_mem hzU h
  have h2 := congrArg (fun T ↦ T e) (heq.fderiv_eq.symm.trans hlhs.fderiv)
  simp only [add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply] at h2
  rw [(hξ e).fderiv, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply, h2,
    hsymm e 1, hsymm e I]
  abel

end Differentiated

section Estimate

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The interior second-derivative estimate.** For `1 < p < ∞` there is `δ > 0` with the
following property. For `U ⊆ ℂ` open, `K ⊆ U` compact and bounds `M`, `L` there is a constant `C`
such that whenever a smooth `u` solves `∂ₛu + A(z) ∂ₜu = f(z)` on `U`, with
`‖A z w - i w‖ ≤ δ ‖w‖`, `‖DA‖ ≤ M`, `‖Df‖ ≤ M` and `‖Du‖ ≤ L` on `U`, every directional
derivative `∂ₑu` with `‖e‖ ≤ 1` satisfies `‖D(∂ₑu)‖_{Lᵖ(K)} ≤ C`. -/
theorem exists_eLpNorm_fderiv_fderiv_apply_le {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ ⦃U K : Set ℂ⦄, IsOpen U → IsCompact K → K ⊆ U → ∀ M L : ℝ≥0,
      ∃ C : ℝ≥0, ∀ (u f : ℂ → F) (A : ℂ → F →L[ℝ] F), ContDiffOn ℝ ∞ u U →
        DifferentiableOn ℝ A U →
        (∀ z ∈ U, ∀ w, ‖A z w - I • w‖ ≤ δ * ‖w‖) →
        (∀ z ∈ U, ‖fderiv ℝ A z‖ ≤ M) → (∀ z ∈ U, ‖fderiv ℝ f z‖ ≤ M) →
        (∀ z ∈ U, ‖fderiv ℝ u z‖ ≤ L) →
        (∀ z ∈ U, fderiv ℝ u z 1 + A z (fderiv ℝ u z I) = f z) →
        ∀ e : ℂ, ‖e‖ ≤ 1 →
          eLpNorm (fderiv ℝ (fun z ↦ fderiv ℝ u z e)) p (volume.restrict K) ≤ C := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_eLpNorm_fderiv_le_of_norm_sub_I_smul_le (F := F) hp hp_top
  refine ⟨δ, hδ0, fun U K hU hK hKU M L ↦ ?_⟩
  -- Work on a bounded open neighbourhood `U'` of `K` inside `U`.
  set U' := U ∩ thickening 1 K
  have hU' : IsOpen U' := hU.inter isOpen_thickening
  have hKU' : K ⊆ U' := subset_inter hKU (self_subset_thickening one_pos K)
  have hU'fin : volume U' ≠ (∞ : ℝ≥0∞) :=
    (hK.isBounded.thickening.subset inter_subset_right).measure_lt_top.ne
  obtain ⟨C₀, hC₀⟩ := hδ hU' hK hKU' 0
  set V : ℝ≥0 := (volume U' ^ p.toReal⁻¹).toNNReal
  have hV : (V : ℝ≥0∞) = volume U' ^ p.toReal⁻¹ :=
    ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      hU'fin)
  refine ⟨C₀ * (V * (M * (1 + L)) + V * L),
    fun u f A hu hA hAI hdA hdf hdu heq e he ↦ ?_⟩
  set ξ : ℂ → F := fun z ↦ fderiv ℝ u z e with hξdef
  have hξ : ContDiffOn ℝ ∞ ξ U' :=
    ((hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).mono inter_subset_left
  have hξc : ContinuousOn (fderiv ℝ ξ) U' := hξ.continuousOn_fderiv_of_isOpen hU' (by simp)
  have hest := hC₀ ξ A (fun _ ↦ 0) hξ (fun z hz ↦ hAI z hz.1) (fun _ _ ↦ by simp)
  simp only [zero_apply, add_zero] at hest
  -- The differentiated equation bounds the right-hand side pointwise on `U'`.
  have hg : eLpNorm (fun z ↦ (2 : ℂ)⁻¹ • (fderiv ℝ ξ z 1 + A z (fderiv ℝ ξ z I))) p
      (volume.restrict U') ≤ V * (M * (1 + L) : ℝ≥0) := by
    have hcont : ContinuousOn
        (fun z ↦ (2 : ℂ)⁻¹ • (fderiv ℝ ξ z 1 + A z (fderiv ℝ ξ z I))) U' :=
      continuousOn_const.smul ((hξc.clm_apply continuousOn_const).add
        ((hA.continuousOn.mono inter_subset_left).clm_apply
          (hξc.clm_apply continuousOn_const)))
    refine (eLpNorm_le_of_ae_bound (C := ((M * (1 + L) : ℝ≥0) : ℝ))
      (hcont.aestronglyMeasurable hU'.measurableSet)
      (ae_restrict_of_forall_mem hU'.measurableSet fun z hz ↦ ?_)).trans_eq ?_
    · rw [hξdef, fderiv_fderiv_apply_add_eq_of_forall_fderiv_add_eq hU (hu.of_le (by simp))
        hA heq hz.1 e, norm_smul, norm_inv, Complex.norm_two]
      have h1 : ‖fderiv ℝ f z e‖ ≤ M := by
        calc ‖fderiv ℝ f z e‖ ≤ ‖fderiv ℝ f z‖ * ‖e‖ := (fderiv ℝ f z).le_opNorm e
          _ ≤ M * 1 := by gcongr; exacts [hdf z hz.1]
          _ = M := mul_one _
      have h2 : ‖fderiv ℝ A z e (fderiv ℝ u z I)‖ ≤ M * L := by
        calc ‖fderiv ℝ A z e (fderiv ℝ u z I)‖
            ≤ ‖fderiv ℝ A z e‖ * ‖fderiv ℝ u z I‖ := (fderiv ℝ A z e).le_opNorm _
          _ ≤ (‖fderiv ℝ A z‖ * ‖e‖) * (‖fderiv ℝ u z‖ * ‖I‖) := by
            gcongr
            exacts [(fderiv ℝ A z).le_opNorm e, (fderiv ℝ u z).le_opNorm I]
          _ ≤ (M * 1) * (L * 1) := by
            gcongr
            exacts [hdA z hz.1, hdu z hz.1, by simp]
          _ = M * L := by ring
      have h3 := norm_sub_le (fderiv ℝ f z e) (fderiv ℝ A z e (fderiv ℝ u z I))
      push_cast
      nlinarith [norm_nonneg (fderiv ℝ f z e - fderiv ℝ A z e (fderiv ℝ u z I)),
        M.coe_nonneg, L.coe_nonneg]
    · rw [Measure.restrict_apply_univ, ← hV, ENNReal.ofReal_coe_nnreal]
  have hξL : eLpNorm ξ p (volume.restrict U') ≤ V * L := by
    refine (eLpNorm_le_of_ae_bound (C := (L : ℝ))
      ((hu.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
        |>.mono inter_subset_left |>.aestronglyMeasurable hU'.measurableSet)
      (ae_restrict_of_forall_mem hU'.measurableSet fun z hz ↦ ?_)).trans_eq ?_
    · calc ‖ξ z‖ ≤ ‖fderiv ℝ u z‖ * ‖e‖ := (fderiv ℝ u z).le_opNorm e
        _ ≤ L * 1 := by gcongr; exacts [hdu z hz.1]
        _ = L := mul_one _
    · rw [Measure.restrict_apply_univ, ← hV, ENNReal.ofReal_coe_nnreal]
  calc eLpNorm (fderiv ℝ ξ) p (volume.restrict K)
      ≤ C₀ * (eLpNorm (fun z ↦ (2 : ℂ)⁻¹ • (fderiv ℝ ξ z 1 + A z (fderiv ℝ ξ z I))) p
          (volume.restrict U') + eLpNorm ξ p (volume.restrict U')) := hest
    _ ≤ C₀ * (V * (M * (1 + L) : ℝ≥0) + V * L) := by gcongr
    _ = _ := by push_cast; ring

end Estimate

section Equicontinuity

variable {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Solutions with bounded derivatives have equicontinuous derivatives.** There is `δ > 0` with
the following property. Let `uᵢ` be smooth solutions of `∂ₛuᵢ + Aᵢ(z) ∂ₜuᵢ = fᵢ(z)` on an open
set `Ω ⊆ ℂ`, with `Aᵢ` differentiable and `‖Aᵢ z w - i w‖ ≤ δ ‖w‖` on `Ω`. If `‖DAᵢ‖`, `‖Dfᵢ‖`
and `‖Duᵢ‖` are bounded on each compact subset of `Ω`, uniformly in `i`, then the derivatives
`Duᵢ` are equicontinuous on `Ω`. -/
theorem exists_pos_forall_equicontinuousOn_fderiv :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ ⦃Ω : Set ℂ⦄ ⦃u f : ι → ℂ → F⦄ ⦃A : ι → ℂ → F →L[ℝ] F⦄, IsOpen Ω →
      (∀ i, ContDiffOn ℝ ∞ (u i) Ω) → (∀ i, DifferentiableOn ℝ (A i) Ω) →
      (∀ i, ∀ z ∈ Ω, ∀ w, ‖A i z w - I • w‖ ≤ δ * ‖w‖) →
      (∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ i, ∀ z ∈ C,
        ‖fderiv ℝ (A i) z‖ ≤ M ∧ ‖fderiv ℝ (f i) z‖ ≤ M ∧ ‖fderiv ℝ (u i) z‖ ≤ M) →
      (∀ i, ∀ z ∈ Ω, fderiv ℝ (u i) z 1 + A i z (fderiv ℝ (u i) z I) = f i z) →
      EquicontinuousOn (fun i ↦ fderiv ℝ (u i)) Ω := by
  have hp4 : ((Module.finrank ℝ ℂ : ℕ) : ℝ≥0) < (4 : ℝ≥0) := by
    rw [Complex.finrank_real_complex]; norm_num
  set a : ℝ := 1 - (Module.finrank ℝ ℂ : ℝ) / ((4 : ℝ≥0) : ℝ) with ha_def
  have ha : 0 < a := by rw [ha_def, Complex.finrank_real_complex]; norm_num
  -- Morrey's inequality on balls, with its constant isolated.
  obtain ⟨c, hc, hmor⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ {v : ℂ → F} {ρ : ℝ} {x y : ℂ},
      ContDiffOn ℝ 1 v (ball x ρ) → y ∈ ball x ρ →
        ‖v x - v y‖ₑ ≤ ENNReal.ofReal (c * (2 * ρ) ^ a) *
          eLpNorm (fderiv ℝ v) ((4 : ℝ≥0) : ℝ≥0∞) (volume.restrict (ball x ρ)) := by
    refine ⟨_, ?_, fun hv hy ↦ enorm_sub_le_of_mem_ball_of_finrank_lt (μ := volume) hv
      (mem_ball_self (pos_of_mem_ball hy)) hy hp4⟩
    rw [Complex.finrank_real_complex]
    refine mul_nonneg (by positivity) (Real.rpow_nonneg ?_ _)
    norm_num
    positivity
  obtain ⟨δ, hδ0, hδ⟩ := exists_eLpNorm_fderiv_fderiv_apply_le (F := F)
    (p := ((4 : ℝ≥0) : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top
  refine ⟨δ, hδ0, fun Ω u f A hΩ hu hA hAI hb heq x hx ↦ ?_⟩
  refine EquicontinuousAt.equicontinuousWithinAt ?_ Ω
  obtain ⟨R₀, hR₀, hR₀Ω⟩ := Metric.isOpen_iff.1 hΩ x hx
  have hRΩ : closedBall x (R₀ / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hR₀Ω
  obtain ⟨M, hM⟩ := hb _ (isCompact_closedBall x (R₀ / 2)) hRΩ
  obtain ⟨C, hC⟩ := hδ (isOpen_ball (x := x) (ε := R₀ / 2)) (isCompact_closedBall x (R₀ / 4))
    (closedBall_subset_ball (by linarith)) M.toNNReal M.toNNReal
  have hball : ball x (R₀ / 2) ⊆ Ω := ball_subset_closedBall.trans hRΩ
  -- The second derivatives are uniformly bounded in `L⁴` on `closedBall x (R₀ / 4)`.
  have hD : ∀ i, ∀ e : ℂ, ‖e‖ ≤ 1 → eLpNorm (fderiv ℝ (fun z ↦ fderiv ℝ (u i) z e))
      ((4 : ℝ≥0) : ℝ≥0∞) (volume.restrict (closedBall x (R₀ / 4))) ≤ C := fun i ↦
    hC (u i) (f i) (A i) ((hu i).mono hball) ((hA i).mono hball)
      (fun z hz ↦ hAI i z (hball hz))
      (fun z hz ↦ (hM i z (ball_subset_closedBall hz)).1.trans (Real.le_coe_toNNReal _))
      (fun z hz ↦ (hM i z (ball_subset_closedBall hz)).2.1.trans (Real.le_coe_toNNReal _))
      (fun z hz ↦ (hM i z (ball_subset_closedBall hz)).2.2.trans (Real.le_coe_toNNReal _))
      (fun z hz ↦ heq i z (hball hz))
  -- Morrey's inequality turns this into a uniform Hölder modulus for each directional derivative.
  have hdir : ∀ i, ∀ e : ℂ, ‖e‖ ≤ 1 → ∀ y, dist y x < R₀ / 8 →
      ‖fderiv ℝ (u i) x e - fderiv ℝ (u i) y e‖ ≤ c * (2 * (2 * dist y x)) ^ a * C := by
    intro i e he y hy
    rcases eq_or_ne y x with rfl | hyx
    · simp only [sub_self, norm_zero]
      positivity
    have hsub : ball x (2 * dist y x) ⊆ closedBall x (R₀ / 4) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
    have hv : ContDiffOn ℝ 1 (fun z ↦ fderiv ℝ (u i) z e) (ball x (2 * dist y x)) :=
      (((hu i).fderiv_of_isOpen (m := 1) hΩ (by simp)).clm_apply contDiffOn_const).mono
        (hsub.trans ((closedBall_subset_ball (by linarith)).trans hball))
    have h := (hmor hv (mem_ball.2 (by linarith [dist_pos.2 hyx]))).trans (mul_le_mul_right
      ((eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans (hD i e he)) _)
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul' C.coe_nonneg,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    exact h
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  -- The modulus `2 c (4 dist(y, x)) ^ a C` tends to zero at `x`.
  have hcont : Continuous fun y : ℂ ↦ 2 * (c * (2 * (2 * dist y x)) ^ a * C) :=
    continuous_const.mul ((continuous_const.mul ((Real.continuous_rpow_const ha.le).comp
      (continuous_const.mul (continuous_const.mul (continuous_id.dist continuous_const))))).mul
        continuous_const)
  have hzero : 2 * (c * (2 * (2 * dist x x)) ^ a * C) = 0 := by
    simp [Real.zero_rpow ha.ne']
  have hlt : ∀ᶠ y in 𝓝 x, 2 * (c * (2 * (2 * dist y x)) ^ a * C) < ε :=
    (hcont.tendsto x).eventually (gt_mem_nhds (hzero ▸ hε))
  filter_upwards [hlt, ball_mem_nhds x (by positivity : 0 < R₀ / 8)] with y hyε hyx i
  set T := fderiv ℝ (u i) x - fderiv ℝ (u i) y
  have hop : ‖T‖ ≤ ‖T 1‖ + ‖T I‖ :=
    T.opNorm_le_bound (by positivity) (ContinuousLinearMap.norm_apply_le_norm_one_add_norm_I T)
  have h1 := hdir i 1 (by simp) y (mem_ball.1 hyx)
  have h2 := hdir i I (by simp) y (mem_ball.1 hyx)
  rw [dist_eq_norm]
  simp only [T, sub_apply] at hop
  linarith

end Equicontinuity

end TauCeti

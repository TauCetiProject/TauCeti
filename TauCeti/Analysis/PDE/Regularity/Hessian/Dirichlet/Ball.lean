/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Existence
import TauCeti.Analysis.Calculus.FDeriv.Homothety
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Basic
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# The `W^{2,p}` Dirichlet problem for constant coefficients on balls

Let `1 < p < ∞`, `0 < λ`, and let `A` be a constant coefficient matrix on `ℝ × E`, elliptic with
`λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and bounded by `‖A‖ ≤ Λ`; `A` need not be symmetric. This file proves that on
every ball `B = B(x₀, R)` the Dirichlet problem

`tr (A ∘ D²u) = f` in `B`, `u ∈ W^{2,p}(B) ∩ W^{1,p}_0(B)`,

is uniquely solvable for every `f ∈ Lᵖ(B)`
(`TauCeti.existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_eq_of_ball`),
and that its solutions satisfy

`‖D²u‖_{Lᵖ(B)} ≤ C ‖f‖_{Lᵖ(B)}`

with a constant `C` depending only on `E`, `p`, `λ` and `Λ`: not on the centre, the radius or the
matrix `A` within the class
(`TauCeti.exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_ball`). On a
fixed bounded domain with `C²` boundary the `W^{2,p}` a priori estimate holds with one constant for
the whole class of matrices
(`TauCeti.exists_norm_le_of_traceCLM_comp_iteratedGradient_eq_of_norm_le`).

This uniformity is what estimates obtained by freezing measurable coefficients on balls need: on
each ball the frozen matrix is an average of the coefficients, so it varies with the ball, and the
balls range over all centres and radii. Splitting a strong solution of `tr (a ∘ D²u) = f` on a
ball into the solution `w` of the frozen problem with zero boundary values and datum
`f + tr ((A - a) ∘ D²u)` and the remainder `u - w`, which solves the homogeneous
constant-coefficient equation, controls `D²w` in `Lᵖ` with this constant, for every
`1 < p < ∞`.

## The argument

* **Balls have smooth boundary.** Every ball has the global `C²` boundary charts of the Dirichlet
  theory on `C²` domains (`TauCeti.exists_contDiff_graph_of_mem_frontier_ball`), so the solvability
  theorem of Gilbarg–Trudinger, Theorem 9.15 (in the `TauCeti` namespace,
  `existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_add_mul_eq`)
  applies.
* **Uniformity in `A`.** On the unit ball, Gilbarg–Trudinger's Lemma 9.17
  (`TauCeti.exists_norm_le_of_traceCLM_comp_iteratedGradient_add_mul_eq`) bounds `‖u‖_{W^{2,p}}` by
  `C_A ‖tr (A ∘ D²u)‖` for each `A`. The operator `u ↦ tr (A ∘ D²u)` depends linearly, hence
  continuously, on `A`, and the class of `A` is compact, so a perturbation argument over a finite
  cover (`IsCompact.exists_forall_norm_le_mul_norm_apply`) makes the constant uniform.
* **Uniformity in the ball.** The homothety `Φ y = R y + x₀` maps the unit ball onto `B(x₀, R)`.
  For `v = u ∘ Φ`, `D²v = R² D²u ∘ Φ` and `tr (A ∘ D²v) = R² f ∘ Φ`, and composition with `Φ` and
  with its inverse scales `Lᵖ` norms by reciprocal powers `R^(∓n/p)` of the Jacobian. These factors
  cancel, so the unit-ball constant serves for every ball.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.15 and Lemma 9.17.
* H. Dong, D. Kim, *On the `Lᵖ`-solvability of higher order parabolic and elliptic systems with
  BMO coefficients*, Arch. Ration. Mech. Anal. 199 (2011) (the splitting on balls).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric Filter Module
open scoped ENNReal InnerProductSpace

namespace TauCeti

open Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The constant-coefficient operator `u ↦ tr (A ∘ D²u)` from `W^{2,p}(Ω)` to `Lᵖ(Ω)`. -/
private def hessianTraceL (Omega : Opens (WithLp 2 (ℝ × E)))
    (A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2 →L[ℝ]
      Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega) :=
  ((traceCLM ℝ (WithLp 2 (ℝ × E))).comp (ContinuousLinearMap.compL ℝ (WithLp 2 (ℝ × E))
    (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) A)).compLpL p _ ∘L iteratedGradientL 1

private theorem hessianTraceL_ae (Omega : Opens (WithLp 2 (ℝ × E)))
    (A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2) :
    ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict Omega,
      hessianTraceL Omega A u x = traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := p) ((traceCLM ℝ (WithLp 2 (ℝ × E))).comp
    (ContinuousLinearMap.compL ℝ (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) A))
    (iteratedGradient 1 u)] with x hx
  rw [hessianTraceL, ContinuousLinearMap.comp_apply, iteratedGradientL_apply, hx,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

/-- The operator `u ↦ tr (A ∘ D²u)` depends continuously on `A`, since it is linear in `A` and the
coefficient matrices form a finite-dimensional space. -/
private theorem continuous_hessianTraceL (Omega : Opens (WithLp 2 (ℝ × E))) :
    Continuous fun A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) =>
      (hessianTraceL (p := p) Omega A) := by
  let T : (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) →ₗ[ℝ]
      (Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2 →L[ℝ]
        Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)) :=
    { toFun := fun A => hessianTraceL Omega A
      map_add' := fun A B => by
        simp only [hessianTraceL, map_add, ContinuousLinearMap.comp_add,
          ContinuousLinearMap.add_compLpL, ContinuousLinearMap.add_comp]
      map_smul' := fun c A => by
        simp only [hessianTraceL, map_smul, ContinuousLinearMap.comp_smul,
          ContinuousLinearMap.smul_compLpL, ContinuousLinearMap.smul_comp, RingHom.id_apply] }
  exact T.continuous_of_finiteDimensional

private theorem exists_norm_le_mul_norm_hessianTraceL (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {lam : ℝ} (hlam : 0 < lam) (Λ : ℝ) :
    ∃ C : ℝ, ∀ A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) → ‖A‖ ≤ Λ →
        ∀ u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2,
          firstOrder 1 u ∈ w1p0Submodule volume Omega p →
            ‖u‖ ≤ C * ‖hessianTraceL Omega A u‖ := by
  -- The class of coefficient matrices is compact.
  set K : Set (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :=
    {A | ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ} ∩ closedBall 0 Λ
  have hK : IsCompact K := by
    -- The norm of the operator space reaches `ProperSpace` through two instance paths.
    have : ProperSpace (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) := by
      simpa +instances using
        FiniteDimensional.proper ℝ (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
    refine (isCompact_closedBall 0 Λ).inter_left ?_
    simp only [ofPred_forall]
    exact isClosed_iInter fun ξ => isClosed_le continuous_const
      ((continuous_id.clm_apply continuous_const).inner continuous_const)
  -- The Banach space `M = W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` and the family `A ↦ tr (A ∘ D²·)` on it.
  set M : Submodule ℝ (Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2) :=
    (w1p0Submodule volume Omega p).toSubmodule.comap (firstOrderL 1).toLinearMap
  have hM : ∀ u, u ∈ M ↔ firstOrder 1 u ∈ w1p0Submodule volume Omega p := fun u => by
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, firstOrderL_apply,
      ClosedSubmodule.mem_toSubmodule_iff]
  have hLc : Continuous fun A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) =>
      (hessianTraceL (p := p) Omega A).comp M.subtypeL :=
    (continuous_hessianTraceL Omega).clm_comp continuous_const
  -- Lemma 9.17 for each `A` in the class, made uniform by compactness.
  obtain ⟨C, hC⟩ := hK.exists_forall_norm_le_mul_norm_apply hLc.continuousOn fun A hA => by
    obtain ⟨hA1, -⟩ := hA
    obtain ⟨C, hC⟩ := exists_norm_le_of_traceCLM_comp_iteratedGradient_add_mul_eq hp hp_top hΩ
      hbdry (A := fun _ => A) (fun _ _ => continuousWithinAt_const)
      (fun _ _ => ⟨lam, hlam, hA1⟩) (c := 0) (γ := 0) aestronglyMeasurable_const
      (ae_of_all _ fun _ => by simp) (ae_of_all _ fun _ => le_rfl)
    refine ⟨C, fun u => ?_⟩
    simpa using hC u _ ((hM u).1 u.property)
      ((hessianTraceL_ae Omega A (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)).mono
        fun x hx => by simp only [Pi.zero_apply, zero_mul, add_zero, hx])
  exact ⟨C, fun A hA hAΛ u hu => by
    -- `mem_closedBall_zero_iff` does not unify with the operator norm here; `dist` does.
    have hAK : A ∈ K := ⟨hA, mem_closedBall.2 ((dist_zero_right A).le.trans hAΛ)⟩
    simpa using hC A hAK ⟨u, (hM u).2 hu⟩⟩

/-- **The a priori estimate, uniformly in the coefficients** (Gilbarg–Trudinger, Lemma 9.17, for
constant coefficients). Let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary, `1 < p < ∞` and
`0 < λ`. There is one constant `C` such that for every constant matrix `A` with
`λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `‖A‖ ≤ Λ`, every `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` with `tr (A ∘ D²u) = f`
almost everywhere on `Ω` satisfies `‖u‖_{W^{2,p}(Ω)} ≤ C ‖f‖_{Lᵖ(Ω)}`. -/
theorem exists_norm_le_of_traceCLM_comp_iteratedGradient_eq_of_norm_le (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {lam : ℝ} (hlam : 0 < lam) (Λ : ℝ) :
    ∃ C : ℝ, ∀ A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) → ‖A‖ ≤ Λ →
        ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
          (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
          firstOrder 1 u ∈ w1p0Submodule volume Omega p →
          (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict Omega,
            traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) = f x) →
          ‖u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_hessianTraceL hp hp_top hΩ hbdry hlam Λ
  refine ⟨C, fun A hA hAΛ u f hu hf => ?_⟩
  have hT : hessianTraceL Omega A u = f := Lp.ext <| by
    filter_upwards [hessianTraceL_ae Omega A u, hf] with x h1 h2
    rw [h1, h2]
  exact hT ▸ hC A hA hAΛ u hu

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The `C²` boundary charts of a ball, in the form taken by the Dirichlet theory. -/
private theorem forall_frontier_exists_contDiff_graph_of_eq_ball (x₀ : WithLp 2 (ℝ × E)) {R : ℝ}
    (hR : 0 < R) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : (Omega : Set (WithLp 2 (ℝ × E))) = ball x₀ R) :
    ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst) := fun x hx => by
  rw [hΩ] at hx
  obtain ⟨e, φ, h₀, r₀, h1, h2, h3, h4, h5, h6⟩ :=
    exists_contDiff_graph_of_mem_frontier_ball x₀ hR (k := 2) hx
  refine ⟨e, φ, h₀, r₀, h1, h2, h3, h4, by exact_mod_cast h5, fun z hz => ?_⟩
  rw [← SetLike.mem_coe, hΩ]
  exact h6 z hz

/-- The weak Hessian of `u ∘ Φ` for the homothety `Φ y = R y + a` is `R² D²u ∘ Φ`. -/
private theorem iteratedGradient_compL_smul_add_const_ae (hp_top : p ≠ ⊤)
    {U V : Opens (WithLp 2 (ℝ × E))} {R : ℝ} {a : WithLp 2 (ℝ × E)} {L c : ℝ}
    (h : IsChangeOfVariables 2 U V (fun y => R • y + a) L c)
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) V p 2) :
    iteratedGradient 1 (compL h u) =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict U]
      fun y => R ^ 2 • iteratedGradient 1 u (R • y + a) := by
  filter_upwards [inner_iteratedGradient_compL_ae h hp_top u] with y hy
  refine ContinuousLinearMap.ext fun f => ext_inner_right ℝ fun g => ?_
  rw [hy, fderiv_smul_add_const]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, inner_zero_right,
    add_zero, smul_apply, ContinuousLinearMap.id_apply, map_smul,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

omit [Fact (1 ≤ p)] in
/-- Composing with the homothety `y ↦ R y + a`, `R > 0`, scales `Lᵖ` norms by at most
`(R ^ n)^(-1 / p)`, the power of the Jacobian. -/
private theorem norm_le_of_ae_eq_smul_comp_smul_add_const {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {U V : Opens (WithLp 2 (ℝ × E))} {R : ℝ} (hR : 0 < R)
    (a : WithLp 2 (ℝ × E)) (hmaps : MapsTo (fun y => R • y + a) U V)
    {g : Lp G p ((volume : Measure (WithLp 2 (ℝ × E))).restrict V)}
    {h : Lp G p ((volume : Measure (WithLp 2 (ℝ × E))).restrict U)} (κ : ℝ)
    (hgh : h =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict U]
      fun y => κ • g (R • y + a)) :
    ‖h‖ ≤ |κ| * ((R ^ finrank ℝ (WithLp 2 (ℝ × E)))⁻¹ ^ (1 / p).toReal) * ‖g‖ := by
  have hn : 0 < R ^ finrank ℝ (WithLp 2 (ℝ × E)) := pow_pos hR _
  have h1 := eLpNorm_comp_restrict_le (μ := (volume : Measure (WithLp 2 (ℝ × E)))) (p := p)
    (f := fun y => R • y + a) isOpen_univ (by fun_prop)
    (fun x _ y _ hxy => smul_right_injective _ hR.ne' (add_right_cancel hxy)) (subset_univ _)
    U.isOpen.measurableSet hn (fun x _ => (abs_det_fderiv_smul_add_const hR a x).ge) g
  have h2 : eLpNorm g p ((volume : Measure (WithLp 2 (ℝ × E))).restrict
      ((fun y => R • y + a) '' U)) ≤
        eLpNorm g p ((volume : Measure (WithLp 2 (ℝ × E))).restrict V) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono (image_subset_iff.2 hmaps) le_rfl)
  have h3 : eLpNorm h p ((volume : Measure (WithLp 2 (ℝ × E))).restrict U) =
      ‖κ‖ₑ * eLpNorm (fun y => g (R • y + a)) p
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict U) :=
    (eLpNorm_congr_ae hgh).trans (eLpNorm_const_smul κ (fun y => g (R • y + a)) p _)
  have hfin : (ENNReal.ofReal (R ^ finrank ℝ (WithLp 2 (ℝ × E))))⁻¹ ^ (1 / p).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hn).ne')
  have h4 := ENNReal.toReal_mono
    (ENNReal.mul_ne_top eNorm_ne_top (ENNReal.mul_ne_top hfin (Lp.eLpNorm_ne_top g)))
    (h3.trans_le (mul_le_mul_right (h1.trans (mul_le_mul_right h2 _)) _))
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_eNorm, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hn.le, ← Lp.norm_def, ← Lp.norm_def,
    Real.norm_eq_abs] at h4
  linarith

/-- The Jacobian factors of a homothety of ratio `R > 0` and of its inverse cancel. -/
private theorem homothety_factors_mul_eq (n : ℕ) {R : ℝ} (hR : 0 < R) (s C t : ℝ) :
    |R⁻¹ ^ 2| * (R⁻¹ ^ n)⁻¹ ^ s * (C * (|R ^ 2| * (R ^ n)⁻¹ ^ s * t)) = C * t := by
  have hm : 0 < R ^ n := pow_pos hR n
  have hcancel : (R⁻¹ ^ n)⁻¹ ^ s * (R ^ n)⁻¹ ^ s = 1 := by
    rw [inv_pow, inv_inv, Real.inv_rpow hm.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hm s).ne']
  have hR2 : |R⁻¹ ^ 2| * |R ^ 2| = 1 := by
    rw [← abs_mul, ← mul_pow, inv_mul_cancel₀ hR.ne', one_pow, abs_one]
  calc _ = (|R⁻¹ ^ 2| * |R ^ 2|) * ((R⁻¹ ^ n)⁻¹ ^ s * (R ^ n)⁻¹ ^ s) * (C * t) := by ring
    _ = C * t := by rw [hR2, hcancel, one_mul, one_mul]

/-- **Rescaling from the unit ball.** A Hessian estimate `‖D²v‖ ≤ C ‖tr (A ∘ D²v)‖`, `C ≥ 0`, on
`W^{2,p} ∩ W^{1,p}_0` of the unit ball gives the same estimate on every ball of positive radius:
for `v = u ∘ Φ`, `Φ y = R y + x₀`, both sides acquire the factor `R²` and reciprocal powers of the
Jacobian of `Φ`. -/
private theorem norm_iteratedGradient_le_of_eq_ball (hp_top : p ≠ ⊤)
    {A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {C : ℝ} (hC0 : 0 ≤ C)
    {B : Opens (WithLp 2 (ℝ × E))} (hB : (B : Set (WithLp 2 (ℝ × E))) = ball 0 1)
    (hC : ∀ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) B p 2,
      firstOrder 1 v ∈ w1p0Submodule volume B p →
        ‖iteratedGradient 1 v‖ ≤ C * ‖hessianTraceL B A v‖)
    {x₀ : WithLp 2 (ℝ × E)} {R : ℝ} (hR : 0 < R) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : (Omega : Set (WithLp 2 (ℝ × E))) = ball x₀ R)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    {f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)}
    (hu : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (hf : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict Omega,
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) = f x) :
    ‖iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  -- The homothety `Φ y = R y + x₀` from the unit ball onto `Ω`, and its inverse `Ψ`.
  have hΦ : IsChangeOfVariables 2 B Omega (fun y => R • y + x₀) R
      (R ^ finrank ℝ (WithLp 2 (ℝ × E))) :=
    IsChangeOfVariables.smul_add_const hR x₀ fun y hy => by
      rw [hB, mem_ball_zero_iff] at hy
      rw [hΩ, mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hR.le]
      nlinarith
  have hΨ : IsChangeOfVariables 2 Omega B (fun x => R⁻¹ • x + -(R⁻¹ • x₀)) R⁻¹
      (R⁻¹ ^ finrank ℝ (WithLp 2 (ℝ × E))) :=
    IsChangeOfVariables.smul_add_const (inv_pos.2 hR) _ fun x hx => by
      rw [hΩ, mem_ball, dist_eq_norm] at hx
      rw [hB, mem_ball_zero_iff]
      beta_reduce
      rw [← sub_eq_add_neg, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
        inv_mul_lt_one₀ hR]
      exact hx
  have hleft : LeftInvOn (fun x => R⁻¹ • x + -(R⁻¹ • x₀)) (fun y => R • y + x₀) B :=
    fun y _ => by simp [smul_add, smul_smul, inv_mul_cancel₀ hR.ne']
  have hright : RightInvOn (fun x => R⁻¹ • x + -(R⁻¹ • x₀)) (fun y => R • y + x₀) Omega :=
    fun x _ => by simp [smul_add, smul_smul, mul_inv_cancel₀ hR.ne']
  -- `v = u ∘ Φ` lies in `W^{2,p}(B) ∩ W^{1,p}_0(B)`, with `D²v = R² D²u ∘ Φ`, `D²u = R⁻² D²v ∘ Ψ`
  -- and `tr (A ∘ D²v) = R² f ∘ Φ`.
  set v := compL hΦ u
  have hv0 : firstOrder 1 v ∈ w1p0Submodule volume B p := by
    rw [firstOrder_compL hΦ hp_top]
    exact hΦ.w1pCompL_mem_w1p0Submodule_of_leftInvOn hp_top
      ((continuous_const_smul _).add continuous_const).continuousOn hΨ.mapsTo hleft hu
  have hDu : iteratedGradient 1 u =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict Omega]
      fun x => R⁻¹ ^ 2 • iteratedGradient 1 v (R⁻¹ • x + -(R⁻¹ • x₀)) := by
    have h := iteratedGradient_compL_smul_add_const_ae hp_top hΨ v
    rwa [show compL hΨ v = u from compL_compL_of_rightInvOn hΦ hΨ hright u] at h
  have hTv : hessianTraceL B A v =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict B]
      fun y => R ^ 2 • f (R • y + x₀) := by
    filter_upwards [hessianTraceL_ae B A v, iteratedGradient_compL_smul_add_const_ae hp_top hΦ u,
      hΦ.ae_comp hf] with y h1 h2 h3
    rw [h1, h2, ContinuousLinearMap.comp_smul, map_smul, h3]
  -- The two changes of variables scale the norms by reciprocal Jacobian factors.
  calc ‖iteratedGradient 1 u‖
      ≤ |R⁻¹ ^ 2| * (R⁻¹ ^ finrank ℝ (WithLp 2 (ℝ × E)))⁻¹ ^ (1 / p).toReal *
          ‖iteratedGradient 1 v‖ :=
        norm_le_of_ae_eq_smul_comp_smul_add_const (inv_pos.2 hR) _ hΨ.mapsTo _ hDu
    _ ≤ |R⁻¹ ^ 2| * (R⁻¹ ^ finrank ℝ (WithLp 2 (ℝ × E)))⁻¹ ^ (1 / p).toReal *
          (C * (|R ^ 2| * (R ^ finrank ℝ (WithLp 2 (ℝ × E)))⁻¹ ^ (1 / p).toReal * ‖f‖)) := by
        gcongr
        exact (hC v hv0).trans (mul_le_mul_of_nonneg_left
          (norm_le_of_ae_eq_smul_comp_smul_add_const hR x₀ hΦ.mapsTo _ hTv) hC0)
    _ = C * ‖f‖ := homothety_factors_mul_eq _ hR _ _ _

/-- **The a priori estimate for constant coefficients on balls, with a universal constant.** Let
`1 < p < ∞` and `0 < λ`. There is a constant `C`, depending only on `E`, `p`, `λ` and `Λ`, such
that for every constant matrix `A` with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `‖A‖ ≤ Λ`, every ball
`Ω = B(x₀, R)` and every `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` with `tr (A ∘ D²u) = f` almost everywhere
on `Ω`, the weak Hessian satisfies `‖D²u‖_{Lᵖ(Ω)} ≤ C ‖f‖_{Lᵖ(Ω)}`. -/
theorem exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_ball
    (hp : 1 < p) (hp_top : p ≠ ⊤) {lam : ℝ} (hlam : 0 < lam) (Λ : ℝ) :
    ∃ C : ℝ, ∀ A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) → ‖A‖ ≤ Λ →
        ∀ (x₀ : WithLp 2 (ℝ × E)) (R : ℝ) (Omega : Opens (WithLp 2 (ℝ × E))),
          (Omega : Set (WithLp 2 (ℝ × E))) = ball x₀ R →
          ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
            (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
            firstOrder 1 u ∈ w1p0Submodule volume Omega p →
            (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict Omega,
              traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) = f x) →
            ‖iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  -- The uniform estimate on the unit ball, with a nonnegative constant.
  set B : Opens (WithLp 2 (ℝ × E)) := ⟨ball 0 1, isOpen_ball⟩
  obtain ⟨C₀, hC₀⟩ := exists_norm_le_mul_norm_hessianTraceL (p := p) hp hp_top (Omega := B)
    isBounded_ball (forall_frontier_exists_contDiff_graph_of_eq_ball 0 one_pos rfl) hlam Λ
  refine ⟨max C₀ 0, fun A hA hAΛ x₀ R Omega hΩ u f hu hf => ?_⟩
  rcases le_or_gt R 0 with hR | hR
  · -- A ball of nonpositive radius is empty, and so is every `Lᵖ` function on it.
    have h0 : iteratedGradient 1 u = 0 := Lp.eq_zero_iff_ae_eq_zero.2
      (ae_restrict_of_forall_mem Omega.isOpen.measurableSet fun x hx => by
        rw [SetLike.mem_coe, ← SetLike.mem_coe, hΩ, ball_eq_empty.2 hR] at hx
        exact hx.elim)
    rw [h0, norm_zero]
    exact mul_nonneg (le_max_right _ _) (norm_nonneg _)
  exact norm_iteratedGradient_le_of_eq_ball hp_top (le_max_right C₀ 0) rfl
    (fun v hv => (norm_iteratedGradient_le 1 v).trans ((hC₀ A hA hAΛ v hv).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _)))) hR hΩ hu hf

/-- **The Dirichlet problem for constant coefficients on a ball.** Let `1 < p < ∞` and let `A` be a
constant matrix with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` for some `λ > 0`. On every ball `Ω = B(x₀, R)`, `R > 0`,
for every `f ∈ Lᵖ(Ω)` there is exactly one `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` with
`tr (A ∘ D²u) = f` almost everywhere on `Ω`. Its weak Hessian is bounded by a universal multiple
of `‖f‖` (in the `TauCeti` namespace,
`exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_ball`). -/
theorem existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_eq_of_ball
    (hp : 1 < p) (hp_top : p ≠ ⊤) {A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {lam : ℝ}
    (hlam : 0 < lam) (hA : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) {x₀ : WithLp 2 (ℝ × E)} {R : ℝ}
    (hR : 0 < R) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : (Omega : Set (WithLp 2 (ℝ × E))) = ball x₀ R)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)) :
    ∃! u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2,
      firstOrder 1 u ∈ w1p0Submodule volume Omega p ∧
      ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict Omega,
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) = f x := by
  obtain ⟨u, ⟨hu0, hu⟩, huniq⟩ :=
    existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_add_mul_eq hp
      hp_top (hΩ ▸ isBounded_ball) (forall_frontier_exists_contDiff_graph_of_eq_ball x₀ hR hΩ)
      (A := fun _ => A) (fun _ _ => continuousWithinAt_const) (fun _ _ => ⟨lam, hlam, hA⟩)
      (c := 0) (γ := 0) aestronglyMeasurable_const (ae_of_all _ fun _ => by simp)
      (ae_of_all _ fun _ => le_rfl) f
  refine ⟨u, ⟨hu0, hu.mono fun x hx => by simpa using hx⟩, fun w ⟨hw0, hw⟩ => huniq w
    ⟨hw0, hw.mono fun x hx => by simpa using hx⟩⟩

end TauCeti

end

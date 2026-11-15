/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Complex.ReProdIm
import TauCeti.Analysis.Complex.Wirtinger.SecondDerivative
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.Geometry.Symplectic.Floer.DerivativeConvergence

/-!
# Exponential convergence of the derivatives of Floer half-cylinders

Let `(V, ω)` be a symplectic vector space, `H` a `1`-periodic Hamiltonian and `J_t(x)` a
`1`-periodic family of almost complex structures tamed by `ω`, and let `u` be a smooth
finite-energy solution of the Floer equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on a
half-cylinder `s > a`, with loops in a compact set, whose loops `u(s, ·)` converge to a
nondegenerate orbit `x` as `s → ∞`. By
`TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp` the loops converge exponentially,
`‖u(s, t) - x(t)‖ ≤ C e^{-κ s}`. This file shows that the convergence is exponential in `C¹`: for
some `κ > 0` and `C`, eventually

`‖u(s, t) - x(t)‖ ≤ C e^{-κ s}` and `‖du(s, t) - ((σ, τ) ↦ τ X_{H_t}(x(t)))‖ ≤ C e^{-κ s}`

for `t ∈ [0, 1]`, where `(σ, τ) ↦ τ X_{H_t}(x(t)) = τ x'(t)` is the derivative of the stationary
cylinder over `x`
(`TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_le_exp`). These
are the bounds that the pre-gluing estimate
`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le` assumes at the positive
end of a solution, and the exponential decay of `u - x` and its derivative that weighted Sobolev
setups of the linearized operator on the end rely on.

**A uniform Hölder bound for the derivative.** The interior `W^{2,4}` estimate for
Cauchy–Riemann equations (`TauCeti.exists_eLpNorm_fderiv_fderiv_apply_le`) and Morrey's
inequality give a Hölder modulus with exponent `1 / 2` for the derivative of a solution, in a
complex frame in which the almost complex structure is close to `i`. Near a point `(y₀, x₀)` with
`J(y₀, x₀)² = -1` such a frame exists, so solutions on a small disc about `y₀`, with values near
`x₀` and derivatives bounded by `L`, satisfy `‖du(z) - du(y)‖ ≤ C √|z - y|`. For data that are
periodic under `z ↦ z + 1` and `z ↦ z + i`, finitely many such discs cover the compact set
`[0, 1]² × K`, so the estimate holds with one constant on the whole plane
(`TauCeti.Floer.exists_pos_forall_norm_fderiv_sub_le_mul_sqrt_of_periodic`).

**From Hölder to exponential decay.** Finite-energy Floer half-cylinders have bounded derivatives
(`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`), so in the complex coordinate of
`TauCeti.SymplecticForm.exists_complexCoordinate` the uniform Hölder bound applies along the end.
On `[s, s + h]` the map `σ ↦ u(σ, t) - x(t)` is at most `C e^{-3κ s}` and its derivative
oscillates by at most `C' √h`, so `h ‖∂_s u(s, t)‖ ≤ 2 C e^{-3κ s} + C' h √h`
(`TauCeti.mul_norm_deriv_le_of_norm_le_of_norm_deriv_sub_le`). The step `h = e^{-2κ s}` gives
`‖∂_s u(s, t)‖ ≤ (2 C + C') e^{-κ s}`. The Floer equation turns this into the bound on
`∂_t u - X_{H_t}(u) = J_t(u) ∂_s u`, and `X_{H_t}` is Lipschitz near `x`, which bounds
`∂_t u - x'`.

## Main results

* `TauCeti.Floer.exists_pos_forall_norm_fderiv_sub_le_mul_sqrt_of_periodic`: for doubly periodic
  data, solutions with values in a compact set and derivatives bounded by `L` have derivatives
  with a common Hölder modulus `C √|z - y|`.
* `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_le_exp`: a
  smooth finite-energy Floer half-cylinder asymptotic to a nondegenerate orbit converges to it
  exponentially in `C¹`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the exponential decay of finite-energy Floer trajectories
  and their derivatives at nondegenerate orbits.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix B.4 (elliptic bootstrapping).
-/

public section

open Complex Filter Function Metric MeasureTheory Set Topology
open scoped ENNReal NNReal Real

namespace TauCeti.Floer

open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)}

omit [FiniteDimensional ℝ V] in
/-- **Frames in which the almost complex structure is nearly `i`.** If `Φ : ℂᵐ → V` conjugates
`J(y₀, x₀)` to multiplication by `i`, then for every `δ > 0` there is a ball about `(y₀, x₀)`,
inside `W`, on which the conjugates `Φ⁻¹ J(q) Φ` are `δ`-close to `i`. -/
private theorem exists_pos_forall_norm_symm_apply_sub_I_smul_le (hW : IsOpen W)
    (hJ : ContinuousOn J W) {y₀ : ℂ} {x₀ : V} (hmem : (y₀, x₀) ∈ W) {m : ℕ}
    {Φ : EuclideanSpace ℂ (Fin m) ≃L[ℝ] V} (hΦ : ∀ w, J (y₀, x₀) (Φ w) = Φ (I • w)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ ε > 0, ∀ q, dist q (y₀, x₀) < ε →
      q ∈ W ∧ ∀ w, ‖Φ.symm (J q (Φ w)) - I • w‖ ≤ δ * ‖w‖ := by
  let C : (V →L[ℝ] V) ≃L[ℝ] (EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)) :=
    Φ.symm.arrowCongr Φ.symm
  have hC (A : V →L[ℝ] V) (w : EuclideanSpace ℂ (Fin m)) : C A w = Φ.symm (A (Φ w)) := by
    simp [C]
  have hJy : ContinuousAt (fun q ↦ C (J q)) (y₀, x₀) :=
    C.continuous.continuousAt.comp (hJ.continuousAt (hW.mem_nhds hmem))
  obtain ⟨ε, hε, hεW⟩ := Metric.eventually_nhds_iff.1
    ((hJy.eventually_mem (ball_mem_nhds _ hδ)).and (hW.eventually_mem hmem))
  refine ⟨ε, hε, fun q hq ↦ ⟨(hεW hq).2, fun w ↦ ?_⟩⟩
  have hw : I • w = C (J (y₀, x₀)) w := by rw [hC, hΦ, ContinuousLinearEquiv.symm_apply_apply]
  rw [← hC, hw, ← sub_apply]
  exact ((C (J q) - C (J (y₀, x₀))).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (mem_ball_iff_norm.1 (hεW hq).1).le (norm_nonneg w))

/-- **A local Hölder estimate for the derivative.** Let `J` and `X` be `C¹` on an open
`W ⊆ ℂ × V`, and let `(y₀, x₀) ∈ W` with `J(y₀, x₀)² = -1`. For every bound `L` there are a radius
`r ∈ (0, 1 / 2]`, a closeness `η > 0` and a constant `C ≥ 0` with the following property. Let `u` be
a smooth solution of `∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` on the disc `B_r(y₀)`, along
which `J² = -1`, with `‖du‖ ≤ L` there. If `z ∈ B_{r/16}(y₀)` and `u z` is `η`-close to `x₀`, then
`‖du(z) - du(y)‖ ≤ C √|y - z|` for `|y - z| < r / 16`. In a frame `Φ : ℂᵐ → V` in which
`J(y₀, x₀)` is multiplication by `i`, the solution `Φ⁻¹ ∘ u` has second derivatives bounded in
`L⁴`, and Morrey's inequality turns these bounds into the Hölder estimate. -/
private theorem exists_forall_norm_fderiv_sub_le_mul_sqrt_of_mem (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) {y₀ : ℂ} {x₀ : V} (hmem : (y₀, x₀) ∈ W)
    (hJsq : ∀ w, J (y₀, x₀) (J (y₀, x₀) w) = -w) (L : ℝ) :
    ∃ r > 0, r ≤ 1 / 2 ∧ ∃ η > 0, ∃ C, 0 ≤ C ∧ ∀ ⦃u : ℂ → V⦄, ContDiffOn ℝ ∞ u (ball y₀ r) →
      (∀ z ∈ ball y₀ r, ∀ w, J (z, u z) (J (z, u z) w) = -w) →
      (∀ z ∈ ball y₀ r, fderiv ℝ u z I - X (z, u z) I =
        J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1)) →
      (∀ z ∈ ball y₀ r, ‖fderiv ℝ u z‖ ≤ L) → ∀ z ∈ ball y₀ (r / 16), dist (u z) x₀ < η →
      ∀ y, dist y z < r / 16 → ‖fderiv ℝ u z - fderiv ℝ u y‖ ≤ C * √(dist y z) := by
  -- A frame `Φ : ℂᵐ → V` in which `J (y₀, x₀)` is multiplication by `i`, the conjugation
  -- `C A = Φ⁻¹ A Φ` it induces on endomorphisms, and a ball about `(y₀, x₀)` on which `C (J q)`
  -- is close enough to `i` for the interior `W^{2,4}` estimate.
  obtain ⟨m, Φ, hΦ⟩ :=
    (J (y₀, x₀)).exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul
      (ContinuousLinearMap.ext fun w ↦ by simpa using hJsq w)
  let C : (V →L[ℝ] V) ≃L[ℝ] (EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)) :=
    Φ.symm.arrowCongr Φ.symm
  have hC (A : V →L[ℝ] V) (w : EuclideanSpace ℂ (Fin m)) : C A w = Φ.symm (A (Φ w)) := by
    simp [C]
  obtain ⟨δ, hδ0, hδ⟩ := exists_eLpNorm_fderiv_fderiv_apply_le (F := EuclideanSpace ℂ (Fin m))
    (p := ((4 : ℝ≥0) : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top
  obtain ⟨c, hc, hhol⟩ := exists_forall_norm_fderiv_sub_le_mul_sqrt (F := EuclideanSpace ℂ (Fin m))
  obtain ⟨ε₀, hε₀, hεW⟩ := exists_pos_forall_norm_symm_apply_sub_I_smul_le hW hJ.continuousOn hmem
    (fun w ↦ by simpa using congr($hΦ w)) (NNReal.coe_pos.2 hδ0)
  obtain ⟨ε, hε, hεε₀, hε1⟩ : ∃ ε > 0, ε ≤ ε₀ ∧ ε ≤ 1 :=
    ⟨min ε₀ 1, lt_min hε₀ one_pos, min_le_left _ _, min_le_right _ _⟩
  set L' := max L 0
  have hL' : 0 ≤ L' := le_max_right _ _
  obtain ⟨η, hη, hηε⟩ : ∃ η > 0, η = ε / 4 := ⟨ε / 4, by positivity, rfl⟩
  -- The radius `r` is small enough that `u` moves by at most `η` over distance `2 r`.
  obtain ⟨r, hr, hrη, hLr⟩ : ∃ r > 0, r ≤ η / 2 ∧ L' * (2 * r) ≤ η := by
    refine ⟨η / (2 * (L' + 1)), by positivity,
      div_le_div_of_nonneg_left hη.le two_pos (by linarith), ?_⟩
    rw [show L' * (2 * (η / (2 * (L' + 1)))) = η * (L' / (L' + 1)) by field_simp]
    exact mul_le_of_le_one_right hη.le ((div_le_one (by positivity)).2 (by linarith))
  refine ⟨r, hr, by linarith, η, hη, ?_⟩
  -- Bounds for the derivatives of the coefficients along the graphs of all admissible maps, on
  -- `closedBall y₀ (r / 2)`.
  set h : ℂ × V → V := fun q ↦ X q 1 + J q (X q I)
  have hh : ContDiffOn ℝ 1 h W :=
    (hX.clm_apply contDiffOn_const).add (hJ.clm_apply (hX.clm_apply contDiffOn_const))
  have hKW : closedBall y₀ (r / 2) ×ˢ closedBall x₀ (ε / 2) ⊆ W := fun q hq ↦ by
    refine (hεW q ?_).1
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.1 hq.1).trans_lt (by linarith),
      (mem_closedBall.1 hq.2).trans_lt (by linarith)⟩
  set P : (ℂ → V) → Prop := fun u ↦ MapsTo u (closedBall y₀ (r / 2)) (closedBall x₀ (ε / 2)) ∧
    (∀ z ∈ closedBall y₀ (r / 2), DifferentiableAt ℝ u z) ∧
    ∀ z ∈ closedBall y₀ (r / 2), ‖fderiv ℝ u z‖ ≤ L'
  obtain ⟨BJ, hBJ⟩ := exists_bound_norm_fderiv_comp_graph (ι := {u // P u}) (u := Subtype.val) hW
    hJ (isCompact_closedBall _ _) (isCompact_closedBall _ _) hKW (fun u ↦ u.2.1)
    (fun u ↦ u.2.2.1) (fun u ↦ u.2.2.2)
  obtain ⟨Bh, hBh⟩ := exists_bound_norm_fderiv_comp_graph (ι := {u // P u}) (u := Subtype.val) hW
    hh (isCompact_closedBall _ _) (isCompact_closedBall _ _) hKW (fun u ↦ u.2.1)
    (fun u ↦ u.2.2.1) (fun u ↦ u.2.2.2)
  set M : ℝ := max (‖(C : (V →L[ℝ] V) →L[ℝ]
    EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * BJ)
    (‖(Φ.symm : V →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * Bh)
  set Lv : ℝ := ‖(Φ.symm : V →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * L'
  obtain ⟨C₀, hC₀⟩ := hδ (U := ball y₀ (r / 2)) (K := closedBall y₀ (r / 4)) isOpen_ball
    (isCompact_closedBall _ _) (closedBall_subset_ball (by linarith)) M.toNNReal Lv.toNNReal
  refine ⟨‖(Φ : EuclideanSpace ℂ (Fin m) →L[ℝ] V)‖ * (c * C₀), by positivity,
    fun u hu hJsq' hCR hL z hz hzx y hy ↦ ?_⟩
  have hzr : z ∈ ball y₀ r := ball_subset_ball (by linarith) hz
  have hdu : ∀ ζ ∈ ball y₀ r, DifferentiableAt ℝ u ζ := fun ζ hζ ↦
    (hu.differentiableOn (by simp) ζ hζ).differentiableAt (isOpen_ball.mem_nhds hζ)
  have hL'u : ∀ ζ ∈ ball y₀ r, ‖fderiv ℝ u ζ‖ ≤ L' := fun ζ hζ ↦ (hL ζ hζ).trans (le_max_left _ _)
  -- `u` stays `ε / 2`-close to `x₀` on `ball y₀ r`, so its graph stays in the ball about
  -- `(y₀, x₀)` where `C (J q)` is `δ`-close to `i`.
  have hgr : ∀ ζ ∈ ball y₀ r, dist (u ζ) x₀ < ε / 2 ∧ dist (ζ, u ζ) (y₀, x₀) < ε₀ := by
    intro ζ hζ
    have h1 : ‖u ζ - u z‖ ≤ L' * ‖ζ - z‖ :=
      (convex_ball y₀ r).norm_image_sub_le_of_norm_fderiv_le hdu hL'u hzr hζ
    have h2 : ‖ζ - z‖ ≤ 2 * r := by
      rw [← dist_eq_norm]
      linarith [dist_triangle_right ζ z y₀, mem_ball.1 hζ, mem_ball.1 hz]
    have h3 : dist (u ζ) x₀ < ε / 2 := by
      rw [dist_eq_norm] at hzx ⊢
      calc ‖u ζ - x₀‖ ≤ ‖u ζ - u z‖ + ‖u z - x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < L' * (2 * r) + η :=
          add_lt_add_of_le_of_lt (h1.trans (mul_le_mul_of_nonneg_left h2 hL')) hzx
        _ ≤ ε / 2 := by linarith
    refine ⟨h3, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.1 hζ).trans_le (by linarith), h3.trans_le (by linarith)⟩
  have hsub2 : closedBall y₀ (r / 2) ⊆ ball y₀ r := closedBall_subset_ball (by linarith)
  have hU : ball y₀ (r / 2) ⊆ ball y₀ r := ball_subset_ball (by linarith)
  have hP : P u := ⟨fun ζ hζ ↦ (hgr ζ (hsub2 hζ)).1.le, fun ζ hζ ↦ hdu ζ (hsub2 hζ),
    fun ζ hζ ↦ hL'u ζ (hsub2 hζ)⟩
  -- In the frame `Φ`, the second derivatives are bounded in `L⁴` on `closedBall y₀ (r / 4)`.
  have hD : ∀ e : ℂ, ‖e‖ ≤ 1 → eLpNorm (fderiv ℝ (fun ζ ↦ fderiv ℝ (Φ.symm ∘ u) ζ e))
      ((4 : ℝ≥0) : ℝ≥0∞) (volume.restrict (closedBall y₀ (r / 4))) ≤ C₀ := by
    refine hC₀ (Φ.symm ∘ u) (Φ.symm ∘ fun ζ ↦ h (ζ, u ζ)) (C ∘ fun ζ ↦ J (ζ, u ζ))
      (Φ.symm.contDiff.comp_contDiffOn (hu.mono hU))
      (fun ζ hζ ↦ (C.differentiableAt.comp ζ (((hJ.differentiableOn one_ne_zero).differentiableAt
        (hW.mem_nhds (hεW _ (hgr ζ (hU hζ)).2).1)).comp ζ
          (differentiableAt_id.prodMk (hdu ζ (hU hζ))))).differentiableWithinAt)
      (fun ζ hζ w ↦ by rw [comp_apply, hC]; exact (hεW _ (hgr ζ (hU hζ)).2).2 w)
      (fun ζ hζ ↦ ?_) (fun ζ hζ ↦ ?_) (fun ζ hζ ↦ ?_) (fun ζ hζ ↦ ?_)
    · rw [C.comp_fderiv]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left
        (hBJ ⟨u, hP⟩ ζ (ball_subset_closedBall hζ)) (norm_nonneg _)).trans
          ((le_max_left _ _).trans (Real.le_coe_toNNReal _)))
    · rw [Φ.symm.comp_fderiv]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left
        (hBh ⟨u, hP⟩ ζ (ball_subset_closedBall hζ)) (norm_nonneg _)).trans
          ((le_max_right _ _).trans (Real.le_coe_toNNReal _)))
    · rw [Φ.symm.comp_fderiv]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left
        (hL'u ζ (hU hζ)) (norm_nonneg _)).trans (Real.le_coe_toNNReal _))
    · simp only [Φ.symm.comp_fderiv, Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, hC, ContinuousLinearEquiv.apply_symm_apply, ← map_add]
      exact congrArg Φ.symm
        (fderiv_one_add_eq_of_fderiv_I_sub_eq (hJsq' ζ (hU hζ)) (hCR ζ (hU hζ)))
  -- Morrey's inequality on the disc of radius `2 |y - z|` about `z`, back in `V`.
  have hsub : ball z (2 * dist y z) ⊆ closedBall y₀ (r / 4) := fun ζ hζ ↦ by
    rw [mem_closedBall]
    linarith [dist_triangle ζ z y₀, mem_ball.1 hζ, mem_ball.1 hz]
  have hmor := hhol (C := C₀) (((Φ.symm.contDiff.comp_contDiffOn hu).of_le (by simp)).mono
    (hsub.trans (closedBall_subset_ball (by linarith))))
    fun e he ↦ (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans (hD e he)
  have hfd (ζ : ℂ) : fderiv ℝ u ζ =
      (Φ : EuclideanSpace ℂ (Fin m) →L[ℝ] V).comp (fderiv ℝ (Φ.symm ∘ u) ζ) := by
    rw [← Φ.comp_fderiv]
    congr 1
    funext ζ
    simp
  rw [hfd z, hfd y, ← ContinuousLinearMap.comp_sub]
  calc _ ≤ ‖(Φ : EuclideanSpace ℂ (Fin m) →L[ℝ] V)‖ *
        ‖fderiv ℝ (Φ.symm ∘ u) z - fderiv ℝ (Φ.symm ∘ u) y‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(Φ : EuclideanSpace ℂ (Fin m) →L[ℝ] V)‖ * (c * C₀ * √(dist y z)) := by gcongr
    _ = _ := by ring

/-- **A uniform Hölder estimate for the derivative with doubly periodic data.** Let `J` and `X` be
`C¹` on an open set `W ⊆ ℂ × V` containing `ℂ × K` for a compact `K ⊆ V`, with `J(z, x)² = -1` on
`ℂ × K`, and let `J(·, x)` and `X(·, x)` be periodic under `z ↦ z + 1` and `z ↦ z + i`. For every
bound `L` there are `ρ > 0` and `C ≥ 0` with the following property. Let `u` be a smooth solution of
`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` on the unit disc about `z`, with image in `K` and
`‖du‖ ≤ L` there. Then `‖du(z) - du(y)‖ ≤ C √|y - z|` whenever `|y - z| < ρ`. -/
theorem exists_pos_forall_norm_fderiv_sub_le_mul_sqrt_of_periodic (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) {K : Set V} (hK : IsCompact K)
    (hKW : univ ×ˢ K ⊆ W) (hJsq : ∀ z, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hJ1 : ∀ x, Periodic (fun z ↦ J (z, x)) 1) (hJI : ∀ x, Periodic (fun z ↦ J (z, x)) I)
    (hX1 : ∀ x, Periodic (fun z ↦ X (z, x)) 1) (hXI : ∀ x, Periodic (fun z ↦ X (z, x)) I)
    (L : ℝ) :
    ∃ ρ > 0, ∃ C, 0 ≤ C ∧ ∀ ⦃u : ℂ → V⦄ ⦃z y : ℂ⦄, ContDiffOn ℝ ∞ u (ball z 1) →
      (∀ w ∈ ball z 1, fderiv ℝ u w I - X (w, u w) I =
        J (w, u w) (fderiv ℝ u w 1 - X (w, u w) 1)) →
      (∀ w ∈ ball z 1, u w ∈ K) → (∀ w ∈ ball z 1, ‖fderiv ℝ u w‖ ≤ L) → dist y z < ρ →
      ‖fderiv ℝ u z - fderiv ℝ u y‖ ≤ C * √(dist y z) := by
  -- The local estimate at each point of the compact set `[0, 1]² × K`, which meets every lattice
  -- orbit, and a finite cover by the neighbourhoods where it applies.
  set Q : Set (ℂ × V) := (Icc 0 1 ×ℂ Icc 0 1) ×ˢ K
  have hQ : IsCompact Q := (isCompact_Icc.reProdIm isCompact_Icc).prod hK
  choose! r hr hr1 η hη C hC0 hC using fun q (hq : q ∈ Q) ↦
    exists_forall_norm_fderiv_sub_le_mul_sqrt_of_mem (y₀ := q.1) (x₀ := q.2) hW hJ hX
      (hKW ⟨mem_univ _, hq.2⟩) (hJsq q.1 q.2 hq.2) L
  obtain ⟨t, htQ, hcover⟩ := hQ.elim_nhds_subcover
    (fun q ↦ ball q.1 (r q / 16) ×ˢ ball q.2 (η q))
    fun q hq ↦ prod_mem_nhds (ball_mem_nhds _ (by linarith [hr q hq])) (ball_mem_nhds _ (hη q hq))
  obtain ⟨ρ, hρ, hρr⟩ : ∃ ρ > 0, ∀ q ∈ t, ρ ≤ r q / 16 := by
    rcases t.eq_empty_or_nonempty with rfl | ht
    · exact ⟨1, one_pos, by simp⟩
    · exact ⟨t.inf' ht fun q ↦ r q / 16, (Finset.lt_inf'_iff ht).2 fun q hq ↦ by
        linarith [hr q (htQ q hq)], fun q hq ↦ Finset.inf'_le _ hq⟩
  refine ⟨ρ, hρ, ∑ q ∈ t, C q, Finset.sum_nonneg fun q hq ↦ hC0 q (htQ q hq),
    fun u z y hu hCR huK hL hyz ↦ ?_⟩
  -- Translate `z` by a lattice vector `w` into `[0, 1]²`; the data do not change.
  set w : ℂ := (⌊z.re⌋ : ℂ) + ⌊z.im⌋ * I
  have hJw (ζ : ℂ) (x : V) : J (ζ + w, x) = J (ζ, x) := by
    simpa only [mul_one] using (hJ1 x).int_mul_add_int_mul (hJI x) ⌊z.re⌋ ⌊z.im⌋ ζ
  have hXw (ζ : ℂ) (x : V) : X (ζ + w, x) = X (ζ, x) := by
    simpa only [mul_one] using (hX1 x).int_mul_add_int_mul (hXI x) ⌊z.re⌋ ⌊z.im⌋ ζ
  have hzQ : (z - w, u z) ∈ Q :=
    ⟨reProdIm_subset_iff.2 (prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
      (sub_floor_mem_reProdIm z), huK z (mem_ball_self one_pos)⟩
  obtain ⟨q, hqt, hqz⟩ := mem_iUnion₂.1 (hcover hzQ)
  have hqQ := htQ q hqt
  -- The translate `v = u (· + w)` solves the same equation on the disc about `q.1`.
  set v : ℂ → V := fun ζ ↦ u (ζ + w)
  have hdv (ζ : ℂ) : fderiv ℝ v ζ = fderiv ℝ u (ζ + w) := fderiv_comp_add_right w
  have hmaps : MapsTo (· + w) (ball q.1 (r q)) (ball z 1) := fun ζ hζ ↦ by
    have h1 : dist (ζ + w) z = dist ζ (z - w) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      ring
    rw [mem_ball, h1]
    linarith [dist_triangle ζ q.1 (z - w), dist_comm (z - w) q.1, mem_ball.1 hζ,
      mem_ball.1 hqz.1, hr1 q hqQ]
  have h := hC q hqQ (u := v)
    (hu.comp (by fun_prop : ContDiff ℝ ∞ fun ζ : ℂ ↦ ζ + w).contDiffOn hmaps)
    (fun ζ hζ x ↦ hJsq ζ (v ζ) (huK _ (hmaps hζ)) x)
    (fun ζ hζ ↦ by rw [hdv]; simpa only [v, hJw, hXw] using hCR _ (hmaps hζ))
    (fun ζ hζ ↦ by rw [hdv]; exact hL _ (hmaps hζ))
    (z - w) hqz.1 (by simpa only [v, sub_add_cancel, mem_ball] using hqz.2)
    (y - w) (by rw [dist_sub_right]; exact hyz.trans_le (hρr q hqt))
  rw [hdv, hdv, sub_add_cancel, sub_add_cancel, dist_sub_right] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun q hq ↦ hC0 q (htQ q hq)) hqt) (Real.sqrt_nonneg _))

end TauCeti.Floer

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V}
  {W : Set (ℝ × V)} {K : Set V} {u : ℝ × ℝ → V} {x : ℝ → V} {a : ℝ}

/-- **The derivative of a Floer solution from its `s`-derivative.** At a point `z` where `u` solves
the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0`, with `‖J v‖ ≤ M ‖v‖`, the derivative of
`u` is within `(1 + M) ‖∂_s u‖ + L ‖u - y‖` of the derivative `(σ, τ) ↦ τ X_{H_t}(y)` of the
stationary cylinder over `y`, whenever `X_{H_t}` changes by at most `L ‖u - y‖` between `y` and
`u(z)`. -/
private theorem norm_fderiv_sub_smulRight_le {Jz : AlmostComplexStructure V} {M L : ℝ}
    {z : ℝ × ℝ} {y : V}
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) Jz
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hJM : ∀ v, ‖Jz v‖ ≤ M * ‖v‖)
    (hX : ‖ω.hamiltonianVectorField (H z.2) (u z) - ω.hamiltonianVectorField (H z.2) y‖ ≤
      L * ‖u z - y‖) :
    ‖fderiv ℝ u z - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (ω.hamiltonianVectorField (H z.2) y)‖ ≤ (1 + M) * ‖fderiv ℝ u z (1, 0)‖ + L * ‖u z - y‖ := by
  rw [isComplexLinearMap_perturbedFDeriv_iff] at hfloer
  simp only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero, stdComplexLineReal_eq,
    stdComplexLineImag_eq] at hfloer
  -- The defect `∂_t u - X_{H_t}(u)` is `J ∂_s u`.
  have hdt : fderiv ℝ u z (0, 1) - ω.hamiltonianVectorField (H z.2) (u z) =
      Jz (fderiv ℝ u z (1, 0)) := by
    have h := congrArg Jz hfloer
    rw [map_add, AlmostComplexStructure.apply_apply, map_zero, add_neg_eq_zero] at h
    exact h.symm
  refine (ContinuousLinearMap.opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one _).trans ?_
  have h01 : (fderiv ℝ u z - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (ω.hamiltonianVectorField (H z.2) y)) (0, 1) =
      Jz (fderiv ℝ u z (1, 0)) + (ω.hamiltonianVectorField (H z.2) (u z) -
        ω.hamiltonianVectorField (H z.2) y) := by
    rw [← hdt]
    simp
  rw [h01]
  have h10 : (fderiv ℝ u z - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (ω.hamiltonianVectorField (H z.2) y)) (1, 0) = fderiv ℝ u z (1, 0) := by
    simp
  rw [h10]
  linarith [norm_add_le_of_le (hJM (fderiv ℝ u z (1, 0))) hX]

omit [FiniteDimensional ℝ V] in
/-- **The `s`-derivative from the values and a Hölder bound.** If on `[s, s + E²]`, for `E > 0`, the
loops of `u` are within `C₀ E³` of `x` and the derivative of `u` along `σ ↦ (σ, t)` stays within
`D E` of its value at `(s, t)`, then `‖∂_s u(s, t)‖ ≤ (2 C₀ + D) E`. -/
private theorem norm_fderiv_apply_one_zero_le {s t E C₀ D : ℝ} (hE : 0 < E)
    (hdiff : ∀ σ ∈ Icc s (s + E ^ 2), DifferentiableAt ℝ u (σ, t))
    (hu : ∀ σ ∈ Icc s (s + E ^ 2), ‖u (σ, t) - x t‖ ≤ C₀ * E ^ 3)
    (hD : ∀ σ ∈ Icc s (s + E ^ 2), ‖fderiv ℝ u (σ, t) - fderiv ℝ u (s, t)‖ ≤ D * E) :
    ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ (2 * C₀ + D) * E := by
  have hf : ∀ σ ∈ Icc s (s + E ^ 2), HasDerivWithinAt (fun σ ↦ u (σ, t) - x t)
      (fderiv ℝ u (σ, t) (1, 0)) (Icc s (s + E ^ 2)) σ := fun σ hσ ↦
    (((hdiff σ hσ).hasFDerivAt.comp_hasDerivAt σ
      ((hasDerivAt_id σ).prodMk (hasDerivAt_const σ t))).sub_const (x t)).hasDerivWithinAt
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
  have key := mul_norm_deriv_le_of_norm_le_of_norm_deriv_sub_le (D := D * E) (by positivity) hf hu
    fun σ hσ ↦ by
      rw [← sub_apply]
      calc _ ≤ ‖fderiv ℝ u (σ, t) - fderiv ℝ u (s, t)‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ D * E := by rw [h10, mul_one]; exact hD σ hσ
  have hE2 : 0 < E ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hE2
  calc E ^ 2 * ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ 2 * (C₀ * E ^ 3) + D * E * E ^ 2 := key
    _ = E ^ 2 * ((2 * C₀ + D) * E) := by ring

/-- Along the end of a smooth finite-energy Floer half-cylinder, the derivative of `u` has a
Hölder modulus with exponent `1 / 2` in `s`, uniformly in `t`. In the complex coordinate of
`TauCeti.SymplecticForm.exists_complexCoordinate` this is
`TauCeti.Floer.exists_pos_forall_norm_fderiv_sub_le_mul_sqrt_of_periodic`, which applies since
`du` is bounded on the end (`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`). -/
private theorem exists_pos_forall_norm_fderiv_sub_le_mul_sqrt_of_floer
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ ρ > 0, ∃ C, 0 ≤ C ∧ ∀ s σ t : ℝ, a + 2 ≤ s → s ≤ σ → σ - s < ρ →
      ‖fderiv ℝ u (σ, t) - fderiv ℝ u (s, t)‖ ≤ C * √(σ - s) := by
  obtain ⟨M, hM⟩ := exists_forall_norm_fderiv_le_of_floer hH hHper hW hJ hJper hK hKW hJt
    (hu.of_le (by simp)) hper huK hfloer hE (lt_add_one a)
  obtain ⟨Jc, Xc, Wc, hWc, hJc, hXc, hKWc, hJsq, hJ1, hJI, hX1, hXI, hcoord⟩ :=
    exists_complexCoordinate (ω := ω) hH hHper hW hJ hJper hKW
  obtain ⟨v, hv, -, hCR, hvK, hdu, -⟩ := hcoord isOpen_Ioi hu hper huK hfloer
  set e : ℂ →L[ℝ] ℝ × ℝ := (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)
  set e' : ℝ × ℝ →L[ℝ] ℂ := (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)
  obtain ⟨ρ, hρ, C, hC0, hC⟩ := Floer.exists_pos_forall_norm_fderiv_sub_le_mul_sqrt_of_periodic
    hWc (hJc.of_le (by norm_num)) (hXc.of_le (by norm_num)) hK hKWc hJsq hJ1 hJI hX1 hXI
    (M * ‖e‖)
  refine ⟨ρ, hρ, C * ‖e'‖, by positivity, fun s σ t hs hsσ hσ ↦ ?_⟩
  set z : ℂ := e' (s, t)
  have hz : z.re = s := by simp [z, e']
  have hball : ball z 1 ⊆ re ⁻¹' Ioi (a + 1) := fun ζ hζ ↦ by
    have := abs_re_le_norm (ζ - z)
    rw [mem_ball, dist_eq_norm] at hζ
    rw [sub_re, abs_le, hz] at this
    rw [mem_preimage, mem_Ioi]
    linarith
  have hre (ζ : ℂ) (hζ : a + 1 < ζ.re) : e ζ ∈ Ioi a ×ˢ (univ : Set ℝ) :=
    ⟨mem_Ioi.2 (by simpa [e] using (by linarith : a < ζ.re)), mem_univ _⟩
  -- `du` is bounded on the end, hence so is `dv` on the unit disc about `z`.
  have hdv : ∀ ζ ∈ ball z 1, ‖fderiv ℝ v ζ‖ ≤ M * ‖e‖ := fun ζ hζ ↦ by
    have hv' : fderiv ℝ v ζ = (fderiv ℝ u (e ζ)).comp e := by
      rw [hdu (e ζ) (hre ζ (hball hζ))]
      ext w
      simp [e, e', equivRealProdCLM_symm_apply, re_add_im]
    rw [hv']
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
      (hM _ (by simpa [e] using (show a + 1 < ζ.re from hball hζ).le)) (norm_nonneg _))
  have hdist : dist (e' (σ, t)) z = σ - s := by
    rw [dist_eq_norm, ← map_sub, Prod.mk_sub_mk, sub_self]
    have he' : e' (σ - s, 0) = ((σ - s : ℝ) : ℂ) := by simp [e', equivRealProdCLM_symm_apply]
    rw [he', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hsσ)]
  have hball' : ball z 1 ⊆ re ⁻¹' Ioi a := fun ζ hζ ↦ by
    rw [mem_preimage, mem_Ioi]
    linarith [show a + 1 < ζ.re from hball hζ]
  have h := hC (u := v) (z := z) (y := e' (σ, t)) (hv.mono hball')
    (fun ζ hζ ↦ hCR ζ (hball' hζ)) (fun ζ hζ ↦ hvK ζ (hball' hζ)) hdv (by rw [hdist]; exact hσ)
  rw [hdist] at h
  have hσa : (σ, t) ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨mem_Ioi.2 (by linarith), mem_univ _⟩
  have hsa : (s, t) ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨mem_Ioi.2 (by linarith), mem_univ _⟩
  rw [hdu _ hσa, hdu _ hsa, ← ContinuousLinearMap.sub_comp]
  calc _ ≤ ‖fderiv ℝ v (e' (σ, t)) - fderiv ℝ v z‖ * ‖e'‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * √(σ - s) * ‖e'‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

/-- **Exponential convergence in `C⁰`.** Under the hypotheses of
`exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_le_exp`, the loops of `u` converge to
`x` exponentially: this is `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp` on the
part `s > a + 1` of the end, where `du` is bounded. -/
private theorem exists_pos_eventually_norm_sub_le_exp_of_floer
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ t, ‖u (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)) := by
  obtain ⟨M, hM⟩ := exists_forall_norm_fderiv_le_of_floer hH hHper hW hJ hJper hK hKW hJt
    (hu.of_le (by simp)) hper huK hfloer hE (lt_add_one a)
  obtain ⟨c, hc, MJ, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJ.continuousOn.mono hKW) hJper hJt
  have hsub : Ioi (a + 1) ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ Icc 0 1 :=
    prod_mono (Ioi_subset_Ioi (by linarith)) le_rfl
  have hsub' : Ioi (a + 1) ×ˢ (univ : Set ℝ) ⊆ Ioi a ×ˢ univ :=
    prod_mono (Ioi_subset_Ioi (by linarith)) le_rfl
  have huK' (z : ℝ × ℝ) (hz : z ∈ Ioi (a + 1) ×ˢ Icc (0 : ℝ) 1) : u z ∈ K :=
    huK z.1 (hsub hz).1 z.2
  exact exists_pos_eventually_norm_sub_le_exp (a := a + 1)
    (J := fun z ↦ J z.2 (u z)) (L := M) (hH.of_le (by norm_num)) hHper
    ((hu.of_le (by simp)).mono hsub') (fun s hs ↦ hper s (by linarith)) hc
    (fun z hz v ↦ (hcM z.2 (u z) (huK' z hz) v).1) (fun z hz v ↦ (hcM z.2 (u z) (huK' z hz) v).2)
    (fun z hz ↦ hfloer z (hsub hz)) (ne_top_of_le_ne_top hE (lintegral_mono_set hsub))
    (fun z hz ↦ ((fderiv ℝ u z).le_opNorm _).trans (by simpa using hM z hz.1.le)) hxper hx hnd
    hux

/-- **Exponential decay of `∂_s u` at a nondegenerate end.** Under the hypotheses of
`exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_le_exp`, for some `κ > 0` and `C`,
eventually `‖u(s, t) - x(t)‖ ≤ C e^{-3κ s}` and `‖∂_s u(s, t)‖ ≤ C e^{-κ s}` for all `t`. -/
private theorem exists_pos_eventually_norm_fderiv_apply_one_zero_le_exp
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop) :
    ∃ κ > 0, ∃ C, 0 ≤ C ∧ ∀ᶠ s in atTop, ∀ t, ‖u (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)) ^ 3 ∧
      ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ C * Real.exp (-(κ * s)) := by
  obtain ⟨ρ, hρ, D, hD0, hD⟩ := exists_pos_forall_norm_fderiv_sub_le_mul_sqrt_of_floer hH hHper
    hW hJ hJper hK hKW hJt hu hper huK hfloer hE
  obtain ⟨κ₀, hκ₀, C₀, hC₀⟩ := exists_pos_eventually_norm_sub_le_exp_of_floer hH hHper hW hJ
    hJper hK hKW hJt hu hper huK hfloer hE hxper hx hnd hux
  set C₀' := max C₀ 0
  have hC₀' : 0 ≤ C₀' := le_max_right _ _
  set κ := κ₀ / 3
  refine ⟨κ, by positivity, 2 * C₀' + D, by positivity, ?_⟩
  -- Eventually the step `E² = e^{-2κ s}` is below the Hölder radius `ρ`.
  have hsmall : ∀ᶠ s in atTop, Real.exp (-(κ * s)) ^ 2 < ρ := by
    have ht : Tendsto (fun s : ℝ ↦ Real.exp (-(κ * s)) ^ 2) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by positivity : 0 < κ))).pow 2
    exact ht.eventually_lt_const hρ
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 hC₀
  filter_upwards [hsmall, eventually_ge_atTop (max s₁ (a + 2))] with s hsρ hs t
  set E := Real.exp (-(κ * s))
  have hE : 0 < E := Real.exp_pos _
  have hs₁s : s₁ ≤ s := (le_max_left _ _).trans hs
  have has : a + 2 ≤ s := (le_max_right _ _).trans hs
  -- On `[s, s + E²]` the loops are within `C₀' E³` of `x`.
  have hu0 : ∀ σ, s ≤ σ → ‖u (σ, t) - x t‖ ≤ C₀' * E ^ 3 := fun σ hσ ↦ by
    have hE3 : Real.exp (-(κ₀ * s)) = E ^ 3 := by
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [κ]
      push_cast
      ring
    refine (hs₁ σ (hs₁s.trans hσ) t).trans (mul_le_mul (le_max_left _ _) ?_ (by positivity)
      (le_max_right _ _))
    rw [← hE3]
    exact Real.exp_le_exp.2 (by nlinarith)
  refine ⟨(hu0 s le_rfl).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)),
    norm_fderiv_apply_one_zero_le hE (fun σ hσ ↦ ?_) (fun σ hσ ↦ hu0 σ hσ.1) fun σ hσ ↦ ?_⟩
  · have hσa : (σ, t) ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨mem_Ioi.2 (by linarith [hσ.1]), mem_univ _⟩
    exact (hu.differentiableOn (by simp) _ hσa).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hσa)
  · -- The Hölder bound `D √(σ - s) ≤ D √(E²) = D E`.
    refine (hD s σ t has hσ.1 (by linarith [hσ.2])).trans (mul_le_mul_of_nonneg_left ?_ hD0)
    calc √(σ - s) ≤ √(E ^ 2) := Real.sqrt_le_sqrt (by linarith [hσ.2])
      _ = E := Real.sqrt_sq hE.le

/-- **Exponential convergence in `C¹` at a nondegenerate end.** Let `H` be a `C³` Hamiltonian,
`1`-periodic in time, and `J_t(x)` a `1`-periodic family of almost complex structures, `C²` on an
open set `W ⊆ ℝ × V` containing `ℝ × K` for a compact `K ⊆ V`, and tamed by `ω` on `ℝ × K`. Let `u`
be a smooth solution of the Floer equation `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` on the
half-cylinder `s > a`, with `1`-periodic loops in `K` and finite energy, whose loops `u(s, ·)`
converge uniformly as `s → ∞` to a `1`-periodic orbit `x` which is nondegenerate: the propagator of
`ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed vector at time `1`. Then for some `κ > 0` and `C`,
eventually, for all `t ∈ [0, 1]`,

`‖u(s, t) - x(t)‖ ≤ C e^{-κ s}` and `‖du(s, t) - (σ, τ) ↦ τ X_{H_t}(x(t))‖ ≤ C e^{-κ s}`. -/
theorem exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_le_exp
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u z)) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)) ∧
      ‖fderiv ℝ u (s, t) - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (H t) (x t))‖ ≤ C * Real.exp (-(κ * s)) := by
  obtain ⟨κ, hκ, C, hC0, hdecay⟩ := exists_pos_eventually_norm_fderiv_apply_one_zero_le_exp hH
    hHper hW hJ hJper hK hKW hJt hu hper huK hfloer hE hxper hx hnd hux
  obtain ⟨c, -, MJ, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJ.continuousOn.mono hKW) hJper hJt
  -- `X_{H_t}` is Lipschitz near the orbit, uniformly in `t ∈ [0, 1]`.
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨δ, hδ, LX, hLX⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_pos_forall_norm_sub_le_mul
    (F := fun t ↦ ω.hamiltonianVectorField (H t))
    (fun _ _ ↦ (ω.contDiff_hamiltonianVectorField_uncurry (n := 1)
      (hH.of_le (by norm_num))).contDiffAt) hxc.continuousOn
  set MJ' := max MJ 0
  have hMJ' : 0 ≤ MJ' := le_max_right _ _
  have hMJ : MJ ≤ MJ' := le_max_left _ _
  set LX' := max LX 0
  have hLX' : 0 ≤ LX' := le_max_right _ _
  refine ⟨κ, hκ, ((1 + MJ') + LX') * C, ?_⟩
  have hclose : ∀ᶠ s in atTop, ∀ t, ‖u (s, t) - x t‖ ≤ δ :=
    (Metric.tendstoUniformly_iff.1 hux δ hδ).mono fun s hs t ↦ by
      rw [← dist_eq_norm, dist_comm]
      exact (hs t).le
  filter_upwards [hdecay, hclose, eventually_gt_atTop a, eventually_ge_atTop 0]
    with s hs hδs has hs0 t ht
  set E := Real.exp (-(κ * s))
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hκ.le hs0))
  have hE3 : E ^ 3 ≤ E := pow_le_of_le_one (Real.exp_pos _).le hE1 (by norm_num)
  obtain ⟨hu0, hds⟩ := hs t
  have hu0' : ‖u (s, t) - x t‖ ≤ C * E := hu0.trans (mul_le_mul_of_nonneg_left hE3 hC0)
  have hCE : 0 ≤ C * E := by positivity
  refine ⟨hu0'.trans (by rw [mul_assoc]; exact le_mul_of_one_le_left hCE (by linarith)), ?_⟩
  have h := norm_fderiv_sub_smulRight_le (z := (s, t)) (Jz := J t (u (s, t)))
    (hfloer (s, t) ⟨has, ht⟩) (fun v ↦ (hcM t (u (s, t)) (huK s has t) v).2)
    (hLX t ht (u (s, t)) (hδs t))
  calc _ ≤ (1 + MJ) * ‖fderiv ℝ u (s, t) (1, 0)‖ + LX * ‖u (s, t) - x t‖ := h
    _ ≤ (1 + MJ') * (C * E) + LX' * (C * E) := by
        have h1 : (1 + MJ) * ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ (1 + MJ') * (C * E) :=
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hds (by linarith))
        have h2 : LX * ‖u (s, t) - x t‖ ≤ LX' * (C * E) :=
          (mul_le_mul_of_nonneg_right (le_max_left LX 0) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hu0' hLX')
        linarith
    _ = _ := by ring

end TauCeti.SymplecticForm

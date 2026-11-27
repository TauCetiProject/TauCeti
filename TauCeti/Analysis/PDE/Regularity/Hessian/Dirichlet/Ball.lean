/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Existence
public import TauCeti.Analysis.Matrix.Contraction
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Analysis.Calculus.IteratedGradient.Basic
import TauCeti.Analysis.Sobolev.Wkp.LinearIsometry
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Bounds
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Basic

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
(`TauCeti.exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_ball`).

This uniformity is what estimates obtained by freezing measurable coefficients on balls need: on
each ball the frozen matrix is an average of the coefficients, so it varies with the ball, and the
balls range over all centres and radii. Splitting a strong solution of `tr (a ∘ D²u) = f` on a
ball into the solution `w` of the frozen problem with zero boundary values and datum
`f + tr ((A - a) ∘ D²u)` and the remainder `u - w`, which solves the homogeneous
constant-coefficient equation, controls `D²w` in `Lᵖ` with this constant, for every
`1 < p < ∞`.

On `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))`, with the operator written in matrix form
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw`, the same holds: for every ball `B` and every `f ∈ Lᵖ(B)` some `w ∈ W^{2,p}(B)`
solves the equation with `‖D²w‖_{Lᵖ(B)} ≤ C ‖f‖_{Lᵖ(B)}`, uniformly in `A`, the centre and the
radius (`TauCeti.exists_sum_mul_inner_iteratedGradient_eq_and_norm_le_of_ball`). It is
transported from `ℝ × ℝⁿ` along a linear isometry, which conjugates `A` and keeps its ellipticity
and its bound.

## The argument

* **Balls have smooth boundary.** Every ball has the global `C²` boundary charts of the Dirichlet
  theory on `C²` domains (`TauCeti.exists_contDiff_graph_of_mem_frontier_ball`), so the solvability
  theorem of Gilbarg–Trudinger, Theorem 9.15 (in the `TauCeti` namespace,
  `existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_add_mul_eq`)
  applies.
* **Uniformity in `A`.** On the unit ball, Gilbarg–Trudinger's Lemma 9.17 for constant
  coefficients holds with one constant for the whole class of matrices
  (`TauCeti.exists_norm_le_of_traceCLM_comp_iteratedGradient_eq_of_norm_le`).
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

/-- The Jacobian factors of a homothety of ratio `R > 0` and of its inverse cancel. -/
private theorem homothety_factors_mul_eq (n : ℕ) {R : ℝ} (hR : 0 < R) (s C t : ℝ) :
    |R⁻¹ ^ 2| * ((R⁻¹ ^ n)⁻¹ ^ s * (C * (|R ^ 2| * ((R ^ n)⁻¹ ^ s * t)))) = C * t := by
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
    (hC : ∀ (v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) B p 2)
      (g : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict B)),
      firstOrder 1 v ∈ w1p0Submodule volume B p →
      (∀ᵐ y ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict B,
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 v y) = g y) →
        ‖iteratedGradient 1 v‖ ≤ C * ‖g‖)
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
  -- `v = u ∘ Φ` lies in `W^{2,p}(B) ∩ W^{1,p}_0(B)`; `D²u = R⁻² D²v ∘ Ψ` and
  -- `tr (A ∘ D²v) = R² f ∘ Φ`.
  set v := compL hΦ u
  have hv0 : firstOrder 1 v ∈ w1p0Submodule volume B p := by
    rw [firstOrder_compL hΦ hp_top]
    exact hΦ.w1pCompL_mem_w1p0Submodule_of_leftInvOn hp_top
      ((continuous_const_smul _).add continuous_const).continuousOn hΨ.mapsTo hleft hu
  -- The two changes of variables scale the norms by reciprocal Jacobian factors.
  have hDu : ‖iteratedGradient 1 u‖ ≤ |R⁻¹ ^ 2| *
      ((R⁻¹ ^ finrank ℝ (WithLp 2 (ℝ × E)))⁻¹ ^ (1 / p).toReal * ‖iteratedGradient 1 v‖) := by
    have h := iteratedGradient_compL_smul_add_const_ae hp_top hΨ v
    rw [show compL hΨ v = u from compL_compL_of_rightInvOn hΦ hΨ hright u] at h
    rw [Lp.norm_def, toReal_eLpNorm, Lp.norm_def, toReal_eLpNorm]
    exact hΨ.lpNorm_le_of_ae_le_mul_comp Omega.isOpen.measurableSet subset_rfl hΨ.mapsTo
      (abs_nonneg _) (Lp.aestronglyMeasurable _) (Lp.memLp _)
      (h.mono fun y hy => by rw [hy, norm_smul, Real.norm_eq_abs])
  have hTv : ‖hessianTraceL B A v‖ ≤ |R ^ 2| *
      ((R ^ finrank ℝ (WithLp 2 (ℝ × E)))⁻¹ ^ (1 / p).toReal * ‖f‖) := by
    rw [Lp.norm_def, toReal_eLpNorm, Lp.norm_def, toReal_eLpNorm]
    refine hΦ.lpNorm_le_of_ae_le_mul_comp B.isOpen.measurableSet subset_rfl hΦ.mapsTo
      (abs_nonneg _) (Lp.aestronglyMeasurable _) (Lp.memLp _) ?_
    filter_upwards [coeFn_hessianTraceL B A v, iteratedGradient_compL_smul_add_const_ae hp_top hΦ u,
      hΦ.ae_comp hf] with y h1 h2 h3
    rw [h1, h2, ContinuousLinearMap.comp_smul, map_smul, h3, norm_smul, Real.norm_eq_abs]
  refine (hDu.trans ?_).trans_eq (homothety_factors_mul_eq (finrank ℝ (WithLp 2 (ℝ × E))) hR
    (1 / p).toReal C ‖f‖)
  gcongr
  exact (hC v _ hv0 ((coeFn_hessianTraceL B A v).mono fun _ h => h.symm)).trans
    (mul_le_mul_of_nonneg_left hTv hC0)

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
  obtain ⟨C₀, hC₀⟩ := exists_norm_le_of_traceCLM_comp_iteratedGradient_eq_of_norm_le (p := p) hp
    hp_top (Omega := B)
    isBounded_ball (forall_frontier_exists_contDiff_graph_of_eq_ball 0 one_pos rfl) hlam Λ
  refine ⟨max C₀ 0, fun A hA hAΛ x₀ R Omega hΩ u f hu hf => ?_⟩
  rcases le_or_gt R 0 with hR | hR
  · -- A ball of nonpositive radius is empty, and so is every `Lᵖ` function on it.
    have h0 : iteratedGradient 1 u = 0 := Lp.eq_zero_iff_ae_eq_zero.2
      (ae_restrict_of_forall_mem Omega.isOpen.measurableSet fun x hx => by
        have hx' : x ∈ (Omega : Set (WithLp 2 (ℝ × E))) := hx
        rw [hΩ, ball_eq_empty.2 hR] at hx'
        exact hx'.elim)
    rw [h0, norm_zero]
    exact mul_nonneg (le_max_right _ _) (norm_nonneg _)
  exact norm_iteratedGradient_le_of_eq_ball hp_top (le_max_right C₀ 0) rfl
    (fun v g hv hg => (norm_iteratedGradient_le 1 v).trans ((hC₀ A hA hAΛ v g hv hg).trans
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

/-- Conjugating the operator `A` of a matrix by a linear isometry `e` keeps its ellipticity and
its bound: `B = e ∘ A ∘ e⁻¹` has `λ ‖ξ‖² ≤ ⟪B ξ, ξ⟫` and `‖B‖ ≤ Λ` when `λ ‖ξ‖² ≤ ξᵀ A ξ` and the
bilinear form of `A` has norm at most `Λ`. -/
private theorem conj_toEuclideanCLM_bounds {m : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] V)
    {A : Matrix (Fin m) (Fin m) ℝ} {lam Λ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ (Fin m), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hAΛ : ‖PDE.matrixBilinearForm A‖ ≤ Λ) :
    (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪((e : EuclideanSpace ℝ (Fin m) →L[ℝ] V) ∘L
      Matrix.toEuclideanCLM (𝕜 := ℝ) A ∘L (e.symm : V →L[ℝ] EuclideanSpace ℝ (Fin m))) ξ,
        ξ⟫_ℝ) ∧
      ‖(e : EuclideanSpace ℝ (Fin m) →L[ℝ] V) ∘L Matrix.toEuclideanCLM (𝕜 := ℝ) A ∘L
        (e.symm : V →L[ℝ] EuclideanSpace ℝ (Fin m))‖ ≤ Λ := by
  refine ⟨fun ξ => ?_, ?_⟩
  · have h := hA (e.symm ξ)
    rw [LinearIsometryEquiv.norm_map, ← PDE.matrixBilinearForm_self,
      PDE.matrixBilinearForm_apply, ← Matrix.inner_toEuclideanCLM, real_inner_comm] at h
    refine h.trans_eq ?_
    rw [← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
    rfl
  · rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
      ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
      ← PDE.norm_matrixBilinearForm_eq_norm_toEuclideanCLM]
    exact hAΛ

/-- **The constant-coefficient problem on balls of `ℝⁿ⁺¹`, in matrix form.** Let `1 < p < ∞` and
`0 < λ`. There is a constant `C` such that for every matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and
`‖A‖ ≤ Λ` (the operator norm of its bilinear form), every ball `Ω = B(x₀, R)` of
`ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))` and every `f ∈ Lᵖ(Ω)`, some `w ∈ W^{2,p}(Ω)` solves
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw = f` almost everywhere on `Ω` and satisfies `‖D²w‖_{Lᵖ(Ω)} ≤ C ‖f‖_{Lᵖ(Ω)}`. The
constant depends only on `n`, `p`, `λ` and `Λ`, not on `A`, `x₀` or `R`. This is
`TauCeti.existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_eq_of_ball`
with its estimate, transported from `ℝ × ℝⁿ` along a linear isometry. -/
theorem exists_sum_mul_inner_iteratedGradient_eq_and_norm_le_of_ball {n : ℕ} (hp : 1 < p)
    (hp_top : p ≠ ⊤) {lam : ℝ} (hlam : 0 < lam) (Λ : ℝ) :
    ∃ C : ℝ, ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      (∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ‖PDE.matrixBilinearForm A‖ ≤ Λ →
      ∀ (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ), 0 < R →
        ∀ (Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
          (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball x₀ R →
          ∀ f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega),
            ∃ w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega p 2,
              (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega,
                ∑ i, ∑ j, A i j * ⟪iteratedGradient 1 w x (EuclideanSpace.single i 1),
                  EuclideanSpace.single j 1⟫_ℝ = f x) ∧
              ‖iteratedGradient 1 w‖ ≤ C * ‖f‖ := by
  -- The model space `V = ℝ × ℝⁿ` of the solvability theorem, and a linear isometry `e` onto it.
  set V := WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))
  have hdim : finrank ℝ V = n + 1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × EuclideanSpace ℝ (Fin n))).finrank_eq, finrank_prod,
      finrank_self, finrank_euclideanSpace_fin, add_comm]
  set g : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ((stdOrthonormalBasis ℝ V).reindex (finCongr hdim)).repr
  set e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] V := g.symm
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_ball
    (E := EuclideanSpace ℝ (Fin n)) hp hp_top hlam Λ
  refine ⟨C, fun A hA hAΛ x₀ R hR Omega hΩ f => ?_⟩
  -- The matrix `A` becomes the operator `B = e ∘ A ∘ e⁻¹` on `V`, with the same constants.
  set M := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  set B : V →L[ℝ] V := (e : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] V) ∘L M ∘L
    (e.symm : V →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨hB, hBΛ⟩ := conj_toEuclideanCLM_bounds e hA hAΛ
  -- The ball `Ω` is the preimage under `e` of the ball `W = e Ω` of `V`.
  set W : Opens V := ⟨g ⁻¹' Omega, Omega.isOpen.preimage g.continuous⟩
  have hW : (W : Set V) = ball (e x₀) R := by
    change g ⁻¹' (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = _
    rw [hΩ, LinearIsometryEquiv.preimage_ball]
  have hΩW : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = e ⁻¹' W := by
    ext x
    simp [W, e]
  have he : MeasurePreserving e volume volume := e.measurePreserving
  have hg' : MeasurePreserving g (volume.restrict (W : Set V))
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    g.measurePreserving.restrict_preimage Omega.isOpen.measurableSet
  have her : MeasurePreserving e
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (volume.restrict (W : Set V)) := by
    rw [hΩW]
    exact he.restrict_preimage W.isOpen.measurableSet
  -- Solve on `W` and transport the solution back to `Ω`.
  obtain ⟨w', ⟨hw'0, hw'⟩, -⟩ :=
    existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_eq_of_ball hp
      hp_top hlam hB hR hW (Lp.compMeasurePreserving g hg' f)
  have hD := iteratedGradient_compLinearIsometryEquiv_ae he hΩW 1 w'
  refine ⟨compLinearIsometryEquiv he hΩW 2 w', ?_, ?_⟩
  · filter_upwards [hD, her.quasiMeasurePreserving.ae hw',
      her.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hg')] with x h₁ h₂ h₃
    rw [← Matrix.contraction_apply, Matrix.contraction_eq_traceCLM_comp, h₁,
      LinearIsometryEquiv.iteratedGradientCongr_symm_succ_apply,
      LinearIsometryEquiv.iteratedGradientCongr_zero]
    rw [Function.comp_apply, show g (e x) = x from g.apply_symm_apply x] at h₃
    rw [← h₃, ← h₂, traceCLM_apply, traceCLM_apply]
    -- Conjugating `M ∘ e⁻¹ ∘ H ∘ e` by `e` gives `B ∘ H`, with the same trace.
    rw [← LinearMap.trace_conj' _ e.toLinearEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply, Matrix.toEuclideanCLM_apply]
  · -- The Hessians, and the data, have the same `Lᵖ` norms on `Ω` and on `W`.
    rw [norm_iteratedGradient_compLinearIsometryEquiv, ← Lp.norm_compMeasurePreserving f hg']
    exact hC B hB hBΛ (e x₀) R W hW w' _ hw'0 hw'

end TauCeti

end

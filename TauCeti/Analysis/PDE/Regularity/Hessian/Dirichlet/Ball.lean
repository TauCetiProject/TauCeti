/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Contraction
public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Existence
import TauCeti.Analysis.Calculus.IteratedGradient.Trace
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

The same Dirichlet problem, with the same uniform estimate, is also stated in matrix form on
balls of `ℝ^{n+1} = EuclideanSpace ℝ (Fin (n + 1))`: for a constant matrix `A` with
`λ ‖ξ‖² ≤ ξᵀ A ξ` and `‖A‖ ≤ Λ`, some `w ∈ W^{2,p}(B) ∩ W^{1,p}_0(B)` solves
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw = f` in `B` with `‖D²w‖_{Lᵖ(B)} ≤ C ‖f‖_{Lᵖ(B)}`, where `C` depends only on `n`,
`p`, `λ` and `Λ`
(`TauCeti.exists_firstOrder_mem_w1p0Submodule_and_contraction_iteratedGradient_eq_and_norm_le`).

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
* **Uniformity in `A`.** On the unit ball, Gilbarg–Trudinger's Lemma 9.17 for constant
  coefficients holds with one constant for the whole class of matrices
  (`TauCeti.exists_norm_le_of_traceCLM_comp_iteratedGradient_eq_of_norm_le`).
* **Uniformity in the ball.** The homothety `Φ y = R y + x₀` maps the unit ball onto `B(x₀, R)`.
  For `v = u ∘ Φ`, `D²v = R² D²u ∘ Φ` and `tr (A ∘ D²v) = R² f ∘ Φ`, and composition with `Φ` and
  with its inverse scales `Lᵖ` norms by reciprocal powers `R^(∓n/p)` of the Jacobian. These factors
  cancel, so the unit-ball constant serves for every ball.
* **Matrix form on `ℝ^{n+1}`.** A linear isometry `g` from `WithLp 2 (ℝ × ℝⁿ)` onto `ℝ^{n+1}`
  carries the ball, the datum and the solution between the two spaces. It turns `A` into
  `g⁻¹ A g`, which has the same ellipticity constant and bound, and it preserves the `Lᵖ` norms
  and the trace `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw = tr (A ∘ D²w)`.

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

/-! ### Balls of `ℝ^{n+1}` and matrix coefficients -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Conjugating a constant matrix `A` on `ℝ^{n+1}` by a linear isometry `g` from another space
keeps its ellipticity constant and its bound: `T = g⁻¹ A g` has `λ ‖ξ‖² ≤ ⟪T ξ, ξ⟫` and
`‖T‖ ≤ Λ`. -/
private theorem le_inner_and_norm_le_of_conj {n : ℕ} (g : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Λ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hAΛ : ‖PDE.matrixBilinearForm A‖ ≤ Λ) :
    (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪((g.symm : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] E) ∘L
      Matrix.toEuclideanCLM (𝕜 := ℝ) A ∘L (g : E →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) ξ, ξ⟫_ℝ) ∧
    ‖(g.symm : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] E) ∘L Matrix.toEuclideanCLM (𝕜 := ℝ) A ∘L
      (g : E →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ Λ := by
  set T := (g.symm : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] E) ∘L
    Matrix.toEuclideanCLM (𝕜 := ℝ) A ∘L (g : E →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
  have hTξ : ∀ ξ, T ξ = g.symm (Matrix.toEuclideanCLM (𝕜 := ℝ) A (g ξ)) := fun ξ => rfl
  refine ⟨fun ξ => ?_, ?_⟩
  · have h := hA (g ξ)
    rw [LinearIsometryEquiv.norm_map, Matrix.toQuadraticForm'_apply,
      ← Matrix.inner_toEuclideanCLM] at h
    rwa [← g.inner_map_map (T ξ), hTξ, LinearIsometryEquiv.apply_symm_apply, real_inner_comm]
  · rwa [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
      ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
      ← PDE.norm_matrixBilinearForm_eq_norm_toEuclideanCLM]

/-- Transport of a ball `Ω = B(x₀, R)` of `ℝ^{n+1}` along a linear isometry `g` from another space:
the preimage `Ω' = g⁻¹ Ω` is the ball `B(g⁻¹ x₀, R)`, `Ω = (g⁻¹)⁻¹ Ω'`, and `g`, `g⁻¹` preserve the
restricted volumes. -/
private theorem exists_opens_eq_ball_and_measurePreserving {n : ℕ}
    (g : WithLp 2 (ℝ × E) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball x₀ R) :
    ∃ Ω' : Opens (WithLp 2 (ℝ × E)), (Ω' : Set (WithLp 2 (ℝ × E))) = ball (g.symm x₀) R ∧
      (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = g.symm ⁻¹' Ω' ∧
      MeasurePreserving g (volume.restrict (Ω' : Set (WithLp 2 (ℝ × E))))
        (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) ∧
      MeasurePreserving g.symm (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
        (volume.restrict (Ω' : Set (WithLp 2 (ℝ × E)))) := by
  set Ω' : Opens (WithLp 2 (ℝ × E)) := ⟨g ⁻¹' Omega, Omega.isOpen.preimage g.continuous⟩
  have hΩΩ' : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = g.symm ⁻¹' Ω' := by
    ext x
    simp [Ω']
  refine ⟨Ω', ?_, hΩΩ', g.measurePreserving.restrict_preimage Omega.isOpen.measurableSet, ?_⟩
  · ext y
    simp only [Ω', Opens.coe_mk, Set.mem_preimage, hΩ, mem_ball]
    rw [← g.dist_map, g.apply_symm_apply]
  · rw [hΩΩ']
    exact g.symm.measurePreserving.restrict_preimage Ω'.isOpen.measurableSet

/-- **The Dirichlet problem for constant matrix coefficients on balls of `ℝ^{n+1}`, with a universal
constant.** Let `1 < p < ∞` and `0 < λ`. There is a constant `C`, depending only on `n`, `p`, `λ`
and `Λ`, such that for every constant matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `‖A‖ ≤ Λ`, in the
operator norm of its bilinear form, every ball `Ω = B(x₀, R)` of `ℝ^{n+1}` and every `f ∈ Lᵖ(Ω)`,
some `w ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solves `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw = f` almost everywhere on `Ω` and has
`‖D²w‖_{Lᵖ(Ω)} ≤ C ‖f‖_{Lᵖ(Ω)}`. This is
`TauCeti.existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_eq_of_ball`
with the estimate
`TauCeti.exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_ball`, in the
coordinates of `ℝ^{n+1}`. -/
theorem exists_firstOrder_mem_w1p0Submodule_and_contraction_iteratedGradient_eq_and_norm_le
    {n : ℕ} (hp : 1 < p) (hp_top : p ≠ ⊤) {lam : ℝ} (hlam : 0 < lam) (Λ : ℝ) :
    ∃ C : ℝ, ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      (∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
        ‖PDE.matrixBilinearForm A‖ ≤ Λ →
        ∀ (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ), 0 < R →
        ∀ (Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
          (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball x₀ R →
          ∀ f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega),
            ∃ w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega p 2,
              firstOrder 1 w ∈ w1p0Submodule volume Omega p ∧
              (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict Omega,
                Matrix.contraction A (iteratedGradient 1 w x) = f x) ∧
              ‖iteratedGradient 1 w‖ ≤ C * ‖f‖ := by
  -- A linear isometry `g` from the product model `ℝ × ℝⁿ` of the ball theory onto `ℝ^{n+1}`.
  set E := EuclideanSpace ℝ (Fin n)
  set V := EuclideanSpace ℝ (Fin (n + 1))
  have hdim : finrank ℝ (WithLp 2 (ℝ × E)) = n + 1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × E)).finrank_eq, finrank_prod, finrank_self,
      finrank_euclideanSpace_fin, add_comm]
  set g : WithLp 2 (ℝ × E) ≃ₗᵢ[ℝ] V :=
    ((stdOrthonormalBasis ℝ (WithLp 2 (ℝ × E))).reindex (finCongr hdim)).repr
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_ball (E := E) hp
      hp_top hlam Λ
  refine ⟨C, fun A hA hAΛ x₀ R hR Omega hΩ f => ?_⟩
  -- The operator `T = g⁻¹ A g` of the product model, with the same constants.
  set T : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) :=
    (g.symm : V →L[ℝ] WithLp 2 (ℝ × E)) ∘L Matrix.toEuclideanCLM (𝕜 := ℝ) A ∘L
      (g : WithLp 2 (ℝ × E) →L[ℝ] V)
  obtain ⟨hT, hTΛ⟩ := le_inner_and_norm_le_of_conj g hA hAΛ
  -- The ball of the product model and the data transported to it.
  obtain ⟨Ω', hΩ', hΩΩ', hgr, hgs⟩ := exists_opens_eq_ball_and_measurePreserving g hΩ
  set f' := Lp.compMeasurePreserving g hgr f
  obtain ⟨w', ⟨hw0, hw⟩, -⟩ :=
    existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_eq_of_ball hp
      hp_top hlam hT hR hΩ' f'
  -- Transport the solution back along `g`.
  set w := compLinearIsometryEquiv g.symm.measurePreserving hΩΩ' 2 w'
  have hH := iteratedGradient_compLinearIsometryEquiv_ae g.symm.measurePreserving hΩΩ' 1 w'
  refine ⟨w, firstOrder_compLinearIsometryEquiv_mem_w1p0Submodule _ hΩΩ' hw0, ?_, ?_⟩
  · filter_upwards [hH, hgs.quasiMeasurePreserving.ae hw,
      hgs.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hgr)] with x h₁ h₂ h₃
    have hfx : (f : V → ℝ) x = (f' : WithLp 2 (ℝ × E) → ℝ) (g.symm x) := by
      rw [h₃, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [h₁, Matrix.contraction_apply_eq_traceCLM, hfx, ← h₂, traceCLM_apply, traceCLM_apply,
      LinearIsometryEquiv.trace_comp_iteratedGradientCongr_symm_one, LinearIsometryEquiv.symm_symm]
  · have hnorm : ‖iteratedGradient 1 w‖ = ‖iteratedGradient 1 w'‖ :=
      norm_iteratedGradient_compLinearIsometryEquiv _ hΩΩ' 1 w'
    rw [hnorm, ← Lp.norm_compMeasurePreserving f hgr]
    exact hC T hT hTΛ (g.symm x₀) R Ω' hΩ' w' f' hw0 hw

end TauCeti


end

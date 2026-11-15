/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Exponential decay of all derivatives of solutions of screened equations

Let `g` be a function on a finite-dimensional real inner product space `E`, with values in a real
normed space, solving

`Δ g = V • g + Φ`

outside a ball, where the potential satisfies `V ≥ a²` and has a bounded derivative. If `g` and the
derivative of the forcing `Φ` decay like `exp (-c ‖x‖)` for some `0 < c < a`, then so does the
derivative of `g` (`TauCeti.isBigO_fderiv_of_laplacian_eq_smul_add`). The proof compares
translates: `D = g (· + h) - g` solves the same equation up to a forcing of size
`‖h‖ exp (-c ‖x‖)`, so the forced exterior comparison principle
(`TauCeti.le_mul_exp_add_div_mul_exp_of_mul_sub_le_laplacian`), applied to each norming functional
of `D`, bounds `D` by `‖h‖` times the same exponential. Dividing by `‖h‖` bounds the derivative.

Iterating this gives the regularity at infinity of the Liouville-type equation

`Δ ℓ = κ (exp ℓ - 1)`,

the scalar equation of the plane vortex: if `ℓ` is smooth near infinity, decays like
`exp (-c ‖x‖)` with `c² < κ`, and has a bounded derivative, then every iterated derivative of `ℓ`
and of `exp ℓ - 1` decays like `exp (-c ‖x‖)`
(`TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`,
`TauCeti.isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one`). The `n`-th derivative
`Dⁿℓ` solves `Δ Dⁿℓ = κ exp ℓ • Dⁿℓ + κ Cₙ`, where the commutator `Cₙ = Dⁿ (exp ℓ) - exp ℓ • Dⁿℓ`
involves only derivatives of order below `n`, so each step of the induction is an instance of the
derivative estimate above. The rate is not lost along the induction.

## Main results

* `TauCeti.isBigO_fderiv_of_laplacian_eq_smul_add`: exponential decay of the derivative of a
  decaying solution of `Δ g = V • g + Φ`.
* `TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`: exponential decay of all iterated
  derivatives of a decaying solution of `Δ ℓ = κ (exp ℓ - 1)`.
* `TauCeti.isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one`: the same for
  `exp ℓ - 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, Chapter 3 (comparison with barriers) and §7.11 (difference quotients).
-/

public section

noncomputable section

namespace TauCeti

open Asymptotics Filter Metric Set Topology InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Translates of a forced screened solution.** Under the hypotheses of
`TauCeti.isBigO_fderiv_of_laplacian_eq_smul_add`, made explicit outside the ball of radius
`R ≥ 1`, the differences `g (x + h) - g x` with `‖h‖ ≤ 1` are bounded by `‖h‖` times a fixed
multiple of `exp (-c ‖x‖)` outside the ball of radius `R + 1`. -/
private theorem exists_norm_sub_le_mul_exp_of_laplacian_eq_smul_add {g Φ : E → G} {V : E → ℝ}
    {a c R L Kg KΦ : ℝ} (hc : 0 < c) (hca : c < a) (hR : 1 ≤ R) (hL : 0 ≤ L) (hKg : 0 ≤ Kg)
    (hKΦ : 0 ≤ KΦ) (hg : ∀ y, R ≤ ‖y‖ → ContDiffAt ℝ 2 g y)
    (hVd : ∀ y, R ≤ ‖y‖ → DifferentiableAt ℝ V y) (hVa : ∀ y, R ≤ ‖y‖ → a ^ 2 ≤ V y)
    (hVL : ∀ y, R ≤ ‖y‖ → ‖fderiv ℝ V y‖ ≤ L) (hΦd : ∀ y, R ≤ ‖y‖ → DifferentiableAt ℝ Φ y)
    (hΦ : ∀ y, R ≤ ‖y‖ → ‖fderiv ℝ Φ y‖ ≤ KΦ * Real.exp (-(c * ‖y‖)))
    (heq : ∀ y, R ≤ ‖y‖ → Δ g y = V y • g y + Φ y)
    (hgd : ∀ y, R ≤ ‖y‖ → ‖g y‖ ≤ Kg * Real.exp (-(c * ‖y‖)))
    (hglim : Tendsto g (cocompact E) (𝓝 0)) :
    ∃ K, 0 ≤ K ∧ ∀ x : E, R + 1 ≤ ‖x‖ → ∀ h : E, ‖h‖ ≤ 1 →
      ‖g (x + h) - g x‖ ≤ ‖h‖ * (K * Real.exp (-(c * ‖x‖))) := by
  set R₁ := R + 1
  have hR₁pos : 0 < R₁ := by linarith
  -- A bound for the derivative of `g` on the annulus `R ≤ ‖y‖ ≤ R₁ + 1`.
  set A : Set E := closedBall 0 (R₁ + 1) ∩ {y | R ≤ ‖y‖}
  have hAc : IsCompact A :=
    (isCompact_closedBall 0 (R₁ + 1)).inter_right (isClosed_le continuous_const continuous_norm)
  have hAcont : ContinuousOn (fderiv ℝ g) A := fun y hy ↦
    ((hg y hy.2).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := hAc.exists_bound_of_continuousOn hAcont
  set M := max M₀ 0
  set B := (L * Kg + KΦ) * Real.exp c with hB
  have hgap : 0 < a ^ 2 - c ^ 2 := by nlinarith
  refine ⟨M * Real.exp (c * R₁) + B / (a ^ 2 - c ^ 2), by positivity, fun x hx h hh ↦ ?_⟩
  set D : E → G := fun y ↦ g (y + h) - g y with hD
  -- A point within distance `‖h‖ ≤ 1` of `y` has norm at least `‖y‖ - 1`, so the exponential
  -- weight there is at most `exp c` times its value at `y`.
  have hnear : ∀ y z : E, z ∈ closedBall y ‖h‖ → ‖y‖ - 1 ≤ ‖z‖ := fun y z hz ↦ by
    have := norm_sub_norm_le y z
    rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub] at hz
    linarith
  have hweight : ∀ y z : E, z ∈ closedBall y ‖h‖ →
      Real.exp (-(c * ‖z‖)) ≤ Real.exp c * Real.exp (-(c * ‖y‖)) := fun y z hz ↦ by
    have := hnear y z hz
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith
  -- Points within distance `‖h‖` of a point outside the ball of radius `R₁` lie outside the
  -- ball of radius `R`.
  have hfar : ∀ y : E, R₁ ≤ ‖y‖ → ∀ z ∈ closedBall y ‖h‖, R ≤ ‖z‖ := fun y hy z hz ↦ by
    have := hnear y z hz
    linarith
  have hyh : ∀ y : E, y + h ∈ closedBall y ‖h‖ := fun y ↦ by
    simp [mem_closedBall, dist_eq_norm]
  have hgsh : ∀ y : E, R₁ ≤ ‖y‖ → ContDiffAt ℝ 2 (fun y ↦ g (y + h)) y := fun y hy ↦
    (hg (y + h) (hfar y hy _ (hyh y))).comp y (contDiffAt_id.add contDiffAt_const)
  have hDcd : ∀ y : E, R₁ ≤ ‖y‖ → ContDiffAt ℝ 2 D y := fun y hy ↦
    (hgsh y hy).sub (hg y (by linarith))
  -- The forcing of the equation for `D` is of size `‖h‖ exp (-c ‖y‖)`.
  have hforce : ∀ y : E, R₁ ≤ ‖y‖ →
      ‖Δ D y - V y • D y‖ ≤ ‖h‖ * B * Real.exp (-(c * ‖y‖)) := fun y hy ↦ by
    have hy₀ : R ≤ ‖y‖ := by linarith
    have hΔD : Δ D y = Δ g (y + h) - Δ g y := by
      rw [hD, ← Pi.sub_def, (hgsh y hy).laplacian_sub (hg y hy₀), laplacian_comp_add_right]
    have hsplit : Δ D y - V y • D y = (V (y + h) - V y) • g (y + h) + (Φ (y + h) - Φ y) := by
      rw [hΔD, heq _ (hfar y hy _ (hyh y)), heq y hy₀, hD]
      module
    have hVmv : ‖V (y + h) - V y‖ ≤ L * ‖y + h - y‖ :=
      (convex_closedBall y ‖h‖).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz ↦ hVd z (hfar y hy z hz)) (fun z hz ↦ hVL z (hfar y hy z hz))
        (mem_closedBall_self (norm_nonneg h)) (hyh y)
    have hΦmv : ‖Φ (y + h) - Φ y‖ ≤ (KΦ * (Real.exp c * Real.exp (-(c * ‖y‖)))) * ‖y + h - y‖ :=
      (convex_closedBall y ‖h‖).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz ↦ hΦd z (hfar y hy z hz))
        (fun z hz ↦ (hΦ z (hfar y hy z hz)).trans
          (mul_le_mul_of_nonneg_left (hweight y z hz) hKΦ))
        (mem_closedBall_self (norm_nonneg h)) (hyh y)
    have hgyh : ‖g (y + h)‖ ≤ Kg * (Real.exp c * Real.exp (-(c * ‖y‖))) :=
      (hgd _ (hfar y hy _ (hyh y))).trans
        (mul_le_mul_of_nonneg_left (hweight y _ (hyh y)) hKg)
    rw [add_sub_cancel_left] at hVmv hΦmv
    rw [hsplit]
    calc ‖(V (y + h) - V y) • g (y + h) + (Φ (y + h) - Φ y)‖
        ≤ ‖V (y + h) - V y‖ * ‖g (y + h)‖ + ‖Φ (y + h) - Φ y‖ :=
          (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ (L * ‖h‖) * (Kg * (Real.exp c * Real.exp (-(c * ‖y‖)))) +
            (KΦ * (Real.exp c * Real.exp (-(c * ‖y‖)))) * ‖h‖ := by gcongr
      _ = ‖h‖ * B * Real.exp (-(c * ‖y‖)) := by rw [hB]; ring
  -- On the sphere of radius `R₁`, `‖D‖ ≤ M ‖h‖` by the mean value inequality on the annulus.
  have hbdry : ∀ y : E, ‖y‖ = R₁ → ‖D y‖ ≤ M * ‖h‖ := fun y hy ↦ by
    have hmv := (convex_closedBall y ‖h‖).norm_image_sub_le_of_norm_fderiv_le (f := g) (C := M)
      (fun z hz ↦ (hg z (hfar y hy.ge z hz)).differentiableAt (by norm_num))
      (fun z hz ↦ ?_) (mem_closedBall_self (norm_nonneg h)) (hyh y)
    · simpa [hD] using hmv
    · refine (hM₀ z ⟨?_, hfar y hy.ge z hz⟩).trans (le_max_left _ _)
      have h1 := norm_le_of_mem_closedBall hz
      rw [mem_closedBall_zero_iff]
      linarith [norm_le_norm_add_norm_sub' z y, norm_sub_rev z y]
  have hDlim : Tendsto D (cocompact E) (𝓝 0) := by
    have hsh : Tendsto (fun y ↦ g (y + h)) (cocompact E) (𝓝 0) :=
      hglim.comp (Homeomorph.addRight h).isClosedEmbedding.tendsto_cocompact
    simpa [hD] using hsh.sub hglim
  -- Compare a norming functional of `D x` with the forced barrier.
  rcases eq_or_ne ‖D x‖ 0 with hDx | hDx
  · simp only [hD] at hDx
    rw [hDx]
    positivity
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector ℝ (D x) hDx
  have hφle : ∀ v : G, φ v ≤ ‖v‖ := fun v ↦
    (le_abs_self _).trans ((φ.le_opNorm v).trans (by rw [hφ1, one_mul]))
  have hcomp := le_mul_exp_add_div_mul_exp_of_mul_sub_le_laplacian (u := fun y ↦ φ (D y))
    (V := V) (R := R₁) (M := M * ‖h‖) (B := ‖h‖ * B) hR₁pos hc hca (by positivity)
    (by positivity)
    (fun y hy ↦ (φ.continuous.continuousAt.comp (hDcd y hy).continuousAt).continuousWithinAt)
    (fun y hy ↦ φ.contDiff.contDiffAt.comp y (hDcd y hy.le))
    (fun y hy ↦ hVa y (by linarith)) (fun y hy ↦ ?_)
    (fun y hy ↦ (hφle _).trans (hbdry y hy))
    (by simpa [Function.comp_def] using (φ.continuous.tendsto 0).comp hDlim) hx
  · simp only [hφx] at hcomp
    have hexp : Real.exp (-(c * (‖x‖ - R₁))) = Real.exp (c * R₁) * Real.exp (-(c * ‖x‖)) := by
      rw [← Real.exp_add]
      ring_nf
    refine hcomp.trans (le_of_eq ?_)
    rw [hexp]
    ring
  · -- The equation for `φ ∘ D`.
    have hΔ : Δ (fun y ↦ φ (D y)) y = φ (Δ D y) :=
      (hDcd y hy.le).laplacian_CLM_comp_left (l := (φ : G →L[ℝ] ℝ))
    rw [hΔ]
    have hlow : -(‖h‖ * B * Real.exp (-(c * ‖y‖))) ≤ φ (Δ D y - V y • D y) := by
      have := (hφle (-(Δ D y - V y • D y))).trans ((norm_neg _).le.trans (hforce y hy.le))
      rw [map_neg] at this
      linarith
    rw [map_sub, map_smul, smul_eq_mul] at hlow
    linarith

/-- **Exponential decay of the derivative of a forced screened solution.** Let `g : E → G` solve
`Δ g = V • g + Φ` outside a compact set, where `V ≥ a²` has a bounded derivative there. If `g`
and the derivative of the forcing `Φ` are `O(exp (-c ‖x‖))` at infinity with `0 < c < a`, then
so is the derivative of `g`. -/
theorem isBigO_fderiv_of_laplacian_eq_smul_add {g Φ : E → G} {V : E → ℝ} {a c : ℝ}
    (hc : 0 < c) (hca : c < a) (hg : ∀ᶠ x in cocompact E, ContDiffAt ℝ 2 g x)
    (hVd : ∀ᶠ x in cocompact E, DifferentiableAt ℝ V x)
    (hVa : ∀ᶠ x in cocompact E, a ^ 2 ≤ V x)
    (hVL : fderiv ℝ V =O[cocompact E] fun _ ↦ (1 : ℝ))
    (hΦd : ∀ᶠ x in cocompact E, DifferentiableAt ℝ Φ x)
    (hΦ : fderiv ℝ Φ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (heq : ∀ᶠ x in cocompact E, Δ g x = V x • g x + Φ x)
    (hgd : g =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) :
    fderiv ℝ g =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  obtain ⟨Kg, hKg⟩ := hgd.bound
  obtain ⟨L, hL⟩ := hVL.bound
  obtain ⟨KΦ, hKΦ⟩ := hΦ.bound
  have hglim : Tendsto g (cocompact E) (𝓝 0) :=
    hgd.trans_tendsto (tendsto_exp_neg_mul_norm_cocompact hc)
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸
      (hg.and (hVd.and (hVa.and (hL.and (hΦd.and (hKΦ.and (heq.and hKg))))))))
  set R := max R₀ 1
  -- Split the hypotheses, which hold outside the ball of radius `R`, into named statements.
  have hfar := fun (y : E) (hy : R ≤ ‖y‖) ↦
    hR₀ (Set.mem_ofPred.mpr ((le_max_left R₀ 1).trans hy))
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one, mul_one, forall_and] at hfar
  obtain ⟨hgR, hVdR, hVaR, hLR, hΦdR, hKΦR, heqR, hKgR⟩ := hfar
  obtain ⟨K, hK₀, hK⟩ := exists_norm_sub_le_mul_exp_of_laplacian_eq_smul_add
    (L := max L 0) (Kg := max Kg 0) (KΦ := max KΦ 0) hc hca (le_max_right R₀ 1)
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) hgR hVdR hVaR
    (fun y hy ↦ (hLR y hy).trans (le_max_left _ _)) hΦdR
    (fun y hy ↦ (hKΦR y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
    heqR
    (fun y hy ↦ (hKgR y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)) hglim
  refine IsBigO.of_bound K ?_
  filter_upwards [(tendsto_norm_cocompact_atTop (E := E)).eventually_gt_atTop (R + 1)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  -- The difference bound makes `g` Lipschitz at `x` with constant `K exp (-c ‖x‖)`.
  have hdx : DifferentiableAt ℝ g x := (hgR x (by linarith)).differentiableAt (by norm_num)
  refine hdx.hasFDerivAt.le_of_lip' (by positivity) ?_
  filter_upwards [ball_mem_nhds x one_pos] with y hy
  have hy' : ‖y - x‖ ≤ 1 := by rw [← dist_eq_norm]; exact (mem_ball.mp hy).le
  have := hK x hx.le (y - x) hy'
  rw [add_sub_cancel] at this
  linarith

/-! ### All derivatives of solutions of `Δ ℓ = κ (exp ℓ - 1)` -/

/-- The commutator `Dᵏ (exp ℓ) - exp ℓ • Dᵏ ℓ`. It involves only derivatives of `ℓ` of order
below `k` (`isBigO_iteratedFDeriv_expCommutator`). -/
private def expCommutator (ℓ : E → ℝ) (k : ℕ) (x : E) : E [×k]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ k (fun y ↦ Real.exp (ℓ y)) x - Real.exp (ℓ x) • iteratedFDeriv ℝ k ℓ x

omit [FiniteDimensional ℝ E] in
private theorem contDiff_expCommutator {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (k : ℕ) :
    ContDiff ℝ ∞ (expCommutator ℓ k) :=
  ((Real.contDiff_exp.comp hℓ).iteratedFDeriv_right (by simp)).sub
    ((Real.contDiff_exp.comp hℓ).smul (hℓ.iteratedFDeriv_right (by simp)))

omit [FiniteDimensional ℝ E] in
private theorem expCommutator_one {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) : expCommutator ℓ 1 = 0 := by
  funext x
  ext m
  simp [expCommutator, iteratedFDeriv_one_apply, fderiv_exp (hℓ.differentiable (by simp) x)]

omit [FiniteDimensional ℝ E] in
/-- The recursion `Cₖ₊₁ = D Cₖ + D (exp ℓ) ⊗ Dᵏ ℓ`, up to the currying isometry. -/
private theorem expCommutator_succ {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (k : ℕ) :
    expCommutator ℓ (k + 1) = (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (k + 1) ↦ E) ℝ).symm ∘ fun y ↦ fderiv ℝ (expCommutator ℓ k) y +
        (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y) := by
  funext y
  have he : ContDiff ℝ ∞ (fun y ↦ Real.exp (ℓ y)) := Real.contDiff_exp.comp hℓ
  have hdC : DifferentiableAt ℝ (expCommutator ℓ k) y :=
    (contDiff_expCommutator hℓ k).differentiable (by simp) y
  have hdℓ : DifferentiableAt ℝ (iteratedFDeriv ℝ k ℓ) y :=
    (hℓ.iteratedFDeriv_right (m := 1) (by simp)).differentiable (by simp) y
  have hde : DifferentiableAt ℝ (fun y ↦ Real.exp (ℓ y)) y := he.differentiable (by simp) y
  -- Differentiate `Dᵏ (exp ℓ) = Cₖ + exp ℓ • Dᵏ ℓ`.
  have hDe : fderiv ℝ (iteratedFDeriv ℝ k fun y ↦ Real.exp (ℓ y)) y =
      fderiv ℝ (expCommutator ℓ k) y + (Real.exp (ℓ y) • fderiv ℝ (iteratedFDeriv ℝ k ℓ) y +
        (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y)) := by
    have hsplit : (iteratedFDeriv ℝ k fun y ↦ Real.exp (ℓ y)) =
        fun x ↦ expCommutator ℓ k x + Real.exp (ℓ x) • iteratedFDeriv ℝ k ℓ x := by
      funext x
      simp [expCommutator]
    rw [hsplit]
    exact (hdC.hasFDerivAt.add (hde.hasFDerivAt.smul hdℓ.hasFDerivAt)).fderiv
  simp only [expCommutator, iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hDe, map_add,
    map_smul]
  abel

omit [FiniteDimensional ℝ E] in
/-- The commutators `Cₖ` are `O(ρ)` with their derivatives, as long as the derivatives of `ℓ` of
order at most `n` are `O(ρ)` and those of `exp ℓ` are bounded, where `j + k ≤ n + 1`. -/
private theorem isBigO_iteratedFDeriv_expCommutator {ℓ : E → ℝ} {ρ : E → ℝ}
    (hℓ : ContDiff ℝ ∞ ℓ) {n : ℕ} (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[cocompact E] ρ)
    (hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[cocompact E]
      fun _ ↦ (1 : ℝ))
    {k : ℕ} (hk : 1 ≤ k) {j : ℕ} (hjk : j + k ≤ n + 1) :
    iteratedFDeriv ℝ j (expCommutator ℓ k) =O[cocompact E] ρ := by
  have he : ContDiff ℝ ∞ (fun y ↦ Real.exp (ℓ y)) := Real.contDiff_exp.comp hℓ
  induction k, hk using Nat.le_induction generalizing j with
  | base =>
    rw [expCommutator_one hℓ, iteratedFDeriv_zero]
    exact isBigO_zero _ _
  | succ k hk ih =>
    -- The term `D (exp ℓ) ⊗ Dᵏ ℓ`.
    have hT := (he.fderiv_right (m := ∞) le_rfl).isBigO_iteratedFDeriv_smulRight
      (hℓ.iteratedFDeriv_right (m := ∞) (i := k) le_rfl) (n := j) (mod_cast le_top)
      (fun i hi ↦ (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.le).trans
        (hen (i + 1) (by omega)))
      (fun i hi ↦ (isBigO_of_le _ fun y ↦ (norm_iteratedFDeriv_iteratedFDeriv ℓ i k y).le).trans
        (hℓn (i + k) (by omega)))
    simp only [one_mul] at hT
    have hF : iteratedFDeriv ℝ j (fderiv ℝ (expCommutator ℓ k)) =O[cocompact E] ρ :=
      (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.le).trans (ih (j := j + 1) (by omega))
    have hsum : iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (expCommutator ℓ k) y +
        (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y))
          =O[cocompact E] ρ := by
      refine (isBigO_of_le _ fun y ↦ (le_of_eq ?_)).trans (hF.add hT)
      rw [fun_iteratedFDeriv_add_apply
        (((contDiff_expCommutator hℓ k).fderiv_right (m := ∞) le_rfl).contDiffAt.of_le
          (by simp))
        (((he.fderiv_right (m := ∞) le_rfl).smulRight
          (hℓ.iteratedFDeriv_right (m := ∞) (i := k) le_rfl)).contDiffAt.of_le
            (by simp))]
    -- The spaces are given explicitly: unifying them against the instances carried by the
    -- currying isometry otherwise fails.
    have hiso : ∀ (f : E → E →L[ℝ] E [×k]→L[ℝ] ℝ) (y : E),
        ‖iteratedFDeriv ℝ j ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E)
          ℝ).symm ∘ f) y‖ = ‖iteratedFDeriv ℝ j f y‖ := fun f y ↦
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := E)
        (F := E →L[ℝ] E [×k]→L[ℝ] ℝ) (G := E [×k + 1]→L[ℝ] ℝ) _ f y j
    rw [expCommutator_succ hℓ k]
    exact (isBigO_of_le _ fun y ↦ (hiso _ y).le).trans hsum

/-- **The inductive step.** For a smooth solution of `Δ ℓ = κ (exp ℓ - 1)` near infinity with
`exp ℓ → 1`, if the derivatives of `ℓ` of order at most `n ≥ 1` are `O(exp (-c ‖x‖))` and those of
`exp ℓ` are bounded, then so is the derivative of order `n + 1`, provided `c < a` and `a² < κ`:
`Dⁿℓ` solves `Δ Dⁿℓ = κ exp ℓ • Dⁿℓ + κ Cₙ`. -/
private theorem isBigO_iteratedFDeriv_succ_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ}
    {κ a c : ℝ} (hc : 0 < c) (hca : c < a) (hκa : a ^ 2 < κ) (hℓ : ContDiff ℝ ∞ ℓ)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (helim : Tendsto (fun x ↦ Real.exp (ℓ x)) (cocompact E) (𝓝 1)) {n : ℕ} (hn : 1 ≤ n)
    (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[cocompact E]
      fun _ ↦ (1 : ℝ)) :
    iteratedFDeriv ℝ (n + 1) ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  set e : E → ℝ := fun y ↦ Real.exp (ℓ y) with he_def
  have he : ContDiff ℝ ∞ e := Real.contDiff_exp.comp hℓ
  -- The equation for `Dⁿℓ` near infinity.
  have hDeq : ∀ᶠ x in cocompact E, Δ (iteratedFDeriv ℝ n ℓ) x =
      (κ * e x) • iteratedFDeriv ℝ n ℓ x + (κ • expCommutator ℓ n) x := by
    obtain ⟨R, -, hR⟩ :=
      hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := E) ▸ heq)
    filter_upwards [(tendsto_norm_cocompact_atTop (E := E)).eventually_gt_atTop R] with x hx
    have hloc : Δ ℓ =ᶠ[𝓝 x] κ • e - fun _ ↦ κ := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
      rw [hR (Set.mem_ofPred.mpr hy.le)]
      simp [e, mul_sub]
    rw [(hℓ.of_le (by simp)).laplacian_iteratedFDeriv,
      (hloc.iteratedFDeriv ℝ n).eq_of_nhds,
      iteratedFDeriv_sub_apply (f := κ • e) ((he.const_smul κ).contDiffAt.of_le (by simp))
        contDiffAt_const, iteratedFDeriv_const_of_ne (by omega),
      iteratedFDeriv_const_smul_apply (he.contDiffAt.of_le (by simp))]
    simp only [Pi.zero_apply, sub_zero, Pi.smul_apply, expCommutator, he_def]
    rw [smul_sub, mul_smul]
    abel
  have hd := isBigO_fderiv_of_laplacian_eq_smul_add (g := iteratedFDeriv ℝ n ℓ)
    (V := fun x ↦ κ * e x) (Φ := κ • expCommutator ℓ n) hc hca
    (Eventually.of_forall fun x ↦ (hℓ.iteratedFDeriv_right (m := 2) (by simp)).contDiffAt)
    (Eventually.of_forall fun x ↦ (he.differentiable (by simp) x).const_mul κ)
    ((helim.const_mul κ).eventually_const_le (by simpa using hκa)) ?_
    (Eventually.of_forall fun x ↦
      ((contDiff_expCommutator hℓ n).differentiable (by simp) x).const_smul κ) ?_ hDeq
    (hℓn n le_rfl)
  · refine (isBigO_of_le _ fun y ↦ le_of_eq ?_).trans hd
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map]
  · -- The potential has a bounded derivative.
    refine (isBigO_of_le' (c := |κ|) _ fun y ↦ le_of_eq ?_).trans (hen 1 hn)
    rw [fderiv_const_mul (he.differentiable (by simp) y), norm_smul, Real.norm_eq_abs,
      norm_iteratedFDeriv_one]
  · -- The forcing has an `O(exp (-c ‖x‖))` derivative.
    refine (isBigO_of_le' (c := |κ|) _ fun y ↦ le_of_eq ?_).trans
      (isBigO_iteratedFDeriv_expCommutator hℓ hℓn hen hn (j := 1) (by omega))
    rw [fderiv_const_smul ((contDiff_expCommutator hℓ n).differentiable (by simp) y), norm_smul,
      Real.norm_eq_abs, norm_iteratedFDeriv_one]

/-- **All derivatives of a globally smooth solution.** The derivatives of `ℓ` are
`O(exp (-c ‖x‖))` and those of `exp ℓ` are bounded, at every order. -/
private theorem isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one_of_contDiff {ℓ : E → ℝ}
    {κ c : ℝ} (hc : 0 < c) (hcκ : c ^ 2 < κ) (hℓ : ContDiff ℝ ∞ ℓ)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) (n : ℕ) :
    (∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) ∧
      ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[cocompact E]
        fun _ ↦ (1 : ℝ) := by
  set ρ : E → ℝ := fun x ↦ Real.exp (-(c * ‖x‖)) with hρ
  set e : E → ℝ := fun x ↦ Real.exp (ℓ x)
  have he : ContDiff ℝ ∞ e := Real.contDiff_exp.comp hℓ
  have hρ1 : ρ =O[cocompact E] fun _ ↦ (1 : ℝ) :=
    isBigO_of_le _ fun x ↦ by
      simp only [hρ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one, Real.exp_le_one_iff,
        Left.neg_nonpos_iff]
      positivity
  have he1 : (fun x ↦ e x - 1) =O[cocompact E] ρ :=
    Real.isBigO_exp_comp_sub_one (hℓd.trans_tendsto (tendsto_exp_neg_mul_norm_cocompact hc)) hℓd
  have helim : Tendsto e (cocompact E) (𝓝 1) := by
    simpa using (he1.trans_tendsto (tendsto_exp_neg_mul_norm_cocompact hc)).add_const 1
  have he0 : e =O[cocompact E] fun _ ↦ (1 : ℝ) := by
    simpa using (he1.trans hρ1).add (isBigO_refl (fun _ : E ↦ (1 : ℝ)) (cocompact E))
  -- A rate `a` between `c` and `√κ`.
  set a := Real.sqrt ((c ^ 2 + κ) / 2)
  have ha2 : a ^ 2 = (c ^ 2 + κ) / 2 := Real.sq_sqrt (by nlinarith)
  have hca : c < a := Real.lt_sqrt hc.le |>.mpr (by linarith)
  have hκa : a ^ 2 < κ := by rw [ha2]; linarith
  -- The first derivative, from `Δ ℓ = κ ℓ + κ (exp ℓ - 1 - ℓ)`.
  have hd1 : fderiv ℝ ℓ =O[cocompact E] ρ := by
    have hΦ : fderiv ℝ (fun x ↦ κ * (e x - 1 - ℓ x)) =
        fun x ↦ (κ * (e x - 1)) • fderiv ℝ ℓ x := by
      funext x
      have h1 : HasFDerivAt (fun x ↦ κ * (e x - 1 - ℓ x))
          (κ • (fderiv ℝ e x - fderiv ℝ ℓ x)) x :=
        (((he.differentiable (by simp) x).hasFDerivAt.sub_const 1).sub
          (hℓ.differentiable (by simp) x).hasFDerivAt).const_mul κ
      rw [h1.fderiv, fderiv_exp (hℓ.differentiable (by simp) x)]
      module
    refine isBigO_fderiv_of_laplacian_eq_smul_add (V := fun _ ↦ κ)
      (Φ := fun x ↦ κ * (e x - 1 - ℓ x)) hc hca
      (Eventually.of_forall fun x ↦ (hℓ.of_le (by simp)).contDiffAt)
      (Eventually.of_forall fun _ ↦ differentiableAt_const _)
      (Eventually.of_forall fun _ ↦ hκa.le) (by rw [fderiv_fun_const]; exact isBigO_zero _ _)
      (Eventually.of_forall fun x ↦ (((he.sub contDiff_const).sub hℓ).differentiable
        (by simp) x).const_mul κ) ?_ ?_ hℓd
    · rw [hΦ]
      simpa using (he1.const_mul_left κ).smul hℓ'
    · filter_upwards [heq] with x hx
      rw [hx, smul_eq_mul]
      ring
  induction n with
  | zero =>
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩ <;> obtain rfl : i = 0 := by omega
    · exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans hℓd
    · exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans he0
  | succ n ih =>
    have hnext : iteratedFDeriv ℝ (n + 1) ℓ =O[cocompact E] ρ := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact (isBigO_of_le _ fun y ↦ (norm_iteratedFDeriv_one ℓ).le).trans hd1
      · exact isBigO_iteratedFDeriv_succ_of_laplacian_eq_exp_sub_one hc hca hκa hℓ heq helim hn
          ih.1 ih.2
    have hℓall : ∀ i ≤ n + 1, iteratedFDeriv ℝ i ℓ =O[cocompact E] ρ := fun i hi ↦ by
      rcases Nat.lt_or_eq_of_le hi with h | rfl
      · exact ih.1 i (by omega)
      · exact hnext
    refine ⟨hℓall, fun i hi ↦ ?_⟩
    rcases Nat.lt_or_eq_of_le hi with h | rfl
    · exact ih.2 i (by omega)
    · exact ((hℓ.of_le (by simp)).isBigO_iteratedFDeriv_succ_exp (fun i _ hi ↦ hℓall i hi)
        ih.2).trans hρ1

/-- **Passing to a globally smooth solution.** A solution of `Δ ℓ = κ (exp ℓ - 1)` that is smooth
outside a compact set agrees near every point outside a compact set with a globally smooth `ℓ'`,
which solves the same equation there and inherits the decay of `ℓ` and the bound on its
derivative. -/
private theorem exists_contDiff_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ c : ℝ}
    (hℓ : ∀ᶠ x in cocompact E, ContDiffAt ℝ ∞ ℓ x)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) :
    ∃ ℓ' : E → ℝ, ContDiff ℝ ∞ ℓ' ∧ (∀ᶠ x in cocompact E, ℓ' =ᶠ[𝓝 x] ℓ) ∧
      (∀ᶠ x in cocompact E, Δ ℓ' x = κ * (Real.exp (ℓ' x) - 1)) ∧
      (ℓ' =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) ∧
      fderiv ℝ ℓ' =O[cocompact E] fun _ ↦ (1 : ℝ) := by
  obtain ⟨ℓ', hℓ'c, hagree⟩ := exists_contDiff_eventually_eventuallyEq hℓ
  have hfar : ℓ' =ᶠ[cocompact E] ℓ := hagree.mono fun x hx ↦ hx.eq_of_nhds
  refine ⟨ℓ', hℓ'c, hagree, ?_, hℓd.congr' hfar.symm EventuallyEq.rfl,
    hℓ'.congr' (hagree.mono fun x hx ↦ hx.fderiv_eq.symm) EventuallyEq.rfl⟩
  filter_upwards [hagree, heq] with x hx hx'
  rw [(laplacian_congr_nhds hx).eq_of_nhds, hx', hx.eq_of_nhds]

/-- **Exponential decay of all derivatives of solutions of `Δ ℓ = κ (exp ℓ - 1)`.** Let `ℓ` be
smooth outside a compact set and solve `Δ ℓ = κ (exp ℓ - 1)` there. If `ℓ` is `O(exp (-c ‖x‖))`
at infinity with `0 < c` and `c² < κ`, and its derivative is bounded at infinity, then every
iterated derivative of `ℓ` is `O(exp (-c ‖x‖))`. -/
theorem isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ c : ℝ} (hc : 0 < c)
    (hcκ : c ^ 2 < κ) (hℓ : ∀ᶠ x in cocompact E, ContDiffAt ℝ ∞ ℓ x)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) (n : ℕ) :
    iteratedFDeriv ℝ n ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  obtain ⟨ℓ', hℓ'c, hagree, heq', hℓd', hℓ'd⟩ :=
    exists_contDiff_of_laplacian_eq_exp_sub_one hℓ heq hℓd hℓ'
  have h := (isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one_of_contDiff hc hcκ hℓ'c heq' hℓd'
    hℓ'd n).1 n le_rfl
  exact h.congr' (hagree.mono fun x hx ↦ (hx.iteratedFDeriv ℝ n).eq_of_nhds) EventuallyEq.rfl

/-- **Exponential decay of all derivatives of `exp ℓ - 1`** for a solution of
`Δ ℓ = κ (exp ℓ - 1)`, under the hypotheses of
`TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`. -/
theorem isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ c : ℝ}
    (hc : 0 < c) (hcκ : c ^ 2 < κ) (hℓ : ∀ᶠ x in cocompact E, ContDiffAt ℝ ∞ ℓ x)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x ↦ Real.exp (ℓ x) - 1) =O[cocompact E]
      fun x ↦ Real.exp (-(c * ‖x‖)) := by
  obtain ⟨ℓ', hℓ'c, hagree, heq', hℓd', hℓ'd⟩ :=
    exists_contDiff_of_laplacian_eq_exp_sub_one hℓ heq hℓd hℓ'
  have hP := isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one_of_contDiff hc hcκ hℓ'c heq' hℓd'
    hℓ'd
  have h : iteratedFDeriv ℝ n (fun x ↦ Real.exp (ℓ' x) - 1) =O[cocompact E]
      fun x ↦ Real.exp (-(c * ‖x‖)) := by
    rcases n with _ | n
    · refine (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans
        (Real.isBigO_exp_comp_sub_one
          (hℓd'.trans_tendsto (tendsto_exp_neg_mul_norm_cocompact hc)) hℓd')
    · have he : ContDiff ℝ ∞ (fun x ↦ Real.exp (ℓ' x)) := Real.contDiff_exp.comp hℓ'c
      refine (isBigO_of_le _ fun y ↦ le_of_eq ?_).trans
        ((hℓ'c.of_le (by simp)).isBigO_iteratedFDeriv_succ_exp
          (fun i _ hi ↦ (hP (n + 1)).1 i hi) (hP n).2)
      rw [fun_iteratedFDeriv_sub_apply (he.contDiffAt.of_le (by simp)) contDiffAt_const,
        iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
  refine h.congr' (hagree.mono fun x hx ↦ ?_) EventuallyEq.rfl
  exact (((hx.fun_comp Real.exp).sub EventuallyEq.rfl).iteratedFDeriv ℝ n).eq_of_nhds

end TauCeti

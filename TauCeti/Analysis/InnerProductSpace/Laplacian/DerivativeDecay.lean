/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Topology.Compactness.Compact

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
(`TauCeti.norm_le_mul_exp_add_div_mul_exp_of_norm_laplacian_sub_smul_le`) bounds `D` by `‖h‖`
times the same exponential. Dividing by `‖h‖` bounds the derivative.

Iterating this gives the regularity at infinity of the Liouville-type equation

`Δ ℓ = κ (exp ℓ - 1)`,

the scalar equation of the plane vortex: if `ℓ` is `C^(n + 1)` near infinity, decays like
`exp (-c ‖x‖)` with `c² < κ`, and has a bounded derivative, then the iterated derivatives of `ℓ`
and of `exp ℓ - 1` of order `n` decay like `exp (-c ‖x‖)`
(`TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`,
`TauCeti.isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one`). The `n`-th derivative
`Dⁿℓ` solves `Δ Dⁿℓ = κ exp ℓ • Dⁿℓ + κ Cₙ`, where the commutator `Cₙ = Dⁿ (exp ℓ) - exp ℓ • Dⁿℓ`
involves only derivatives of order below `n`
(`TauCeti.isBigO_iteratedFDeriv_iteratedFDeriv_exp_sub_smul`), so each step of the induction is an
instance of the derivative estimate above. The rate is not lost along the induction.

## Main results

* `TauCeti.isBigO_fderiv_of_laplacian_eq_smul_add`: exponential decay of the derivative of a
  decaying solution of `Δ g = V • g + Φ`.
* `TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`: exponential decay of the iterated
  derivative of order `n` of a decaying `C^(n + 1)` solution of `Δ ℓ = κ (exp ℓ - 1)`.
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
  -- Compare `D` with the forced barrier.
  have hcomp := norm_le_mul_exp_add_div_mul_exp_of_norm_laplacian_sub_smul_le (u := D) (V := V)
    (R := R₁) (M := M * ‖h‖) (B := ‖h‖ * B) hR₁pos hc hca (by positivity) (by positivity)
    (fun y hy ↦ (hDcd y hy).continuousAt.continuousWithinAt) (fun y hy ↦ hDcd y hy.le)
    (fun y hy ↦ hVa y (by linarith)) (fun y hy ↦ hforce y hy.le) hbdry hDlim hx
  refine hcomp.trans_eq ?_
  rw [exp_neg_mul_sub]
  ring

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

/-- **The inductive step.** For a `C^(n + 2)` solution of `Δ ℓ = κ (exp ℓ - 1)` near infinity with
`exp ℓ → 1`, if the derivatives of `ℓ` of order at most `n ≥ 1` are `O(exp (-c ‖x‖))` and those of
`exp ℓ` are bounded, then so is the derivative of order `n + 1`, provided `c < a` and `a² < κ`:
`Dⁿℓ` solves `Δ Dⁿℓ = κ exp ℓ • Dⁿℓ + κ Cₙ` with the commutator `Cₙ = Dⁿ (exp ℓ) - exp ℓ • Dⁿℓ`. -/
private theorem isBigO_iteratedFDeriv_succ_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ}
    {κ a c : ℝ} {n : ℕ} (hc : 0 < c) (hca : c < a) (hκa : a ^ 2 < κ) (hn : 1 ≤ n)
    (hℓ : ContDiff ℝ (n + 2) ℓ) (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (helim : Tendsto (fun x ↦ Real.exp (ℓ x)) (cocompact E) (𝓝 1))
    (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[cocompact E]
      fun _ ↦ (1 : ℝ)) :
    iteratedFDeriv ℝ (n + 1) ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  set e : E → ℝ := fun y ↦ Real.exp (ℓ y) with he_def
  have he : ContDiff ℝ (n + 2) e := Real.contDiff_exp.comp hℓ
  -- The commutator `Cₙ`.
  set C : E → E [×n]→L[ℝ] ℝ := fun x ↦ iteratedFDeriv ℝ n e x - e x • iteratedFDeriv ℝ n ℓ x
    with hC_def
  have hC : ContDiff ℝ 1 C :=
    (he.iteratedFDeriv_right (by norm_cast; omega)).sub ((he.of_le (by norm_cast; omega)).smul
      (hℓ.iteratedFDeriv_right (by norm_cast; omega)))
  -- The equation for `Dⁿℓ` near infinity.
  have hDeq : ∀ᶠ x in cocompact E, Δ (iteratedFDeriv ℝ n ℓ) x =
      (κ * e x) • iteratedFDeriv ℝ n ℓ x + (κ • C) x := by
    filter_upwards [heq.eventually_nhds_cocompact] with x hx
    have hloc : Δ ℓ =ᶠ[𝓝 x] κ • e - fun _ ↦ κ := hx.mono fun y hy ↦ by
      rw [hy]
      simp [e, mul_sub]
    rw [hℓ.contDiffAt.laplacian_iteratedFDeriv, (hloc.iteratedFDeriv ℝ n).eq_of_nhds,
      iteratedFDeriv_sub_apply (f := κ • e)
        ((he.const_smul κ).contDiffAt.of_le (by norm_cast; omega)) contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega),
      iteratedFDeriv_const_smul_apply (he.contDiffAt.of_le (by norm_cast; omega))]
    simp only [Pi.zero_apply, sub_zero, Pi.smul_apply, hC_def, he_def]
    rw [smul_sub, mul_smul]
    abel
  have hd := isBigO_fderiv_of_laplacian_eq_smul_add (g := iteratedFDeriv ℝ n ℓ)
    (V := fun x ↦ κ * e x) (Φ := κ • C) hc hca
    (Eventually.of_forall fun x ↦
      (hℓ.iteratedFDeriv_right (m := 2) (by norm_cast; omega)).contDiffAt)
    (Eventually.of_forall fun x ↦ (he.differentiable (by simp) x).const_mul κ)
    ((helim.const_mul κ).eventually_const_le (by simpa using hκa)) ?_
    (Eventually.of_forall fun x ↦ (hC.differentiable (by simp) x).const_smul κ) ?_ hDeq
    (hℓn n le_rfl)
  · refine (isBigO_of_le _ fun y ↦ le_of_eq ?_).trans hd
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map]
  · -- The potential has a bounded derivative.
    refine (isBigO_of_le' (c := |κ|) _ fun y ↦ le_of_eq ?_).trans (hen 1 hn)
    rw [fderiv_const_mul (he.differentiable (by simp) y), norm_smul, Real.norm_eq_abs,
      norm_iteratedFDeriv_one]
  · -- The forcing has an `O(exp (-c ‖x‖))` derivative.
    refine (isBigO_of_le' (c := |κ|) _ fun y ↦ le_of_eq ?_).trans
      (isBigO_iteratedFDeriv_iteratedFDeriv_exp_sub_smul (j := 1) hn
        (Eventually.of_forall fun _ ↦ (hℓ.of_le (by norm_cast; omega)).contDiffAt)
        (fun i _ hi ↦ hℓn i (by omega)) fun i _ hi ↦ hen i (by omega))
    rw [fderiv_const_smul (hC.differentiable (by simp) y), norm_smul, Real.norm_eq_abs,
      norm_iteratedFDeriv_one]

/-- **The first derivative of a global `C²` solution.** If `ℓ` is `O(exp (-c ‖x‖))` with a
bounded derivative, then its derivative is `O(exp (-c ‖x‖))` too, provided `c < a` and `a² < κ`:
`ℓ` solves `Δ ℓ = κ ℓ + κ (exp ℓ - 1 - ℓ)`, whose forcing has derivative `κ (exp ℓ - 1) Dℓ`. -/
private theorem isBigO_fderiv_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ a c : ℝ} (hc : 0 < c)
    (hca : c < a) (hκa : a ^ 2 < κ) (hℓ : ContDiff ℝ 2 ℓ)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) :
    fderiv ℝ ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  set e : E → ℝ := fun x ↦ Real.exp (ℓ x)
  have he : ContDiff ℝ 2 e := Real.contDiff_exp.comp hℓ
  have he1 : (fun x ↦ e x - 1) =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) :=
    Real.isBigO_exp_comp_sub_one (hℓd.trans_tendsto (tendsto_exp_neg_mul_norm_cocompact hc)) hℓd
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
    (Eventually.of_forall fun x ↦ hℓ.contDiffAt)
    (Eventually.of_forall fun _ ↦ differentiableAt_const _)
    (Eventually.of_forall fun _ ↦ hκa.le) (by rw [fderiv_fun_const]; exact isBigO_zero _ _)
    (Eventually.of_forall fun x ↦ (((he.sub contDiff_const).sub hℓ).differentiable
      (by simp) x).const_mul κ) ?_ ?_ hℓd
  · rw [hΦ]
    simpa using (he1.const_mul_left κ).smul hℓ'
  · filter_upwards [heq] with x hx
    rw [hx, smul_eq_mul]
    ring

/-- **The derivatives of a global `C^(n + 1)` solution.** The derivatives of `ℓ` of order at most
`n` are `O(exp (-c ‖x‖))`. -/
private theorem isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one_of_contDiff {ℓ : E → ℝ}
    {κ c : ℝ} (hc : 0 < c) (hcκ : c ^ 2 < κ) (n : ℕ) (hℓ : ContDiff ℝ (n + 1) ℓ)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) :
    ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  have hρ1 := (tendsto_exp_neg_mul_norm_cocompact (E := E) hc).isBigO_one (F := ℝ)
  have hℓ0 : Tendsto ℓ (cocompact E) (𝓝 0) :=
    hℓd.trans_tendsto (tendsto_exp_neg_mul_norm_cocompact hc)
  have helim : Tendsto (fun x ↦ Real.exp (ℓ x)) (cocompact E) (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hℓ0
  have he1 := helim.isBigO_one (F := ℝ)
  -- A rate `a` between `c` and `√κ`.
  set a := Real.sqrt ((c ^ 2 + κ) / 2)
  have ha2 : a ^ 2 = (c ^ 2 + κ) / 2 := Real.sq_sqrt (by nlinarith)
  have hca : c < a := Real.lt_sqrt hc.le |>.mpr (by linarith)
  have hκa : a ^ 2 < κ := by rw [ha2]; linarith
  induction n with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans hℓd
  | succ n ih =>
    have ih := ih (hℓ.of_le (by norm_cast; omega))
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with h | rfl
    · exact ih i (by omega)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (isBigO_of_le _ fun y ↦ (norm_iteratedFDeriv_one ℓ).le).trans
        (isBigO_fderiv_of_laplacian_eq_exp_sub_one hc hca hκa (by exact_mod_cast hℓ) heq hℓd hℓ')
    · exact isBigO_iteratedFDeriv_succ_of_laplacian_eq_exp_sub_one hc hca hκa hn
        (by exact_mod_cast hℓ) heq helim ih fun i hi ↦ isBigO_iteratedFDeriv_exp
          (Eventually.of_forall fun _ ↦ (hℓ.of_le (by norm_cast; omega)).contDiffAt) he1
          fun j _ hj ↦ (ih j (by omega)).trans hρ1

/-- **Passing to a global solution.** A solution of `Δ ℓ = κ (exp ℓ - 1)` that is `C^m` outside a
compact set agrees near every point outside a compact set with a globally `C^m` function `ℓ'`,
which solves the same equation there and inherits the decay of `ℓ` and the bound on its
derivative. -/
private theorem exists_contDiff_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ c : ℝ} {m : ℕ}
    (hℓ : ∀ᶠ x in cocompact E, ContDiffAt ℝ m ℓ x)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) :
    ∃ ℓ' : E → ℝ, ContDiff ℝ m ℓ' ∧ (∀ᶠ x in cocompact E, ℓ' =ᶠ[𝓝 x] ℓ) ∧
      (∀ᶠ x in cocompact E, Δ ℓ' x = κ * (Real.exp (ℓ' x) - 1)) ∧
      (ℓ' =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) ∧
      fderiv ℝ ℓ' =O[cocompact E] fun _ ↦ (1 : ℝ) := by
  obtain ⟨ℓ', hℓ'c, hagree⟩ := exists_contDiff_eventually_eventuallyEq (n := m) hℓ
  have hfar : ℓ' =ᶠ[cocompact E] ℓ := hagree.mono fun x hx ↦ hx.eq_of_nhds
  refine ⟨ℓ', hℓ'c, hagree, ?_, hℓd.congr' hfar.symm EventuallyEq.rfl,
    hℓ'.congr' (hagree.mono fun x hx ↦ hx.fderiv_eq.symm) EventuallyEq.rfl⟩
  filter_upwards [hagree, heq] with x hx hx'
  rw [(laplacian_congr_nhds hx).eq_of_nhds, hx', hx.eq_of_nhds]

/-- **Exponential decay of the derivatives of solutions of `Δ ℓ = κ (exp ℓ - 1)`.** Let `ℓ` be
`C^(n + 1)` outside a compact set and solve `Δ ℓ = κ (exp ℓ - 1)` there. If `ℓ` is
`O(exp (-c ‖x‖))` at infinity with `0 < c` and `c² < κ`, and its derivative is bounded at
infinity, then its iterated derivative of order `n` is `O(exp (-c ‖x‖))`. -/
theorem isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ c : ℝ} {n : ℕ}
    (hc : 0 < c) (hcκ : c ^ 2 < κ) (hℓ : ∀ᶠ x in cocompact E, ContDiffAt ℝ (n + 1) ℓ x)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) :
    iteratedFDeriv ℝ n ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  obtain ⟨ℓ', hℓ'c, hagree, heq', hℓd', hℓ'd⟩ :=
    exists_contDiff_of_laplacian_eq_exp_sub_one (m := n + 1) (by exact_mod_cast hℓ) heq hℓd hℓ'
  have h := isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one_of_contDiff hc hcκ n
    (by exact_mod_cast hℓ'c) heq' hℓd' hℓ'd n le_rfl
  exact h.congr' (hagree.mono fun x hx ↦ (hx.iteratedFDeriv ℝ n).eq_of_nhds) EventuallyEq.rfl

/-- **Exponential decay of the derivatives of `exp ℓ - 1`** for a solution of
`Δ ℓ = κ (exp ℓ - 1)`, under the hypotheses of
`TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`. -/
theorem isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ c : ℝ}
    {n : ℕ} (hc : 0 < c) (hcκ : c ^ 2 < κ) (hℓ : ∀ᶠ x in cocompact E, ContDiffAt ℝ (n + 1) ℓ x)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (hℓ' : fderiv ℝ ℓ =O[cocompact E] fun _ ↦ (1 : ℝ)) :
    iteratedFDeriv ℝ n (fun x ↦ Real.exp (ℓ x) - 1) =O[cocompact E]
      fun x ↦ Real.exp (-(c * ‖x‖)) :=
  isBigO_iteratedFDeriv_exp_sub_one (hℓ.mono fun _ hx ↦ hx.of_le (by norm_cast; omega))
    (hℓd.trans_tendsto (tendsto_exp_neg_mul_norm_cocompact hc))
    ((tendsto_exp_neg_mul_norm_cocompact hc).isBigO_one (F := ℝ)) fun i hi ↦
      isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one hc hcκ
        (hℓ.mono fun _ hx ↦ hx.of_le (by norm_cast; omega)) heq hℓd hℓ'

end TauCeti

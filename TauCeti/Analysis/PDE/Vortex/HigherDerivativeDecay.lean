/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.SmulConst
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import TauCeti.Analysis.InnerProductSpace.Laplacian.IteratedFDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.IteratedFDerivComp
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Exponential decay of all derivatives of a plane vortex

Let `x` be a smooth plane vortex whose section satisfies `|α| → 1` at infinity. Outside the zeros
of `α`, the logarithmic modulus `ℓ = log |α|²` solves the scalar equation

`Δ ℓ = (exp ℓ - 1) / 4`

(`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`), and `ℓ` and its gradient decay like
`exp (-c |z|)` for every `c < 1 / 2`
(`TauCeti.Vortex.exists_eventually_norm_fderiv_log_normSq_le_mul_exp`).
This file proves the same decay for the derivatives of every order, and deduces that the winding-`m`
end trivialization of a vortex normalized at its end converges to the vacuum `(0, 1)` together with
all its derivatives.

**The scalar equation.** Let `ℓ` be a smooth solution of `Δ ℓ = (exp ℓ - 1) / 4` outside a disc
with `ℓ → 0` and decaying gradient, and put `E = exp ℓ`. The Laplacian commutes with the iterated
derivatives (`ContDiff.laplacian_iteratedFDeriv`), so for `n ≥ 1` the field `F = Dⁿ ℓ` of
multilinear maps solves `Δ F = Dⁿ E / 4`. By the Leibniz rule applied to `D E = E • D ℓ`,
`Dⁿ E = E • F + ρ`, where the residual `ρ` involves only derivatives of order less than `n`. For a
translation `k` with `|k| ≤ 1`, the difference `D = F - F (· + k)` therefore solves

`Δ D = (E / 4) • D + H`,  `H = ((ρ - ρ (· + k)) + (E - E (· + k)) • F (· + k)) / 4`.

If the derivatives of orders `1, …, n` decay at rate `c`, the forcing is `O(|k| exp (-c |z|))`.
Since `E / 4 → 1 / 4 > c²`, the comparison principle for forced vector-valued equations
(`TauCeti.norm_le_mul_exp_add_mul_exp_of_laplacian_eq`) bounds `‖D‖` by `|k| K exp (-c |z|)`, and
dividing by `|k|` bounds `Dⁿ⁺¹ ℓ`. Translation differences are used instead of `Dⁿ⁺¹ ℓ` itself
because the comparison principle needs a function known to tend to zero at infinity.

**The end trivialization.** Where the section of `x` is `|α|` times the winding phase `(z / |z|)^m`,
the end trivialization `y = (z / |z|)^(-m) · x` has the real section `|α| = exp (ℓ / 2)`, and the
holomorphicity rows of the vortex equation determine its connection:
`y = (-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)`. Hence every derivative of `y` minus the
vacuum decays at every rate `c < 1 / 2`.

These are estimates for one smooth vortex; uniformity over compact families of divisors and decay
of derivatives in the divisor parameters are not treated here.

## Main results

* `TauCeti.Vortex.exists_eventually_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq`: every
  derivative of a solution of `Δ ℓ = (exp ℓ - 1) / 4` whose gradient decays at a rate
  `0 < c < 1 / 2` decays at the same rate.
* `TauCeti.Vortex.exists_eventually_norm_iteratedFDeriv_log_normSq_le_mul_exp`: every derivative
  of `log |α|²` decays at every rate `c < 1 / 2`.
* `exists_eventually_norm_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_le_mul_exp`:
  every derivative of the winding end trivialization minus the vacuum decays at every rate
  `c < 1 / 2`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology Asymptotics InnerProductSpace Laplacian
open scoped ContDiff

/-! ### The scalar equation `Δ ℓ = (exp ℓ - 1) / 4` -/

/-- For `c ≥ 0` the weight `exp (-c |z|)` is bounded. -/
private theorem isBigO_exp_neg_mul_norm_one {c : ℝ} (hc : 0 ≤ c) :
    (fun z : ℂ ↦ Real.exp (-(c * ‖z‖))) =O[cocompact ℂ] fun _ ↦ (1 : ℝ) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, norm_one, one_mul, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (by positivity))

/-- Every finite order `n + 2` is at most `∞`. -/
private theorem natCast_add_two_le_infty (n : ℕ) : (n : WithTop ℕ∞) + 2 ≤ ∞ := by
  rw [← Nat.cast_ofNat, ← Nat.cast_add]
  exact WithTop.coe_le_coe.2 le_top

/-- Outside the disc where `Δ ℓ = (exp ℓ - 1) / 4` holds, the Laplacian of `D^n ℓ`, `n ≥ 1`, is
`(1 / 4) • D^n (exp ∘ ℓ)`. -/
private theorem laplacian_iteratedFDeriv_of_laplacian_eq {ℓ : ℂ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ)
    {R₀ : ℝ} (heq : ∀ z : ℂ, R₀ < ‖z‖ → Δ ℓ z = (Real.exp (ℓ z) - 1) / 4) {n : ℕ} (hn : n ≠ 0)
    {w : ℂ} (hw : R₀ < ‖w‖) :
    Δ (iteratedFDeriv ℝ n ℓ) w = (1 / 4 : ℝ) • iteratedFDeriv ℝ n (fun v ↦ Real.exp (ℓ v)) w := by
  have hE : ContDiff ℝ ∞ (fun v ↦ Real.exp (ℓ v)) := Real.contDiff_exp.comp hℓ
  have hloc : Δ ℓ =ᶠ[𝓝 w] (fun v ↦ (1 / 4 : ℝ) • Real.exp (ℓ v)) - fun _ ↦ (1 / 4 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with v hv
    rw [heq v hv, Pi.sub_apply, smul_eq_mul]
    ring
  rw [congrFun (hℓ.of_le (natCast_add_two_le_infty n)).laplacian_iteratedFDeriv w,
    (hloc.iteratedFDeriv ℝ n).eq_of_nhds,
    iteratedFDeriv_sub_apply ((hE.const_smul _).contDiffAt.of_le (by exact_mod_cast le_top))
      contDiffAt_const, iteratedFDeriv_const_of_ne hn, Pi.zero_apply, sub_zero,
    iteratedFDeriv_const_smul_apply' (hE.contDiffAt.of_le (by exact_mod_cast le_top))]

/-- **The forcing of a translation difference.** Write `E = exp ∘ ℓ`, `F = D^n ℓ`, `n ≥ 1`, and
`ρ = D^n E - E • F` for the Leibniz residual. Where `Δ ℓ = (E - 1) / 4` holds at `w` and `w + k`,
the difference `D = F - F (· + k)` solves `Δ D = (E / 4) • D + H` with
`H = (1 / 4) • ((ρ w - ρ (w + k)) + (E w - E (w + k)) • F (w + k))`. -/
private theorem laplacian_sub_comp_add_sub_smul {ℓ : ℂ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) {R₀ : ℝ}
    (heq : ∀ z : ℂ, R₀ < ‖z‖ → Δ ℓ z = (Real.exp (ℓ z) - 1) / 4) {n : ℕ} (hn : n ≠ 0)
    {w k : ℂ} (hw : R₀ < ‖w‖) (hwk : R₀ < ‖w + k‖) :
    Δ (iteratedFDeriv ℝ n ℓ - fun v ↦ iteratedFDeriv ℝ n ℓ (v + k)) w -
        (Real.exp (ℓ w) / 4) •
          (iteratedFDeriv ℝ n ℓ w - iteratedFDeriv ℝ n ℓ (w + k)) =
      (1 / 4 : ℝ) • (((iteratedFDeriv ℝ n (fun v ↦ Real.exp (ℓ v)) w -
          Real.exp (ℓ w) • iteratedFDeriv ℝ n ℓ w) -
        (iteratedFDeriv ℝ n (fun v ↦ Real.exp (ℓ v)) (w + k) -
          Real.exp (ℓ (w + k)) • iteratedFDeriv ℝ n ℓ (w + k))) +
        (Real.exp (ℓ w) - Real.exp (ℓ (w + k))) • iteratedFDeriv ℝ n ℓ (w + k)) := by
  have hF : ContDiff ℝ ∞ (iteratedFDeriv ℝ n ℓ) :=
    hℓ.iteratedFDeriv_right (by exact_mod_cast le_top)
  have hFk : ContDiff ℝ ∞ fun v ↦ iteratedFDeriv ℝ n ℓ (v + k) :=
    hF.comp (contDiff_id.add contDiff_const)
  rw [(hF.contDiffAt.of_le (by norm_cast)).laplacian_sub (hFk.contDiffAt.of_le (by norm_cast)),
    congrFun (laplacian_comp_add_right _ k) w,
    laplacian_iteratedFDeriv_of_laplacian_eq hℓ heq hn hw,
    laplacian_iteratedFDeriv_of_laplacian_eq hℓ heq hn hwk]
  simp only [smul_sub, smul_add, sub_smul, smul_smul, div_eq_mul_inv]
  abel_nf
  module

/-- **One more derivative decays.** Let `ℓ` be a smooth solution of `Δ ℓ = (exp ℓ - 1) / 4`
outside a disc with `ℓ → 0` at infinity, and let `0 < c < 1 / 2`. If the derivatives of `ℓ` of
orders `1, …, n`, `n ≥ 1`, are `O(exp (-c |z|))` at infinity, then so is the derivative of order
`n + 1`.

The translation difference `D = D^n ℓ - D^n ℓ (· + k)` solves `Δ D = (exp ℓ / 4) • D + H`, where
the forcing `H` involves only derivatives of order at most `n` and is `O(|k| exp (-c |z|))`
(`laplacian_sub_comp_add_sub_smul`). Since `exp ℓ / 4 → 1 / 4 > c²`, the forced comparison
principle bounds `‖D‖` by `|k| K exp (-c |z|)`, and dividing by `|k|` bounds `D^(n+1) ℓ`. -/
private theorem isBigO_norm_iteratedFDeriv_succ {ℓ : ℂ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) {R₀ : ℝ}
    (heq : ∀ z : ℂ, R₀ < ‖z‖ → Δ ℓ z = (Real.exp (ℓ z) - 1) / 4)
    (hlim : Tendsto ℓ (cocompact ℂ) (𝓝 0)) {c : ℝ} (hc₀ : 0 < c) (hc : c < 1 / 2) {n : ℕ}
    (hn : 1 ≤ n)
    (hdec : ∀ j, 1 ≤ j → j ≤ n →
      (fun z ↦ ‖iteratedFDeriv ℝ j ℓ z‖) =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖))) :
    (fun z ↦ ‖iteratedFDeriv ℝ (n + 1) ℓ z‖) =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  -- The proof has four steps: explicit decay bounds for `D ρ`, `D E` and `F = Dⁿ ℓ`; a radius `R`
  -- beyond which they hold and `exp ℓ / 4 ≥ c² + δ`; the forced comparison principle for the
  -- translation differences `F - F (· + k)`; and division by `|k|`.
  set E : ℂ → ℝ := fun w ↦ Real.exp (ℓ w) with hEdef
  set F := iteratedFDeriv ℝ n ℓ with hFdef
  set ρ := fun w ↦ iteratedFDeriv ℝ n E w - E w • F w with hρdef
  have hE : ContDiff ℝ ∞ E := Real.contDiff_exp.comp hℓ
  have hF : ContDiff ℝ ∞ F := hℓ.iteratedFDeriv_right (by exact_mod_cast le_top)
  have hρ : ContDiff ℝ ∞ ρ :=
    (hE.iteratedFDeriv_right (by exact_mod_cast le_top)).sub (hE.smul hF)
  have hElim : Tendsto E (cocompact ℂ) (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hlim
    rwa [Real.exp_zero] at h
  have hEbdd : E =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := hElim.isBigO_one ℝ
  -- Explicit bounds for `D ρ`, `D E` and `F` outside a disc of radius `R₁`.
  obtain ⟨K₁, R₁, hK₁, hρb⟩ := exists_nonneg_forall_norm_le_mul_exp_of_isBigO
    (isBigO_norm_fderiv_iteratedFDeriv_exp_comp_sub_smul hℓ (isBigO_exp_neg_mul_norm_one hc₀.le)
      hEbdd hn hdec)
  have hE1 := isBigO_norm_iteratedFDeriv_exp_comp hℓ (isBigO_exp_neg_mul_norm_one hc₀.le) hEbdd
    hdec le_rfl hn
  simp only [norm_iteratedFDeriv_one] at hE1
  obtain ⟨K₂, R₂, hK₂, hEb⟩ := exists_nonneg_forall_norm_le_mul_exp_of_isBigO hE1
  obtain ⟨K₃, R₃, hK₃, hFb⟩ := exists_nonneg_forall_norm_le_mul_exp_of_isBigO (hdec n hn le_rfl)
  simp only [norm_norm] at hEb hFb
  replace hρb : ∀ z : ℂ, R₁ ≤ ‖z‖ → ‖fderiv ℝ ρ z‖ ≤ K₁ * Real.exp (-(c * ‖z‖)) := fun z hz ↦ by
    have h := hρb z hz
    rwa [Real.norm_eq_abs, abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _)] at h
  -- The potential `exp ℓ / 4` exceeds `c² + δ` outside a disc of radius `R₄`.
  set δ := (1 / 4 - c ^ 2) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; nlinarith
  obtain ⟨R₄, -, hVb⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ (hElim.div_const 4).eventually
      (lt_mem_nhds (show c ^ 2 + δ < 1 / 4 by rw [hδdef]; nlinarith)))
  set R := max (max R₀ (max R₁ (max R₂ (max R₃ R₄)))) 0 + 2 with hRdef
  have hR : ∀ w : ℂ, R - 1 ≤ ‖w‖ →
      R₀ + 1 ≤ ‖w‖ ∧ R₁ + 1 ≤ ‖w‖ ∧ R₂ + 1 ≤ ‖w‖ ∧ R₃ + 1 ≤ ‖w‖ ∧ R₄ + 1 ≤ ‖w‖ :=
    fun w hw ↦ by
    simp only [hRdef] at hw
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [le_max_left R₀ (max R₁ (max R₂ (max R₃ R₄))), le_max_right R₀
      (max R₁ (max R₂ (max R₃ R₄))), le_max_left R₁ (max R₂ (max R₃ R₄)),
      le_max_right R₁ (max R₂ (max R₃ R₄)), le_max_left R₂ (max R₃ R₄),
      le_max_right R₂ (max R₃ R₄), le_max_left R₃ R₄, le_max_right R₃ R₄,
      le_max_left (max R₀ (max R₁ (max R₂ (max R₃ R₄)))) 0,
      le_max_right (max R₀ (max R₁ (max R₂ (max R₃ R₄)))) 0]
  have hR₀ : 0 < R := by simp only [hRdef]; positivity
  -- A bound `L` for `D F` on the annulus `R - 1 ≤ |w| ≤ R + 1`.
  obtain ⟨L₀, hL₀⟩ := ((isCompact_closedBall (0 : ℂ) (R + 1)).inter_right
    (isClosed_le continuous_const continuous_norm)).exists_bound_of_continuousOn
    (f := fderiv ℝ F) (hF.continuous_fderiv (by simp)).continuousOn
  set L := max L₀ 0
  set Γ := (K₁ * Real.exp c + K₂ * Real.exp c * (K₃ * Real.exp c)) / 4
  have hexp0 : Tendsto (fun z : ℂ ↦ K₃ * Real.exp (-(c * ‖z‖))) (cocompact ℂ) (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      ((tendsto_norm_cocompact_atTop (E := ℂ)).const_mul_atTop hc₀))).const_mul K₃
    rw [mul_zero] at h
    exact h
  have hFlim : Tendsto F (cocompact ℂ) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall
      fun z ↦ norm_nonneg _) ?_ hexp0)
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop R₃] with z hz
    exact hFb z hz
  -- The translation differences decay at rate `c`, uniformly in `|k| ≤ 1`.
  have hD (k : ℂ) (hk : ‖k‖ ≤ 1) (z : ℂ) (hz : R ≤ ‖z‖) :
      ‖F z - F (z + k)‖ ≤ ‖k‖ * (L * Real.exp (c * R) + Γ / δ) * Real.exp (-(c * ‖z‖)) := by
    have hforce (w : ℂ) (hw : R < ‖w‖) :
        ‖Δ (F - fun v ↦ F (v + k)) w - (E w / 4) • (F - fun v ↦ F (v + k)) w‖ ≤
          Γ * ‖k‖ * Real.exp (-(c * ‖w‖)) := by
      have hw₁ := hR w (by linarith)
      have hwk : R - 1 ≤ ‖w + k‖ := by
        have := norm_sub_norm_le w (-k)
        rw [sub_neg_eq_add, norm_neg] at this
        linarith
      rw [Pi.sub_apply, laplacian_sub_comp_add_sub_smul hℓ heq (by omega) (by linarith [hw₁.1])
          (by linarith [(hR _ hwk).1]),
        norm_smul, Real.norm_of_nonneg (by norm_num)]
      have hρk := norm_sub_comp_add_le_of_norm_fderiv_le (hρ.differentiable (by simp)) hc₀.le
        hK₁ hρb (z := w) (by linarith [hw₁.2.1]) hk
      have hEk := norm_sub_comp_add_le_of_norm_fderiv_le (hE.differentiable (by simp)) hc₀.le
        hK₂ hEb (z := w) (by linarith [hw₁.2.2.1]) hk
      have hFk : ‖F (w + k)‖ ≤ K₃ * Real.exp c * Real.exp (-(c * ‖w‖)) := by
        refine (hFb _ (by linarith [(hR _ hwk).2.2.2.1])).trans ?_
        rw [mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK₃
        have := norm_sub_norm_le w (-k)
        rw [sub_neg_eq_add, norm_neg] at this
        nlinarith
      have hexp : Real.exp (-(c * ‖w‖)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg w])
      have hEk' : ‖E w - E (w + k)‖ ≤ K₂ * Real.exp c * ‖k‖ := hEk.trans (by
        have := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ K₂ * Real.exp c)
        nlinarith [norm_nonneg k])
      calc 1 / 4 * ‖(ρ w - ρ (w + k)) + (E w - E (w + k)) • F (w + k)‖
          ≤ 1 / 4 * (‖ρ w - ρ (w + k)‖ + ‖E w - E (w + k)‖ * ‖F (w + k)‖) := by
            gcongr
            exact (norm_add_le _ _).trans
              (add_le_add le_rfl (norm_smul_le (E w - E (w + k)) (F (w + k))))
        _ ≤ 1 / 4 * (K₁ * Real.exp c * Real.exp (-(c * ‖w‖)) * ‖k‖ +
            K₂ * Real.exp c * ‖k‖ * (K₃ * Real.exp c * Real.exp (-(c * ‖w‖)))) := by
            gcongr
        _ = Γ * ‖k‖ * Real.exp (-(c * ‖w‖)) := by ring
    have hbdry (w : ℂ) (hw : ‖w‖ = R) : ‖(F - fun v ↦ F (v + k)) w‖ ≤ L * ‖k‖ := by
      have hball : closedBall w 1 ⊆ closedBall 0 (R + 1) ∩ {v | R - 1 ≤ ‖v‖} := fun v hv ↦ by
        rw [mem_closedBall, dist_eq_norm] at hv
        have := abs_norm_sub_norm_le v w
        rw [abs_le] at this
        exact ⟨mem_closedBall_zero_iff.mpr (by linarith), show R - 1 ≤ ‖v‖ by linarith⟩
      have h := (convex_closedBall w 1).norm_image_sub_le_of_norm_fderiv_le (f := F) (C := L)
        (fun v _ ↦ hF.differentiable (by simp) v)
        (fun v hv ↦ (hL₀ v (hball hv)).trans (le_max_left _ _)) (mem_closedBall_self zero_le_one)
        (show w + k ∈ closedBall w 1 by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
      rwa [add_sub_cancel_left, norm_sub_rev] at h
    have hDlim : Tendsto (F - fun v ↦ F (v + k)) (cocompact ℂ) (𝓝 0) := by
      have := hFlim.sub (hFlim.comp (Homeomorph.addRight k).isClosedEmbedding.tendsto_cocompact)
      exact (by simpa [Function.comp_def] using this :
        Tendsto (fun v ↦ F v - F (v + k)) (cocompact ℂ) (𝓝 0))
    have h := norm_le_mul_exp_add_mul_exp_of_laplacian_eq (D := F - fun v ↦ F (v + k))
      (H := fun w ↦ Δ (F - fun v ↦ F (v + k)) w - (E w / 4) • (F - fun v ↦ F (v + k)) w)
      (V := fun w ↦ E w / 4) (M := L * ‖k‖) (G := Γ * ‖k‖) hR₀ hc₀ hδ (by positivity)
      (by positivity) (hF.continuous.sub (hF.continuous.comp
        (continuous_id.add continuous_const))).continuousOn
      (fun w _ ↦ (hF.sub (hF.comp (contDiff_id.add contDiff_const))).contDiffAt.of_le
        (by norm_cast))
      (fun w hw ↦ (hVb (show R₄ ≤ ‖w‖ by linarith [(hR w (by linarith)).2.2.2.2])).le)
      (fun w _ ↦ by simp) hforce hbdry
      hDlim hz
    rw [Pi.sub_apply, exp_neg_mul_sub] at h
    calc ‖F z - F (z + k)‖ ≤ _ := h
      _ = _ := by field_simp
  -- Dividing by `|k|` bounds `D^(n+1) ℓ = D F`.
  refine IsBigO.of_bound (L * Real.exp (c * R) + Γ / δ) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop R] with z hz
  have hd : HasFDerivAt F (fderiv ℝ F z) z := (hF.differentiable (by simp) z).hasFDerivAt
  have hle := hd.le_of_lip' (C := (L * Real.exp (c * R) + Γ / δ) * Real.exp (-(c * ‖z‖)))
    (by positivity) (by
    filter_upwards [closedBall_mem_nhds z one_pos] with y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have h := hD (y - z) hy z hz
    rw [add_sub_cancel, norm_sub_rev] at h
    exact h.trans_eq (by ring))
  rw [← norm_fderiv_iteratedFDeriv, Real.norm_eq_abs,
    abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hle

/-- **All derivatives of a solution of `Δ ℓ = (exp ℓ - 1) / 4` decay exponentially.** Let `ℓ` be
a smooth function on the plane which solves `Δ ℓ = (exp ℓ - 1) / 4` outside a compact set and tends
to `0` at infinity, and let `0 < c < 1 / 2`. If the gradient of `ℓ` is bounded by `K exp (-c |z|)`
outside a compact set, then for every `n ≥ 1` so is the `n`-th derivative of `ℓ`, with another
constant `K`. -/
theorem exists_eventually_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq {ℓ : ℂ → ℝ}
    (hℓ : ContDiff ℝ ∞ ℓ) (heq : ∀ᶠ z in cocompact ℂ, Δ ℓ z = (Real.exp (ℓ z) - 1) / 4)
    (hlim : Tendsto ℓ (cocompact ℂ) (𝓝 0)) {c : ℝ} (hc₀ : 0 < c) (hc : c < 1 / 2)
    (hgrad : ∃ K, ∀ᶠ z in cocompact ℂ, ‖fderiv ℝ ℓ z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ K, ∀ᶠ z in cocompact ℂ, ‖iteratedFDeriv ℝ n ℓ z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ heq)
  have heq' : ∀ z : ℂ, R₀ < ‖z‖ → Δ ℓ z = (Real.exp (ℓ z) - 1) / 4 := fun z hz ↦ hR₀ hz.le
  have key (m : ℕ) : ∀ j, 1 ≤ j → j ≤ m →
      (fun z ↦ ‖iteratedFDeriv ℝ j ℓ z‖) =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
    induction m with
    | zero => intro j h₁ h₂; omega
    | succ m ih =>
      intro j h₁ h₂
      rcases (show j ≤ m ∨ j = m + 1 by omega) with h | rfl
      · exact ih j h₁ h
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · obtain ⟨K, hK⟩ := hgrad
        refine IsBigO.of_bound K (hK.mono fun z hz ↦ ?_)
        rwa [norm_norm, norm_iteratedFDeriv_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      · exact isBigO_norm_iteratedFDeriv_succ hℓ heq' hlim hc₀ hc hm ih
  obtain ⟨K, hK⟩ := (key n n hn le_rfl).bound
  refine ⟨K, hK.mono fun z hz ↦ ?_⟩
  rwa [norm_norm, Real.norm_of_nonneg (Real.exp_pos _).le] at hz

/-! ### The logarithmic modulus of a plane vortex -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- For a smooth vortex with `|α| → 1`, `ℓ = log |α|²` agrees outside a compact set with a smooth
function on the whole plane, obtained by adding a bump function to `|α|²` near the zeros of `α`,
which solves `Δ ℓ = (exp ℓ - 1) / 4` outside a compact set and tends to zero at infinity. -/
private theorem exists_contDiff_eventuallyEq_log_normSq (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ ℓ : ℂ → ℝ, ContDiff ℝ ∞ ℓ ∧ ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ →
      (ℓ =ᶠ[𝓝 z] fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) ∧
      Δ ℓ z = (Real.exp (ℓ z) - 1) / 4 ∧ 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  have hcd (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  have hs : ContDiff ℝ ∞ s := contDiff_const.mul (((hcd 2).pow 2).add ((hcd 3).pow 2))
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸
      hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)))
  set R := max R₀ 0
  -- A bump function equal to `1` where `α` may vanish and to `0` outside a disc.
  let χ : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  have hpos (z : ℂ) : 0 < s z + χ z := by
    by_cases hz : ‖z‖ ≤ R + 1
    · rw [χ.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hz)]
      positivity
    · linarith [hR₀ (show R₀ ≤ ‖z‖ by linarith [le_max_left R₀ 0]), χ.nonneg' z]
  have hχ (w : ℂ) (hw : R + 2 ≤ ‖w‖) : χ w = 0 := χ.zero_of_le_dist (by simpa using hw)
  refine ⟨fun z ↦ Real.log (s z + χ z), (hs.add χ.contDiff).log fun z ↦ (hpos z).ne',
    R + 2, fun z hz ↦ ?_⟩
  have hloc : (fun w ↦ Real.log (s w + χ w)) =ᶠ[𝓝 z] fun w ↦ Real.log (s w) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    rw [hχ w (le_of_lt hw), add_zero]
  have hsz : 1 / 2 < s z := hR₀ (show R₀ ≤ ‖z‖ by linarith [le_max_left R₀ 0])
  refine ⟨hloc, ?_, hsz⟩
  rw [(laplacian_congr_nhds hloc).eq_of_nhds, laplacian_log_normSq_of_equation_eq_zero
    ((hcd 0).differentiable (by simp) z) ((hcd 1).differentiable (by simp) z)
    ((hcd 2).contDiffAt.of_le (by norm_cast)) ((hcd 3).contDiffAt.of_le (by norm_cast))
    (by intro h; simp only [s] at hsz; rw [h] at hsz; norm_num at hsz)
    (Eventually.of_forall hsol)]
  dsimp only
  rw [hχ z hz.le, add_zero, Real.exp_log (by linarith)]

/-- The decay of all derivatives of the smooth modification `ℓ` of `log |α|²` built in
`exists_contDiff_eventuallyEq_log_normSq`. -/
private theorem exists_eventually_norm_iteratedFDeriv_le_mul_exp_of_log_normSq
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {ℓ : ℂ → ℝ}
    (hℓ : ContDiff ℝ ∞ ℓ) {R : ℝ}
    (hR : ∀ z : ℂ, R < ‖z‖ →
      (ℓ =ᶠ[𝓝 z] fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) ∧
      Δ ℓ z = (Real.exp (ℓ z) - 1) / 4 ∧ 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (n : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ, ‖iteratedFDeriv ℝ n ℓ z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hcd (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  have hb₁ := (hcd 0).differentiable (by simp)
  have hb₂ := (hcd 1).differentiable (by simp)
  have hp : ContDiff ℝ 2 (fun z ↦ x z 2) := (hcd 2).of_le (by norm_cast)
  have hq : ContDiff ℝ 2 (fun z ↦ x z 3) := (hcd 3).of_le (by norm_cast)
  have hev : ∀ᶠ z in cocompact ℂ, R < ‖z‖ := tendsto_norm_cocompact_atTop.eventually_gt_atTop R
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `|log |α|²| ≤ 2 (1 - |α|²)` where `1 / 2 < |α|² ≤ 1`.
    obtain ⟨K, hK⟩ := exists_one_sub_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc
    refine ⟨2 * K, hev.mono fun z hz ↦ ?_⟩
    set t := 4 * (x z 2 ^ 2 + x z 3 ^ 2)
    have ht := (hR z hz).2.2
    have ht₁ : t ≤ 1 := normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim z
    rw [norm_iteratedFDeriv_zero, (hR z hz).1.eq_of_nhds, Real.norm_eq_abs,
      abs_of_nonpos (Real.log_nonpos (by linarith) ht₁)]
    have hlog : -Real.log t ≤ 2 * (1 - t) := by
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith : 0 < t))
      rw [Real.log_inv] at this
      have : t⁻¹ - 1 ≤ 2 * (1 - t) := by
        rw [inv_eq_one_div, div_sub_one (by linarith), div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    linarith [hK z]
  -- For `n ≥ 1`, apply the decay of the derivatives of solutions of the scalar equation at the
  -- rate `c' = max c (1 / 4) ∈ (0, 1 / 2)`, which is at least `c`.
  set c' := max c (1 / 4)
  have hc' : c' < 1 / 2 := max_lt hc (by norm_num)
  obtain ⟨K, hK⟩ := exists_eventually_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq hℓ
    (hev.mono fun z hz ↦ (hR z hz).2.1)
    (by
      have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
      rw [Real.log_one] at h
      exact h.congr' (hev.mono fun z hz ↦ ((hR z hz).1.eq_of_nhds).symm))
    (lt_max_of_lt_right (by norm_num)) hc'
    (by
      obtain ⟨K, hK⟩ := exists_eventually_norm_fderiv_log_normSq_le_mul_exp hb₁ hb₂ hp hq hsol
        hlim hc'
      exact ⟨K, (hK.and hev).mono fun z hz ↦ by rw [(hR z hz.2).1.fderiv_eq]; exact hz.1⟩)
    hn
  refine ⟨max K 0, hK.mono fun z hz ↦ hz.trans ?_⟩
  refine (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (le_max_right _ _))
  exact neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- **Exponential decay of all derivatives of `log |α|²`.** A smooth vortex on the whole plane
whose section satisfies `|α| → 1` at infinity has, for every order `n` and every rate
`c < 1 / 2`, `‖Dⁿ log |α|² (z)‖ ≤ K exp (-c |z|)` outside a compact set. -/
theorem exists_eventually_norm_iteratedFDeriv_log_normSq_le_mul_exp (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) (n : ℕ) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ n (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨ℓ, hℓ, R, hR⟩ := exists_contDiff_eventuallyEq_log_normSq hx hsol hlim
  obtain ⟨K, hK⟩ := exists_eventually_norm_iteratedFDeriv_le_mul_exp_of_log_normSq hx hsol hlim hℓ
    hR n hc
  exact ⟨K, (hK.and (tendsto_norm_cocompact_atTop.eventually_gt_atTop R)).mono fun z hz ↦ by
    rw [← ((hR z hz.2).1.iteratedFDeriv ℝ n).eq_of_nhds]; exact hz.1⟩

/-! ### The winding end trivialization -/

variable {m : ℕ}

/-- **The end trivialization in terms of `ℓ = log |α|²`.** Near a point `w ≠ 0` around which the
section of a smooth vortex `x` is `|α|` times the winding phase and `|α| > 0`, its winding-`m` end
trivialization has real section `|α| = exp (ℓ / 2)`, and the holomorphicity rows determine its
connection: `y = (-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)` at `w`. -/
private theorem gaugeTransform_inv_windingPhase_apply_eq (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) {ℓ : ℂ → ℝ} {w : ℂ} (hw : w ≠ 0)
    (hphase : ∀ᶠ v in 𝓝 w, sectionValue x v = ‖sectionValue x v‖ * windingPhase m v)
    (hℓ : ℓ =ᶠ[𝓝 w] fun v ↦ Real.log (4 * (x v 2 ^ 2 + x v 3 ^ 2)))
    (hpos : ∀ᶠ v in 𝓝 w, 0 < 4 * (x v 2 ^ 2 + x v 3 ^ 2)) :
    gaugeTransform (windingPhase m)⁻¹ x w =
      !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2, Real.exp (ℓ w / 2) / 2, 0] := by
  set y := gaugeTransform (windingPhase m)⁻¹ x
  have hcd (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.1 hx i
  -- Near `w` the section of `y` is `|α| = exp (ℓ / 2)`.
  have hsec : ∀ᶠ v in 𝓝 w, y v 2 = Real.exp (ℓ v / 2) / 2 ∧ y v 3 = 0 := by
    filter_upwards [hphase, hℓ, hpos] with v hv hℓv hposv
    have h1 : ((windingPhase m v)⁻¹ : Circle) * (windingPhase m v : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    have hs : sectionValue y v = ‖sectionValue x v‖ := by
      rw [sectionValue_gaugeTransform, Pi.inv_apply]
      nth_rw 1 [hv]
      rw [mul_left_comm, h1, mul_one]
    have hnorm : ‖sectionValue x v‖ = Real.exp (ℓ v / 2) := by
      have hsq := sq_norm_sectionValue x v
      refine (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 ?_
      rw [hsq, ← Real.exp_nat_mul, hℓv]
      push_cast
      rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hposv]
    rw [sectionValue_apply, hnorm] at hs
    constructor
    · have := congrArg Complex.re hs
      simp only [mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at this
      linarith
    · have := congrArg Complex.im hs
      simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at this
      linarith
  have hsd : DifferentiableAt ℝ (fun v ↦ 4 * (x v 2 ^ 2 + x v 3 ^ 2)) w :=
    (contDiff_const.mul (((hcd 2).pow 2).add ((hcd 3).pow 2))).differentiable (by simp) w
  have hℓd : DifferentiableAt ℝ ℓ w :=
    (hsd.log hpos.self_of_nhds.ne').congr_of_eventuallyEq hℓ
  have hd2 : fderiv ℝ (fun v ↦ y v 2) w = (Real.exp (ℓ w / 2) / 2 * (1 / 2)) • fderiv ℝ ℓ w := by
    rw [Filter.EventuallyEq.fderiv_eq (f₁ := fun v ↦ y v 2)
      (f := fun v ↦ Real.exp (ℓ v / 2) / 2) (hsec.mono fun v hv ↦ hv.1)]
    have hfun : (fun v ↦ Real.exp (ℓ v / 2) / 2) = fun v ↦ 1 / 2 * Real.exp (1 / 2 * ℓ v) := by
      funext v; ring_nf
    rw [hfun, (((hℓd.hasFDerivAt.const_mul (1 / 2 : ℝ)).exp).const_mul (1 / 2 : ℝ)).fderiv]
    ext v
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring_nf
  have hd3 : fderiv ℝ (fun v ↦ y v 3) w = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (f₁ := fun v ↦ y v 3) (f := fun _ ↦ (0 : ℝ))
      (hsec.mono fun v hv ↦ hv.2), fderiv_const_apply]
  -- The holomorphicity rows of `equation y = 0` at `w`.
  have hu : ContDiffAt ℝ 2 (fun v ↦ (((windingPhase m)⁻¹ v : Circle) : ℂ)) w := by
    have h := (conjCLE.contDiff.contDiffAt (x := (windingPhase m w : ℂ))).comp w
      (contDiffAt_windingPhase m hw (n := 2))
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun v ↦ ?_)
    simp [-Circle.coe_inv, Circle.coe_inv_eq_conj]
  have heq : equation y w = 0 := (equation_gaugeTransform_eq_zero_iff hu
    fun i ↦ (hcd i).differentiable (by simp) w).2 (hsol w)
  have h1 := congrArg (· 1) heq
  have h2 := congrArg (· 2) heq
  simp only [equation_apply_one, equation_apply_two, PiLp.zero_apply, hd2, hd3,
    hsec.self_of_nhds.1, hsec.self_of_nhds.2, smul_apply, smul_eq_mul, zero_apply] at h1 h2
  have he := Real.exp_pos (ℓ w / 2)
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    field_simp
    nlinarith
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
    nlinarith
  · simpa using hsec.self_of_nhds.1
  · simpa using hsec.self_of_nhds.2

/-- The derivatives of `(exp (ℓ / 2) - 1) / 2` decay at rate `c ≥ 0` when those of `ℓ` of every
order do. -/
private theorem exists_eventually_norm_iteratedFDeriv_exp_half_le {ℓ : ℂ → ℝ}
    (hℓ : ContDiff ℝ ∞ ℓ) (hlim : Tendsto ℓ (cocompact ℂ) (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (hdec : ∀ j, ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ j ℓ z‖ ≤ K * Real.exp (-(c * ‖z‖))) (n : ℕ) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ n (fun w ↦ (Real.exp (ℓ w / 2) - 1) / 2) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  have hℓ2 : ContDiff ℝ ∞ (fun w ↦ ℓ w / 2) := hℓ.div_const 2
  have hE : ContDiff ℝ ∞ (fun w ↦ Real.exp (ℓ w / 2) - 1) :=
    (Real.contDiff_exp.comp hℓ2).sub contDiff_const
  -- The derivatives of `ℓ / 2` are half those of `ℓ`.
  have hdec2 : ∀ j ≤ n, (fun z ↦ ‖iteratedFDeriv ℝ j (fun w ↦ ℓ w / 2) z‖)
      =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := fun j _ ↦ by
    obtain ⟨K, hK⟩ := hdec j
    refine IsBigO.of_bound (K / 2) (hK.mono fun z hz ↦ ?_)
    have h2 : (fun w ↦ ℓ w / 2) = fun w ↦ (1 / 2 : ℝ) • ℓ w := funext fun w ↦ by
      rw [smul_eq_mul]; ring
    rw [norm_norm, h2, iteratedFDeriv_const_smul_apply'
      (hℓ.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    norm_num
    linarith
  obtain ⟨K, hK⟩ := (isBigO_norm_iteratedFDeriv_exp_comp_sub_one hℓ2
    (isBigO_exp_neg_mul_norm_one hc) (by simpa using hlim.div_const 2) hdec2).bound
  refine ⟨K / 2, hK.mono fun z hz ↦ ?_⟩
  rw [norm_norm, Real.norm_of_nonneg (Real.exp_pos _).le] at hz
  have h2 : (fun w ↦ (Real.exp (ℓ w / 2) - 1) / 2) =
      fun w ↦ (1 / 2 : ℝ) • (Real.exp (ℓ w / 2) - 1) :=
    funext fun w ↦ by rw [smul_eq_mul]; ring
  rw [h2, iteratedFDeriv_const_smul_apply' (hE.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul]
  norm_num
  linarith

/-- The `n`-th derivative of `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` is bounded by
`‖Dⁿ⁺¹ ℓ‖ + ‖Dⁿ ((exp (ℓ / 2) - 1) / 2)‖`. -/
private theorem norm_iteratedFDeriv_endField_le {ℓ : ℂ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (n : ℕ)
    (z : ℂ) :
    ‖iteratedFDeriv ℝ n
        ((fun w ↦ (-(fderiv ℝ ℓ w I / 2)) • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) +
        (fun w ↦ (fderiv ℝ ℓ w 1 / 2) • EuclideanSpace.single (1 : Fin 4) (1 : ℝ)) +
        fun w ↦ ((Real.exp (ℓ w / 2) - 1) / 2) • EuclideanSpace.single (2 : Fin 4) (1 : ℝ)) z‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) ℓ z‖ +
        ‖iteratedFDeriv ℝ n (fun w ↦ (Real.exp (ℓ w / 2) - 1) / 2) z‖ := by
  have hℓ' : ContDiff ℝ ∞ (fderiv ℝ ℓ) := hℓ.fderiv_right (by norm_cast)
  -- A derivative component `a ∂_v ℓ` has `n`-th derivative at most `|a| |v| ‖Dⁿ⁺¹ ℓ‖`.
  have hcomp (v : ℂ) (a : ℝ) : ‖iteratedFDeriv ℝ n (fun w ↦ (a * fderiv ℝ ℓ w v)) z‖ ≤
      |a| * ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) ℓ z‖ := by
    rw [show (fun w ↦ a * fderiv ℝ ℓ w v) = fun w ↦ a • fderiv ℝ ℓ w v from rfl,
      iteratedFDeriv_const_smul_apply' ((hℓ'.clm_apply contDiff_const).contDiffAt.of_le
        (by exact_mod_cast le_top)), norm_smul, Real.norm_eq_abs, mul_assoc,
      ← norm_iteratedFDeriv_fderiv]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_clm_apply_const hℓ'.contDiffAt
      (by exact_mod_cast le_top)) (abs_nonneg a)
  -- The coordinate vectors have norm one.
  have hsingle (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
      ‖iteratedFDeriv ℝ n (fun w ↦ f w • EuclideanSpace.single i (1 : ℝ)) z‖ ≤
        ‖iteratedFDeriv ℝ n f z‖ := by
    refine (norm_iteratedFDeriv_smul_const_le
      (hf.contDiffAt.of_le (by exact_mod_cast le_top)) _).trans_eq ?_
    rw [PiLp.norm_single, norm_one, mul_one]
  have hcd₀ : ContDiff ℝ ∞ fun w ↦ -(fderiv ℝ ℓ w I / 2) :=
    ((hℓ'.clm_apply contDiff_const).div_const 2).neg
  have hcd₁ : ContDiff ℝ ∞ fun w ↦ fderiv ℝ ℓ w 1 / 2 :=
    (hℓ'.clm_apply contDiff_const).div_const 2
  have hcd₂ : ContDiff ℝ ∞ fun w ↦ (Real.exp (ℓ w / 2) - 1) / 2 :=
    ((Real.contDiff_exp.comp (hℓ.div_const 2)).sub contDiff_const).div_const 2
  set A : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ (-(fderiv ℝ ℓ w I / 2)) •
    EuclideanSpace.single 0 1
  set B : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ (fderiv ℝ ℓ w 1 / 2) •
    EuclideanSpace.single 1 1
  set C : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ ((Real.exp (ℓ w / 2) - 1) / 2) •
    EuclideanSpace.single 2 1
  have hA : ContDiff ℝ ∞ A := hcd₀.smul contDiff_const
  have hB : ContDiff ℝ ∞ B := hcd₁.smul contDiff_const
  have hC : ContDiff ℝ ∞ C := hcd₂.smul contDiff_const
  have hAB : ContDiff ℝ ∞ (A + B) := hA.add hB
  rw [iteratedFDeriv_add_apply (hAB.contDiffAt.of_le (by exact_mod_cast le_top))
      (hC.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_add_apply (hA.contDiffAt.of_le (by exact_mod_cast le_top))
      (hB.contDiffAt.of_le (by exact_mod_cast le_top))]
  have hA' : ‖iteratedFDeriv ℝ n A z‖ ≤ 1 / 2 * ‖iteratedFDeriv ℝ (n + 1) ℓ z‖ := by
    refine (hsingle _ hcd₀ 0).trans ?_
    rw [show (fun w ↦ -(fderiv ℝ ℓ w I / 2)) = fun w ↦ (-1 / 2) * fderiv ℝ ℓ w I from
      funext fun w ↦ by ring]
    refine (hcomp I (-1 / 2)).trans_eq ?_
    rw [norm_I]
    norm_num
  have hB' : ‖iteratedFDeriv ℝ n B z‖ ≤ 1 / 2 * ‖iteratedFDeriv ℝ (n + 1) ℓ z‖ := by
    refine (hsingle _ hcd₁ 1).trans ?_
    rw [show (fun w ↦ fderiv ℝ ℓ w 1 / 2) = fun w ↦ (1 / 2) * fderiv ℝ ℓ w 1 from
      funext fun w ↦ by ring]
    refine (hcomp 1 (1 / 2)).trans_eq ?_
    rw [norm_one]
    norm_num
  have hC' := hsingle _ hcd₂ 2
  calc _ ≤ _ := norm_add₃_le
    _ ≤ _ := by linarith

/-- **Exponential decay of all derivatives in the winding end trivialization.** Let `x` be a
smooth plane vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase
`(z / |z|)^m` outside a compact set. Then its winding-`m` end trivialization
`y = (z / |z|)^(-m) · x` tends to the vacuum `(0, 1)` with all its derivatives: for every order
`n` and every rate `c < 1 / 2`, `‖Dⁿ (y - vacuum) (z)‖ ≤ K exp (-c |z|)` outside a compact set.

Outside a compact set the end trivialization is `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)`
for `ℓ = log |α|²`, so this follows from the decay of all derivatives of `ℓ`. -/
theorem exists_eventually_norm_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_le_mul_exp
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (n : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ n (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w - vacuumField w) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨ℓ, hℓ, R, hR⟩ := exists_contDiff_eventuallyEq_log_normSq hx hsol hlim
  obtain ⟨Rφ, -, hRφ⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hphase)
  set R' := max (max R Rφ) 0
  -- Outside the disc of radius `R'` the end trivialization minus the vacuum is `Y`.
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) :=
    (fun w ↦ (-(fderiv ℝ ℓ w I / 2)) • EuclideanSpace.single 0 1) +
      (fun w ↦ (fderiv ℝ ℓ w 1 / 2) • EuclideanSpace.single 1 1) +
      fun w ↦ ((Real.exp (ℓ w / 2) - 1) / 2) • EuclideanSpace.single 2 1
  have hopen : IsOpen {w : ℂ | R' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hY (z : ℂ) (hz : R' < ‖z‖) :
      (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w - vacuumField w) =ᶠ[𝓝 z] Y := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    have hw' : R' < ‖w‖ := hw
    have hRw : R < ‖w‖ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hw'
    have hnhds : ∀ᶠ v in 𝓝 w, R < ‖v‖ ∧ Rφ ≤ ‖v‖ :=
      Filter.eventually_of_mem (hopen.mem_nhds hw') fun v (hv : R' < ‖v‖) ↦
        ⟨lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hv,
          (le_trans (le_max_right _ _) (le_max_left _ _)).trans hv.le⟩
    rw [gaugeTransform_inv_windingPhase_apply_eq hx hsol (ne_of_gt (lt_of_le_of_lt
        (le_max_right _ _) hw') |>.symm |> fun h ↦ norm_ne_zero_iff.mp h.symm)
      (hnhds.mono fun v hv ↦ hRφ hv.2) (hR w hRw).1
      (hnhds.mono fun v hv ↦ by linarith [(hR v hv.1).2.2]), vacuumField_apply]
    ext i
    fin_cases i <;> simp [Y]
    ring
  -- Decay of the three components of `Y`.
  set c' := max c 0
  have hdec := fun j ↦ exists_eventually_norm_iteratedFDeriv_le_mul_exp_of_log_normSq hx hsol hlim
    hℓ hR j (c := c') (max_lt hc (by norm_num))
  obtain ⟨K₁, hK₁⟩ := hdec (n + 1)
  obtain ⟨K₂, hK₂⟩ := exists_eventually_norm_iteratedFDeriv_exp_half_le hℓ
    (by
      have hev : ∀ᶠ z in cocompact ℂ, R < ‖z‖ :=
        tendsto_norm_cocompact_atTop.eventually_gt_atTop R
      have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
      rw [Real.log_one] at h
      exact h.congr' (hev.mono fun z hz ↦ ((hR z hz).1.eq_of_nhds).symm))
    (le_max_right c 0) hdec n
  refine ⟨K₁ + K₂, ?_⟩
  filter_upwards [hK₁, hK₂, tendsto_norm_cocompact_atTop.eventually_gt_atTop R'] with z h₁ h₂ hz
  rw [((hY z hz).iteratedFDeriv ℝ n).eq_of_nhds]
  have hexp : Real.exp (-(c' * ‖z‖)) ≤ Real.exp (-(c * ‖z‖)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  have hK : 0 ≤ K₁ + K₂ := by
    by_contra hneg
    nlinarith [(norm_nonneg _).trans h₁, (norm_nonneg _).trans h₂, Real.exp_pos (-(c' * ‖z‖))]
  calc _ ≤ _ := norm_iteratedFDeriv_endField_le hℓ n z
    _ ≤ (K₁ + K₂) * Real.exp (-(c' * ‖z‖)) := by rw [add_mul]; exact add_le_add h₁ h₂
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hK

end TauCeti.Vortex

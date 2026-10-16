/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.HessianMultiplier
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Cutoff
import TauCeti.Analysis.Normed.Lp.SmoothApprox
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Hessian
import TauCeti.MeasureTheory.Function.Lp.IntegralBoundedSmul

/-!
# The kernel of the Hessian Fourier multiplier

For `v, w ∈ ℝⁿ`, the Fourier multiplier `T_{m_{v,w}}` on `L²(ℝⁿ, F)` with symbol
`m_{v,w}(ξ) = ⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` (`TauCeti.hessianSymbolLp`) is the operator `∂_v ∂_w Δ⁻¹`
(`SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM`). This file shows that for
`n ≥ 3` it is a singular integral operator whose kernel is the Hessian of the Newtonian kernel
`Gₙ = TauCeti.newtonianKernel n`: if `f ∈ L²` vanishes off a compact set `s`, then for almost
every `x ∉ s`

`T_{m_{v,w}} f (x) = -∫ D²Gₙ(x - y)(v, w) f(y) dy`

(`TauCeti.ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral`). Together with the size and
smoothness estimates of `D²Gₙ` (`TauCeti.norm_iteratedFDeriv_two_newtonianKernel_le`,
`TauCeti.norm_iteratedFDeriv_two_newtonianKernel_sub_le`), this is the kernel representation that
the Calderón–Zygmund theory asks of an `L²`-bounded operator before it bounds the operator on
`Lᵖ`, `1 < p < ∞`; for `T_{m_{v,w}}` that bound is the estimate `‖∂_v ∂_w u‖_p ≤ C ‖Δu‖_p`.

## The argument

For `φ` smooth with compact support, the Newtonian potential `u = Gₙ ⋆ φ` solves `-Δu = φ`, so
`T_{m_{v,w}} φ` should be `-∂_v ∂_w u`. The identity `∂_v ∂_w = T_{m_{v,w}} ∘ Δ` holds on Schwartz
functions, and `u` is not one, but its truncations `χ_R u` are: `χ_R` is a cutoff equal to `1` on
`ball 0 R` with `‖Dχ_R‖ = O(1/R)` and `|Δχ_R| = O(1/R²)`
(`TauCeti.exists_forall_contDiff_cutoff_ball_norm_laplacian_le`). Since `u = O(‖x‖ ^ (2 - n))` and
`Du = O(‖x‖ ^ (1 - n))` (`TauCeti.norm_newtonianKernel_convolution_le`,
`TauCeti.norm_fderiv_newtonianKernel_convolution_le`), the error
`Δ(χ_R u) + φ = 2 Du(∇χ_R) + (Δχ_R) u` lives on the annulus `R ≤ ‖x‖ ≤ 2R`, where it is
`O(R ^ (1 - n))`, so its `L²` norm is `O(R ^ (1 - n/2))`, which tends to zero exactly because
`n ≥ 3`. Hence `T_{m_{v,w}} φ = -∂_v ∂_w u` almost everywhere
(`TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp`).

Off the support of `φ`, integrating by parts twice moves the derivatives from `φ` onto the
kernel: `D²u(x)(v, w) = ∫ D²Gₙ(x - y)(v, w) φ(y) dy`
(`TauCeti.iteratedFDeriv_two_newtonianKernel_convolution_apply_of_notMem_tsupport`). A general
`f ∈ L²` vanishing off `s` is the `L²` limit of smooth functions supported in shrinking
thickenings of `s`
(`MeasureTheory.MemLp.exist_contDiff_tsupport_subset_cthickening_eLpNorm_sub_le`).
For `x ∉ s` the kernel is bounded on a fixed thickening of `s`, so the kernel integrals converge
(`TauCeti.integrable_smul_and_norm_integral_smul_le`), while `T_{m_{v,w}}` of the approximations
converges almost everywhere along a subsequence.

## Main declarations

* `TauCeti.iteratedFDeriv_two_newtonianKernel_convolution_apply_of_notMem_tsupport`: the second
  derivatives of the Newtonian potential off the support of the density.
* `TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp`: `T_{m_{v,w}} φ = -D²(Gₙ ⋆ φ)(v, w)`
  for `φ` smooth with compact support.
* `TauCeti.ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral`: the kernel representation of
  `T_{m_{v,w}}` off the support of its argument.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.4 and Section 9.4.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Set Topology
open scoped Convolution ContDiff

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : EuclideanSpace ℝ (Fin n) → F}

open scoped Laplacian Gradient in
/-- **The truncation error of the Newtonian potential.** Let `φ` be smooth with support in
`closedBall 0 R₀`, let `u = Gₙ ⋆ φ`, and let `χ` be a cutoff equal to `1` on `ball 0 R` and to `0`
off `closedBall 0 (2R)` with `‖Dχ‖ ≤ C / R` and `|Δχ| ≤ C / R²`. Since `-Δu = φ`, the error
`Δ(χ u) + φ = 2 Du(∇χ) + (Δχ) u` lives on the annulus `R ≤ ‖x‖ ≤ 2R`, where the decay of `u` and
`Du` bounds it by a multiple of `R⁻¹ (R / 2) ^ (2 - n)`. -/
private theorem norm_laplacian_smul_newtonianKernel_convolution_add_le [CompleteSpace F]
    (hn : 3 ≤ n) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {R₀ C R : ℝ}
    (hR₀ : tsupport φ ⊆ closedBall 0 R₀) (hR : 1 ≤ R) (hR₀R : 2 * R₀ ≤ R)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ1 : ∀ x, ‖x‖ < R → χ =ᶠ[𝓝 x] fun _ => 1) (hχ0 : ∀ x, 2 * R < ‖x‖ → χ =ᶠ[𝓝 x] fun _ => 0)
    (hχ' : ∀ x, ‖fderiv ℝ χ x‖ ≤ C / R) (hχ'' : ∀ x, ‖Δ χ x‖ ≤ C / R ^ 2)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Δ (fun y => χ y • (newtonianKernel n ⋆ φ) y) x + φ x‖ ≤
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R)).indicator (fun _ =>
        (4 * ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ +
          ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
          C * (∫ y, ‖φ y‖) * R⁻¹ * (R / 2) ^ (2 - (n : ℝ))) x := by
  set u := newtonianKernel n ⋆ φ
  set Cd := ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
  set Cn := ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hχ' 0)
    rwa [le_div_iff₀ hR0, zero_mul] at this
  have hCd : 0 ≤ Cd := inv_nonneg.2 (mul_nonneg (by linarith) (volume_real_unitBall_pos n).le)
  have hCn : 0 ≤ Cn := inv_nonneg.2 (mul_nonneg (mul_nonneg (by linarith) (by linarith))
    (volume_real_unitBall_pos n).le)
  have hu : ContDiff ℝ ∞ u := contDiff_newtonianKernel_convolution hφ hc
  have hΔu : Δ u = -φ := laplacian_newtonianKernel_convolution hn (hφ.of_le (by simp)) hc
  have hφx : ∀ y : EuclideanSpace ℝ (Fin n), R₀ < ‖y‖ → φ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => (mem_closedBall_zero_iff.1 (hR₀ h)).not_gt hy
  have hA₀ := integral_nonneg (μ := volume) (f := fun y => ‖φ y‖) fun y => norm_nonneg _
  have hbound_nonneg : 0 ≤ (4 * Cd + Cn) * C * (∫ y, ‖φ y‖) * R⁻¹ * (R / 2) ^ (2 - (n : ℝ)) := by
    positivity
  rcases lt_or_ge ‖x‖ R with hxR | hxR
  · -- Inside `ball 0 R` the truncation is `u` itself, and `Δu = -φ`.
    have h : (fun y => χ y • u y) =ᶠ[𝓝 x] u := by
      filter_upwards [hχ1 x hxR] with y hy
      rw [hy, one_smul]
    rw [(laplacian_congr_nhds h).eq_of_nhds, hΔu, Pi.neg_apply, neg_add_cancel, norm_zero]
    exact indicator_nonneg (fun _ _ => hbound_nonneg) x
  rcases lt_or_ge (2 * R) ‖x‖ with hx2R | hx2R
  · -- Off `closedBall 0 (2R)` the truncation vanishes identically, and so does `φ`.
    have h : (fun y => χ y • u y) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [hχ0 x hx2R] with y hy
      rw [hy, zero_smul]
    rw [(laplacian_congr_nhds h).eq_of_nhds, laplacian_const, hφx x (by linarith), add_zero,
      Pi.zero_apply, norm_zero]
    exact indicator_nonneg (fun _ _ => hbound_nonneg) x
  -- On the annulus, expand `Δ(χ u)` by the Leibniz rule.
  have hxR₀ : R / 2 ≤ ‖x‖ - R₀ := by linarith
  have hpow : (‖x‖ - R₀) ^ (2 - (n : ℝ)) ≤ (R / 2) ^ (2 - (n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hxR₀ (by linarith)
  -- Since `1 ≤ R`, the faster decay `(R / 2) ^ (1 - n)` of `Du` is at most `2 (R / 2) ^ (2 - n)`.
  have hpow₁ : (‖x‖ - R₀) ^ (1 - (n : ℝ)) ≤ 2 * (R / 2) ^ (2 - (n : ℝ)) := by
    have hexp : 1 - (n : ℝ) = 2 - n - 1 := by ring
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) hxR₀ (by linarith)).trans ?_
    rw [hexp, Real.rpow_sub_one (by positivity), div_le_iff₀ (by positivity)]
    have : 0 ≤ (R / 2) ^ (2 - (n : ℝ)) := by positivity
    nlinarith
  have hgrad : ‖∇ χ x‖ ≤ C / R := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact hχ' x
  rw [indicator_of_mem (mem_closedBall_zero_iff.2 hx2R),
    (hχ.contDiffAt.of_le (by simp)).laplacian_fun_smul (hu.contDiffAt.of_le (by simp)), hΔu,
    Pi.neg_apply, hφx x (by linarith), neg_zero, smul_zero, zero_add, add_zero]
  have hR₀x : R₀ < ‖x‖ := by linarith
  have hφi := hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hc
  have h₁ := norm_fderiv_newtonianKernel_convolution_le (by omega) hφi
    ((subset_tsupport φ).trans hR₀) hR₀x
  have h₂ := norm_newtonianKernel_convolution_le hn hφi ((subset_tsupport φ).trans hR₀) hR₀x
  have hΔχ : ‖Δ χ x‖ ≤ C / R := (hχ'' x).trans (div_le_div_of_nonneg_left hC hR0
    (by nlinarith))
  calc ‖(2 : ℝ) • fderiv ℝ u x (∇ χ x) + Δ χ x • u x‖
      ≤ 2 * ‖fderiv ℝ u x (∇ χ x)‖ + ‖Δ χ x‖ * ‖u x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_two]
    _ ≤ 2 * (Cd * (2 * (R / 2) ^ (2 - (n : ℝ))) * (∫ y, ‖φ y‖) * (C / R)) +
        C / R * (Cn * (R / 2) ^ (2 - (n : ℝ)) * ∫ y, ‖φ y‖) := by
        gcongr
        · exact (le_opNorm _ _).trans (mul_le_mul (h₁.trans (by gcongr)) hgrad (norm_nonneg _)
            (by positivity))
        · exact h₂.trans (by gcongr)
    _ = _ := by ring

/-- For `n ≥ 3`, `K R⁻¹ (R / 2) ^ (2 - n) |B(0, 2R)| ^ (1/2) = O(R ^ (1 - n/2))` tends to zero as
`R → ∞`: the `L²` norm of the truncation error of the Newtonian potential vanishes in the limit. -/
private theorem tendsto_mul_rpow_mul_measureReal_closedBall_rpow (hn : 3 ≤ n) (K : ℝ) :
    Tendsto (fun R : ℝ => K * R⁻¹ * (R / 2) ^ (2 - (n : ℝ)) *
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set V := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hV : 0 < V := volume_real_unitBall_pos n
  set c := K / 2 ^ (2 - (n : ℝ)) * (2 ^ n * V) ^ (1 / 2 : ℝ)
  have key : ∀ R : ℝ, 0 < R → K * R⁻¹ * (R / 2) ^ (2 - (n : ℝ)) *
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R)) ^ (1 / 2 : ℝ) =
        c * R ^ (1 - (n : ℝ) / 2) := by
    intro R hR
    have hvol : volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R)) =
        R ^ (n : ℝ) * (2 ^ n * V) := by
      rw [Measure.addHaar_real_closedBall _ _ (by positivity), finrank_euclideanSpace_fin,
        mul_pow, Real.rpow_natCast]
      ring
    rw [hvol, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR.le,
      Real.div_rpow hR.le zero_le_two]
    have h₁ : R ^ (1 - (n : ℝ) / 2) = R⁻¹ * R ^ (2 - (n : ℝ)) * R ^ ((n : ℝ) * (1 / 2)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hR, ← Real.rpow_add hR]
      congr 1
      ring
    have h₂ : (0 : ℝ) < 2 ^ (2 - (n : ℝ)) := by positivity
    rw [h₁]
    field_simp
    simp only [c]
    field_simp
  have hlim : Tendsto (fun R : ℝ => c * R ^ (1 - (n : ℝ) / 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (n : ℝ) / 2 - 1) (by linarith)).const_mul c
    rw [mul_zero] at h
    refine h.congr fun R => ?_
    congr 2
    ring
  exact hlim.congr' (eventually_gt_atTop 0 |>.mono fun R hR => (key R hR).symm)

/-- Away from a closed set `s`, the kernel `y ↦ D²Gₙ(x - y)(v, w)` is continuous and bounded on a
closed thickening of `s`. -/
private theorem exists_continuousOn_norm_le_cthickening {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : IsClosed s) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ s) (v w : EuclideanSpace ℝ (Fin n)) :
    ∃ η > 0, x ∉ cthickening η s ∧ ∃ B, 0 ≤ B ∧
      ContinuousOn (fun y => iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w])
        (cthickening η s) ∧
      ∀ y ∈ cthickening η s, ‖iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w]‖ ≤ B := by
  -- Choose `η > 0` with `x ∉ cthickening (2η) s`; then `η ≤ ‖x - y‖` on `cthickening η s`.
  obtain ⟨η, hη, hxη⟩ : ∃ η > 0, x ∉ cthickening (η + η) s := by
    have : x ∉ closure s := hs.closure_eq.symm ▸ hx
    rw [closure_eq_iInter_cthickening] at this
    simp only [mem_iInter, not_forall] at this
    obtain ⟨δ, hδ, hxδ⟩ := this
    exact ⟨δ / 2, half_pos hδ, by rwa [add_halves]⟩
  have hdist : ∀ y ∈ cthickening η s, η ≤ ‖x - y‖ := fun y hy => by
    rw [← dist_eq_norm]
    by_contra h
    exact hxη (cthickening_cthickening_subset hη.le hη.le s
      (mem_cthickening_of_dist_le x y η _ hy (not_le.1 h).le))
  have hne : ∀ y ∈ cthickening η s, x - y ≠ 0 := fun y hy h => by
    have := hdist y hy
    rw [h, norm_zero] at this
    exact hη.not_ge this
  have := volume_real_unitBall_pos n
  refine ⟨η, hη, fun h => hxη (cthickening_mono (by linarith) s h),
    ((n : ℝ) + 1) * ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      η ^ (-(n : ℝ)) * (‖v‖ * ‖w‖), by positivity, fun y hy => ?_, fun y hy => ?_⟩
  · exact (((contDiffAt_newtonianKernel n (hne y hy)).continuousAt_iteratedFDeriv le_rfl).comp
      (continuous_const.sub continuous_id).continuousAt).eval_const _ |>.continuousWithinAt
  refine ((iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y)).le_opNorm _).trans ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine mul_le_mul_of_nonneg_right ((norm_iteratedFDeriv_two_newtonianKernel_le
    (hne y hy)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))) (by positivity)
  exact Real.rpow_le_rpow_of_nonpos hη (hdist y hy) (neg_nonpos.2 (Nat.cast_nonneg n))

section Multiplier

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {φ : EuclideanSpace ℝ (Fin n) → F}

open scoped Laplacian LineDeriv SchwartzMap

/-- **Truncations of the Newtonian potential.** For `n ≥ 3` and `φ` smooth with compact support,
there are Schwartz functions `Sₘ` that agree with `u = Gₙ ⋆ φ` on `ball 0 m` and whose Laplacians
tend to `-φ` in `L²`. They are `χ_R u` for cutoffs `χ_R` at radii `R ≥ m`. -/
private theorem exists_schwartzMap_eventuallyEq_tendsto_toLp_laplacian_add (hn : 3 ≤ n)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ S : ℕ → 𝓢(EuclideanSpace ℝ (Fin n), F),
      (∀ (m : ℕ) x, ‖x‖ < m → (S m : EuclideanSpace ℝ (Fin n) → F) =ᶠ[𝓝 x] newtonianKernel n ⋆ φ) ∧
        Tendsto (fun m => (Δ (S m)).toLp 2 +
          (hφ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).toLp φ) atTop
          (𝓝 0) := by
  set u := newtonianKernel n ⋆ φ
  have hu : ContDiff ℝ ∞ u := contDiff_newtonianKernel_convolution hφ hc
  obtain ⟨C, hC⟩ :=
    exists_forall_contDiff_cutoff_ball_norm_laplacian_le (E := EuclideanSpace ℝ (Fin n))
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R : ℕ → ℝ := fun m => max (max m 1) (2 * R₀)
  have hR1 : ∀ m, 1 ≤ R m := fun m => (le_max_right _ _).trans (le_max_left _ _)
  have hRm : ∀ m : ℕ, (m : ℝ) ≤ R m := fun m => (le_max_left _ _).trans (le_max_left _ _)
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRm tendsto_natCast_atTop_atTop
  choose χ hχ hχc hχ1 hχ0 hχ' hχ'' using fun m => hC (R m) (zero_lt_one.trans_le (hR1 m))
  have hψc : ∀ m, HasCompactSupport fun y => χ m y • u y := fun m => (hχc m).smul_right
  refine ⟨fun m => (hψc m).toSchwartzMap ((hχ m).smul hu), fun m x hx => ?_, ?_⟩
  · filter_upwards [hχ1 m x (hx.trans_le (hRm m))] with y hy
    simp [hy]
  -- The `L²` norm of `Δ Sₘ + φ` is bounded by the pointwise bound on its support.
  set K := (4 * ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ +
    ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
    C * (∫ y, ‖φ y‖)
  refine squeeze_zero_norm (fun m => ?_)
    ((tendsto_mul_rpow_mul_measureReal_closedBall_rpow hn K).comp hR)
  have hbound := fun x => norm_laplacian_smul_newtonianKernel_convolution_add_le hn hφ hc hR₀
    (hR1 m) (le_max_right _ _) (hχ m) (hχ1 m) (hχ0 m) (hχ' m) (hχ'' m) x
  have hK : 0 ≤ K * (R m)⁻¹ * (R m / 2) ^ (2 - (n : ℝ)) := by
    have := (norm_nonneg _).trans (hbound 0)
    rwa [indicator_of_mem (mem_closedBall_self (by linarith [hR1 m]))] at this
  set I := indicatorConstLp 2 (measurableSet_closedBall (x := (0 : EuclideanSpace ℝ (Fin n)))
    (ε := 2 * R m)) (measure_closedBall_lt_top (μ := volume)).ne
    (K * (R m)⁻¹ * (R m / 2) ^ (2 - (n : ℝ)))
  refine (Lp.norm_le_norm_of_ae_le (g := I) ?_).trans_eq ?_
  · filter_upwards [Lp.coeFn_add ((Δ ((hψc m).toSchwartzMap ((hχ m).smul hu))).toLp 2)
      ((hφ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).toLp φ),
      SchwartzMap.coeFn_toLp (Δ ((hψc m).toSchwartzMap ((hχ m).smul hu))) 2 volume,
      (hφ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).coeFn_toLp,
      indicatorConstLp_coeFn (p := 2) (μ := volume)
        (hs := measurableSet_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 2 * R m))
        (hμs := (measure_closedBall_lt_top (μ := volume)).ne)
        (c := K * (R m)⁻¹ * (R m / 2) ^ (2 - (n : ℝ)))] with x h₁ h₂ h₃ h₄
    rw [h₁, Pi.add_apply, h₂, h₃, h₄, SchwartzMap.laplacian_apply, norm_indicator_eq_indicator_norm,
      Real.norm_of_nonneg hK]
    exact hbound x
  · rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, Real.norm_of_nonneg hK,
      ENNReal.toReal_ofNat]
    rfl

/-- **The Hessian multiplier on smooth functions with compact support.** For `n ≥ 3` and `φ`
smooth with compact support on `ℝⁿ`, the Fourier multiplier `T_{m_{v,w}}` with symbol
`⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` sends `φ` to `-D²(Gₙ ⋆ φ)(v, w)`. Since `-Δ (Gₙ ⋆ φ) = φ`, this says that
`T_{m_{v,w}} = ∂_v ∂_w Δ⁻¹` on such functions, with `Δ⁻¹` given by the Newtonian potential.

The Newtonian potential `u = Gₙ ⋆ φ` is not a Schwartz function, so the identity
`∂_v ∂_w = T_{m_{v,w}} ∘ Δ` on Schwartz functions does not apply to it directly. It applies to
truncations `χ_R u`, which agree with `u` on `ball 0 R` and whose Laplacians tend to `-φ` in `L²`
because `u` decays like `‖x‖ ^ (2 - n)` and `n ≥ 3`. -/
theorem coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp (hn : 3 ≤ n) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v w : EuclideanSpace ℝ (Fin n)) :
    Lp.fourierMultiplierCLM F (hessianSymbolLp v w)
        ((hφ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).toLp φ) =ᵐ[volume]
      fun x => -iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ φ) x ![v, w] := by
  set T := Lp.fourierMultiplierCLM F (hessianSymbolLp v w)
  set Φ := (hφ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).toLp φ
  have hu : ContDiff ℝ 2 (newtonianKernel n ⋆ φ) :=
    contDiff_newtonianKernel_convolution (hφ.of_le (by simp)) hc
  obtain ⟨S, hSu, hSlim⟩ := exists_schwartzMap_eventuallyEq_tendsto_toLp_laplacian_add hn hφ hc
  -- `T (Δ Sₘ + φ) - T φ = ∂_v ∂_w Sₘ`, and `T (Δ Sₘ + φ) → 0` in `L²`, so almost everywhere along
  -- a subsequence.
  have hT : ∀ m, T ((Δ (S m)).toLp 2 + Φ) - T Φ = (∂_{v} (∂_{w} (S m))).toLp 2 := fun m => by
    rw [map_add, add_sub_cancel_right]
    exact (SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM (S m) v w).symm
  have hlim : Tendsto (fun m => T ((Δ (S m)).toLp 2 + Φ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using (T.continuous.tendsto 0).comp hSlim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hpt : ∀ᵐ x, ∀ m, T ((Δ (S m)).toLp 2 + Φ) x - T Φ x = ∂_{v} (∂_{w} (S m)) x := by
    rw [ae_all_iff]
    intro m
    filter_upwards [Lp.coeFn_sub (T ((Δ (S m)).toLp 2 + Φ)) (T Φ),
      SchwartzMap.coeFn_toLp (∂_{v} (∂_{w} (S m))) 2 volume] with x h₁ h₂
    rw [← Pi.sub_apply, ← h₁, hT m, h₂]
  filter_upwards [hae, hpt, Lp.coeFn_zero F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))]
    with x hx hx' h0
  rw [h0, Pi.zero_apply] at hx
  -- Once `‖x‖ < ns i`, `Sₘ` agrees with `Gₙ ⋆ φ` near `x`, and so do their second derivatives.
  have hev : ∀ᶠ i in atTop, T ((Δ (S (ns i))).toLp 2 + Φ) x =
      T Φ x + iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ φ) x ![v, w] := by
    obtain ⟨m₀, hm₀⟩ := exists_nat_gt ‖x‖
    filter_upwards [hns.tendsto_atTop.eventually_ge_atTop m₀] with i hi
    have h : (fun y => fderiv ℝ (S (ns i)) y w) =ᶠ[𝓝 x]
        fun y => fderiv ℝ (newtonianKernel n ⋆ φ) y w :=
      ((hSu (ns i) x (hm₀.trans_le (by exact_mod_cast hi))).fderiv (𝕜 := ℝ)).mono fun y hy => by
        simp only [hy]
    have hw : (⇑(∂_{w} (S (ns i)) : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
        EuclideanSpace ℝ (Fin n) → F) = fun y => fderiv ℝ (S (ns i)) y w :=
      funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv w (S (ns i)) y
    rw [← sub_eq_iff_eq_add', hx' (ns i), SchwartzMap.lineDerivOp_apply_eq_fderiv, hw,
      h.fderiv_eq, fderiv_clm_apply_const_apply
        ((hu.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero x),
      iteratedFDeriv_two_apply]
    simp
  have h := tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun i hi => hi.symm)) hx
  exact eq_neg_of_add_eq_zero_left h

/-- **The kernel of the Hessian multiplier.** Let `n ≥ 3` and `v, w ∈ ℝⁿ`, and let `T_{m_{v,w}}`
be the Fourier multiplier with symbol `⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²`, that is `∂_v ∂_w Δ⁻¹`. If `f ∈ L²`
vanishes almost everywhere off a compact set `s`, then for almost every `x ∉ s`

`T_{m_{v,w}} f (x) = -∫ D²Gₙ(x - y)(v, w) f(y) dy`.

So off the support of its argument, `T_{m_{v,w}}` is the singular integral operator with kernel
`-D²Gₙ(x - y)(v, w)`, the Hessian of the Newtonian kernel; the integral converges because the
kernel is bounded for `y ∈ s` and `x` away from `s`. -/
theorem ae_fourierMultiplierCLM_hessianSymbolLp_eq_neg_integral (hn : 3 ≤ n)
    (v w : EuclideanSpace ℝ (Fin n)) (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsCompact s) (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → Lp.fourierMultiplierCLM F (hessianSymbolLp v w) f x =
      -∫ y, iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] • f y := by
  set T := Lp.fourierMultiplierCLM F (hessianSymbolLp v w)
  -- A representative `f'` of `f` vanishing everywhere off `s`, and smooth approximations `φ k`
  -- of it supported in shrinking thickenings of `s`.
  obtain ⟨f', hff', hf'0⟩ : ∃ f' : EuclideanSpace ℝ (Fin n) → F,
      (f : EuclideanSpace ℝ (Fin n) → F) =ᵐ[volume] f' ∧ ∀ y, y ∉ s → f' y = 0 := by
    refine ⟨s.indicator f, ?_, fun y hy => indicator_of_notMem hy _⟩
    filter_upwards [hf] with x hx
    by_cases h : x ∈ s
    · simp [h]
    · simp [h, hx h]
  have hf'L : MemLp f' 2 := (Lp.memLp f).ae_eq hff'
  choose φ hφc hφ hφs hφf using fun k : ℕ =>
    hf'L.exist_contDiff_tsupport_subset_cthickening_eLpNorm_sub_le ENNReal.ofNat_ne_top
      one_le_two hs.isClosed (ae_of_all _ hf'0) (Nat.one_div_pos_of_nat (n := k))
      (Nat.one_div_pos_of_nat (n := k))
  have hφL : ∀ k, MemLp (φ k) 2 := fun k =>
    (hφ k).continuous.memLp_of_hasCompactSupport (μ := volume) (hφc k)
  have hΦ : Tendsto (fun k => (hφL k).toLp (φ k)) atTop (𝓝 f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h : ⇑((hφL k).toLp (φ k) - f) =ᵐ[volume] φ k - f' := by
      filter_upwards [Lp.coeFn_sub ((hφL k).toLp (φ k)) f, (hφL k).coeFn_toLp, hff']
        with x h₁ h₂ h₃
      rw [h₁, Pi.sub_apply, h₂, h₃, Pi.sub_apply]
    rw [Lp.norm_def, eLpNorm_congr_ae h, eLpNorm_sub_comm]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hφf k)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((T.continuous.tendsto f).comp hΦ)).exists_seq_tendsto_ae
  have hsmooth : ∀ᵐ x, ∀ k, T ((hφL k).toLp (φ k)) x =
      -iteratedFDeriv ℝ 2 (newtonianKernel n ⋆ φ k) x ![v, w] :=
    ae_all_iff.2 fun k => coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp hn (hφ k) (hφc k) v w
  filter_upwards [hae, hsmooth] with x hx hxk hxs
  rw [integral_congr_ae (hff'.mono fun y hy => by rw [hy])]
  obtain ⟨η, hη, hxη, B, hB, hkc, hkB⟩ :=
    exists_continuousOn_norm_le_cthickening (n := n) hs.isClosed hxs v w
  -- Eventually `tsupport (φ k) ⊆ cthickening η s`, so `x ∉ tsupport (φ k)` and `T (φ k) x` is
  -- given by the kernel.
  have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ η :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hη)).mono fun _ h => h.le
  have hφW : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ η → tsupport (φ k) ⊆ cthickening η s := fun k hk =>
    (hφs k).trans (cthickening_mono hk s)
  have hev : ∀ᶠ k in atTop, T ((hφL k).toLp (φ k)) x =
      -∫ y, iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] • φ k y := by
    filter_upwards [hsmall] with k hk
    rw [hxk k, iteratedFDeriv_two_newtonianKernel_convolution_apply_of_notMem_tsupport
      ((hφ k).of_le (by simp)) (hφc k) (fun h => hxη (hφW k hk h)) v w]
  -- The kernel integrals of `φ k` converge to that of `f'`, by the Cauchy–Schwarz bound.
  have hf'W : ∀ y, y ∉ cthickening η s → f' y = 0 := fun y hy =>
    hf'0 y fun h => hy (self_subset_cthickening s h)
  have hconv : Tendsto (fun k => ∫ y, iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] •
      φ k y) atTop (𝓝 (∫ y, iteratedFDeriv ℝ 2 (newtonianKernel n) (x - y) ![v, w] • f' y)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul
      (B * (volume (cthickening η s) ^ (1 / 2 : ℝ)).toReal)
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hsmall] with k hk
    have hφk0 : ∀ y, y ∉ cthickening η s → φ k y = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun h => hy (hφW k hk h)
    have hW := hs.cthickening (r := η)
    have hkm := hkc.aestronglyMeasurable (μ := volume) hW.measurableSet
    have hkB' := ae_restrict_of_forall_mem (μ := volume) hW.measurableSet hkB
    obtain ⟨hint₁, -⟩ := integrable_smul_and_norm_integral_smul_le hW.measure_lt_top.ne hB
      hkm hkB' one_le_two (hφL k) (ae_of_all _ hφk0)
    obtain ⟨hint₂, -⟩ := integrable_smul_and_norm_integral_smul_le hW.measure_lt_top.ne hB
      hkm hkB' one_le_two hf'L (ae_of_all _ hf'W)
    obtain ⟨-, hle⟩ := integrable_smul_and_norm_integral_smul_le hW.measure_lt_top.ne hB
      hkm hkB' one_le_two ((hφL k).sub hf'L)
      (ae_of_all _ fun y hy => by simp [hφk0 y hy, hf'W y hy])
    have h12 : (1 : ℝ) - 1 / (2 : ENNReal).toReal = 1 / 2 := by norm_num
    rw [h12] at hle
    rw [norm_norm, ← integral_sub hint₁ hint₂]
    simp_rw [← smul_sub]
    refine hle.trans ?_
    rw [ENNReal.toReal_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB ENNReal.toReal_nonneg)
    rw [eLpNorm_sub_comm]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hφf k)
  exact tendsto_nhds_unique hx ((hconv.comp hns.tendsto_atTop).neg.congr'
    ((hns.tendsto_atTop.eventually hev).mono fun _ h => h.symm))

end Multiplier

end TauCeti

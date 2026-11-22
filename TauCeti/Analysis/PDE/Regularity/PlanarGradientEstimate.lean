/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Complex.Pompeiu.Newtonian
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential

/-!
# The interior gradient estimate for Poisson's equation in the plane

Let `u` be a real function on `ℂ` with `|u| ≤ ε` on the disc `B(x, 2ρ)` and `|Δu| ≤ K` on the disc
`B(x, 3ρ)`. Then

`‖Du(x)‖ ≤ 8 ε / ρ + 340 K ρ`

(`TauCeti.norm_fderiv_le_of_abs_le_of_abs_laplacian_le`). This is the interior gradient estimate
for Poisson's equation, with explicit constants: the derivative of a solution is controlled at
interior points by the size of the solution and of its Laplacian. Optimizing over `ρ` gives the
familiar consequence that a function which is uniformly small, with a uniformly bounded Laplacian,
has a uniformly small gradient. In particular, if `u i → v` uniformly on `ℂ` and
`|Δ (u i) - Δ v| ≤ K` everywhere with one constant `K`, then `D (u i) → D v` uniformly
(`TendstoUniformly.fderiv_of_abs_laplacian_sub_le`). This is how uniform convergence of
solutions of a semilinear equation `Δu = F(z, u)` with bounded right-hand sides is upgraded to
uniform convergence of their first derivatives.

Applied to the components `y ↦ Dⁿu(y)(v₁, …, vₙ)`, whose Laplacians are the components of
`Dⁿ(Δu)` because the Laplacian commutes with iterated derivatives
(`ContDiff.laplacian_iteratedFDeriv`), the estimate bounds `Dⁿ⁺¹u(x)` by `Dⁿu` and `Dⁿ(Δu)`
(`TauCeti.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le`). For a semilinear
equation `Δu = F(u)` this bounds every derivative of a solution, by induction on the order.

The proof splits `u` into a Newtonian potential and a harmonic function. Choose a smooth cutoff
`χ`, equal to one on `B(x, 2ρ)` and supported in `B(x, 3ρ)`, and let `p = G ⋆ (χ Δu)` be the
Newtonian potential of `χ Δu`, with `G = TauCeti.planarNewtonianKernel`. Then `Δp = -χ Δu`
(`TauCeti.laplacian_planarNewtonianKernel_convolution`), so `h = u + p` is harmonic on
`B(x, 2ρ)`. The derivative of `p` is bounded on `B(x, 2ρ)` by `20 K ρ`
(`TauCeti.abs_fderiv_planarNewtonianKernel_convolution_apply_one_le_and_apply_I_le`), hence `p`
oscillates by at most `40 K ρ²` there, and `|h - p(x)| ≤ ε + 40 K ρ²` on `B(x, 2ρ)`. The gradient
estimate for harmonic functions
(`InnerProductSpace.HarmonicOnNhd.norm_fderiv_le_of_norm_le`) bounds `‖Dh(x)‖` by `8 / ρ` times
this, and `Du(x) = Dh(x) - Dp(x)`.

The classical Poisson equation for `p` needs `χ Δu` to be `C²`, so `u` is assumed `C⁴` near the
closed disc of radius `3ρ` about `x`. Since the estimate only sees `u` on that disc, it is first
proved for globally `C⁴` functions and then applied to a globally `C⁴` function agreeing with `u`
near the disc (`IsCompact.exists_contDiff_eventuallyEq`). This allows `u` to be singular away
from the disc, as `log |α|²` is at the zeros of a section `α`.

## Main results

* `TauCeti.norm_fderiv_le_of_abs_le_of_abs_laplacian_le`: the interior gradient estimate.
* `TauCeti.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le`: the same estimate
  for the derivatives, `‖Dⁿ⁺¹u(x)‖ ≤ 8 ε / ρ + 340 K ρ` when `‖Dⁿu‖ ≤ ε` on `B(x, 2ρ)` and
  `‖Dⁿ(Δu)‖ ≤ K` on `B(x, 3ρ)`.
* `TendstoUniformly.fderiv_of_abs_laplacian_sub_le`: uniform convergence of the derivatives of
  uniformly converging functions whose Laplacians stay within a fixed distance.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.4 and Theorem 4.6.
* L. C. Evans, *Partial Differential Equations*, Section 2.2.3.
-/

public section

namespace TauCeti

open Complex Filter InnerProductSpace Laplacian Metric Set Topology
open scoped Convolution

/-- The Newtonian correction of the interior gradient estimate: if `u` is `C⁴` with `|Δu| ≤ K` on
`B(x, 3ρ)`, then there is a `C²` function `p`, the Newtonian potential of `Δu` cut off outside
`B(x, 3ρ)`, such that `u + p` is harmonic on `B(x, 2ρ)` and `‖Dp‖ ≤ 20 K ρ` on its closure. -/
private theorem exists_harmonicOnNhd_add_and_norm_fderiv_le {u : ℂ → ℝ} (hu : ContDiff ℝ 4 u)
    {x : ℂ} {ρ K : ℝ} (hρ : 0 < ρ) (hK : ∀ y ∈ ball x (3 * ρ), |Δ u y| ≤ K) :
    ∃ p : ℂ → ℝ, ContDiff ℝ 2 p ∧ HarmonicOnNhd (u + p) (ball x (2 * ρ)) ∧
      ∀ y ∈ closedBall x (2 * ρ), ‖fderiv ℝ p y‖ ≤ 20 * K * ρ := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK x (mem_ball_self (by positivity)))
  -- The cutoff `χ`, equal to one on `B(x, 2ρ)` and supported in `B(x, 3ρ)`, and the source
  -- `f = χ Δu`.
  let χ : ContDiffBump x := ⟨2 * ρ, 3 * ρ, by positivity, by linarith⟩
  set f : ℂ → ℝ := fun y ↦ χ y * Δ u y with hf_def
  have hf : ContDiff ℝ 2 f := χ.contDiff.mul (hu.laplacian (by norm_num))
  have hfc : HasCompactSupport f := χ.hasCompactSupport.mul_right
  have hfs : Function.support f ⊆ closedBall x (3 * ρ) := by
    refine (Function.support_mul_subset_left _ _).trans ?_
    rw [χ.support_eq]
    exact ball_subset_closedBall
  have hfK (y : ℂ) : ‖f y‖ ≤ K := by
    rw [Real.norm_eq_abs, hf_def, abs_mul, abs_of_nonneg χ.nonneg]
    by_cases hy : y ∈ ball x (3 * ρ)
    · exact (mul_le_mul χ.le_one (hK y hy) (abs_nonneg _) zero_le_one).trans_eq (one_mul K)
    · rw [← χ.support_eq, Function.notMem_support] at hy
      rw [hy, zero_mul]
      exact hK0
  -- The Newtonian potential `p = G ⋆ f`, with `Δp = -f`.
  set p : ℂ → ℝ := planarNewtonianKernel ⋆ f
  have hp : ContDiff ℝ 2 p := contDiff_planarNewtonianKernel_convolution hf hfc
  have hΔp : Δ p = -f := laplacian_planarNewtonianKernel_convolution hf hfc
  refine ⟨p, hp, fun y hy ↦ ⟨(hu.of_le (by norm_num)).contDiffAt.add hp.contDiffAt, ?_⟩,
    fun y hy ↦ ?_⟩
  · -- `Δ(u + p) = Δu - χ Δu = 0` on `B(x, 2ρ)`, where `χ = 1`.
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    rw [ContDiffAt.laplacian_add (hu.of_le (by norm_num)).contDiffAt hp.contDiffAt, hΔp,
      Pi.neg_apply, hf_def]
    simp only [χ.one_of_mem_closedBall (ball_subset_closedBall hz), one_mul, add_neg_cancel,
      Pi.zero_apply]
  · obtain ⟨h1, hI⟩ := abs_fderiv_planarNewtonianKernel_convolution_apply_one_le_and_apply_I_le
      (hf.of_le (by norm_num)) (by positivity : (0 : ℝ) ≤ 3 * ρ)
      (by positivity : (0 : ℝ) ≤ 2 * ρ) hfs hfK hy
    have hL := (fderiv ℝ p y).opNorm_le_bound (by positivity)
      (fderiv ℝ p y).norm_apply_le_norm_one_add_norm_I
    rw [RCLike.I_to_complex, Real.norm_eq_abs, Real.norm_eq_abs] at hL
    linarith

/-- The interior gradient estimate for a globally `C⁴` function. -/
private theorem norm_fderiv_le_of_abs_le_of_abs_laplacian_le_of_contDiff {u : ℂ → ℝ}
    (hu : ContDiff ℝ 4 u) {x : ℂ} {ρ ε K : ℝ} (hρ : 0 < ρ)
    (hε : ∀ y ∈ ball x (2 * ρ), |u y| ≤ ε) (hK : ∀ y ∈ ball x (3 * ρ), |Δ u y| ≤ K) :
    ‖fderiv ℝ u x‖ ≤ 8 * ε / ρ + 340 * K * ρ := by
  obtain ⟨p, hp, hharm, hDp⟩ := exists_harmonicOnNhd_add_and_norm_fderiv_le hu hρ hK
  -- The oscillation of `p` on `B(x, 2ρ)` is at most `40 K ρ²`.
  have hosc (y : ℂ) (hy : y ∈ ball x (2 * ρ)) : |p y - p x| ≤ 40 * K * ρ ^ 2 := by
    have h := (convex_ball x (2 * ρ)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hp.differentiable (by norm_num)).differentiableAt)
      (fun z hz ↦ hDp z (ball_subset_closedBall hz)) (mem_ball_self (by positivity)) hy
    rw [Real.norm_eq_abs] at h
    have hyx : ‖y - x‖ ≤ 2 * ρ := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
    calc |p y - p x| ≤ 20 * K * ρ * ‖y - x‖ := h
      _ ≤ 20 * K * ρ * (2 * ρ) := by gcongr; linarith [(norm_nonneg _).trans (hDp x
          (mem_closedBall_self (by positivity)))]
      _ = 40 * K * ρ ^ 2 := by ring
  -- The gradient estimate for the harmonic function `h = u + p - p(x)`.
  have hbound (y : ℂ) (hy : y ∈ ball x (2 * ρ)) : ‖u y + p y - p x‖ ≤ ε + 40 * K * ρ ^ 2 := by
    rw [Real.norm_eq_abs, add_sub_assoc]
    exact (abs_add_le _ _).trans (add_le_add (hε y hy) (hosc y hy))
  have hDh := (hharm.sub (harmonicOnNhd_const (p x))).norm_fderiv_le_of_norm_le hbound hρ
  rw [Complex.finrank_real_complex] at hDh
  -- `Du(x) = Dh(x) - Dp(x)`.
  have hDeq : fderiv ℝ u x = fderiv ℝ (fun y ↦ u y + p y - p x) x - fderiv ℝ p x := by
    rw [fderiv_sub_const, fderiv_fun_add ((hu.differentiable (by norm_num)).differentiableAt)
      ((hp.differentiable (by norm_num)).differentiableAt), add_sub_cancel_right]
  rw [hDeq]
  calc ‖fderiv ℝ (fun y ↦ u y + p y - p x) x - fderiv ℝ p x‖
      ≤ ‖fderiv ℝ (fun y ↦ u y + p y - p x) x‖ + ‖fderiv ℝ p x‖ := norm_sub_le _ _
    _ ≤ 2 ^ 2 * 2 / ρ * (ε + 40 * K * ρ ^ 2) + 20 * K * ρ :=
        add_le_add (by exact_mod_cast hDh) (hDp x (mem_closedBall_self (by positivity)))
    _ = 8 * ε / ρ + 340 * K * ρ := by field_simp; ring

/-- **Interior gradient estimate for Poisson's equation in the plane.** If `u` is `C⁴` near every
point of the closed disc of radius `3ρ` about `x`, with `|u| ≤ ε` on `B(x, 2ρ)` and `|Δu| ≤ K` on
`B(x, 3ρ)`, then `‖Du(x)‖ ≤ 8 ε / ρ + 340 K ρ`. Nothing is assumed about `u` outside that disc. -/
theorem norm_fderiv_le_of_abs_le_of_abs_laplacian_le {u : ℂ → ℝ} {x : ℂ} {ρ ε K : ℝ}
    (hu : ∀ y ∈ closedBall x (3 * ρ), ContDiffAt ℝ 4 u y) (hρ : 0 < ρ)
    (hε : ∀ y ∈ ball x (2 * ρ), |u y| ≤ ε) (hK : ∀ y ∈ ball x (3 * ρ), |Δ u y| ≤ K) :
    ‖fderiv ℝ u x‖ ≤ 8 * ε / ρ + 340 * K * ρ := by
  -- A globally `C⁴` function `v` agreeing with `u` near the closed disc.
  obtain ⟨v, hv, -, hvu⟩ := (isCompact_closedBall x (3 * ρ)).exists_contDiff_eventuallyEq 4 hu
  have hvu' (y : ℂ) (hy : y ∈ ball x (3 * ρ)) : v =ᶠ[𝓝 y] u :=
    hvu y (ball_subset_closedBall hy)
  rw [← (hvu x (mem_closedBall_self (by positivity))).fderiv_eq]
  refine norm_fderiv_le_of_abs_le_of_abs_laplacian_le_of_contDiff hv hρ (fun y hy ↦ ?_)
    fun y hy ↦ ?_
  · have hy' : y ∈ ball x (3 * ρ) := ball_subset_ball (by linarith) hy
    rw [(hvu' y hy').self_of_nhds]
    exact hε y hy
  · rw [(laplacian_congr_nhds (hvu' y hy)).self_of_nhds]
    exact hK y hy

/-- **Interior estimate for the derivatives of a solution of Poisson's equation in the plane.** If
`u` is `C^(n + 4)` near every point of the closed disc of radius `3ρ` about `x`, with `‖Dⁿu‖ ≤ ε`
on `B(x, 2ρ)` and `‖Dⁿ(Δu)‖ ≤ K` on `B(x, 3ρ)`, then `‖Dⁿ⁺¹u(x)‖ ≤ 8 ε / ρ + 340 K ρ`. For
`n = 0` this is `TauCeti.norm_fderiv_le_of_abs_le_of_abs_laplacian_le`. Iterated, it bounds every
derivative of a solution of a semilinear equation `Δu = F(u)` by its lower derivatives. -/
theorem norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le {u : ℂ → ℝ} {x : ℂ}
    {ρ ε K : ℝ} {n : ℕ} (hu : ∀ y ∈ closedBall x (3 * ρ), ContDiffAt ℝ (n + 4) u y) (hρ : 0 < ρ)
    (hε : ∀ y ∈ ball x (2 * ρ), ‖iteratedFDeriv ℝ n u y‖ ≤ ε)
    (hK : ∀ y ∈ ball x (3 * ρ), ‖iteratedFDeriv ℝ n (Δ u) y‖ ≤ K) :
    ‖iteratedFDeriv ℝ (n + 1) u x‖ ≤ 8 * ε / ρ + 340 * K * ρ := by
  -- A globally `C^(n + 4)` function `v` agreeing with `u` near the closed disc.
  obtain ⟨v, hv, -, hvu⟩ :=
    (isCompact_closedBall x (3 * ρ)).exists_contDiff_eventuallyEq (n + 4) hu
  have hvu' (y : ℂ) (hy : y ∈ ball x (3 * ρ)) : v =ᶠ[𝓝 y] u :=
    hvu y (ball_subset_closedBall hy)
  have hε₀ : 0 ≤ ε := (norm_nonneg _).trans (hε x (mem_ball_self (by positivity)))
  have hK₀ : 0 ≤ K := (norm_nonneg _).trans (hK x (mem_ball_self (by positivity)))
  have hDv : ContDiff ℝ 4 (iteratedFDeriv ℝ n v) := hv.iteratedFDeriv_right (by norm_cast; omega)
  -- On `B(x, 3ρ)` the derivatives of `v` and of `Δ v` are those of `u` and of `Δ u`.
  have hDvu (y : ℂ) (hy : y ∈ ball x (3 * ρ)) : iteratedFDeriv ℝ n v y = iteratedFDeriv ℝ n u y :=
    ((hvu' y hy).iteratedFDeriv ℝ n).self_of_nhds
  have hΔvu (y : ℂ) (hy : y ∈ ball x (3 * ρ)) :
      Δ (iteratedFDeriv ℝ n v) y = iteratedFDeriv ℝ n (Δ u) y := by
    rw [(hv.of_le (by norm_cast; omega)).laplacian_iteratedFDeriv]
    refine (Filter.EventuallyEq.iteratedFDeriv ℝ ?_ n).self_of_nhds
    filter_upwards [(hvu' y hy).eventually_nhds] with y' hy' using
      (laplacian_congr_nhds hy').self_of_nhds
  rw [← ((hvu x (mem_closedBall_self (by positivity))).iteratedFDeriv ℝ (n + 1)).self_of_nhds]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  -- The component `g = Dⁿv(·)(m₁, …, mₙ)` and the gradient estimate for it.
  set P : ℝ := ∏ i, ‖Fin.tail m i‖
  have hP : 0 ≤ P := by positivity
  set l := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ ℂ) ℝ (Fin.tail m)
  have hg : ContDiff ℝ 4 (l ∘ iteratedFDeriv ℝ n v) := l.contDiff.comp hDv
  have hgx := norm_fderiv_le_of_abs_le_of_abs_laplacian_le (u := l ∘ iteratedFDeriv ℝ n v) (x := x)
    (ε := ε * P) (K := K * P) (fun y _ ↦ hg.contDiffAt) hρ (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply
      ((hDv.differentiable (by norm_num)) x), Fin.prod_univ_succ]
    calc ‖fderiv ℝ (fun y ↦ iteratedFDeriv ℝ n v y (Fin.tail m)) x (m 0)‖
        ≤ ‖fderiv ℝ (l ∘ iteratedFDeriv ℝ n v) x‖ * ‖m 0‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (8 * (ε * P) / ρ + 340 * (K * P) * ρ) * ‖m 0‖ :=
        mul_le_mul_of_nonneg_right hgx (norm_nonneg _)
      _ = (8 * ε / ρ + 340 * K * ρ) * (‖m 0‖ * P) := by ring
  · have hy' : y ∈ ball x (3 * ρ) := ball_subset_ball (by linarith) hy
    rw [← Real.norm_eq_abs, Function.comp_apply, ContinuousMultilinearMap.apply_apply, hDvu y hy']
    exact ((iteratedFDeriv ℝ n u y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hε y hy) hP)
  · rw [← Real.norm_eq_abs, (hDv.contDiffAt.of_le (by norm_num)).laplacian_CLM_comp_left,
      Function.comp_apply, ContinuousMultilinearMap.apply_apply, hΔvu y hy]
    exact ((iteratedFDeriv ℝ n (Δ u) y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hK y hy) hP)

end TauCeti

open TauCeti InnerProductSpace Laplacian Metric in
/-- **Uniform convergence of derivatives.** If `C⁴` functions `u i` converge uniformly on `ℂ` to a
`C⁴` function `v`, and eventually `|Δ (u i) - Δ v| ≤ K` everywhere with one constant `K`, then
their derivatives converge uniformly: `D (u i) → D v`. -/
theorem TendstoUniformly.fderiv_of_abs_laplacian_sub_le {ι : Type*} {l : Filter ι}
    {u : ι → ℂ → ℝ} {v : ℂ → ℝ} {K : ℝ} (h : TendstoUniformly u v l)
    (hu : ∀ᶠ i in l, ContDiff ℝ 4 (u i)) (hv : ContDiff ℝ 4 v)
    (hK : ∀ᶠ i in l, ∀ z, |Δ (u i) z - Δ v z| ≤ K) :
    TendstoUniformly (fun i ↦ fderiv ℝ (u i)) (fderiv ℝ v) l := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  -- A radius `ρ` with `340 K₀ ρ < ε / 2`, where `K₀ = max K 0`.
  set K₀ := max K 0
  set ρ := ε / (680 * (K₀ + 1))
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  have hρ : 0 < ρ := by positivity
  have hKρ : 340 * K₀ * ρ < ε / 2 := by
    rw [show 340 * K₀ * ρ = ε / 2 * (K₀ / (K₀ + 1)) by simp only [ρ]; field_simp; ring]
    exact mul_lt_of_lt_one_right (half_pos hε) ((div_lt_one (by positivity)).2 (by linarith))
  filter_upwards [h (ε * ρ / 16) (by positivity), hu, hK] with i hi hui hKi z
  -- Apply the interior gradient estimate to `u i - v`.
  have hd := norm_fderiv_le_of_abs_le_of_abs_laplacian_le (u := u i - v) (x := z) (ρ := ρ)
    (ε := ε * ρ / 16) (K := K₀) (fun y _ ↦ (hui.sub hv).contDiffAt) hρ
    (fun y _ ↦ by rw [Pi.sub_apply, abs_sub_comm, ← Real.dist_eq]; exact (hi y).le)
    (fun y _ ↦ by
      rw [ContDiffAt.laplacian_sub (hui.of_le (by norm_num)).contDiffAt
        (hv.of_le (by norm_num)).contDiffAt]
      exact (hKi y).trans (le_max_left _ _))
  rw [fderiv_sub ((hui.differentiable (by norm_num)).differentiableAt)
    ((hv.differentiable (by norm_num)).differentiableAt)] at hd
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖fderiv ℝ (u i) z - fderiv ℝ v z‖ ≤ 8 * (ε * ρ / 16) / ρ + 340 * K₀ * ρ := hd
    _ = ε / 2 + 340 * K₀ * ρ := by field_simp; ring
    _ < ε := by linarith

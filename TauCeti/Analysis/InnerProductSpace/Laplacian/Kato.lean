/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.Gradient.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay

/-!
# A Kato subsolution for `Δ g = k g`

For a vector-valued `g` with `Δ g = k g`, `k ≥ 0`, the Bochner identity
`Δ ‖g‖² = 2 ‖Dg‖² + 2 k ‖g‖²` and the Kato inequality `|∇ ‖g‖| ≤ ‖Dg‖` show that `‖g‖` is a
subsolution of `-Δ + k`. Since `‖g‖` need not be differentiable where `g` vanishes, the
statement here uses the smooth regularization `w = √(‖g‖² + δ)`, `δ > 0`:

`k (w - √δ) ≤ Δ w`  (`ContDiffAt.mul_sqrt_norm_sq_add_sub_le_laplacian`).

As `δ → 0` the function `w - √δ` increases to `‖g‖`, so a comparison principle applied to
`w - √δ` with bounds uniform in `δ` transfers to `‖g‖` itself. This gives exponential decay of
`‖g‖` at every rate below `√k`, whereas the Bochner identity alone only makes `‖g‖²` a
subsolution of `-Δ + 2k`, which gives `‖g‖` the slower rates below `√(k / 2)`.

Combined with the exterior comparison principle `TauCeti.le_mul_exp_of_sq_mul_le_laplacian`:
if `Δ g = k g` with `c² ≤ k` outside the ball of radius `R`, `‖g‖ ≤ M` on its boundary sphere
and `g → 0` at infinity, then `‖g x‖ ≤ M exp (-c (‖x‖ - R))`
(`TauCeti.norm_le_mul_exp_of_laplacian_eq_smul`).

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001, Chapter 3 (the comparison principle).
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Topology
open scoped Gradient RealInnerProductSpace

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- **A Kato subsolution.** Let `g` be `C²` at `x` with `Δ g = k g` at `x`, where `k ≥ 0`. For
`δ > 0` the regularized norm `w = √(‖g‖² + δ)` satisfies `k (w - √δ) ≤ Δ w` at `x`. As `δ → 0`,
`w - √δ` increases to `‖g‖`, which is therefore a subsolution of `-Δ + k` in the limit. -/
theorem _root_.ContDiffAt.mul_sqrt_norm_sq_add_sub_le_laplacian {g : E → G} {x : E} {k δ : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hΔ : Δ g x = k • g x) (hk : 0 ≤ k) (hδ : 0 < δ) :
    k * (√(‖g x‖ ^ 2 + δ) - √δ) ≤ Δ (fun y ↦ √(‖g y‖ ^ 2 + δ)) x := by
  set b := stdOrthonormalBasis ℝ E
  set v : E → ℝ := fun y ↦ ‖g y‖ ^ 2
  set w : E → ℝ := fun y ↦ √(v y + δ)
  have hv : ContDiffAt ℝ 2 v x := hg.norm_sq ℝ
  have hvδ : ∀ y, 0 < v y + δ := fun y ↦ by positivity
  have hw : ContDiffAt ℝ 2 w x := (hv.add contDiffAt_const).sqrt (hvδ x).ne'
  have hwx : 0 < w x := Real.sqrt_pos.mpr (hvδ x)
  have hww : ∀ y, w y * w y = v y + δ := fun y ↦ Real.mul_self_sqrt (hvδ y).le
  -- The Bochner identity for `‖g‖²`, with `H = ∑ᵢ ‖Dg (bᵢ)‖²`.
  set H := ∑ i, ‖fderiv ℝ g x (b i)‖ ^ 2
  have hΔv : Δ v x = 2 * H + 2 * k * v x := by
    rw [hg.laplacian_norm_sq b, hΔ, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  -- Differentiating `w² = ‖g‖² + δ` gives `w ∂ᵥw = ⟪g, ∂ᵥg⟫`.
  have hD (h : E) : w x * fderiv ℝ w x h = ⟪g x, fderiv ℝ g x h⟫ := by
    have hgd := hg.differentiableAt (by norm_num)
    have hwd := hw.differentiableAt (by norm_num)
    have h₁ := congrArg (fun L : E →L[ℝ] ℝ ↦ L h)
      (congrArg (fun f ↦ fderiv ℝ f x) (funext hww))
    rw [fderiv_fun_mul hwd hwd, fderiv_add_const, hgd.hasFDerivAt.norm_sq.fderiv] at h₁
    simp only [add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h₁
    linarith
  -- The Kato inequality: `‖∇w‖² ≤ H`, since `‖g‖ ≤ w`.
  have hkato : ‖∇ w x‖ ^ 2 ≤ H := by
    rw [← b.sum_sq_inner_left]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [inner_gradient_left]
    have hcs := abs_real_inner_le_norm (g x) (fderiv ℝ g x (b i))
    have hgw : ‖g x‖ ^ 2 ≤ w x ^ 2 := by
      rw [sq (w x), hww]
      exact le_add_of_nonneg_right hδ.le
    have hsq : (w x * fderiv ℝ w x (b i)) ^ 2 ≤ w x ^ 2 * ‖fderiv ℝ g x (b i)‖ ^ 2 := by
      rw [hD, ← sq_abs]
      calc |⟪g x, fderiv ℝ g x (b i)⟫| ^ 2 ≤ (‖g x‖ * ‖fderiv ℝ g x (b i)‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hcs 2
        _ = ‖g x‖ ^ 2 * ‖fderiv ℝ g x (b i)‖ ^ 2 := by ring
        _ ≤ w x ^ 2 * ‖fderiv ℝ g x (b i)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hgw (by positivity)
    rw [mul_pow] at hsq
    exact le_of_mul_le_mul_left hsq (by positivity)
  -- The Laplacian of `w² = ‖g‖² + δ`, computed in two ways.
  have hΔww : 2 * w x * Δ w x + 2 * ‖∇ w x‖ ^ 2 = 2 * H + 2 * k * v x := by
    have h₁ := hw.laplacian_fun_mul hw
    rw [real_inner_self_eq_norm_sq] at h₁
    have h₂ : Δ (fun y ↦ w y * w y) x = Δ v x := by
      rw [funext hww]
      exact (hv.laplacian_add (contDiffAt_const (c := δ))).trans (by simp [laplacian_const])
    rw [h₂, hΔv] at h₁
    linarith
  -- Hence `w Δw ≥ k ‖g‖² = k (w² - δ) ≥ k w (w - √δ)`.
  have hsδ : √δ ≤ w x := Real.sqrt_le_sqrt (le_add_of_nonneg_left (by positivity))
  have hsqδ : √δ * √δ = δ := Real.mul_self_sqrt hδ.le
  have hmain : w x * (k * (w x - √δ)) ≤ w x * Δ w x := by
    have hvx : v x = w x * w x - δ := by rw [hww]; ring
    nlinarith [mul_nonneg hk (mul_nonneg (Real.sqrt_nonneg δ) (sub_nonneg.mpr hsδ))]
  exact le_of_mul_le_mul_left hmain hwx

/-- **Exponential decay of solutions of `Δ g = k g`.** Let `g` be continuous on the exterior
`‖x‖ ≥ R` of a ball and `C²` with `Δ g = k g` outside the closed ball, where `c² ≤ k` there and
`c ≥ 0`. If `‖g‖ ≤ M` on the sphere `‖x‖ = R` and `g → 0` at infinity, then
`‖g x‖ ≤ M exp (-c (‖x‖ - R))` for every `x` with `‖x‖ ≥ R`. The proof applies the comparison
principle to the Kato subsolutions `√(‖g‖² + δ) - √δ` and lets `δ → 0`. -/
theorem norm_le_mul_exp_of_laplacian_eq_smul {g : E → G} {k : E → ℝ} {R c M : ℝ} (hR : 0 < R)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hcont : ContinuousOn g {x | R ≤ ‖x‖})
    (hcd : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 g x) (hΔ : ∀ x, R < ‖x‖ → Δ g x = k x • g x)
    (hk : ∀ x, R < ‖x‖ → c ^ 2 ≤ k x) (hbdry : ∀ x, ‖x‖ = R → ‖g x‖ ≤ M)
    (hlim : Tendsto g (cocompact E) (𝓝 0)) {x : E} (hx : R ≤ ‖x‖) :
    ‖g x‖ ≤ M * Real.exp (-(c * (‖x‖ - R))) := by
  -- For each `δ > 0`, the exterior comparison principle applied to the Kato subsolution.
  have hδ : ∀ δ : ℝ, 0 < δ → √(‖g x‖ ^ 2 + δ) - √δ ≤ M * Real.exp (-(c * (‖x‖ - R))) := by
    intro δ hδ
    have hle : ∀ t : ℝ, 0 ≤ t → √(t ^ 2 + δ) - √δ ≤ t := fun t ht ↦ by
      have : √(t ^ 2 + δ) ≤ √((t + √δ) ^ 2) := Real.sqrt_le_sqrt (by
        nlinarith [Real.sq_sqrt hδ.le, Real.sqrt_nonneg δ])
      rw [Real.sqrt_sq (by positivity)] at this
      linarith
    have hge : ∀ t : ℝ, 0 ≤ √(t ^ 2 + δ) - √δ := fun t ↦
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t]))
    have hsq : ∀ y, R < ‖y‖ → ContDiffAt ℝ 2 (fun y ↦ √(‖g y‖ ^ 2 + δ)) y := fun y hy ↦
      (((hcd y hy).norm_sq ℝ).add contDiffAt_const).sqrt (by positivity)
    refine le_mul_exp_of_sq_mul_le_laplacian (u := fun y ↦ √(‖g y‖ ^ 2 + δ) - √δ) hR hc hM
      (fun y hy ↦ ((((hcont y hy).norm.pow 2).add continuousWithinAt_const).sqrt.sub
        continuousWithinAt_const)) (fun y hy ↦ (hsq y hy).sub contDiffAt_const)
      (fun y hy ↦ ?_) (fun y hy ↦ (hle _ (norm_nonneg _)).trans (hbdry y hy)) ?_ hx
    · have hΔsub : Δ (fun y ↦ √(‖g y‖ ^ 2 + δ) - √δ) y = Δ (fun y ↦ √(‖g y‖ ^ 2 + δ)) y :=
        ((hsq y hy).laplacian_sub (contDiffAt_const (c := √δ))).trans (by simp [laplacian_const])
      rw [hΔsub]
      exact (mul_le_mul_of_nonneg_right (hk y hy) (hge _)).trans
        ((hcd y hy).mul_sqrt_norm_sq_add_sub_le_laplacian (hΔ y hy)
          ((sq_nonneg c).trans (hk y hy)) hδ)
    · have hφ : Continuous fun t : ℝ ↦ √(t ^ 2 + δ) - √δ :=
        ((continuous_id.pow 2).add continuous_const).sqrt.sub continuous_const
      simpa [Function.comp_def] using
        (hφ.tendsto 0).comp (tendsto_zero_iff_norm_tendsto_zero.mp hlim)
  -- Let `δ → 0`.
  have hconv : Tendsto (fun δ : ℝ ↦ √(‖g x‖ ^ 2 + δ) - √δ) (𝓝[>] 0) (𝓝 ‖g x‖) := by
    have hψ : Continuous fun δ : ℝ ↦ √(‖g x‖ ^ 2 + δ) - √δ :=
      (continuous_const.add continuous_id).sqrt.sub Real.continuous_sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using
      (hψ.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  exact le_of_tendsto hconv (eventually_mem_nhdsWithin.mono hδ)

end TauCeti

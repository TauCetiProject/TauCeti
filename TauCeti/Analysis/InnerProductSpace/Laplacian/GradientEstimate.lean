/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison
import TauCeti.Analysis.InnerProductSpace.Laplacian.Commute
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The interior gradient estimate for Poisson's equation

Let `u` be a `C²` function on a ball `B(x₀, d)` of a finite-dimensional real inner product space
of dimension `n`, continuous up to the boundary. If `|u| ≤ M` on the closed ball and `|Δu| ≤ F`
on the open ball, then

`|∇u(x₀)| ≤ n M / d + d F / 2`

(`TauCeti.norm_fderiv_le_of_abs_laplacian_le`). This is the interior gradient estimate of
Gilbarg and Trudinger (Theorem 3.9). It bounds a first derivative by the function and its
Laplacian alone, with no information on the other second derivatives, and it is the step that
lets the derivatives of a solution of an elliptic equation `Δu = f(x, u)` be controlled one order
at a time.

The proof is by the comparison principle. Fix a unit vector `e` and reflect in the hyperplane
through `x₀` orthogonal to `e`: the odd part `ψ(x) = (u(x) - u(σx)) / 2` vanishes on the
hyperplane, is bounded by `M` on the half-sphere, and satisfies `|Δψ| ≤ F` on the half-ball. With
`t = ⟪e, x - x₀⟫`, the barrier

`φ(x) = (M / d²) ‖x - x₀‖² + A t - B t²`,  `A = n M / d + d F / 2`,  `B = n M / d² + F / 2`,

has `Δφ = -F`, is nonnegative on the hyperplane and at least `M` on the half-sphere, so the
comparison principle gives `|ψ| ≤ φ` on the half-ball. Along the ray `x₀ + s e`, `φ = A s + O(s²)`
while `ψ(x₀ + s e) = s ∂ₑu(x₀) + o(s)`, hence `|∂ₑu(x₀)| ≤ A`.

## Main results

* `TauCeti.abs_fderiv_apply_le_of_abs_laplacian_le`: the directional estimate
  `|∂ₑu(x₀)| ≤ n M / d + d F / 2` for a unit vector `e`.
* `TauCeti.norm_fderiv_le_of_abs_laplacian_le`: the same bound for `‖fderiv ℝ u x₀‖`.
* `TauCeti.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le`: the componentwise
  estimate `‖D^(k+1) L(z)‖ ≤ n M / d + d F / 2` from bounds `M` on `Dᵏ L` and `F` on `Dᵏ (Δ L)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 3.9.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Metric Filter Topology Set
open scoped RealInnerProductSpace Gradient ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If `q 0 = 0`, `q` has derivative `a` at `0` and `|q s| ≤ s (A + C s)` for `0 < s < d`, then
`|a| ≤ A`. -/
private theorem abs_le_of_hasDerivAt_of_abs_le {q : ℝ → ℝ} {a A C d : ℝ} (hd : 0 < d)
    (hq : HasDerivAt q a 0) (hq₀ : q 0 = 0) (hb : ∀ s ∈ Ioo 0 d, |q s| ≤ s * (A + C * s)) :
    |a| ≤ A := by
  have hslope : Tendsto (fun s ↦ |s⁻¹ * q s|) (𝓝[>] 0) (𝓝 |a|) := by
    have := hq.tendsto_slope_zero_right
    simp only [zero_add, hq₀, sub_zero, smul_eq_mul] at this
    exact this.abs
  have hlim : Tendsto (fun s : ℝ ↦ A + |C| * s) (𝓝[>] 0) (𝓝 A) := by
    have : Tendsto (fun s : ℝ ↦ A + |C| * s) (𝓝 0) (𝓝 (A + |C| * 0)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
    rw [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hslope hlim
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hd) fun s hs ↦ ?_)
  dsimp only
  rw [abs_mul, abs_inv, abs_of_pos hs.1, inv_mul_le_iff₀ hs.1]
  have hCs : s * (C * s) ≤ s * (|C| * s) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hs.1.le) hs.1.le
  linarith [hb s hs, mul_add s A (C * s), mul_add s A (|C| * s)]

/-- The Laplacian of the barrier `a ‖x - x₀‖² + A t - B t²`, `t = ⟪e, x - x₀⟫`, for a unit
vector `e` is the constant `2 n a - 2 B`. -/
private theorem laplacian_barrier {e : E} (he : ‖e‖ = 1) (x₀ : E) (a A B : ℝ) (x : E) :
    Δ (fun y ↦ a * ‖y - x₀‖ ^ 2 + (A * ⟪e, y - x₀⟫ - B * ⟪e, y - x₀⟫ ^ 2)) x =
      2 * Module.finrank ℝ E * a - 2 * B := by
  have hns : ContDiff ℝ 2 fun y : E ↦ ‖y - x₀‖ ^ 2 := (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hg : ContDiff ℝ 2 fun s : ℝ ↦ A * s - B * s ^ 2 := by fun_prop
  have hg'' : deriv (deriv fun s : ℝ ↦ A * s - B * s ^ 2) = fun _ ↦ -(2 * B) := by
    have h1 : deriv (fun s : ℝ ↦ A * s - B * s ^ 2) = fun s ↦ A - B * (2 * s) := by
      funext s
      rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop),
        deriv_const_mul _ (by fun_prop)]
      simp
    funext s
    rw [h1, deriv_fun_sub (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop),
      deriv_const_mul _ (by fun_prop)]
    simp [mul_comm]
  have hn : Δ (fun y : E ↦ ‖y - x₀‖ ^ 2) x = 2 * Module.finrank ℝ E := by
    have h := congrFun (laplacian_comp_add_right (fun y : E ↦ ‖y‖ ^ 2) (-x₀)) x
    simp only [← sub_eq_add_neg] at h
    rw [h, laplacian_norm_sq]
  have hsplit : (fun y ↦ a * ‖y - x₀‖ ^ 2 + (A * ⟪e, y - x₀⟫ - B * ⟪e, y - x₀⟫ ^ 2)) =
      a • (fun y : E ↦ ‖y - x₀‖ ^ 2) + fun y ↦ (fun s ↦ A * s - B * s ^ 2) ⟪e, y - x₀⟫ := rfl
  have h₁ : ContDiffAt ℝ 2 (a • fun y : E ↦ ‖y - x₀‖ ^ 2) x := hns.contDiffAt.const_smul a
  have h₂ : ContDiffAt ℝ 2 (fun y ↦ (fun s ↦ A * s - B * s ^ 2) ⟪e, y - x₀⟫) x :=
    (hg.comp ((innerSL ℝ e).contDiff.comp (contDiff_id.sub contDiff_const))).contDiffAt
  rw [hsplit, h₁.laplacian_add h₂, laplacian_smul _ hns.contDiffAt, hn,
    hg.laplacian_comp_inner_sub, hg'', he, smul_eq_mul]
  ring

/-- **The interior gradient estimate for Poisson's equation**, along a unit vector. Let `u` be
continuous on the closed ball `closedBall x₀ d` and `C²` on the open ball, with `|u| ≤ M` on the
closed ball and `|Δu| ≤ F` on the open ball. Then for every unit vector `e`,
`|∂ₑu(x₀)| ≤ n M / d + d F / 2`, where `n` is the dimension. -/
theorem abs_fderiv_apply_le_of_abs_laplacian_le {u : E → ℝ} {x₀ e : E} {d M F : ℝ}
    (hd : 0 < d) (he : ‖e‖ = 1) (hcont : ContinuousOn u (closedBall x₀ d))
    (hcd : ∀ x ∈ ball x₀ d, ContDiffAt ℝ 2 u x)
    (hM : ∀ x ∈ closedBall x₀ d, |u x| ≤ M) (hF : ∀ x ∈ ball x₀ d, |Δ u x| ≤ F) :
    |fderiv ℝ u x₀ e| ≤ Module.finrank ℝ E * M / d + d * F / 2 := by
  -- Structure: build the reflection `σ`, the odd part `ψ` and the barrier `φ`; compare `±ψ`
  -- with `φ` on the half-ball `K` by the comparison principle; then read off `∂ₑu(x₀)` from
  -- the bound `|ψ(x₀ + s e)| ≤ φ(x₀ + s e) = A s + O(s²)` along the ray.
  have : Nontrivial E := ⟨⟨e, 0, fun h ↦ by simp [h] at he⟩⟩
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_closedBall_self hd.le))
  have hF₀ : 0 ≤ F := (abs_nonneg _).trans (hF x₀ (mem_ball_self hd))
  set A := n * M / d + d * F / 2 with hA
  set B := n * M / d ^ 2 + F / 2 with hB
  have hAB : A = B * d := by rw [hA, hB]; field_simp
  have hB₀ : 0 ≤ B := by positivity
  -- The reflection `σ` in the hyperplane through `x₀` orthogonal to `e`.
  set R := (ℝ ∙ e)ᗮ.reflection
  have hR : ∀ y, R y = y - (2 * ⟪e, y⟫) • e := by
    intro y
    rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, he]
    simp only [neg_sub]
    norm_num
    module
  set σ : E → E := fun x ↦ R (x - x₀) + x₀ with hσ
  set t : E → ℝ := fun x ↦ ⟪e, x - x₀⟫ with ht
  have hσdist : ∀ x, dist (σ x) x₀ = dist x x₀ := fun x ↦ by
    simp only [hσ, dist_eq_norm, add_sub_cancel_right, R.norm_map]
  have hσcont : Continuous σ := (R.continuous.comp (continuous_id.sub continuous_const)).add
    continuous_const
  have hσsmooth : ContDiff ℝ 2 σ :=
    (R.toContinuousLinearEquiv.contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const
  have hσt : ∀ x, t x = 0 → σ x = x := fun x hx ↦ by
    simp only [hσ, hR]
    simp only [ht] at hx
    rw [hx]
    simp
  have hσray : ∀ s : ℝ, σ (x₀ + s • e) = x₀ - s • e := fun s ↦ by
    simp only [hσ, hR, add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq, he,
      one_pow, mul_one]
    module
  -- The Laplacian of `u ∘ σ` is `(Δ u) ∘ σ`.
  have hΔσ : ∀ x, Δ (fun y ↦ u (σ y)) x = Δ u (σ x) := by
    intro x
    have h : (fun y ↦ u (σ y)) = fun y ↦ ((fun w ↦ u (w + x₀)) ∘ R) (y + -x₀) := by
      funext y
      simp [hσ, sub_eq_add_neg]
    rw [h, laplacian_comp_add_right, laplacian_comp_linearIsometryEquiv_right,
      laplacian_comp_add_right]
    simp [hσ, sub_eq_add_neg]
  -- The odd part `ψ` and the barrier `φ`.
  set ψ : E → ℝ := fun x ↦ (1 / 2 : ℝ) * (u x - u (σ x)) with hψ
  set g : ℝ → ℝ := fun s ↦ A * s - B * s ^ 2 with hg
  set φ : E → ℝ := fun x ↦ M / d ^ 2 * ‖x - x₀‖ ^ 2 + g (t x) with hφ
  have hφsmooth : ContDiff ℝ 2 φ :=
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)).add
      ((by fun_prop : ContDiff ℝ 2 g).comp
        ((innerSL ℝ e).contDiff.comp (contDiff_id.sub contDiff_const)))
  have hΔφ : ∀ x, Δ φ x = -F := fun x ↦ by
    rw [laplacian_barrier he x₀ (M / d ^ 2) A B x, hB]
    field_simp
    ring
  -- The half-ball `K` on the side of `e`.
  set K : Set E := closedBall x₀ d ∩ {x | 0 ≤ t x} with hK
  have htcont : Continuous t := (innerSL ℝ e).continuous.comp (continuous_id.sub continuous_const)
  have hKc : IsCompact K :=
    (isCompact_closedBall x₀ d).inter_right (isClosed_le continuous_const htcont)
  have hKball : ∀ x ∈ K, σ x ∈ closedBall x₀ d := fun x hx ↦ by
    rw [mem_closedBall, hσdist]; exact hx.1
  have hint : ∀ x ∈ interior K, x ∈ ball x₀ d := fun x hx ↦ by
    have := interior_mono inter_subset_left hx
    rwa [interior_closedBall x₀ hd.ne'] at this
  have hfront : ∀ x ∈ frontier K, x ∈ K ∧ (t x = 0 ∨ dist x x₀ = d) := by
    intro x hx
    have hxK : x ∈ K := hKc.isClosed.frontier_subset hx
    refine ⟨hxK, ?_⟩
    by_contra! h
    have hU : IsOpen (ball x₀ d ∩ {y | 0 < t y}) :=
      isOpen_ball.inter (isOpen_lt continuous_const htcont)
    have hxU : x ∈ ball x₀ d ∩ {y | 0 < t y} :=
      ⟨lt_of_le_of_ne hxK.1 h.2, lt_of_le_of_ne hxK.2 (Ne.symm h.1)⟩
    have hsub : ball x₀ d ∩ {y | 0 < t y} ⊆ K := fun y hy ↦
      ⟨ball_subset_closedBall hy.1, show 0 ≤ t y from (show 0 < t y from hy.2).le⟩
    exact hx.2 (interior_maximal hsub hU hxU)
  -- Regularity of `ψ` on the half-ball.
  have hψcont : ContinuousOn ψ K := by
    refine continuousOn_const.mul ((hcont.mono inter_subset_left).sub ?_)
    exact hcont.comp hσcont.continuousOn fun x hx ↦ hKball x hx
  have hψcd : ∀ x ∈ interior K, ContDiffAt ℝ 2 ψ x := by
    intro x hx
    have hxb := hint x hx
    have hσb : σ x ∈ ball x₀ d := by rw [mem_ball, hσdist]; exact hxb
    exact contDiffAt_const.mul ((hcd x hxb).sub
      ((hcd (σ x) hσb).comp x hσsmooth.contDiffAt))
  have hΔψ : ∀ x ∈ interior K, |Δ ψ x| ≤ F := by
    intro x hx
    have hxb := hint x hx
    have hσb : σ x ∈ ball x₀ d := by rw [mem_ball, hσdist]; exact hxb
    have hu₁ := hcd x hxb
    have hu₂ : ContDiffAt ℝ 2 (fun y ↦ u (σ y)) x := (hcd (σ x) hσb).comp x hσsmooth.contDiffAt
    have hsmul : ψ = (1 / 2 : ℝ) • (u - fun y ↦ u (σ y)) := rfl
    have hsub : ContDiffAt ℝ 2 (u - fun y ↦ u (σ y)) x := hu₁.sub hu₂
    rw [hsmul, laplacian_smul _ hsub, hu₁.laplacian_sub hu₂, hΔσ, smul_eq_mul]
    have h₁ := hF x hxb
    have h₂ := hF (σ x) hσb
    rw [abs_le] at h₁ h₂ ⊢
    constructor <;> linarith
  -- The barrier dominates `±ψ` on the frontier.
  have hbd : ∀ x ∈ frontier K, |ψ x| ≤ φ x := by
    intro x hx
    obtain ⟨hxK, h | h⟩ := hfront x hx
    · simp only [hψ, hφ, hg, hσt x h, h, sub_self, mul_zero, abs_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      positivity
    · have hu₁ := hM x hxK.1
      have hu₂ := hM (σ x) (hKball x hxK)
      have hψM : |ψ x| ≤ M := by
        rw [hψ, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have := abs_sub (u x) (u (σ x))
        linarith
      have htd : t x ≤ d := by
        calc t x ≤ ‖e‖ * ‖x - x₀‖ := real_inner_le_norm _ _
          _ = d := by rw [he, one_mul, ← dist_eq_norm, h]
      have hφM : M ≤ φ x := by
        simp only [hφ, hg, ← dist_eq_norm, h]
        have h₀ : 0 ≤ t x * (A - B * t x) := mul_nonneg hxK.2 (by rw [hAB]; nlinarith)
        field_simp
        nlinarith
      linarith
  have hψle : ∀ x ∈ K, ψ x ≤ φ x :=
    le_of_laplacian_le_of_le_frontier hKc hψcont hφsmooth.continuous.continuousOn hψcd
      (fun x _ ↦ hφsmooth.contDiffAt)
      (fun x hx ↦ by rw [hΔφ]; exact neg_le_of_abs_le (hΔψ x hx))
      (fun x hx ↦ (le_abs_self _).trans (hbd x hx))
  have hψge : ∀ x ∈ K, -ψ x ≤ φ x :=
    le_of_laplacian_le_of_le_frontier hKc hψcont.neg hφsmooth.continuous.continuousOn
      (fun x hx ↦ (hψcd x hx).neg) (fun x _ ↦ hφsmooth.contDiffAt)
      (fun x hx ↦ by
        rw [← Pi.neg_def, hΔφ, laplacian_neg, Pi.neg_apply]
        exact neg_le_neg (le_of_abs_le (hΔψ x hx)))
      (fun x hx ↦ (neg_le_abs _).trans (hbd x hx))
  -- Along the ray `x₀ + s e`, `u (x₀ + s e) - u (x₀ - s e) = 2 ψ (x₀ + s e) = O(s)`, and its
  -- derivative at `s = 0` is `2 ∂ₑu(x₀)`.
  set q : ℝ → ℝ := fun s ↦ u (x₀ + s • e) - u (x₀ - s • e) with hq
  have hq_bound : ∀ s ∈ Ioo 0 d, |q s| ≤ s * (2 * A + 2 * (M / d ^ 2 - B) * s) := by
    intro s hs
    have hnx : ‖x₀ + s • e - x₀‖ = s := by
      rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hs.1]
    have htx : t (x₀ + s • e) = s := by
      simp [ht, inner_smul_right, he]
    have hxK : x₀ + s • e ∈ K :=
      ⟨by rw [mem_closedBall, dist_eq_norm, hnx]; exact hs.2.le,
        show 0 ≤ t (x₀ + s • e) by rw [htx]; exact hs.1.le⟩
    have hqψ : q s = 2 * ψ (x₀ + s • e) := by
      simp only [hq, hψ, hσray]
      ring
    have hφx : φ (x₀ + s • e) = s * (A + (M / d ^ 2 - B) * s) := by
      simp only [hφ, hg, htx, hnx]
      ring
    have habs : |ψ (x₀ + s • e)| ≤ φ (x₀ + s • e) :=
      abs_le.2 ⟨by linarith [hψge _ hxK], hψle _ hxK⟩
    rw [hqψ, abs_mul, abs_two]
    rw [hφx] at habs
    linarith
  have hderiv : HasDerivAt q (2 * fderiv ℝ u x₀ e) 0 := by
    have hu : HasFDerivAt u (fderiv ℝ u x₀) x₀ :=
      ((hcd x₀ (mem_ball_self hd)).differentiableAt (by norm_num)).hasFDerivAt
    have h₁ : HasDerivAt (fun s : ℝ ↦ x₀ + s • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x₀
    have h₂ : HasDerivAt (fun s : ℝ ↦ x₀ - s • e) (-e) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_sub x₀
    have hu₁ : HasDerivAt (fun s : ℝ ↦ u (x₀ + s • e)) (fderiv ℝ u x₀ e) 0 := by
      have hu' : HasFDerivAt u (fderiv ℝ u x₀) (x₀ + (0 : ℝ) • e) := by simpa using hu
      exact hu'.comp_hasDerivAt (0 : ℝ) h₁
    have hu₂ : HasDerivAt (fun s : ℝ ↦ u (x₀ - s • e)) (fderiv ℝ u x₀ (-e)) 0 := by
      have hu' : HasFDerivAt u (fderiv ℝ u x₀) (x₀ - (0 : ℝ) • e) := by simpa using hu
      exact hu'.comp_hasDerivAt (0 : ℝ) h₂
    convert hu₁.sub hu₂ using 1
    rw [map_neg]
    ring
  have h := abs_le_of_hasDerivAt_of_abs_le hd hderiv (by simp [hq]) hq_bound
  rw [abs_mul, abs_two] at h
  linarith

/-- **The interior gradient estimate for Poisson's equation.** Let `u` be continuous on the
closed ball `closedBall x₀ d` and `C²` on the open ball, with `|u| ≤ M` on the closed ball and
`|Δu| ≤ F` on the open ball. Then `‖∇u(x₀)‖ ≤ n M / d + d F / 2`, where `n` is the dimension. -/
theorem norm_fderiv_le_of_abs_laplacian_le {u : E → ℝ} {x₀ : E} {d M F : ℝ}
    (hd : 0 < d) (hcont : ContinuousOn u (closedBall x₀ d))
    (hcd : ∀ x ∈ ball x₀ d, ContDiffAt ℝ 2 u x)
    (hM : ∀ x ∈ closedBall x₀ d, |u x| ≤ M) (hF : ∀ x ∈ ball x₀ d, |Δ u x| ≤ F) :
    ‖fderiv ℝ u x₀‖ ≤ Module.finrank ℝ E * M / d + d * F / 2 := by
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_closedBall_self hd.le))
  have hF₀ : 0 ≤ F := (abs_nonneg _).trans (hF x₀ (mem_ball_self hd))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have he : ‖‖v‖⁻¹ • v‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]
  have h := abs_fderiv_apply_le_of_abs_laplacian_le hd he hcont hcd hM hF
  rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm, inv_mul_le_iff₀
    (norm_pos_iff.2 hv)] at h
  rw [Real.norm_eq_abs, mul_comm]
  exact h

/-- **The interior estimate for the next derivative.** Let `L` be of class `C^(k + 2)`. If the
`k`-th derivative of `L` is bounded by `M` on the closed ball `closedBall z d` and the `k`-th
derivative of `Δ L` is bounded by `F` on the open ball, then
`‖D^(k+1) L(z)‖ ≤ n M / d + d F / 2`, where `n` is the dimension. Each component
`y ↦ Dᵏ L(y) m` has Laplacian `Dᵏ (Δ L)(y) m`, so this is the interior gradient estimate applied
componentwise. -/
theorem norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le {L : E → ℝ} {N : ℕ∞ω}
    (hL : ContDiff ℝ N L) {k : ℕ} (hk : (k : ℕ∞ω) + 2 ≤ N) {z : E} {d M F : ℝ} (hd : 0 < d)
    (hM : ∀ y ∈ closedBall z d, ‖iteratedFDeriv ℝ k L y‖ ≤ M)
    (hF : ∀ y ∈ ball z d, ‖iteratedFDeriv ℝ k (Δ L) y‖ ≤ F) :
    ‖iteratedFDeriv ℝ (k + 1) L z‖ ≤ Module.finrank ℝ E * M / d + d * F / 2 := by
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM z (mem_closedBall_self hd.le))
  have hF₀ : 0 ≤ F := (norm_nonneg _).trans (hF z (mem_ball_self hd))
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  set P := ∏ j, ‖Fin.tail m j‖
  have hP₀ : 0 ≤ P := by positivity
  -- The component `u = Dᵏ L (·) (tail m)` and its Laplacian `Dᵏ (Δ L) (·) (tail m)`.
  set u : E → ℝ := fun y ↦ iteratedFDeriv ℝ k L y (Fin.tail m)
  have hu : ContDiff ℝ 2 u :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) ℝ (Fin.tail m)).contDiff.comp
      (hL.iteratedFDeriv_right (by rwa [add_comm]))
  have huM : ∀ y ∈ closedBall z d, |u y| ≤ M * P := fun y hy ↦
    ((iteratedFDeriv ℝ k L y).le_opNorm (Fin.tail m)).trans
      (mul_le_mul_of_nonneg_right (hM y hy) hP₀)
  have huF : ∀ y ∈ ball z d, |Δ u y| ≤ F * P := fun y hy ↦ by
    rw [show Δ u y = iteratedFDeriv ℝ k (Δ L) y (Fin.tail m) from
      congrFun (laplacian_iteratedFDeriv_apply hL hk (Fin.tail m)) y]
    exact ((iteratedFDeriv ℝ k (Δ L) y).le_opNorm (Fin.tail m)).trans
      (mul_le_mul_of_nonneg_right (hF y hy) hP₀)
  have hgrad := norm_fderiv_le_of_abs_laplacian_le hd hu.continuous.continuousOn
    (fun y _ ↦ hu.contDiffAt) huM huF
  -- The derivative of `u` at `z` in the direction `m 0` is `D^(k+1) L(z) m`.
  have hrep : iteratedFDeriv ℝ (k + 1) L z m = fderiv ℝ u z (m 0) := by
    rw [iteratedFDeriv_succ_apply_left, fderiv_continuousMultilinear_apply_const_apply
      ((hL.differentiable_iteratedFDeriv (lt_of_lt_of_le (by norm_cast; omega) hk)) z)]
  rw [hrep, Fin.prod_univ_succ]
  calc ‖fderiv ℝ u z (m 0)‖ ≤ ‖fderiv ℝ u z‖ * ‖m 0‖ := (fderiv ℝ u z).le_opNorm (m 0)
    _ ≤ (Module.finrank ℝ E * (M * P) / d + d * (F * P) / 2) * ‖m 0‖ :=
        mul_le_mul_of_nonneg_right hgrad (norm_nonneg _)
    _ = (Module.finrank ℝ E * M / d + d * F / 2) * (‖m 0‖ * P) := by ring

end TauCeti

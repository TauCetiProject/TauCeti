/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence

/-!
# The comparison principle for parabolic equations on the whole space

On the slab `Q = [0, T] × ℝⁿ`, with `ℝⁿ = EuclideanSpace ℝ ι`, consider the parabolic operator in
non-divergence form

`P u = ∂ₜu - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

with time-dependent coefficients `a : ℝ → ℝⁿ → Matrix ι ι ℝ`, `b : ℝ → ℝⁿ → ℝⁿ` and
`c : ℝ → ℝⁿ → ℝ`. A function `u : ℝ → ℝⁿ → ℝ` (time first, so `u t` is the spatial slice at time
`t`) is a classical solution when it is continuous on `Q`, `C²` in space and differentiable in time
for `0 < t < T`. In Lean `∂ᵢ∂ⱼu` at `(t, x)` is
`fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)`, `bⁱ ∂ᵢu` is
`fderiv ℝ (u t) x (b t x)` and `∂ₜu` is `deriv (fun s ↦ u s x) t`, as in
`TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence` and
`TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Basic`.

The coefficients are only required to satisfy, for `0 < t < T`,

* `0 ≤ ξᵀ a(t, x) ξ` (degenerate ellipticity) and `tr a(t, x) ≤ Λ`;
* `‖b(t, x)‖ ≤ β`;
* `c(t, x) ≤ γ`, an upper bound only.

No regularity of the coefficients is needed, since the argument is pointwise. A uniformly
elliptic `a` with `ξᵀ a ξ ≤ Λ' ‖ξ‖²` has `tr a ≤ n Λ'`. If a classical solution `u`, bounded above,
satisfies `P u ≤ F` and `u(·, 0) ≤ M`, where `0 ≤ γ`, `0 ≤ M` and `0 ≤ F`, then

`u(t, x) ≤ exp (γ t) (M + t F)`.

Taking `γ = C₊ = max (0, sup c)`, `M = sup u(·, 0)⁺` and `F = sup (P u)⁺` gives
`sup u⁺ ≤ exp (C₊ T) (sup u(·, 0)⁺ + T sup (P u)⁺)`. The comparison principle and uniqueness for
the Cauchy problem among classical solutions with bounded difference follow. These are the
whole-space analogues of the maximum principle on bounded cylinders; on `ℝⁿ` the parabolic
boundary is the initial slice alone, and the boundedness hypothesis replaces the lateral boundary
condition.

## The argument

First let `c ≤ 0`, `P u ≤ 0` and `u(·, 0) ≤ 0`. The barrier `ψ(t, x) = exp (K t) (1 + ‖x‖²)` with
`K = 2 |Λ| + |β| + 1` satisfies `P ψ > 0` wherever `u > 0`, because `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼ‖x‖² = 2 tr a`
and `2 ⟪x, b⟫ ≤ |β| (1 + ‖x‖²)`. Since `u` is bounded above, `u - ε ψ` is negative outside a ball,
so if it were positive somewhere on `[0, τ] × ℝⁿ` it would attain a positive maximum on a compact
cylinder, at a point with `t > 0`. There its spatial gradient vanishes, its principal part is
nonpositive and its time derivative is nonnegative, which contradicts `P (u - ε ψ) < 0`. Letting
`ε → 0` gives `u ≤ 0`. The general bound follows by applying this to
`exp (-γ t) u - (M + t F)`, which satisfies the same kind of inequality with the zeroth-order
coefficient `c - γ ≤ 0`.

## Main declarations

All declarations are in the `TauCeti.PDE` namespace.

* `le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add`:
  **the a priori bound** `u ≤ exp (γ t) (M + t F)` for subsolutions `P u ≤ F`.
* `abs_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`:
  the two-sided bound for `|P u| ≤ F`.
* `le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_initial`:
  **the comparison principle**.
* `eqOn_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq_of_eqOn_initial`:
  uniqueness for the Cauchy problem among classical solutions with bounded difference.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4
  (Theorem 9 and its corollaries).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004),
  Chapter 4.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Matrix RealInnerProductSpace Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}
  {u v : ℝ → EuclideanSpace ℝ ι → ℝ} {T Lam β γ : ℝ}

/-- The barrier step of the maximum principle: if `c ≤ 0` and `P u ≤ 0`, then at a point
`(t₀, x₀)` of the open slab where `u` is positive, the function `u - ε exp (K t) (1 + ‖x‖²)` with
`K = 2 |Λ| + |β| + 1` does not attain its maximum over `[0, t₀] × ℝⁿ`. -/
private theorem not_forall_sub_mul_exp_mul_le
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (htr : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, (a t x).trace ≤ Lam)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ 0)
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)
    {ε : ℝ} (hε : 0 < ε) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) {x₀ : EuclideanSpace ℝ ι}
    (hu₀ : 0 < u t₀ x₀) :
    ¬∀ s ∈ Icc 0 t₀, ∀ y, u s y - ε * (Real.exp ((2 * |Lam| + |β| + 1) * s) * (1 + ‖y‖ ^ 2)) ≤
      u t₀ x₀ - ε * (Real.exp ((2 * |Lam| + |β| + 1) * t₀) * (1 + ‖x₀‖ ^ 2)) := by
  intro hglob
  set K := 2 * |Lam| + |β| + 1
  set e := Real.exp (K * t₀)
  have he : 0 < e := Real.exp_pos _
  set q := ‖x₀‖
  -- In space, `u t₀ - ε e ‖·‖²` has a local maximum at `x₀`, so its operator is nonpositive.
  set f : EuclideanSpace ℝ ι → ℝ := u t₀ + (-(ε * e)) • fun y ↦ ‖y‖ ^ 2
  have hf : ∀ y, f y = u t₀ y - ε * (e * (1 + ‖y‖ ^ 2)) + ε * e := fun y ↦ by
    simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hfmax : IsLocalMax f x₀ := Filter.Eventually.of_forall fun y ↦ by
    rw [hf, hf]
    linarith [hglob t₀ ⟨ht₀.1.le, le_rfl⟩ y]
  have hnormcd : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ ι ↦ ‖y‖ ^ 2) x₀ :=
    contDiff_norm_sq ℝ |>.contDiffAt
  have hfcd : ContDiffAt ℝ 2 f x₀ := (hcd ht₀ x₀).add (hnormcd.const_smul (-(ε * e)))
  have hLf : ∑ i, ∑ j, a t₀ x₀ i j * fderiv ℝ (fderiv ℝ f) x₀ (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ f x₀ (b t₀ x₀) ≤ 0 := by
    rw [hfmax.fderiv_eq_zero, _root_.zero_apply, add_zero]
    exact sum_mul_fderiv_fderiv_nonpos_of_isLocalMax (ha ht₀ x₀) hfcd hfmax
  rw [sum_mul_fderiv_fderiv_add_fderiv_add_smul (hcd ht₀ x₀) hnormcd,
    sum_mul_fderiv_fderiv_add_fderiv_norm_sq] at hLf
  -- In time, `t₀` maximizes `s ↦ u s x₀ - ε exp (K s) (1 + q²)` from the left, so its derivative
  -- `∂ₜu - ε K e (1 + q²)` is nonnegative.
  have hg : HasDerivAt (fun s ↦ u s x₀ - ε * (Real.exp (K * s) * (1 + q ^ 2)))
      (deriv (fun s ↦ u s x₀) t₀ - ε * (K * e * (1 + q ^ 2))) t₀ := by
    have hexp : HasDerivAt (fun s ↦ Real.exp (K * s)) (K * e) t₀ := by
      have := ((hasDerivAt_id t₀).const_mul K).exp
      simp only [id, mul_one] at this
      rw [mul_comm]
      exact this
    exact (hdiff ht₀ x₀).hasDerivAt.sub ((hexp.mul_const (1 + q ^ 2)).const_mul ε)
  have hleft : IsLocalMaxOn (fun s ↦ u s x₀ - ε * (Real.exp (K * s) * (1 + q ^ 2))) (Iic t₀) t₀ :=
    Filter.mem_of_superset (Icc_mem_nhdsLE ht₀.1) fun s hs ↦ hglob s hs x₀
  have htime := hleft.hasDerivWithinAt_Iic_nonneg hg.hasDerivWithinAt
  -- The zeroth-order term is nonpositive, since `c ≤ 0` and `u t₀ x₀ > 0`.
  have hcu : c t₀ x₀ * u t₀ x₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hc ht₀ x₀) hu₀.le
  -- Bound the barrier terms: `tr a ≤ |Λ|` and `2 ⟪x₀, b⟫ ≤ |β| (1 + q²)`.
  have htr' : (a t₀ x₀).trace ≤ |Lam| := (htr ht₀ x₀).trans (le_abs_self Lam)
  have hinner : 2 * ⟪x₀, b t₀ x₀⟫ ≤ |β| * (1 + q ^ 2) := by
    have h1 : ⟪x₀, b t₀ x₀⟫ ≤ q * |β| :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        ((hb ht₀ x₀).trans (le_abs_self β)) (norm_nonneg _))
    nlinarith [sq_nonneg (q - 1), abs_nonneg β]
  -- Hence `ε e K (1 + q²) ≤ ∂ₜu ≤ ε e (2 |Λ| + |β| (1 + q²))`, which contradicts the choice of `K`.
  have hεe : 0 < ε * e := mul_pos hε he
  have hkey := hsub ht₀ x₀
  have hpos : 0 < ε * e * (2 * |Lam| * q ^ 2 + 1 + q ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left htr' hεe.le, mul_le_mul_of_nonneg_left hinner hεe.le]

/-- The perturbed bound behind the maximum principle: if `c ≤ 0`, `P u ≤ 0` and `u(·, 0) ≤ 0`,
then `u ≤ ε exp (K t) (1 + ‖x‖²)` below the top slice, for every `ε > 0`, where
`K = 2 |Λ| + |β| + 1`. -/
private theorem le_mul_exp_mul_of_deriv_le_of_nonpos
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (htr : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, (a t x).trace ≤ Lam)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ 0)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hbdd : BddAbove (Function.uncurry u '' Icc 0 T ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)
    (hinit : ∀ x, u 0 x ≤ 0) {ε : ℝ} (hε : 0 < ε) {t₁ : ℝ} (ht₁ : t₁ ∈ Ico 0 T)
    (x₁ : EuclideanSpace ℝ ι) :
    u t₁ x₁ ≤ ε * (Real.exp ((2 * |Lam| + |β| + 1) * t₁) * (1 + ‖x₁‖ ^ 2)) := by
  set K := 2 * |Lam| + |β| + 1
  have hK : 0 < K := by positivity
  set w : ℝ × EuclideanSpace ℝ ι → ℝ :=
    fun p ↦ u p.1 p.2 - ε * (Real.exp (K * p.1) * (1 + ‖p.2‖ ^ 2))
  obtain ⟨Mu, hMu⟩ := hbdd
  have hsub' : Icc 0 t₁ ⊆ Icc 0 T := Icc_subset_Icc_right ht₁.2.le
  -- Outside the ball of radius `R`, the perturbation dominates the bound on `u`, so `w < 0`.
  set R := |Mu| / ε + 1
  have hout : ∀ ⦃s⦄, s ∈ Icc 0 t₁ → ∀ y, R < ‖y‖ → w (s, y) < 0 := by
    intro s hs y hy
    have h1 : 1 ≤ Real.exp (K * s) := Real.one_le_exp (mul_nonneg hK.le hs.1)
    have h2 : |Mu| < ε * ‖y‖ := by
      rw [← div_lt_iff₀' hε]
      linarith
    have h3 : ‖y‖ ≤ ‖y‖ ^ 2 := by
      have : 0 ≤ |Mu| / ε := by positivity
      nlinarith
    have h4 : ε * (1 + ‖y‖ ^ 2) ≤ ε * (Real.exp (K * s) * (1 + ‖y‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) h1) hε.le
    have h5 : u s y ≤ Mu := hMu ⟨(s, y), ⟨hsub' hs, mem_univ y⟩, rfl⟩
    simp only [w]
    nlinarith [le_abs_self Mu]
  by_contra hlt
  have hw₁ : 0 < w (t₁, x₁) := by simp only [w]; linarith
  have hx₁ : x₁ ∈ Metric.closedBall 0 R := by
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact (hout ⟨ht₁.1, le_rfl⟩ x₁ (not_le.mp h)).not_gt hw₁
  -- `w` attains its maximum over the compact cylinder `[0, t₁] × closedBall 0 R`.
  have hwcont : ContinuousOn w (Icc 0 t₁ ×ˢ Metric.closedBall 0 R) :=
    ((hcont.mono (prod_mono hsub' (subset_univ _)))).sub
      (by fun_prop : Continuous fun p : ℝ × EuclideanSpace ℝ ι ↦
        ε * (Real.exp (K * p.1) * (1 + ‖p.2‖ ^ 2))).continuousOn |>.mono
      (prod_mono le_rfl (subset_univ _))
  obtain ⟨⟨t₀, x₀⟩, ⟨ht₀, -⟩, hmax⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall 0 R)).exists_isMaxOn
      ⟨(t₁, x₁), ⟨ht₁.1, le_rfl⟩, hx₁⟩ hwcont
  have hw₀ : 0 < w (t₀, x₀) := hw₁.trans_le (hmax ⟨⟨ht₁.1, le_rfl⟩, hx₁⟩)
  -- The maximum over the cylinder is a maximum over the whole slab `[0, t₁] × ℝⁿ`.
  have hglob : ∀ ⦃s⦄, s ∈ Icc 0 t₁ → ∀ y, w (s, y) ≤ w (t₀, x₀) := by
    intro s hs y
    by_cases hy : ‖y‖ ≤ R
    · exact hmax ⟨hs, mem_closedBall_zero_iff.mpr hy⟩
    · exact ((hout hs y (not_le.mp hy)).trans hw₀).le
  -- The maximum is not attained on the initial slice, where `w < 0`.
  rcases ht₀.1.eq_or_lt with h0 | hpos
  · subst h0
    have : w (0, x₀) < 0 := by
      have := hinit x₀
      simp only [w, mul_zero, Real.exp_zero, one_mul]
      nlinarith [sq_nonneg ‖x₀‖]
    exact this.not_gt hw₀
  -- Nor at a point of the open slab, by the barrier step.
  have hu₀ : 0 < u t₀ x₀ := by
    have : 0 < ε * (Real.exp (K * t₀) * (1 + ‖x₀‖ ^ 2)) := by positivity
    simp only [w] at hw₀
    linarith
  exact not_forall_sub_mul_exp_mul_le ha htr hb hc hcd hdiff hsub hε
    ⟨hpos, ht₀.2.trans_lt ht₁.2⟩ hu₀ fun s hs y ↦ hglob ⟨hs.1, hs.2.trans ht₀.2⟩ y

/-- The maximum principle for `P` when `c ≤ 0`: a classical solution of `P u ≤ 0` that is
bounded above on `[0, T] × ℝⁿ` and nonpositive on the initial slice is nonpositive. -/
private theorem nonpos_of_deriv_le_of_nonpos
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (htr : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, (a t x).trace ≤ Lam)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ 0)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hbdd : BddAbove (Function.uncurry u '' Icc 0 T ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)
    (hinit : ∀ x, u 0 x ≤ 0) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, u t x ≤ 0 := by
  intro t ht x
  -- Below the top, let `ε → 0` in the perturbed bound.
  have hlt : ∀ s ∈ Ico 0 T, u s x ≤ 0 := fun s hs ↦
    le_of_forall_pos_mul_le (C := Real.exp ((2 * |Lam| + |β| + 1) * s) * (1 + ‖x‖ ^ 2))
      (by positivity) fun ε hε ↦ by
      rw [zero_add]
      exact le_mul_exp_mul_of_deriv_le_of_nonpos ha htr hb hc hcont hbdd hcd hdiff hsub hinit
        hε hs x
  rcases ht.2.lt_or_eq with htT | rfl
  · exact hlt t ⟨ht.1, htT⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · exact h0 ▸ hinit x
  -- At the top `t = T > 0`, pass to the limit from below by continuity.
  have hcw : ContinuousWithinAt (fun s ↦ u s x) (Ico 0 t) t :=
    ((hcont.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦ ⟨hs, mem_univ x⟩) t
      ht).mono Ico_subset_Icc_self
  exact hcw.closure_le (by rw [closure_Ico hpos.ne]; exact ht) continuousWithinAt_const hlt

/-- The exponential change of variables: if `P u ≤ F` at `(t, x)` with `c ≤ γ` there, then
`w = exp (-γ t) u - (M + t F)` satisfies `P w ≤ 0` at `(t, x)` for the zeroth-order coefficient
`c - γ`, provided `0 ≤ γ t`, `0 ≤ M + t F` and `0 ≤ F`. -/
private theorem deriv_le_of_eq_exp_neg_mul_mul_sub {A : Matrix ι ι ℝ}
    {u w : ℝ → EuclideanSpace ℝ ι → ℝ} {c γ M F t : ℝ} {x v : EuclideanSpace ℝ ι}
    (hw : ∀ s y, w s y = Real.exp (-(γ * s)) * u s y - (M + s * F))
    (hc : c ≤ γ) (hγt : 0 ≤ γ * t) (hMF : 0 ≤ M + t * F) (hF : 0 ≤ F)
    (hcd : ContDiffAt ℝ 2 (u t) x) (hdiff : DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x v + c * u t x + F) :
    deriv (fun s ↦ w s x) t ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ (w t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (w t) x v + (c - γ) * w t x := by
  set e := Real.exp (-(γ * t))
  have he : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hwt : w t = (fun _ ↦ -(M + t * F)) + e • u t := funext fun y ↦ by
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
    ring
  have hexp : HasDerivAt (fun s ↦ Real.exp (-(γ * s))) (-γ * e) t := by
    simpa [e, mul_comm] using ((hasDerivAt_id t).const_mul γ).neg.exp
  have hderiv : deriv (fun s ↦ w s x) t = -γ * e * u t x + e * deriv (fun s ↦ u s x) t - F := by
    simp only [hw]
    rw [((hexp.fun_mul hdiff.hasDerivAt).fun_sub
      (((hasDerivAt_id' t).mul_const F).const_add M)).deriv]
    ring
  rw [hderiv, hwt, sum_mul_fderiv_fderiv_add_fderiv_add_smul contDiffAt_const hcd]
  simp only [fderiv_fun_const, fderiv_zero, Pi.zero_apply, _root_.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcγ : (c - γ) * (M + t * F) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) hMF
  nlinarith [mul_le_mul_of_nonneg_left hsub he.le, mul_le_mul_of_nonneg_right he1 hF]

/-- **The a priori bound for parabolic equations on the whole space.** Let
`P u = ∂ₜu - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` where, for `0 < t < T`, the matrix `a(t, x)` has
nonnegative quadratic form and trace at most `Λ`, `‖b(t, x)‖ ≤ β` and `c(t, x) ≤ γ` with
`0 ≤ γ`. Let `u` be continuous on `[0, T] × ℝⁿ` and bounded above there, `C²` in space and
differentiable in time for `0 < t < T`, with `P u ≤ F` there and `u(·, 0) ≤ M`, where `0 ≤ M` and
`0 ≤ F`. Then `u(t, x) ≤ exp (γ t) (M + t F)` on `[0, T] × ℝⁿ`. -/
theorem le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (htr : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, (a t x).trace ≤ Lam)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ γ) (hγ : 0 ≤ γ) {M F : ℝ} (hM : 0 ≤ M)
    (hF : 0 ≤ F)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hbdd : BddAbove (Function.uncurry u '' Icc 0 T ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x + F)
    (hinit : ∀ x, u 0 x ≤ M) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, u t x ≤ Real.exp (γ * t) * (M + t * F) := by
  -- Apply the maximum principle to `w = exp (-γ t) u - (M + t F)` and the coefficient `c - γ`.
  set w : ℝ → EuclideanSpace ℝ ι → ℝ :=
    fun t ↦ (fun _ ↦ -(M + t * F)) + Real.exp (-(γ * t)) • u t
  have hw : ∀ t x, w t x = Real.exp (-(γ * t)) * u t x - (M + t * F) := fun t x ↦ by
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hwcont : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ univ) := by
    refine ContinuousOn.congr ?_ fun p _ ↦ hw p.1 p.2
    exact (((by fun_prop : Continuous fun p : ℝ × EuclideanSpace ℝ ι ↦
      Real.exp (-(γ * p.1))).continuousOn.mul hcont).sub
      (by fun_prop : Continuous fun p : ℝ × EuclideanSpace ℝ ι ↦ M + p.1 * F).continuousOn)
  have hwbdd : BddAbove (Function.uncurry w '' Icc 0 T ×ˢ univ) := by
    obtain ⟨Mu, hMu⟩ := hbdd
    refine ⟨max Mu 0, ?_⟩
    rintro _ ⟨⟨t, x⟩, ⟨ht, -⟩, rfl⟩
    have h1 : Real.exp (-(γ * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have h2 : u t x ≤ max Mu 0 := (hMu ⟨(t, x), ⟨ht, mem_univ x⟩, rfl⟩).trans (le_max_left _ _)
    have h3 : 0 ≤ M + t * F := by nlinarith [ht.1]
    simp only [Function.uncurry_apply_pair, hw]
    nlinarith [Real.exp_pos (-(γ * t)), le_max_right Mu 0,
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(γ * t))).le,
      mul_le_mul_of_nonneg_right h1 (le_max_right Mu 0)]
  have hwle := nonpos_of_deriv_le_of_nonpos (u := w) (c := fun t x ↦ c t x - γ) ha htr hb
    (fun t ht x ↦ sub_nonpos.mpr (hc ht x)) hwcont hwbdd
    (fun t ht x ↦ contDiffAt_const.add ((hcd ht x).const_smul (Real.exp (-(γ * t)))))
    (fun t ht x ↦ by
      simp only [hw]
      fun_prop (disch := exact hdiff ht x))
    (fun t ht x ↦ deriv_le_of_eq_exp_neg_mul_mul_sub hw (hc ht x) (mul_nonneg hγ ht.1.le)
      (add_nonneg hM (mul_nonneg ht.1.le hF)) hF (hcd ht x) (hdiff ht x) (hsub ht x))
    (fun x ↦ by simpa [hw] using hinit x)
  intro t ht x
  have h := hwle ht x
  rwa [hw, sub_nonpos, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at h

/-- **The two-sided a priori bound for parabolic equations on the whole space.** Under the
hypotheses on `a`, `b`, `c` of
`le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add`, a function `u`
that is continuous and bounded on `[0, T] × ℝⁿ`, `C²` in space and differentiable in time for
`0 < t < T`, with `|P u| ≤ F` there and `|u(·, 0)| ≤ M`, satisfies
`|u(t, x)| ≤ exp (γ t) (M + t F)`. -/
theorem abs_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (htr : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, (a t x).trace ≤ Lam)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ γ) (hγ : 0 ≤ γ) {M F : ℝ} (hM : 0 ≤ M)
    (hF : 0 ≤ F)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hbdd : BddAbove (Function.uncurry u '' Icc 0 T ×ˢ univ))
    (hbdd' : BddBelow (Function.uncurry u '' Icc 0 T ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)| ≤ F)
    (hinit : ∀ x, |u 0 x| ≤ M) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, |u t x| ≤ Real.exp (γ * t) * (M + t * F) := by
  intro t ht x
  have hle := le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add ha htr
    hb hc hγ hM hF hcont hbdd hcd hdiff
    (fun s hs y ↦ by linarith [(abs_le.mp (hP hs y)).2]) (fun y ↦ (abs_le.mp (hinit y)).2) ht x
  -- The lower bound is the upper bound for `-u`.
  have hge := le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add
    (u := -u) ha htr hb hc hγ hM hF
    (hcont.neg.congr fun _ _ ↦ by simp [Function.uncurry_def])
    (by
      obtain ⟨m, hm⟩ := hbdd'
      refine ⟨-m, ?_⟩
      rintro _ ⟨⟨s, y⟩, hp, rfl⟩
      have : m ≤ u s y := hm ⟨(s, y), hp, rfl⟩
      simp only [Function.uncurry_apply_pair, Pi.neg_apply]
      linarith)
    (fun s hs y ↦ (hcd hs y).neg) (fun s hs y ↦ (hdiff hs y).neg)
    (fun s hs y ↦ by
      simp only [Pi.neg_apply, deriv.fun_neg]
      rw [sum_mul_fderiv_fderiv_add_fderiv_neg]
      linarith [(abs_le.mp (hP hs y)).1])
    (fun y ↦ by
      simp only [Pi.neg_apply]
      linarith [(abs_le.mp (hinit y)).1]) ht x
  simp only [Pi.neg_apply] at hge
  exact abs_le.mpr ⟨by linarith, hle⟩

/-- **The comparison principle for parabolic equations on the whole space.** Let `a`, `b` be as
in `le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add` and let `c` be
bounded above for `0 < t < T`. Let `u` and `v` be continuous on `[0, T] × ℝⁿ`, `C²` in space and
differentiable in time for `0 < t < T`, with `u - v` bounded above. If
`P u ≤ P v` for `0 < t < T` and `u(·, 0) ≤ v(·, 0)`, then `u ≤ v` on `[0, T] × ℝⁿ`. -/
theorem le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_initial
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (htr : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, (a t x).trace ≤ Lam)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ γ)
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hbdd : BddAbove (Function.uncurry (u - v) '' Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, deriv (fun s ↦ u s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x) ≤
      deriv (fun s ↦ v s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (v t) x (b t x) + c t x * v t x))
    (hinit : ∀ x, u 0 x ≤ v 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, u t x ≤ v t x := by
  -- Apply the a priori bound to `w = u - v` with `M = F = 0`.
  set w : ℝ → EuclideanSpace ℝ ι → ℝ := fun t ↦ u t + (-1 : ℝ) • v t
  have hw : ∀ t x, w t x = u t x - v t x := fun t x ↦ by
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨Mw, hMw⟩ := hbdd
  have h := le_exp_mul_mul_add_mul_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_add (u := w)
    (γ := max γ 0) (M := 0) (F := 0) ha htr hb (fun t ht x ↦ (hc ht x).trans (le_max_left _ _))
    (le_max_right _ _) le_rfl le_rfl
    ((hucont.sub hvcont).congr fun p _ ↦ hw p.1 p.2)
    ⟨Mw, by
      rintro _ ⟨⟨t, x⟩, hp, rfl⟩
      have h1 : u t x - v t x ≤ Mw := hMw ⟨(t, x), hp, rfl⟩
      simpa only [Function.uncurry_apply_pair, hw] using h1⟩
    (fun t ht x ↦ (hucd ht x).add ((hvcd ht x).const_smul (-1 : ℝ)))
    (fun t ht x ↦ by
      simp only [hw]
      exact (hudiff ht x).sub (hvdiff ht x))
    (fun t ht x ↦ by
      rw [sum_mul_fderiv_fderiv_add_fderiv_add_smul (hucd ht x) (hvcd ht x)]
      simp only [hw]
      rw [deriv_fun_sub (hudiff ht x) (hvdiff ht x)]
      linarith [hP ht x])
    (fun x ↦ by simpa [hw] using hinit x)
  intro t ht x
  have := h ht x
  rw [hw, mul_zero, add_zero, mul_zero] at this
  linarith

/-- **Uniqueness for the Cauchy problem on the whole space.** With `a`, `b`, `c` as in
`le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_initial`, two functions that are
continuous on `[0, T] × ℝⁿ` with bounded difference there, `C²` in space and differentiable in
time for `0 < t < T`, with `P u = P v` there and `u(·, 0) = v(·, 0)`, agree on `[0, T] × ℝⁿ`. -/
theorem eqOn_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq_of_eqOn_initial
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (htr : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, (a t x).trace ≤ Lam)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ γ)
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hbdd : Bornology.IsBounded (Function.uncurry (u - v) '' Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, deriv (fun s ↦ u s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x) =
      deriv (fun s ↦ v s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (v t) x (b t x) + c t x * v t x))
    (hinit : EqOn (u 0) (v 0) univ) :
    EqOn (Function.uncurry u) (Function.uncurry v) (Icc 0 T ×ˢ univ) := by
  rw [isBounded_iff_bddBelow_bddAbove] at hbdd
  -- The difference `v - u` is bounded above because `u - v` is bounded below.
  have hbdd' : BddAbove (Function.uncurry (v - u) '' Icc 0 T ×ˢ univ) := by
    obtain ⟨m, hm⟩ := hbdd.1
    refine ⟨-m, ?_⟩
    rintro _ ⟨⟨t, x⟩, hp, rfl⟩
    have h1 : m ≤ u t x - v t x := hm ⟨(t, x), hp, rfl⟩
    simp only [Function.uncurry_apply_pair, Pi.sub_apply]
    linarith
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact le_antisymm
    (le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_initial ha htr hb hc hucont
      hvcont hbdd.2 hucd hvcd hudiff hvdiff (fun s hs y ↦ (hP hs y).le)
      (fun y ↦ (hinit (mem_univ y)).le) ht x)
    (le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_initial ha htr hb hc hvcont
      hucont hbdd' hvcd hucd hvdiff hudiff (fun s hs y ↦ (hP hs y).ge)
      (fun y ↦ (hinit (mem_univ y)).ge) ht x)

end PDE

end TauCeti

end

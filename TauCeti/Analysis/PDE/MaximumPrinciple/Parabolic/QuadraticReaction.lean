/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Lower bounds for parabolic inequalities with a quadratic reaction term

Let `c ≥ 0`. A function `u` with `∂ₜu ≥ Δu + c u²` satisfies `∂ₜu ≥ c u²` at every spatial
minimum, because the Laplacian is nonnegative there. This file shows that this weaker condition
alone forces `u` to stay above every subsolution `φ` of the ODE `φ' = c φ²` that lies below `u`
on the parabolic boundary. In particular a lower bound `u ≥ ρ` at time zero propagates to the
explicit bound `u(t, x) ≥ ρ / (1 - c ρ t)` for as long as the barrier has not blown up, that is
while `1 - c ρ t > 0`. For `ρ ≤ 0` this holds for all later times.

Only spatial local minima enter the hypotheses, so the results apply to any elliptic operator
that is nonnegative at a minimum. This includes a Laplacian depending on time through a moving
metric. The main application is the scalar curvature of a Ricci flow
`∂ₜg = -2 Ric` on a closed `n`-manifold: it evolves by `∂ₜR = ΔR + 2|Ric|²`, and
`|Ric|² ≥ R² / n`. So `R` is a supersolution with `c = 2 / n`. In dimension three, a lower bound
`R ≥ -6` at time zero propagates to `R ≥ -6 / (1 + 4t)`.

The proof applies the perturbation argument of the weak parabolic maximum principle,
`TauCeti.le_of_deriv_nonpos_of_isLocalMax_le_parabolicBoundary`, to `exp (-2cMt) (φ - u)`, where
`M` is the maximum of `φ`. At an interior spatial maximum of `φ - u` with `u < φ`, the time
derivative of `φ - u` is at most `c (φ² - u²) = c (φ - u)(φ + u) ≤ 2cM (φ - u)`, which the
exponential weight absorbs.

## Main results

* `TauCeti.ge_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary`: comparison with an
  ODE subsolution on a cylinder `[0, T] × K`.
* `TauCeti.div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary`: the
  explicit lower bound `ρ / (1 - c ρ t)` on such a cylinder.
* `TauCeti.div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin`: the same bound on a compact space
  without lateral boundary, such as a closed manifold.

The three-dimensional normalization `-6 / (1 + 4t)` is in
`TauCeti.Geometry.RicciFlow.ScalarCurvatureComparison`.

## References

* R. S. Hamilton, *Three-manifolds with positive Ricci curvature*, J. Differential Geom. 17
  (1982), 255–306 (comparison of a reaction–diffusion inequality with its ODE).
* J. W. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Chapter 4 (the maximum principle and the scalar curvature lower bound
  for normalized initial metrics).
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] {K : Set X} {T c : ℝ} {u : ℝ → X → ℝ}

/-- **Comparison with an ODE subsolution for a quadratic reaction.**

Let `K` be compact, `c ≥ 0`, and let `φ` be a subsolution `φ' ≤ c φ²` of the ODE `φ' = c φ²` on
`[0, T]`. Let `u` be continuous on the closed cylinder `[0, T] × K` and differentiable in time on
the open cylinder `(0, T) × interior K`. Suppose that `∂ₜu ≥ c u²` at every point of the open
cylinder at which `x` is a spatial local minimum of `u t` and `u t x < φ t`. If `φ ≤ u` on the
parabolic boundary, then `φ ≤ u` on all of `[0, T] × K`. -/
theorem ge_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary (hK : IsCompact K)
    (hc : 0 ≤ c) {φ : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc 0 T))
    (hφdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo 0 T → deriv φ t ≤ c * φ t ^ 2)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → IsLocalMin (u t) x → u t x < φ t →
      c * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ ⦃x⦄, x ∈ K → φ 0 ≤ u 0 x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → φ t ≤ u t x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → φ t ≤ u t x := by
  intro t ht x hx
  -- With `M = max φ`, the weight `exp (-2cMs)` absorbs the reaction term of `φ - u`.
  obtain ⟨t₀, -, hφmax⟩ := isCompact_Icc.exists_isMaxOn ⟨t, ht⟩ hφcont
  set k := 2 * c * φ t₀
  have h := le_of_deriv_nonpos_of_isLocalMax_le_parabolicBoundary
    (u := fun s y ↦ Real.exp (-(k * s)) * (φ s - u s y)) (m := 0) hK
    ((by fun_prop : ContinuousOn (fun p : ℝ × X ↦ Real.exp (-(k * p.1))) _).mul
      ((hφcont.comp continuousOn_fst mapsTo_fst_prod).sub hcont))
    (fun s hs y hy ↦ (by fun_prop : DifferentiableAt ℝ (fun r ↦ Real.exp (-(k * r))) s).mul
      ((hφdiff hs).sub (hdiff hs hy)))
    (fun s hs y hy hmax hpos ↦ by
      have hw : 0 < φ s - u s y := pos_of_mul_pos_right hpos (Real.exp_pos _).le
      have hmin : IsLocalMin (u s) y := hmax.mono fun z hz ↦ by
        linarith [le_of_mul_le_mul_left hz (Real.exp_pos _)]
      have hd : HasDerivAt (fun r ↦ Real.exp (-(k * r)) * (φ r - u r y))
          (Real.exp (-(k * s)) * -k * (φ s - u s y) +
            Real.exp (-(k * s)) * (deriv φ s - deriv (fun r ↦ u r y) s)) s := by
        convert ((((hasDerivAt_id s).const_mul k).neg).exp).mul
          ((hφdiff hs).hasDerivAt.sub (hdiff hs hy).hasDerivAt) using 1
        · ext r
          simp
        · simp
      rw [hd.deriv]
      -- Since `u < φ ≤ M`, `c (φ² - u²) = c (φ - u)(φ + u) ≤ 2cM (φ - u)`.
      have hφs : φ s ≤ φ t₀ := hφmax (Ioo_subset_Icc_self hs)
      have hsign : 0 ≤ c * ((φ s - u s y) * (2 * (φ t₀ - φ s) + (φ s - u s y))) :=
        mul_nonneg hc (mul_nonneg hw.le (by linarith))
      have hkey : deriv φ s - deriv (fun r ↦ u r y) s - k * (φ s - u s y) ≤ 0 := by
        nlinarith [hφ hs, hloc hs hy hmin (by linarith)]
      have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-(k * s))).le hkey
      linarith)
    (fun y hy ↦ mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hinit hy]))
    (fun s hs y hy ↦ mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (by linarith [hlat hs hy])) ht hx
  nlinarith [Real.exp_pos (-(k * t))]

/-- **The explicit lower bound for a quadratic reaction on a cylinder.**

Let `K` be compact, `c ≥ 0`, and let `ρ` satisfy `0 < 1 - c ρ T`, so that the barrier
`ρ / (1 - c ρ t)` has not blown up by time `T`. Let `u` be continuous on `[0, T] × K` and
differentiable in time on `(0, T) × interior K`, with `∂ₜu ≥ c u²` at every interior spatial local
minimum lying below the bound. If `u` satisfies the bound `ρ / (1 - c ρ t)` on the parabolic
boundary, in particular `ρ ≤ u` at time zero, then it satisfies it on all of `[0, T] × K`. -/
theorem div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary
    (hK : IsCompact K) (hc : 0 ≤ c) {ρ : ℝ} (hT : 0 < 1 - c * ρ * T)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → IsLocalMin (u t) x →
      u t x < ρ / (1 - c * ρ * t) → c * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ ⦃x⦄, x ∈ K → ρ ≤ u 0 x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → ρ / (1 - c * ρ * t) ≤ u t x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → ρ / (1 - c * ρ * t) ≤ u t x := by
  have hden {t : ℝ} (ht : t ∈ Icc 0 T) : 0 < 1 - c * ρ * t := by
    rcases le_total 0 (c * ρ) with h | h
    · nlinarith [mul_le_mul_of_nonneg_left ht.2 h]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg h ht.1]
  have hderiv {t : ℝ} (ht : t ∈ Icc 0 T) : HasDerivAt (fun s ↦ ρ / (1 - c * ρ * s))
      (c * (ρ / (1 - c * ρ * t)) ^ 2) t := by
    have hlin : HasDerivAt (fun s ↦ 1 - c * ρ * s) (-(c * ρ)) t := by
      simpa using ((hasDerivAt_id t).const_mul (c * ρ)).const_sub 1
    convert (hasDerivAt_const t ρ).div hlin (hden ht).ne' using 1
    field_simp
    ring
  refine ge_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary hK hc
    (fun t ht ↦ (hderiv ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv (Ioo_subset_Icc_self ht)).differentiableAt)
    (fun t ht ↦ (hderiv (Ioo_subset_Icc_self ht)).deriv.le) hcont hdiff hloc
    (fun x hx ↦ by simpa using hinit hx) hlat

/-- **The explicit lower bound for a quadratic reaction on a compact space.**

On a compact space `X` without lateral boundary, such as a closed manifold, let `c ≥ 0` and let
`ρ` satisfy `0 < 1 - c ρ T`. Let `u` be continuous on `[0, T] × X` and differentiable in time on
`(0, T) × X`, with `∂ₜu ≥ c u²` at every spatial local minimum lying below the bound. If `ρ ≤ u`
at time zero, then `ρ / (1 - c ρ t) ≤ u` at every time `t ∈ [0, T]`. -/
theorem div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin [CompactSpace X] (hc : 0 ≤ c)
    {ρ : ℝ} (hT : 0 < 1 - c * ρ * T) (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, IsLocalMin (u t) x →
      u t x < ρ / (1 - c * ρ * t) → c * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, ρ ≤ u 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, ρ / (1 - c * ρ * t) ≤ u t x := fun t ht x ↦
  div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary isCompact_univ hc hT
    hcont (fun s hs y _ ↦ hdiff hs y) (fun s hs y _ ↦ hloc hs y) (fun y _ ↦ hinit y)
    (fun s _ y hy ↦ by simp at hy) ht (mem_univ x)

end TauCeti

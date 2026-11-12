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
alone forces `u` to stay above every nonpositive subsolution `φ` of the ODE `φ' = c φ²` that lies
below `u` on the parabolic boundary. In particular a lower bound `u ≥ ρ` at time zero with
`ρ ≤ 0` propagates to the explicit bound `u(t, x) ≥ ρ / (1 - c ρ t)` for all later times.

Only spatial local minima enter the hypotheses, so the results apply to any elliptic operator
that is nonnegative at a minimum. This includes a Laplacian depending on time through a moving
metric. The main application is the scalar curvature of a Ricci flow
`∂ₜg = -2 Ric` on a closed `n`-manifold: it evolves by `∂ₜR = ΔR + 2|Ric|²`, and
`|Ric|² ≥ R² / n`. So `R` is a supersolution with `c = 2 / n`. In dimension three, a lower bound
`R ≥ -6` at time zero propagates to `R ≥ -6 / (1 + 4t)`.

The proof applies the perturbation argument of the weak parabolic maximum principle,
`TauCeti.le_of_deriv_nonpos_of_isLocalMax_le_parabolicBoundary`, to `φ - u`. At an interior
spatial maximum of `φ - u` with `u < φ ≤ 0`, the time derivative of `φ - u` is at most
`c (φ² - u²) = c (φ - u)(φ + u) ≤ 0`.

## Main results

* `TauCeti.ge_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary`: comparison with a
  nonpositive ODE subsolution on a cylinder `[0, T] × K`.
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

Let `K` be compact, `c ≥ 0`, and let `φ` be a nonpositive subsolution `φ' ≤ c φ²` of the ODE
`φ' = c φ²` on `[0, T]`. Let `u` be continuous on the closed cylinder `[0, T] × K` and
differentiable in time on the open cylinder `(0, T) × interior K`. Suppose that
`∂ₜu ≥ c u²` at every point of the open cylinder at which `x` is a spatial local minimum of `u t`
and `u t x < φ t`. If `φ ≤ u` on the parabolic boundary, then `φ ≤ u` on all of `[0, T] × K`. -/
theorem ge_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary (hK : IsCompact K)
    (hc : 0 ≤ c) {φ : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc 0 T))
    (hφdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ φ t)
    (hφnonpos : ∀ ⦃t⦄, t ∈ Ioo 0 T → φ t ≤ 0)
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
  have h := le_of_deriv_nonpos_of_isLocalMax_le_parabolicBoundary
    (u := fun s y ↦ φ s - u s y) (m := 0) hK
    ((hφcont.comp continuousOn_fst mapsTo_fst_prod).sub hcont)
    (fun s hs y hy ↦ (hφdiff hs).sub (hdiff hs hy))
    (fun s hs y hy hmax hpos ↦ by
      have hmin : IsLocalMin (u s) y := hmax.mono fun z hz ↦ by linarith
      have hlt : u s y < φ s := by linarith
      rw [deriv_fun_sub (hφdiff hs) (hdiff hs hy)]
      -- At such a point `c (φ² - u²) = c (φ - u)(φ + u) ≤ 0`, since `u < φ ≤ 0`.
      have hsign : 0 ≤ c * ((φ s - u s y) * -(φ s + u s y)) :=
        mul_nonneg hc (mul_nonneg (by linarith) (by linarith [hφnonpos hs]))
      nlinarith [hφ hs, hloc hs hy hmin hlt])
    (fun y hy ↦ by linarith [hinit hy]) (fun s hs y hy ↦ by linarith [hlat hs hy]) ht hx
  linarith

/-- **The explicit lower bound for a quadratic reaction on a cylinder.**

Let `K` be compact, `c ≥ 0` and `ρ ≤ 0`. Let `u` be continuous on `[0, T] × K` and
differentiable in time on `(0, T) × interior K`, with `∂ₜu ≥ c u²` at every interior spatial local
minimum lying below the bound. If `u` satisfies the bound `ρ / (1 - c ρ t)` on the parabolic
boundary, in particular `ρ ≤ u` at time zero, then it satisfies it on all of `[0, T] × K`. -/
theorem div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary
    (hK : IsCompact K) (hc : 0 ≤ c) {ρ : ℝ} (hρ : ρ ≤ 0)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → IsLocalMin (u t) x →
      u t x < ρ / (1 - c * ρ * t) → c * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ ⦃x⦄, x ∈ K → ρ ≤ u 0 x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → ρ / (1 - c * ρ * t) ≤ u t x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → ρ / (1 - c * ρ * t) ≤ u t x := by
  have hden {t : ℝ} (ht : 0 ≤ t) : 0 < 1 - c * ρ * t := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hρ, mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hc hρ) ht]
  have hderiv {t : ℝ} (ht : 0 ≤ t) : HasDerivAt (fun s ↦ ρ / (1 - c * ρ * s))
      (c * (ρ / (1 - c * ρ * t)) ^ 2) t := by
    have hlin : HasDerivAt (fun s ↦ 1 - c * ρ * s) (-(c * ρ)) t := by
      simpa using ((hasDerivAt_id t).const_mul (c * ρ)).const_sub 1
    convert (hasDerivAt_const t ρ).div hlin (hden ht).ne' using 1
    field_simp
    ring
  refine ge_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary hK hc
    (fun t ht ↦ (hderiv ht.1).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv ht.1.le).differentiableAt)
    (fun t ht ↦ div_nonpos_of_nonpos_of_nonneg hρ (hden ht.1.le).le)
    (fun t ht ↦ (hderiv ht.1.le).deriv.le) hcont hdiff hloc (fun x hx ↦ by simpa using hinit hx)
    hlat

/-- **The explicit lower bound for a quadratic reaction on a compact space.**

On a compact space `X` without lateral boundary, such as a closed manifold, let `c ≥ 0` and
`ρ ≤ 0`. Let `u` be continuous on `[0, T] × X` and differentiable in time on `(0, T) × X`, with
`∂ₜu ≥ c u²` at every spatial local minimum lying below the bound. If `ρ ≤ u` at time zero, then
`ρ / (1 - c ρ t) ≤ u` at every time `t ∈ [0, T]`. -/
theorem div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin [CompactSpace X] (hc : 0 ≤ c)
    {ρ : ℝ} (hρ : ρ ≤ 0) (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, IsLocalMin (u t) x →
      u t x < ρ / (1 - c * ρ * t) → c * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, ρ ≤ u 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, ρ / (1 - c * ρ * t) ≤ u t x := fun t ht x ↦
  div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin_ge_parabolicBoundary isCompact_univ hc hρ
    hcont (fun s hs y _ ↦ hdiff hs y) (fun s hs y _ ↦ hloc hs y) (fun y _ ↦ hinit y)
    (fun s _ y hy ↦ by simp at hy) ht (mem_univ x)

end TauCeti

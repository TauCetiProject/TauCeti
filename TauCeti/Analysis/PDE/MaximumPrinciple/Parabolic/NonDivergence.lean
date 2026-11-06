/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Basic

/-!
# The parabolic maximum principle on a bounded cylinder with variable coefficients

Let `K` be a compact subset of `ℝⁿ = EuclideanSpace ℝ ι` and `T` a time. On the space-time
cylinder `[0, T] × K` consider the parabolic operator in non-divergence form

`P u = ∂ₜu - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

with time-dependent coefficients `a : ℝ → ℝⁿ → Matrix ι ι ℝ`, `b : ℝ → ℝⁿ → ℝⁿ` and
`c : ℝ → ℝⁿ → ℝ`. As in `TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeSpace`, a function
`u : ℝ → ℝⁿ → ℝ` has time first, `∂ᵢ∂ⱼu` at `(t, x)` is
`fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)`, `bⁱ ∂ᵢu`
is `fderiv ℝ (u t) x (b t x)` and `∂ₜu` is `deriv (fun s ↦ u s x) t`.

The **parabolic boundary** of the cylinder is its bottom `{0} × K` together with its lateral side
`[0, T] × frontier K`. The functions considered are continuous on the closed cylinder, `C²` in
space and differentiable in time on the open cylinder `(0, T) × interior K`. Of the coefficients
only the following is asked, on the open cylinder: `a(t, x)` has nonnegative quadratic form
(degenerate ellipticity; `a` need not be symmetric), and `c` is bounded above. Nothing is asked of
the drift `b`, and no regularity or measurability of any coefficient is needed, since the argument
is pointwise.

* If `c ≤ 0` and `P u ≤ 0`, then every nonnegative bound `m` for `u` on the parabolic boundary
  bounds `u` on the whole cylinder; without a zeroth-order term every bound `m` does.
* If `c ≤ γ` with `0 ≤ γ`, `P u ≤ F` and `u ≤ M` on the parabolic boundary, where `0 ≤ M` and
  `0 ≤ F`, then `u(t, x) ≤ exp (γ t) (M + t F)`. Applied to `-u` it gives the two-sided bound
  `|u(t, x)| ≤ exp (γ t) (M + t F)` for `|P u| ≤ F` and `|u| ≤ M` on the parabolic boundary.
* The comparison principle and uniqueness for the initial-boundary value problem follow, for
  every zeroth-order coefficient that is bounded above.

The heat operator `∂ₜ - Δ - b·∇` on a compact subset of an arbitrary finite-dimensional inner
product space is treated in `TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Basic`, and the
whole-space problem, where the boundedness of `u` replaces the lateral boundary condition, in
`TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeSpace`.

## The argument

For `ε > 0` the function `u - εt` cannot attain its maximum over `[0, τ] × K` (for `τ < T`) at a
point `(t₀, x₀)` of the open cylinder where it exceeds the bound `m ≥ 0`: there `u > 0`, so
`c u ≤ 0`; `x₀` is a spatial local maximum, so the gradient vanishes and
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ 0` (`TauCeti.PDE.sum_mul_fderiv_fderiv_nonpos_of_isLocalMax`); and `t₀` is a
maximum from the left, so `∂ₜu ≥ ε`, contradicting `P u ≤ 0`. Letting `ε → 0` gives the bound
for `t < T`, and continuity carries it to the top; this part of the argument is shared with the
heat operator as `TauCeti.le_of_deriv_nonpos_of_isLocalMax_le_parabolicBoundary`. The
perturbation `εt` does not depend on the space variable, which is why neither a lower ellipticity
constant nor a bound on `b` is needed.
The general bound follows by applying this to `exp (-γ t) u - (M + t F)`, which satisfies
`P w ≤ 0` for the zeroth-order coefficient `c - γ ≤ 0`
(`TauCeti.PDE.deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_of_eq_exp_neg_mul_mul_sub`).

## Main declarations

All declarations are in the `TauCeti.PDE` namespace.

* `deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_of_eq_exp_neg_mul_mul_sub`: the exponential
  change of variables, pointwise.
* `le_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_parabolicBoundary`: the **weak
  maximum principle** for `P` when `c ≤ 0`.
* `le_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_le_parabolicBoundary`: the weak maximum
  principle for `∂ₜ - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼ - bⁱ ∂ᵢ`, with no zeroth-order term.
* `le_exp_mul_mul_add_mul_of_le_parabolicBoundary`:
  **the a priori bound** `u ≤ exp (γ t) (M + t F)`.
* `abs_le_exp_mul_mul_add_mul_of_abs_le_parabolicBoundary`:
  the two-sided a priori bound.
* `le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_parabolicBoundary`:
  **the comparison principle**.
* `eqOn_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq_of_eqOn_parabolicBoundary`:
  uniqueness for the initial-boundary value problem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 7.1.4, Theorems 8 and 9.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 1.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Matrix Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The exponential change of variables.** If `P u ≤ F` at `(t, x)` with `c ≤ γ` there, then
`w = exp (-γ t) u - (M + t F)` satisfies `P w ≤ 0` at `(t, x)` for the zeroth-order coefficient
`c - γ`, provided `0 ≤ γ t`, `0 ≤ M + t F` and `0 ≤ F`. Here `A` and `v` are the values of the
principal and drift coefficients at `(t, x)`. -/
theorem deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_of_eq_exp_neg_mul_mul_sub
    {A : Matrix ι ι ℝ} {u w : ℝ → EuclideanSpace ℝ ι → ℝ} {c γ M F t : ℝ} {x v : EuclideanSpace ℝ ι}
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

variable {K : Set (EuclideanSpace ℝ ι)} {T : ℝ} {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}
  {u v : ℝ → EuclideanSpace ℝ ι → ℝ}

/-- The weak maximum principle for `P` under the pointwise sign condition `c u ≤ 0` wherever
`u > m`, from which both public forms follow. -/
private theorem le_of_deriv_le_of_mul_nonpos (hK : IsCompact K)
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      0 ≤ (a t x).toQuadraticForm' ξ) {m : ℝ}
    (hcu : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → m < u t x → c t x * u t x ≤ 0)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ m :=
  -- At a spatial local maximum above `m` the principal part is `≤ 0`, the gradient vanishes and
  -- `c u ≤ 0`, so `∂ₜu ≤ 0`.
  le_of_deriv_nonpos_of_isLocalMax_le_parabolicBoundary hK hcont hdiff
    (fun t ht x hx hloc hlt ↦ by
      have hgrad : fderiv ℝ (u t) x (b t x) = 0 := by
        rw [hloc.fderiv_eq_zero, _root_.zero_apply]
      linarith [hsub ht hx, sum_mul_fderiv_fderiv_nonpos_of_isLocalMax (ha ht hx) (hcd ht hx) hloc,
        hcu ht hx hlt])
    hinit hlat

/-- **The weak maximum principle for parabolic equations in non-divergence form.**

Let `K` be compact, and on the open cylinder `(0, T) × interior K` let `a(t, x)` have nonnegative
quadratic form and `c ≤ 0`. Suppose `u` is continuous on the closed cylinder `[0, T] × K`, is `C²`
in space and differentiable in time on the open cylinder, and is a subsolution there:
`∂ₜu ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u`. If `u ≤ m` on the parabolic boundary, that is on the bottom
`{0} × K` and on the lateral side `[0, T] × frontier K`, and `0 ≤ m`, then `u ≤ m` on all of
`[0, T] × K`. No bound on the drift `b` and no lower ellipticity constant are needed. -/
theorem le_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_parabolicBoundary
    (hK : IsCompact K)
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      0 ≤ (a t x).toQuadraticForm' ξ)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → c t x ≤ 0) {m : ℝ} (hm : 0 ≤ m)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ m :=
  le_of_deriv_le_of_mul_nonpos hK ha
    (fun _ ht _ hx hlt ↦ mul_nonpos_of_nonpos_of_nonneg (hc ht hx) (hm.trans hlt.le))
    hcont hcd hdiff hsub hinit hlat

/-- **The weak maximum principle without a zeroth-order term.** Under the hypotheses of
`le_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_parabolicBoundary` with `c = 0`, a
subsolution `∂ₜu ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu` is bounded on `[0, T] × K` by every bound `m` it
satisfies on the parabolic boundary, with no sign condition on `m`. -/
theorem le_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_le_parabolicBoundary (hK : IsCompact K)
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      0 ≤ (a t x).toQuadraticForm' ξ) {m : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ m :=
  le_of_deriv_le_of_mul_nonpos (c := 0) hK ha (fun _ _ _ _ _ ↦ by simp) hcont hcd hdiff
    (fun _ ht _ hx ↦ by simpa using hsub ht hx) hinit hlat

/-- **The a priori bound for parabolic equations on a bounded cylinder.** Let
`P u = ∂ₜu - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` where, on the open cylinder `(0, T) × interior K` over
a compact `K`, the matrix `a(t, x)` has nonnegative quadratic form and `c(t, x) ≤ γ` with
`0 ≤ γ`. Let `u` be continuous on `[0, T] × K`, `C²` in space and differentiable in time on the
open cylinder, with `P u ≤ F` there, and let `u ≤ M` on the parabolic boundary
`({0} × K) ∪ ([0, T] × frontier K)`, where `0 ≤ M` and `0 ≤ F`. Then
`u(t, x) ≤ exp (γ t) (M + t F)` on `[0, T] × K`. -/
theorem le_exp_mul_mul_add_mul_of_le_parabolicBoundary
    (hK : IsCompact K)
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      0 ≤ (a t x).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → c t x ≤ γ) (hγ : 0 ≤ γ)
    {M F : ℝ} (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → deriv (fun s ↦ u s x) t ≤
      ∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x + F)
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ M)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ M) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ Real.exp (γ * t) * (M + t * F) := by
  -- Apply the maximum principle to `w = exp (-γ t) u - (M + t F)` and the coefficient `c - γ`.
  set w : ℝ → EuclideanSpace ℝ ι → ℝ :=
    fun t ↦ (fun _ ↦ -(M + t * F)) + Real.exp (-(γ * t)) • u t
  have hw : ∀ t x, w t x = Real.exp (-(γ * t)) * u t x - (M + t * F) := fun t x ↦ by
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hwcont : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ K) := by
    refine ContinuousOn.congr ?_ fun p _ ↦ hw p.1 p.2
    exact (((by fun_prop : Continuous fun p : ℝ × EuclideanSpace ℝ ι ↦
      Real.exp (-(γ * p.1))).continuousOn.mul hcont).sub
      (by fun_prop : Continuous fun p : ℝ × EuclideanSpace ℝ ι ↦ M + p.1 * F).continuousOn)
  have hwle := le_of_deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_parabolicBoundary
    (u := w) (b := b) (c := fun t x ↦ c t x - γ) hK ha
    (fun t ht x hx ↦ sub_nonpos.mpr (hc ht hx)) le_rfl hwcont
    (fun t ht x hx ↦ contDiffAt_const.add ((hcd ht hx).const_smul (Real.exp (-(γ * t)))))
    (fun t ht x hx ↦ by
      simp only [hw]
      fun_prop (disch := exact hdiff ht hx))
    (fun t ht x hx ↦ deriv_le_sum_mul_fderiv_fderiv_add_fderiv_add_mul_of_eq_exp_neg_mul_mul_sub hw
      (hc ht hx) (mul_nonneg hγ ht.1.le) (add_nonneg hM (mul_nonneg ht.1.le hF)) hF (hcd ht hx)
      (hdiff ht hx) (hsub ht hx))
    (fun x hx ↦ by simpa [hw] using hinit hx)
    (fun t ht x hx ↦ by
      have h1 : Real.exp (-(γ * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      rw [hw]
      nlinarith [mul_le_mul_of_nonneg_left (hlat ht hx) (Real.exp_pos (-(γ * t))).le,
        mul_le_mul_of_nonneg_right h1 hM, mul_nonneg ht.1 hF])
  intro t ht x hx
  have h := hwle ht hx
  rwa [hw, sub_nonpos, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at h

/-- **The two-sided a priori bound on a bounded cylinder.** Under the hypotheses on `a` and `c`
of `le_exp_mul_mul_add_mul_of_le_parabolicBoundary`,
a function `u` that is continuous on `[0, T] × K`, `C²` in space and differentiable in time on the
open cylinder, with `|P u| ≤ F` there and `|u| ≤ M` on the parabolic boundary, satisfies
`|u(t, x)| ≤ exp (γ t) (M + t F)` on `[0, T] × K`. -/
theorem abs_le_exp_mul_mul_add_mul_of_abs_le_parabolicBoundary
    (hK : IsCompact K)
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      0 ≤ (a t x).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → c t x ≤ γ) (hγ : 0 ≤ γ)
    {M F : ℝ} (hF : 0 ≤ F)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → |deriv (fun s ↦ u s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)| ≤ F)
    (hinit : ∀ ⦃x⦄, x ∈ K → |u 0 x| ≤ M)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → |u t x| ≤ M) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → |u t x| ≤ Real.exp (γ * t) * (M + t * F) := by
  intro t ht x hx
  -- `M` is nonnegative, as a bound for an absolute value at a point of `K`.
  have hM : 0 ≤ M := (abs_nonneg _).trans (hinit hx)
  have hle :=
    le_exp_mul_mul_add_mul_of_le_parabolicBoundary
      hK ha hc hγ hM hF hcont hcd hdiff
      (fun s hs y hy ↦ by linarith [(abs_le.mp (hP hs hy)).2])
      (fun y hy ↦ (abs_le.mp (hinit hy)).2) (fun s hs y hy ↦ (abs_le.mp (hlat hs hy)).2) ht hx
  -- The lower bound is the upper bound for `-u`.
  have hge :=
    le_exp_mul_mul_add_mul_of_le_parabolicBoundary
      (u := -u) hK ha hc hγ hM hF
      (hcont.neg.congr fun _ _ ↦ by simp [Function.uncurry_def])
      (fun s hs y hy ↦ (hcd hs hy).neg) (fun s hs y hy ↦ (hdiff hs hy).neg)
      (fun s hs y hy ↦ by
        simp only [Pi.neg_apply, deriv.fun_neg]
        rw [sum_mul_fderiv_fderiv_add_fderiv_neg]
        linarith [(abs_le.mp (hP hs hy)).1])
      (fun y hy ↦ by
        simp only [Pi.neg_apply]
        linarith [(abs_le.mp (hinit hy)).1])
      (fun s hs y hy ↦ by
        simp only [Pi.neg_apply]
        linarith [(abs_le.mp (hlat hs hy)).1]) ht hx
  simp only [Pi.neg_apply] at hge
  exact abs_le.mpr ⟨by linarith, hle⟩

/-- **The comparison principle for parabolic equations on a bounded cylinder.** Let `a(t, x)` have
nonnegative quadratic form and let `c` be bounded above on the open cylinder
`(0, T) × interior K` over a compact `K`. Let `u` and `v` be continuous on `[0, T] × K`, `C²` in
space and differentiable in time on the open cylinder. If `P u ≤ P v` there and `u ≤ v` on the
parabolic boundary `({0} × K) ∪ ([0, T] × frontier K)`, then `u ≤ v` on `[0, T] × K`. No sign
condition on `c` is needed. -/
theorem le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_parabolicBoundary
    (hK : IsCompact K)
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      0 ≤ (a t x).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → c t x ≤ γ)
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ K))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → deriv (fun s ↦ u s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x) ≤
      deriv (fun s ↦ v s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (v t) x (b t x) + c t x * v t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u 0 x ≤ v 0 x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ ⦃x⦄, x ∈ K → u t x ≤ v t x := by
  -- Apply the a priori bound to `w = u - v` with `M = F = 0`.
  set w : ℝ → EuclideanSpace ℝ ι → ℝ := fun t ↦ u t + (-1 : ℝ) • v t
  have hw : ∀ t x, w t x = u t x - v t x := fun t x ↦ by
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h :=
    le_exp_mul_mul_add_mul_of_le_parabolicBoundary
      (u := w) (γ := max γ 0) (M := 0) (F := 0) hK ha
      (fun t ht x hx ↦ (hc ht hx).trans (le_max_left _ _)) (le_max_right _ _) le_rfl le_rfl
      ((hucont.sub hvcont).congr fun p _ ↦ hw p.1 p.2)
      (fun t ht x hx ↦ (hucd ht hx).add ((hvcd ht hx).const_smul (-1 : ℝ)))
      (fun t ht x hx ↦ by
        simp only [hw]
        exact (hudiff ht hx).sub (hvdiff ht hx))
      (fun t ht x hx ↦ by
        rw [sum_mul_fderiv_fderiv_add_fderiv_add_smul (hucd ht hx) (hvcd ht hx)]
        simp only [hw]
        rw [deriv_fun_sub (hudiff ht hx) (hvdiff ht hx)]
        linarith [hP ht hx])
      (fun x hx ↦ by simpa [hw] using hinit hx)
      (fun t ht x hx ↦ by simpa [hw] using hlat ht hx)
  intro t ht x hx
  have := h ht hx
  rw [hw, mul_zero, add_zero, mul_zero] at this
  linarith

/-- **Uniqueness for the initial-boundary value problem on a bounded cylinder.** With `a` and `c`
as in `le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_parabolicBoundary`, two
functions that are continuous on `[0, T] × K`, `C²` in space and differentiable in time on the
open cylinder, with `P u = P v` there and `u = v` on the parabolic boundary, agree on
`[0, T] × K`. -/
theorem eqOn_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq_of_eqOn_parabolicBoundary
    (hK : IsCompact K)
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      0 ≤ (a t x).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → c t x ≤ γ)
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ K))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ ⦃x⦄, x ∈ interior K → deriv (fun s ↦ u s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x) =
      deriv (fun s ↦ v s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (v t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (v t) x (b t x) + c t x * v t x))
    (hinit : EqOn (u 0) (v 0) K)
    (hlat : ∀ ⦃t⦄, t ∈ Icc 0 T → EqOn (u t) (v t) (frontier K)) :
    EqOn (Function.uncurry u) (Function.uncurry v) (Icc 0 T ×ˢ K) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  exact le_antisymm
    (le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_parabolicBoundary hK ha hc
      hucont hvcont hucd hvcd hudiff hvdiff (fun s hs y hy ↦ (hP hs hy).le)
      (fun y hy ↦ (hinit hy).le) (fun s hs y hy ↦ (hlat hs hy).le) ht hx)
    (le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_parabolicBoundary hK ha hc
      hvcont hucont hvcd hucd hvdiff hudiff (fun s hs y hy ↦ (hP hs hy).ge)
      (fun y hy ↦ (hinit hy).ge) (fun s hs y hy ↦ (hlat hs hy).ge) ht hx)

end PDE

end TauCeti

end

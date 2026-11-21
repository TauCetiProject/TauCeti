/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.Manifold

/-!
# Normalizing the Hamiltonians of a continuation cylinder

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time:
`H(t, x)` and `H(t, x) + c(t)` generate the same flow and have the same one-periodic orbits, while
the action of a loop measured against a map drops by the time average `∫₀¹ c`
(`TauCeti.cylinderAction_add_const`). This file shows how the energy identity of a continuation
cylinder absorbs a change of normalization of its two end Hamiltonians.

A continuation cylinder from `H₀` to `H₁` solves the Floer equation for the perturbation
`K = H_{(s, t)} dt` given by the linear homotopy `H_{(s, t)} = H₀(t) + β(s) (H₁(t) - H₀(t))`
(`TauCeti.Floer.linearHomotopy`), whose curvature is the `s`-derivative `∂_s H`. For a manifold
target the energy identity reads

`E(u) = A_{H(a, ·)}(γ_a, w # v) - A_{H(b, ·)}(γ_b, v) - ∫∫ ∂_s H(s, t, u(s, t))`

over `[a, b] × [0, 1]`
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub_sub_integral`).
The linear homotopy is additive in its two end Hamiltonians, so normalizing them by `c₀` and `c₁`
adds the linear homotopy of `c₀` and `c₁`, which does not depend on the target point
(`TauCeti.Floer.linearHomotopy_add_const`). Consequently:

* the Hamiltonian vector fields `X_{H_{(s, t)}}`, hence the Floer equation, are unchanged
  (`TauCeti.SmoothTwoForm.hamiltonianVectorField_linearHomotopy_add_const`);
* the curvature `∂_s H` changes by `β'(s) (c₁ - c₀)(t)`
  (`TauCeti.Floer.fderiv_linearHomotopy_add_const_stdComplexLineReal`), so its integral over
  `[a, b] × [0, 1]` changes by `(β(b) - β(a)) ∫₀¹ (c₁ - c₀)`
  (`TauCeti.Floer.setIntegral_fderiv_linearHomotopy_add_const_stdComplexLineReal`).

At the ends the Hamiltonians `H(a, ·)` and `H(b, ·)` are normalized by `c₀ + β(a) (c₁ - c₀)` and
`c₀ + β(b) (c₁ - c₀)`, so the difference of the two actions changes by the same amount
`(β(b) - β(a)) ∫₀¹ (c₁ - c₀)`. The two changes cancel in the energy identity, as they must, since
the energy itself is unchanged.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public section

open Set Function MeasureTheory
open scoped Manifold

namespace TauCeti

namespace Floer

variable {V : Type*} {H₀ H₁ : ℝ → V → ℝ} {c₀ c₁ : ℝ → ℝ}

/-- **Normalizing the end Hamiltonians of a linear homotopy.** Adding functions `c₀` and `c₁` of
time to the end Hamiltonians adds the linear homotopy of the target-independent Hamiltonians `c₀`
and `c₁`. -/
theorem linearHomotopy_add_const (β : ℝ → ℝ) (H₀ H₁ : ℝ → V → ℝ) (c₀ c₁ : ℝ → ℝ) (z : ℝ × ℝ)
    (x : V) :
    linearHomotopy β (fun t y ↦ H₀ t y + c₀ t) (fun t y ↦ H₁ t y + c₁ t) z x =
      linearHomotopy β H₀ H₁ z x +
        linearHomotopy β (fun t (_ : V) ↦ c₀ t) (fun t _ ↦ c₁ t) z x := by
  simp only [linearHomotopy_def]
  ring

/-- **The curvature of a normalized linear homotopy.** The `s`-derivative of the linear homotopy
with normalized end Hamiltonians `H₀ + c₀` and `H₁ + c₁` is the `s`-derivative for `H₀` and `H₁`
plus `β'(s) (c₁ - c₀)(t)`. -/
theorem fderiv_linearHomotopy_add_const_stdComplexLineReal {β : ℝ → ℝ} {z : ℝ × ℝ} {x : V}
    (hH₀ : DifferentiableAt ℝ (fun t ↦ H₀ t x) z.2)
    (hH₁ : DifferentiableAt ℝ (fun t ↦ H₁ t x) z.2) (hc₀ : DifferentiableAt ℝ c₀ z.2)
    (hc₁ : DifferentiableAt ℝ c₁ z.2) :
    fderiv ℝ (fun w ↦ linearHomotopy β (fun t y ↦ H₀ t y + c₀ t) (fun t y ↦ H₁ t y + c₁ t) w x) z
        stdComplexLineReal =
      fderiv ℝ (fun w ↦ linearHomotopy β H₀ H₁ w x) z stdComplexLineReal +
        deriv β z.1 * (c₁ z.2 - c₀ z.2) := by
  rw [fderiv_linearHomotopy_stdComplexLineReal (H₀ := fun t y ↦ H₀ t y + c₀ t)
      (H₁ := fun t y ↦ H₁ t y + c₁ t) (hH₀.add hc₀) (hH₁.add hc₁),
    fderiv_linearHomotopy_stdComplexLineReal hH₀ hH₁]
  ring

/-- **The integrated curvature of a normalized linear homotopy.** Let `β` be a `C¹` profile, let
the end Hamiltonians `H₀`, `H₁` be differentiable in time, and let `c₀`, `c₁` be differentiable
functions of time. Along a map `u` for which the `s`-derivative of the linear homotopy of `H₀` and
`H₁` is integrable over `[a, b] × [0, 1]`, `a ≤ b`, the integral of the `s`-derivative of the
linear homotopy of `H₀ + c₀` and `H₁ + c₁` is the integral for `H₀` and `H₁` plus
`(β(b) - β(a)) ∫₀¹ (c₁ - c₀)`. -/
theorem setIntegral_fderiv_linearHomotopy_add_const_stdComplexLineReal {β : ℝ → ℝ}
    (hβ : ContDiff ℝ 1 β) (hH₀ : ∀ x, Differentiable ℝ fun t ↦ H₀ t x)
    (hH₁ : ∀ x, Differentiable ℝ fun t ↦ H₁ t x) (hc₀ : Differentiable ℝ c₀)
    (hc₁ : Differentiable ℝ c₁) {u : ℝ × ℝ → V} {a b : ℝ} (hab : a ≤ b)
    (hu : IntegrableOn (fun z ↦ fderiv ℝ (fun w ↦ linearHomotopy β H₀ H₁ w (u z)) z
      stdComplexLineReal) (Icc a b ×ˢ Icc 0 1)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ linearHomotopy β (fun t y ↦ H₀ t y + c₀ t)
        (fun t y ↦ H₁ t y + c₁ t) w (u z)) z stdComplexLineReal =
      (∫ z in Icc a b ×ˢ Icc 0 1,
        fderiv ℝ (fun w ↦ linearHomotopy β H₀ H₁ w (u z)) z stdComplexLineReal) +
        (β b - β a) * ∫ t in (0 : ℝ)..1, (c₁ t - c₀ t) := by
  have hdβ : Continuous (deriv β) := hβ.continuous_deriv le_rfl
  have hk : IntegrableOn (fun z : ℝ × ℝ ↦ deriv β z.1 * (c₁ z.2 - c₀ z.2)) (Icc a b ×ˢ Icc 0 1) :=
    ((hdβ.comp continuous_fst).mul ((hc₁.continuous.sub hc₀.continuous).comp
      continuous_snd)).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦
      fderiv_linearHomotopy_add_const_stdComplexLineReal (hH₀ (u z) z.2) (hH₁ (u z) z.2)
        (hc₀ z.2) (hc₁ z.2),
    integral_add hu hk]
  congr 1
  -- The correction is a product of a function of `s` and a function of `t`.
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (deriv β) fun t ↦ c₁ t - c₀ t,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hβ.differentiable one_ne_zero x)
      (hdβ.intervalIntegrable a b),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

end Floer

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M]

/-- **Normalizing the end Hamiltonians does not change the Floer equation of a continuation
cylinder.** At every point of the domain, the Hamiltonian vector field of the linear homotopy of
the normalized end Hamiltonians `H₀ + c₀` and `H₁ + c₁` is that of the linear homotopy of `H₀` and
`H₁`. -/
@[simp]
theorem hamiltonianVectorField_linearHomotopy_add_const (ω : SmoothTwoForm I M) (β : ℝ → ℝ)
    (H₀ H₁ : ℝ → M → ℝ) (c₀ c₁ : ℝ → ℝ) (z : ℝ × ℝ) :
    ω.hamiltonianVectorField
        (linearHomotopy β (fun t y ↦ H₀ t y + c₀ t) (fun t y ↦ H₁ t y + c₁ t) z) =
      ω.hamiltonianVectorField (linearHomotopy β H₀ H₁ z) := by
  have h : linearHomotopy β (fun t y ↦ H₀ t y + c₀ t) (fun t y ↦ H₁ t y + c₁ t) z =
      fun x ↦ linearHomotopy β H₀ H₁ z x + (c₀ z.2 + β z.1 * (c₁ z.2 - c₀ z.2)) := by
    funext x
    simp only [linearHomotopy_def]
    ring
  rw [h, hamiltonianVectorField_add_const]

end SmoothTwoForm

end TauCeti

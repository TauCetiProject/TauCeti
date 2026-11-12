/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Holomorphy and the conjugate Wirtinger derivative

For a real-differentiable map between complex normed spaces, vanishing of the conjugate
Wirtinger derivative characterizes complex differentiability. The real-differentiability
hypothesis is essential because the totalized real derivative vanishes at nondifferentiable
points. In one variable the real differential has coefficients `wirtingerDeriv f x 1` and
`conjWirtingerDeriv f x 1` in the basis `dz`, `dbar z`; testing the latter coefficient alone
detects its vanishing.

On the coordinate space `ι → ℂ` the conjugate Wirtinger derivative is conjugate-linear, so it
vanishes as soon as it vanishes on the coordinate vectors: a real-differentiable map is holomorphic
exactly when all its partial derivatives `∂g/∂(conj z_j)` vanish
(`TauCeti.differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero`). Composing with a
holomorphic map `φ` multiplies the conjugate Wirtinger derivative by the complex derivative of `φ`
(`TauCeti.conjWirtingerDeriv_comp`).

These statements connect the real differential and its type decomposition with holomorphy.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter II.
-/

public noncomputable section

open Complex
open scoped ComplexConjugate

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A real-differentiable map between complex normed spaces is complex differentiable
exactly when its conjugate Wirtinger derivative vanishes. -/
theorem differentiableAt_iff_conjWirtingerDeriv_eq_zero {g : V → W} {x : V}
    (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℂ g x ↔ conjWirtingerDeriv g x = 0 := by
  constructor
  · exact fun h ↦ h.conjWirtingerDeriv_eq_zero
  · intro h
    apply (differentiableAt_iff_restrictScalars ℝ hg).mpr
    refine ⟨wirtingerDeriv g x, ?_⟩
    ext v
    simpa only [ContinuousLinearMap.coe_restrictScalars', h, zero_apply, add_zero] using
      wirtingerDeriv_add_conjWirtingerDeriv g x v

/-- For a real-differentiable function of one complex variable, the single equation
`conjWirtingerDeriv f x 1 = 0` characterizes complex differentiability. -/
theorem differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero {f : ℂ → W} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℂ f x ↔ conjWirtingerDeriv f x 1 = 0 := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hf,
    conjWirtingerDeriv_eq_zero_iff_apply_one_eq_zero]

/-- On `ι → ℂ`, a real-differentiable map is complex differentiable exactly when its conjugate
Wirtinger derivatives `∂g/∂(conj z_j)` in the coordinate directions all vanish. -/
theorem differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] {g : (ι → ℂ) → W} {x : ι → ℂ} (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℂ g x ↔ ∀ j, conjWirtingerDeriv g x (Pi.single j 1) = 0 := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hg]
  refine ⟨fun h j ↦ by simp [h], fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    simp [← Pi.single_smul]
  rw [hv, map_sum]
  simp [h]

/-- **The chain rule for the conjugate Wirtinger derivative** after a holomorphic map: if `φ` is
complex differentiable at `g x`, then `\bar∂(φ ∘ g) = Dφ(g x) ∘ \bar∂g`. -/
theorem conjWirtingerDeriv_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {φ : W → X} {g : V → W} {x : V} (hφ : DifferentiableAt ℂ φ (g x))
    (hg : DifferentiableAt ℝ g x) :
    conjWirtingerDeriv (φ ∘ g) x = (fderiv ℂ φ (g x)).comp (conjWirtingerDeriv g x) := by
  rw [conjWirtingerDeriv_eq_complexAntilinearPart, conjWirtingerDeriv_eq_complexAntilinearPart,
    fderiv_comp x (hφ.restrictScalars ℝ) hg, hφ.fderiv_restrictScalars ℝ,
    ContinuousLinearMap.complexAntilinearPart_restrictScalars_comp]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
import TauCeti.Geometry.Symplectic.Complex.AntilinearPart

/-!
# The gradient of `|α|²` against the `∂bar`-part of `∇_a α`

For a section `α` of a trivial Hermitian line with connection form `a = i b`, the differential of
`|α|²` is `2 Re (conj α ∇_a α)`, so `|∇ |α|²| ≤ 2 |α| |∇_a α|`
(`TauCeti.SeibergWitten.norm_fderiv_norm_sq_le_mul_norm_covariantDeriv`). When `∇_a α` is
complex-linear for an orthogonal complex structure `J`, the identity
`|∇ |α|²|² = 2 |α|² |∇_a α|²` holds instead, with Hilbert–Schmidt norms. This file proves a lower
bound on `|∇ |α|²|²` that keeps the factor `2` and pays for it with the `J`-antilinear part
`∂bar_a α` (`TauCeti.SeibergWitten.covariantDBar`): for every `ε > 0`,

`2 |α|² ((1 - ε) |∇_a α|² - (2 + 18 / ε) |∂bar_a α|²) ≤ |∇ |α|²|²`

(`TauCeti.SeibergWitten.two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq`). This is the pointwise
linear algebra `TauCeti.AlmostComplexStructure.two_mul_norm_sq_mul_sub_le_sum_sq_re` for
`L = ∇_a α` and `a = α` at one point, since `∂bar_a α` is the complex-antilinear part of `∇_a α`
(`TauCeti.SeibergWitten.coe_covariantDBar_eq_complexAntilinearPart`).

The factor `2` is what cancels the gradient term of `Δ log |α|²`, so that `-log |α|²` satisfies a
screened inequality where `|α|` is bounded below; see
`TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.VacuumDecay`.

## Main results

* `TauCeti.SeibergWitten.two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq`: the gradient of
  `|α|²` against `∂bar_a α`.
-/

public section

open Complex InnerProductSpace
open scoped ComplexConjugate RealInnerProductSpace Gradient

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The gradient of `|α|²` against `∂bar_a α`.** For a section `α` of the trivial line,
differentiable at `x`, a connection form `b`, an orthogonal complex structure `J` and an
orthonormal basis `e`, write `|∇_a α|² = ∑ᵢ |∇_a α (eᵢ)|²` and `|∂bar_a α|² = ∑ᵢ |∂bar_a α (eᵢ)|²`
at `x`. Then for every `ε > 0`

`2 |α|² ((1 - ε) |∇_a α|² - (2 + 18 / ε) |∂bar_a α|²) ≤ |∇ |α|²|²`.

The factor `2` in front of `|α|² |∇_a α|²` is what cancels the gradient term of
`Δ log |α|²`. -/
theorem two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq {ι : Type*} [Fintype ι]
    (J : AlmostComplexStructure E) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (e : OrthonormalBasis ι ℝ E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) {α : E → ℂ} {x : E}
    (hα : DifferentiableAt ℝ α x) {ε : ℝ} (hε : 0 < ε) :
    2 * ‖α x‖ ^ 2 * ((1 - ε) * ∑ i, ‖covariantDeriv b α x (e i)‖ ^ 2 -
        (2 + 18 / ε) * ∑ i, ‖covariantDBar J b α x (e i)‖ ^ 2) ≤
      ‖∇ (fun y ↦ ‖α y‖ ^ 2) x‖ ^ 2 := by
  have h := J.two_mul_norm_sq_mul_sub_le_sum_sq_re hJ e (covariantDeriv b α x) (α x) hε
  rw [← coe_covariantDBar_eq_complexAntilinearPart] at h
  rw [← e.sum_sq_inner_left]
  simpa only [inner_gradient_left,
    fderiv_norm_sq_apply_eq_re_conj_mul_covariantDeriv (b := b) hα] using h

end TauCeti.SeibergWitten

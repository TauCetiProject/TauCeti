/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.QuadraticTwoForm

/-!
# The curvature term of the product Dirac square at a Seiberg–Witten point

On a product `X = S¹ × Y` with unit vector field `T = ∂ₛ` and product metric, the Dirac operator
of a `Spinᶜ` connection with determinant connection `A` splits as `D = c(ds) ∇_T + B_A`, where
`B_A` differentiates only along `Y`. Since `c(ds)` anticommutes with the Clifford multiplication
by covectors of `Y`, the cross terms of `D²` reduce to a commutator of covariant derivatives, and

`D² = -∇_T² + B_A² + (1 / 2) c₂(ds ∧ ι_T F_A)`.

For a solution of the unperturbed Seiberg–Witten equations `D ψ = 0`, `F_A⁺ = q(ψ)`, pairing
`D² ψ` with `ψ` and integrating gives
`0 = ‖∇_T ψ‖² + ‖B_A ψ‖² + ‖ι_T F_A‖² + 2π² ⟨c₁(L)², [X]⟩`. This file proves the pointwise
algebra behind the last two terms: at a point where the curvature equation holds, the curvature
term of `D²` pairs with `ψ` to `|ι_T F_A|² + (i F_A ∧ i F_A) / 2`.

As elsewhere, the imaginary curvature `F_A = i F` is indexed by a real two-form `F`, and the
curvature equation `F_A⁺ = q(ψ)` reads `F + ⋆F = 2 q(ψ)`. For a unit vector `s` (the covector
`ds`, through the metric) put `a = s ⌟ F`, so that `ι_T F_A = i a`. Then
`(1 / 2) c₂(ds ∧ ι_T F_A) = (1 / 2) C(i (s ∧ a)) = (i / 2) c(s) c(a)` on `W⁺`, and

`Re⟪ψ, (i / 2) c(s) c(a) ψ⟫ = ‖a‖² + vol (F ∧ F) / 2`.

The proof pairs `s ∧ a` with `F + ⋆F` in two ways: through the adjunction
`⟪q(ψ), ω⟫ = Re⟪ψ, C(iω) ψ⟫ / 4` (`TauCeti.SeibergWitten.inner_quadraticTwoForm_eq_re_inner`),
and through the energy identity of a two-form split along a unit vector,
`⟪s ∧ a, F + ⋆F⟫ = ‖a‖² + vol (F ∧ F) / 2`
(`Orientation.inner_ιMulti_twoVectorContraction_add_hodgeStar`).

## Main results

* `TauCeti.SeibergWitten.re_inner_cliffordRestriction_ιMulti_twoVectorContraction`: if
  `F + ⋆F = 2 q(ψ)` and `‖s‖ = 1`, then
  `Re⟪ψ, C(i (s ∧ s ⌟ F)) ψ⟫ = 2 ‖s ⌟ F‖² + vol (F ∧ F)`.
* `TauCeti.SeibergWitten.re_inner_I_div_two_smul_ι_mul_ι_twoVectorContraction`: the same identity
  for the operator `(i / 2) c(s) c(s ⌟ F)`, the curvature term of `D²`, in the form
  `Re⟪ψ, (i / 2) c(s) c(s ⌟ F) ψ⟫ = ‖s ⌟ F‖² + vol (F ∧ F) / 2`.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance finiteDimensional_of_fact_finrank_eq_four : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

include hQ

/-- **The curvature term at a Seiberg–Witten point.** Let `s` be a unit vector and let the real
two-form `F` satisfy the curvature equation `F + ⋆F = 2 q(ψ)`. Then the Clifford map of
`s ∧ (s ⌟ F)` pairs with `ψ` to `Re⟪ψ, C(i (s ∧ s ⌟ F)) ψ⟫ = 2 ‖s ⌟ F‖² + vol (F ∧ F)`. -/
theorem re_inner_cliffordRestriction_ιMulti_twoVectorContraction {s : V} (hs : ‖s‖ = 1)
    {F : ⋀[ℝ]^2 V} {ψ : positiveHalfSpinors o ρ}
    (hF : F + o.hodgeStar hkl F = (2 : ℝ) • (quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V)) :
    (⟪ψ, cliffordRestriction o ρ (ιMulti ℝ 2 ![s, twoVectorContraction F s]) ψ⟫_ℂ).re =
      2 * ‖twoVectorContraction F s‖ ^ 2 + wedgePairing o.volumeEquiv hkl F F := by
  have hq := inner_quadraticTwoForm_eq_re_inner o ρ hQ hkl
    (ιMulti ℝ 2 ![s, twoVectorContraction F s]) ψ
  have hE := o.inner_ιMulti_twoVectorContraction_add_hodgeStar hkl hs F
  rw [hF, real_inner_smul_right, real_inner_comm] at hE
  linarith

/-- **The curvature term of the product Dirac square at a Seiberg–Witten point.** Let `s` be a
unit vector and let the real two-form `F` satisfy the curvature equation `F + ⋆F = 2 q(ψ)`. Then
the operator `(i / 2) c(s) c(s ⌟ F)`, the term `(1 / 2) c₂(ds ∧ ι_T F_A)` of the square of the
product Dirac operator, pairs with `ψ` to
`Re⟪ψ, (i / 2) c(s) c(s ⌟ F) ψ⟫ = ‖s ⌟ F‖² + vol (F ∧ F) / 2`. -/
theorem re_inner_I_div_two_smul_ι_mul_ι_twoVectorContraction {s : V} (hs : ‖s‖ = 1)
    {F : ⋀[ℝ]^2 V} {ψ : positiveHalfSpinors o ρ}
    (hF : F + o.hodgeStar hkl F = (2 : ℝ) • (quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V)) :
    (⟪(ψ : W), (Complex.I / 2) • ρ (ι Q s * ι Q (twoVectorContraction F s)) ψ⟫_ℂ).re =
      ‖twoVectorContraction F s‖ ^ 2 + wedgePairing o.volumeEquiv hkl F F / 2 := by
  have h := re_inner_cliffordRestriction_ιMulti_twoVectorContraction o ρ hQ hkl hs hF
  have hsa : ⟪s, twoVectorContraction F s⟫ = 0 := by
    rw [real_inner_comm]
    exact inner_twoVectorContraction_apply_self F s
  rw [Submodule.coe_inner, coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ hsa]
    at h
  rw [div_eq_inv_mul, ← smul_smul, inner_smul_right,
    show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, h]
  ring

end TauCeti.SeibergWitten

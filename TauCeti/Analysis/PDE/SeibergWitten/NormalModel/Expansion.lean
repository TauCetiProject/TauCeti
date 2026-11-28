/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Flat.Weitzenbock
public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic

/-!
# The exact quadratic expansion of the flat limiting Seiberg–Witten equations

After rescaling by `h = (2r)^(-1/2)`, Taubes's large-parameter Seiberg–Witten equations near a
pseudoholomorphic curve become, to leading order, the **flat limiting equations** on an oriented
Euclidean four-space `V`, for a real connection form `b` (the imaginary connection `a = i b` on the
trivial line) and a positive half-spinor field `ψ`:

`D_b ψ = 0`,  `F + ⋆F + q(ψ) / 2 = ω / 8`,  `F = -db`,

where `D_b = ∑ₖ c(eₖ) ∇_{eₖ}` is the flat Dirac operator (`TauCeti.SeibergWitten.flatDirac`), `q`
the quadratic two-form (`TauCeti.SeibergWitten.quadraticTwoForm`) and `ω` the Kähler form; these
are the equations satisfied by limits of rescaled solutions (`TauCeti.SeibergWitten.`
`sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale`).
The left side of the curvature equation is `flatCurvature b ψ`, a self-dual two-vector
(`hodgeStar_flatCurvature`), defined together with the deformation rows `flatDeformationCurvature`
and `flatDeformationDirac` and their exact quadratic expansions and first-variation identities in
`TauCeti.Analysis.PDE.SeibergWitten.Flat.Operator`.

* **Dirac row.** For fields differentiable at the point,
  `D_{b + b'} (ψ + ζ) = D_b ψ + D'_{(b, ψ)}(b', ζ) + i c(b') ζ`
  (`flatDirac_add_eq_add_flatDeformationDirac_add`), where `D'` is `flatDeformationDirac` and the
  remainder `i c(b') ζ` is the flat Dirac operator of the constant field `ζ x` for the connection
  `b'`.
* **Curvature row.** For connection forms differentiable at the point,
  `flatCurvature (b + b') (ψ + ζ) = flatCurvature b ψ + F'_ψ(b', ζ) + q(ζ) / 2`
  (`flatCurvature_add`), where `F'` is `flatDeformationCurvature`.

The two remainders are the bilinear map `(b', ζ) ↦ i c(b') ζ` and the quadratic map `ζ ↦ q(ζ) / 2`.
Pointwise, `‖i c(b') ζ‖ = ‖b'‖ ‖ζ‖` (`TauCeti.SeibergWitten.norm_flatDirac_const`) and `‖q(ζ)‖ =
‖ζ‖² / (2 √2)` (`TauCeti.SeibergWitten.norm_quadraticTwoForm`), and their differences obey the
quadratic Lipschitz bounds
`‖i c(b₁) ζ₁ - i c(b₂) ζ₂‖ ≤ ‖b₁ - b₂‖ ‖ζ₁‖ + ‖b₂‖ ‖ζ₁ - ζ₂‖`
(`TauCeti.SeibergWitten.norm_flatDirac_const_sub_flatDirac_const_le`) and
`‖q(ζ₁) - q(ζ₂)‖ ≤ ‖ζ₁ - ζ₂‖ (‖ζ₁‖ + ‖ζ₂‖) / (2 √2)`
(`TauCeti.SeibergWitten.norm_quadraticTwoForm_sub_le`). So the nonlinear part `N` of each row at
a fixed pair `(b, ψ)`, the row at `(b + b', ψ + ζ)` minus its deformation row, satisfies the
quadratic estimate `‖N(b₁, ζ₁) - N(b₂, ζ₂)‖ ≤ ‖b₁ - b₂‖ ‖ζ₁‖ + ‖b₂‖ ‖ζ₁ - ζ₂‖` for the Dirac row
(`norm_flatDirac_sub_flatDeformationDirac_sub_le`) and
`‖N(b₁, ζ₁) - N(b₂, ζ₂)‖ ≤ ‖ζ₁ - ζ₂‖ (‖ζ₁‖ + ‖ζ₂‖) / (4 √2)` for the curvature row
(`norm_flatCurvature_sub_flatDeformationCurvature_sub_le`), at every point. This is the pointwise
form of the quadratic estimate on the nonlinear part used by the contraction mapping argument of
Taubes's gluing construction.

## Main results

* `TauCeti.SeibergWitten.norm_flatDirac_sub_flatDeformationDirac_sub_le`,
  `TauCeti.SeibergWitten.norm_flatCurvature_sub_flatDeformationCurvature_sub_le`: the pointwise
  quadratic estimates on the nonlinear parts of the two rows.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §4.
-/

public section

noncomputable section

open exteriorPower

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Complex
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V}

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

variable [Fact (finrank ℝ V = 4)] {ψ ζ : V → positiveHalfSpinors o ρ}

/-! ### The Dirac row -/

section Dirac

variable (e) in
/-- **The quadratic estimate for the nonlinear part of the flat Dirac operator**: at a pair
`(b, ψ)`, the nonlinear part `D_{b + b'} (ψ + ζ) - D'_{(b, ψ)}(b', ζ)` of the flat Dirac operator,
compared at two variations `(b₁, ζ₁)` and `(b₂, ζ₂)` differentiable at `x`, satisfies
`‖N(b₁, ζ₁) - N(b₂, ζ₂)‖ ≤ ‖b₁ - b₂‖ ‖ζ₁‖ + ‖b₂‖ ‖ζ₁ - ζ₂‖` at `x`. -/
theorem norm_flatDirac_sub_flatDeformationDirac_sub_le [FiniteDimensional ℂ W]
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} (hψ : DifferentiableAt ℝ (fun y ↦ (ψ y : W)) x)
    (hζ₁ : DifferentiableAt ℝ (fun y ↦ (ζ₁ y : W)) x)
    (hζ₂ : DifferentiableAt ℝ (fun y ↦ (ζ₂ y : W)) x) :
    ‖(flatDirac ρ (b + b₁) (fun y ↦ ((ψ + ζ₁) y : W)) x - flatDeformationDirac e b b₁ ψ ζ₁ x) -
        (flatDirac ρ (b + b₂) (fun y ↦ ((ψ + ζ₂) y : W)) x -
          flatDeformationDirac e b b₂ ψ ζ₂ x)‖ ≤
      ‖b₁ x - b₂ x‖ * ‖ζ₁ x‖ + ‖b₂ x‖ * ‖ζ₁ x - ζ₂ x‖ := by
  have h : (flatDirac ρ (b + b₁) (fun y ↦ ((ψ + ζ₁) y : W)) x -
        flatDeformationDirac e b b₁ ψ ζ₁ x) -
      (flatDirac ρ (b + b₂) (fun y ↦ ((ψ + ζ₂) y : W)) x - flatDeformationDirac e b b₂ ψ ζ₂ x) =
        flatDirac ρ b₁ (fun _ ↦ (ζ₁ x : W)) x - flatDirac ρ b₂ (fun _ ↦ (ζ₂ x : W)) x := by
    rw [flatDirac_add_eq_add_flatDeformationDirac_add e hψ hζ₁,
      flatDirac_add_eq_add_flatDeformationDirac_add e hψ hζ₂]
    abel
  rw [h, ← Submodule.norm_coe (ζ₁ x), ← Submodule.norm_coe (ζ₁ x - ζ₂ x), Submodule.coe_sub]
  exact norm_flatDirac_const_sub_flatDirac_const_le ρ hQ hρ b₁ b₂ _ _

end Dirac

/-! ### The curvature row -/

section Curvature

variable [FiniteDimensional ℂ W] (hkl : 2 + 2 = finrank ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

include hQ in
/-- **The quadratic estimate for the nonlinear part of the flat curvature equation**: at a pair
`(b, ψ)`, the nonlinear part `flatCurvature (b + b') (ψ + ζ) - F'_ψ(b', ζ)`, compared at two
variations `(b₁, ζ₁)` and `(b₂, ζ₂)` with connection forms differentiable at `x`, satisfies
`‖N(b₁, ζ₁) - N(b₂, ζ₂)‖ ≤ ‖ζ₁ - ζ₂‖ (‖ζ₁‖ + ‖ζ₂‖) / (4 √2)` at `x`. -/
theorem norm_flatCurvature_sub_flatDeformationCurvature_sub_le
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ}
    (hb : DifferentiableAt ℝ b x) (hb₁ : DifferentiableAt ℝ b₁ x) (hb₂ : DifferentiableAt ℝ b₂ x) :
    ‖(flatCurvature o ρ hkl (b + b₁) (ψ + ζ₁) x - flatDeformationCurvature o ρ hkl b₁ ψ ζ₁ x) -
        (flatCurvature o ρ hkl (b + b₂) (ψ + ζ₂) x - flatDeformationCurvature o ρ hkl b₂ ψ ζ₂ x)‖ ≤
      ‖ζ₁ x - ζ₂ x‖ * (‖ζ₁ x‖ + ‖ζ₂ x‖) / (4 * √2) := by
  have h : (flatCurvature o ρ hkl (b + b₁) (ψ + ζ₁) x -
        flatDeformationCurvature o ρ hkl b₁ ψ ζ₁ x) -
      (flatCurvature o ρ hkl (b + b₂) (ψ + ζ₂) x - flatDeformationCurvature o ρ hkl b₂ ψ ζ₂ x) =
        (2⁻¹ : ℝ) •
          (↑(quadraticTwoForm o ρ hkl (ζ₁ x) - quadraticTwoForm o ρ hkl (ζ₂ x)) : ⋀[ℝ]^2 V) := by
    rw [flatCurvature_add hkl hb hb₁, flatCurvature_add hkl hb hb₂, Submodule.coe_sub, smul_sub]
    abel
  rw [h, norm_smul, Submodule.norm_coe]
  calc ‖(2⁻¹ : ℝ)‖ * ‖quadraticTwoForm o ρ hkl (ζ₁ x) - quadraticTwoForm o ρ hkl (ζ₂ x)‖
      ≤ 2⁻¹ * (‖ζ₁ x - ζ₂ x‖ * (‖ζ₁ x‖ + ‖ζ₂ x‖) / (2 * √2)) := by
        rw [Real.norm_of_nonneg (by norm_num)]
        exact mul_le_mul_of_nonneg_left
          (norm_quadraticTwoForm_sub_le o hQ hkl hρ _ _) (by norm_num)
    _ = ‖ζ₁ x - ζ₂ x‖ * (‖ζ₁ x‖ + ‖ζ₂ x‖) / (4 * √2) := by ring

end Curvature

end TauCeti.SeibergWitten

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.FlatWeitzenbock
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
(`hodgeStar_flatCurvature`). The gauge-fixed normal model of
`TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic` is built from the rows
`flatDeformationCurvature` and `flatDeformationDirac`, introduced there as the linearizations of
these two equations. This file proves that they are, and that the equations have no terms beyond
the quadratic ones. The rows are linear in the variation `(b', ζ)` (`flatDeformationDirac_add`,
`flatDeformationDirac_smul`, `flatDeformationCurvature_add`, `flatDeformationCurvature_smul`).

* **Dirac row.** For fields differentiable at the point,
  `D_{b + b'} (ψ + ζ) = D_b ψ + D'_{(b, ψ)}(b', ζ) + i c(b') ζ`
  (`flatDirac_add_eq_add_flatDeformationDirac_add`), where `D'` is `flatDeformationDirac` and the
  remainder `i c(b') ζ` is the flat Dirac operator of the constant field `ζ x` for the connection
  `b'`. The linear row itself is `D_b ζ + i c(b') ψ`
  (`flatDeformationDirac_eq_flatDirac_add_flatDirac`).
* **Curvature row.** For connection forms differentiable at the point,
  `flatCurvature (b + b') (ψ + ζ) = flatCurvature b ψ + F'_ψ(b', ζ) + q(ζ) / 2`
  (`flatCurvature_add`), where `F'` is `flatDeformationCurvature`, since the curvature is linear
  in `b` and `q(ψ + ζ) = q(ψ) + q(ζ) + q'(ψ, ζ)`.
* **Lines.** Along `t ↦ (b + t b', ψ + t ζ)` both rows are exact quadratic polynomials in `t`
  (`flatDirac_add_smul`, `flatCurvature_add_smul`), so the deformation rows are the first
  variations at `t = 0` (`hasDerivAt_flatDirac_add_smul`, `hasDerivAt_flatCurvature_add_smul`), the
  analogue of `TauCeti.Vortex.hasDerivAt_equation` for the plane vortex equations.

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

## Main definitions

* `TauCeti.SeibergWitten.flatCurvature`: the curvature side `F + ⋆F + q(ψ) / 2` of the flat
  limiting curvature equation.

## Main results

* `TauCeti.SeibergWitten.flatDirac_add_eq_add_flatDeformationDirac_add`,
  `TauCeti.SeibergWitten.flatCurvature_add`: the exact expansions of the two rows.
* `TauCeti.SeibergWitten.hasDerivAt_flatDirac_add_smul`,
  `TauCeti.SeibergWitten.hasDerivAt_flatCurvature_add_smul`: the deformation rows of the normal
  model are the first variations of the flat limiting equations.
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

/-- A quadratic polynomial `t ↦ u + t • v + t ^ 2 • w` has derivative `v` at `0`. -/
private theorem hasDerivAt_add_smul_add_sq_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u v w : E) : HasDerivAt (fun t : ℝ ↦ u + t • v + t ^ 2 • w) v 0 := by
  convert ((hasDerivAt_const (0 : ℝ) u).add ((hasDerivAt_id (0 : ℝ)).smul_const v)).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const w) using 1 <;> simp [Pi.add_def]

variable [Fact (finrank ℝ V = 4)] {ψ ζ : V → positiveHalfSpinors o ρ}

/-- The field into `W` underlying a sum of half-spinor fields is the sum of the underlying
fields. -/
private theorem coe_comp_add (ψ ζ : V → positiveHalfSpinors o ρ) :
    (fun y ↦ ((ψ + ζ) y : W)) = (fun y ↦ (ψ y : W)) + fun y ↦ (ζ y : W) :=
  rfl

/-- The field into `W` underlying a real multiple of a half-spinor field is the corresponding
complex multiple of the underlying field. -/
private theorem coe_comp_smul (t : ℝ) (ζ : V → positiveHalfSpinors o ρ) :
    (fun y ↦ ((t • ζ) y : W)) = (t : ℂ) • fun y ↦ (ζ y : W) :=
  funext fun _ ↦ (Complex.coe_smul t _).symm

/-! ### The Dirac row -/

section Dirac

variable (ρ) in
/-- **The Dirac row of the normal model through the flat Dirac operator**:
`flatDeformationDirac` at `(b, ψ)` applied to `(b', ζ)` is `D_b ζ + i c(b') ψ`, the flat Dirac
operator of `ζ` plus the Clifford multiplication of `ψ` by `b'`. -/
theorem flatDeformationDirac_eq_flatDirac_add_flatDirac (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (x : V) :
    flatDeformationDirac e b b' ψ ζ x =
      flatDirac ρ b (fun y ↦ (ζ y : W)) x + flatDirac ρ b' (fun _ ↦ (ψ x : W)) x := by
  rw [flatDeformationDirac_def, flatDirac_eq_sum ρ e, flatDirac_eq_sum ρ e,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [covariantDeriv_apply, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_add,
    ← map_add, mul_comm I, mul_smul, Complex.coe_smul]

/-- The Dirac row of the normal model is linear in the variation `(b', ζ)`: scaling both by
`t` scales the row by `t`. -/
theorem flatDeformationDirac_smul (t : ℝ) :
    flatDeformationDirac e b (t • b') ψ (t • ζ) x = t • flatDeformationDirac e b b' ψ ζ x := by
  rw [flatDeformationDirac_eq_flatDirac_add_flatDirac ρ, coe_comp_smul, flatDirac_smul,
    Complex.coe_smul, flatDirac_smul_connection_const,
    flatDeformationDirac_eq_flatDirac_add_flatDirac ρ, smul_add]

/-- The Dirac row of the normal model is additive in the variation `(b', ζ)`, for spinor
variations differentiable at the point. -/
theorem flatDeformationDirac_add {b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} (hζ₁ : DifferentiableAt ℝ (fun y ↦ (ζ₁ y : W)) x)
    (hζ₂ : DifferentiableAt ℝ (fun y ↦ (ζ₂ y : W)) x) :
    flatDeformationDirac e b (b₁ + b₂) ψ (ζ₁ + ζ₂) x =
      flatDeformationDirac e b b₁ ψ ζ₁ x + flatDeformationDirac e b b₂ ψ ζ₂ x := by
  simp only [flatDeformationDirac_eq_flatDirac_add_flatDirac ρ]
  rw [coe_comp_add, flatDirac_add ρ hζ₁ hζ₂, flatDirac_add_connection]
  abel

variable (e) in
/-- **The exact expansion of the flat Dirac operator**: for spinor fields `ψ` and `ζ`
differentiable at `x`,

`D_{b + b'} (ψ + ζ) = D_b ψ + D'_{(b, ψ)}(b', ζ) + i c(b') ζ`,

where `D'` is the Dirac row of the normal model (`flatDeformationDirac`) and the remainder
`i c(b') ζ` is the flat Dirac operator of the constant field with value `ζ x` for the
connection `b'`. -/
theorem flatDirac_add_eq_add_flatDeformationDirac_add
    (hψ : DifferentiableAt ℝ (fun y ↦ (ψ y : W)) x)
    (hζ : DifferentiableAt ℝ (fun y ↦ (ζ y : W)) x) :
    flatDirac ρ (b + b') (fun y ↦ ((ψ + ζ) y : W)) x =
      flatDirac ρ b (fun y ↦ (ψ y : W)) x + flatDeformationDirac e b b' ψ ζ x +
        flatDirac ρ b' (fun _ ↦ (ζ x : W)) x := by
  have hconst : flatDirac ρ b' (fun _ ↦ (ψ x : W) + (ζ x : W)) x =
      flatDirac ρ b' (fun _ ↦ (ψ x : W)) x + flatDirac ρ b' (fun _ ↦ (ζ x : W)) x :=
    flatDirac_add ρ (differentiableAt_const _) (differentiableAt_const _)
  rw [coe_comp_add, flatDirac_add_connection, flatDirac_add ρ hψ hζ, Pi.add_apply, hconst,
    flatDeformationDirac_eq_flatDirac_add_flatDirac ρ]
  abel

variable (e) in
/-- **The flat Dirac operator along a line is quadratic**: for spinor fields `ψ` and `ζ`
differentiable at `x` and every real `t`,

`D_{b + t b'} (ψ + t ζ) = D_b ψ + t D'_{(b, ψ)}(b', ζ) + t² i c(b') ζ`. -/
theorem flatDirac_add_smul (hψ : DifferentiableAt ℝ (fun y ↦ (ψ y : W)) x)
    (hζ : DifferentiableAt ℝ (fun y ↦ (ζ y : W)) x) (t : ℝ) :
    flatDirac ρ (b + t • b') (fun y ↦ ((ψ + t • ζ) y : W)) x =
      flatDirac ρ b (fun y ↦ (ψ y : W)) x + t • flatDeformationDirac e b b' ψ ζ x +
        t ^ 2 • flatDirac ρ b' (fun _ ↦ (ζ x : W)) x := by
  have htζ : DifferentiableAt ℝ (fun y ↦ ((t • ζ) y : W)) x := by
    rw [coe_comp_smul]
    exact hζ.const_smul _
  have hconst : (fun _ : V ↦ ((t • ζ) x : W)) = (t : ℂ) • fun _ ↦ (ζ x : W) :=
    coe_comp_smul t fun _ ↦ ζ x
  rw [flatDirac_add_eq_add_flatDeformationDirac_add e hψ htζ, flatDeformationDirac_smul, hconst,
    flatDirac_smul, Complex.coe_smul, flatDirac_smul_connection_const, smul_smul, ← sq]

variable (e) in
/-- **The Dirac row of the normal model is the first variation of the flat Dirac operator**:
for spinor fields differentiable at `x`, the derivative of `t ↦ D_{b + t b'} (ψ + t ζ)` at `x`
at `t = 0` is `flatDeformationDirac` at `(b, ψ)` applied to `(b', ζ)`. -/
theorem hasDerivAt_flatDirac_add_smul (hψ : DifferentiableAt ℝ (fun y ↦ (ψ y : W)) x)
    (hζ : DifferentiableAt ℝ (fun y ↦ (ζ y : W)) x) :
    HasDerivAt (fun t : ℝ ↦ flatDirac ρ (b + t • b') (fun y ↦ ((ψ + t • ζ) y : W)) x)
      (flatDeformationDirac e b b' ψ ζ x) 0 := by
  simp_rw [flatDirac_add_smul e hψ hζ]
  exact hasDerivAt_add_smul_add_sq_smul _ _ _

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

variable (o ρ) in
/-- The **curvature side of the flat limiting curvature equation** at a pair `(b, ψ)`:
`F + ⋆F + q(ψ) / 2`, with the real curvature `F = -db` read as a two-vector. The flat limiting
curvature equation is `flatCurvature b ψ x = ω / 8` (`flatCurvature_eq_iff`). -/
def flatCurvature (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V → positiveHalfSpinors o ρ) (x : V) :
    ⋀[ℝ]^2 V :=
  (alternatingFormEquiv V 2).symm (-extDeriv b x) +
      o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) +
    (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ψ x) : ⋀[ℝ]^2 V)

theorem flatCurvature_def (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V → positiveHalfSpinors o ρ)
    (x : V) :
    flatCurvature o ρ hkl b ψ x =
      (alternatingFormEquiv V 2).symm (-extDeriv b x) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) +
        (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ψ x) : ⋀[ℝ]^2 V) :=
  (rfl)

/-- The flat limiting curvature equation `flatCurvature b ψ x = ω / 8` is the equation
`F + ⋆F = ω / 8 - q(ψ) / 2` of the rescaled limits. -/
theorem flatCurvature_eq_iff (ω : ⋀[ℝ]^2 V) :
    flatCurvature o ρ hkl b ψ x = (8⁻¹ : ℝ) • ω ↔
      (alternatingFormEquiv V 2).symm (-extDeriv b x) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
        (8⁻¹ : ℝ) • ω - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ψ x) : ⋀[ℝ]^2 V) := by
  rw [flatCurvature_def, eq_sub_iff_add_eq]

/-- The curvature side of the flat limiting curvature equation is self-dual. -/
theorem hodgeStar_flatCurvature (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V → positiveHalfSpinors o ρ)
    (x : V) : o.hodgeStar hkl (flatCurvature o ρ hkl b ψ x) = flatCurvature o ρ hkl b ψ x := by
  rw [flatCurvature_def, map_add, map_add, map_smul,
    o.hodgeStar_hodgeStar_of_even even_two hkl, o.hodgeStar_coe_of_mem_eigenspace_one hkl]
  abel

/-- The curvature row of the normal model is linear in the variation `(b', ζ)`: scaling both by
`t` scales the row by `t`. -/
theorem flatDeformationCurvature_smul (t : ℝ) :
    flatDeformationCurvature o ρ hkl (t • b') ψ (t • ζ) x =
      t • flatDeformationCurvature o ρ hkl b' ψ ζ x := by
  simp only [flatDeformationCurvature_def, extDeriv_smul, ← smul_neg, map_smul, Pi.smul_apply,
    Submodule.coe_smul, smul_add, smul_comm t (2⁻¹ : ℝ)]

/-- The curvature row of the normal model is additive in the variation `(b', ζ)`, for connection
variations differentiable at the point. -/
theorem flatDeformationCurvature_add {b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} (hb₁ : DifferentiableAt ℝ b₁ x)
    (hb₂ : DifferentiableAt ℝ b₂ x) :
    flatDeformationCurvature o ρ hkl (b₁ + b₂) ψ (ζ₁ + ζ₂) x =
      flatDeformationCurvature o ρ hkl b₁ ψ ζ₁ x + flatDeformationCurvature o ρ hkl b₂ ψ ζ₂ x := by
  simp only [flatDeformationCurvature_def, extDeriv_add hb₁ hb₂, Pi.add_apply, neg_add, map_add,
    Submodule.coe_add, smul_add]
  abel

/-- **The exact expansion of the flat curvature equation**: for connection forms `b` and `b'`
differentiable at `x`,

`flatCurvature (b + b') (ψ + ζ) = flatCurvature b ψ + F'_ψ(b', ζ) + q(ζ) / 2`,

where `F'` is the curvature row of the normal model (`flatDeformationCurvature`). -/
theorem flatCurvature_add (hb : DifferentiableAt ℝ b x) (hb' : DifferentiableAt ℝ b' x) :
    flatCurvature o ρ hkl (b + b') (ψ + ζ) x =
      flatCurvature o ρ hkl b ψ x + flatDeformationCurvature o ρ hkl b' ψ ζ x +
        (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ x) : ⋀[ℝ]^2 V) := by
  rw [flatCurvature_def, flatCurvature_def, flatDeformationCurvature_def, extDeriv_add hb hb',
    Pi.add_apply, quadraticTwoForm_add]
  simp only [neg_add, map_add, Submodule.coe_add, smul_add]
  abel

/-- **The flat curvature equation along a line is quadratic**: for connection forms `b` and `b'`
differentiable at `x` and every real `t`,

`flatCurvature (b + t b') (ψ + t ζ) = flatCurvature b ψ + t F'_ψ(b', ζ) + t² q(ζ) / 2`. -/
theorem flatCurvature_add_smul (hb : DifferentiableAt ℝ b x) (hb' : DifferentiableAt ℝ b' x)
    (t : ℝ) :
    flatCurvature o ρ hkl (b + t • b') (ψ + t • ζ) x =
      flatCurvature o ρ hkl b ψ x + t • flatDeformationCurvature o ρ hkl b' ψ ζ x +
        t ^ 2 • (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ x) : ⋀[ℝ]^2 V) := by
  have hq : quadraticTwoForm o ρ hkl ((t • ζ) x) = t ^ 2 • quadraticTwoForm o ρ hkl (ζ x) := by
    rw [Pi.smul_apply, ← Complex.coe_smul, quadraticTwoForm_smul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [flatCurvature_add hkl hb (hb'.const_smul t), flatDeformationCurvature_smul, hq,
    Submodule.coe_smul, smul_comm (2⁻¹ : ℝ)]

/-- **The curvature row of the normal model is the first variation of the flat curvature
equation**: for connection forms differentiable at `x`, the derivative of
`t ↦ flatCurvature (b + t b') (ψ + t ζ) x` at `t = 0` is `flatDeformationCurvature` at `ψ`
applied to `(b', ζ)`. -/
theorem hasDerivAt_flatCurvature_add_smul (hb : DifferentiableAt ℝ b x)
    (hb' : DifferentiableAt ℝ b' x) :
    HasDerivAt (fun t : ℝ ↦ flatCurvature o ρ hkl (b + t • b') (ψ + t • ζ) x)
      (flatDeformationCurvature o ρ hkl b' ψ ζ x) 0 := by
  simp_rw [flatCurvature_add_smul hkl hb hb']
  exact hasDerivAt_add_smul_add_sq_smul _ _ _

include hQ in
/-- **The quadratic estimate for the nonlinear part of the flat curvature equation**: at a pair
`(b, ψ)`, the nonlinear part `flatCurvature (b + b') (ψ + ζ) - F'_ψ(b', ζ)`, compared at two
variations `(b₁, ζ₁)` and `(b₂, ζ₂)` with connection forms differentiable at `x`, satisfies
`‖N(b₁, ζ₁) - N(b₂, ζ₂)‖ ≤ ‖ζ₁ - ζ₂‖ (‖ζ₁‖ + ‖ζ₂‖) / (4 √2)` at `x`. -/
theorem norm_flatCurvature_sub_flatDeformationCurvature_sub_le
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) {b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ζ₁ ζ₂ : V → positiveHalfSpinors o ρ} (hb : DifferentiableAt ℝ b x)
    (hb₁ : DifferentiableAt ℝ b₁ x) (hb₂ : DifferentiableAt ℝ b₂ x) :
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
          (norm_quadraticTwoForm_sub_le o hQ hkl hρ h₂ _ _) (by norm_num)
    _ = ‖ζ₁ x - ζ₂ x‖ * (‖ζ₁ x‖ + ‖ζ₂ x‖) / (4 * √2) := by ring

end Curvature

end TauCeti.SeibergWitten

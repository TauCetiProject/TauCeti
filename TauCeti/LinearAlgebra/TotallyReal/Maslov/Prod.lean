/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import TauCeti.LinearAlgebra.TotallyReal.Complex
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index

/-!
# The Maslov index is additive under the direct sum

The Maslov index `μ(Λ)` of a loop of maximal totally real subspaces is a winding number, and a
winding number adds over a direct sum. This file proves the corresponding **direct-sum axiom**

`μ(Λ ⊕ Λ') = μ(Λ) + μ(Λ')`,

where `Λ ⊕ Λ'` is the loop `t ↦ Λ t ⊕ Λ' t` of coordinate subspaces of `E × E'`, packaged as
`TauCeti.TotallyRealLoop.prod`.

The two ingredients are multiplicative. The Maslov phase of a direct sum is the product of the two
phases, `ρ(L₀ ⊕ L₀', L ⊕ L') = ρ(L₀, L) ρ(L₀', L')`, because an automorphism carrying `L₀` to `L`
and `L₀'` to `L'` is carried out blockwise, its determinant is the product of the two block
determinants, and the determinant phase is multiplicative. And the degree of a pointwise product of
loops in the circle is the sum of the degrees. Composing the two, and reading the Maslov index as
the degree of the loop of phases relative to an arbitrary reference subspace, gives the axiom.

The linear-algebra input, that a coordinate submodule `L.prod M` of a product of complex modules is
maximal totally real whenever the two summands are, is
`TauCeti.IsMaximalTotallyReal.isMaximalTotallyReal_prod`
(`TauCeti/LinearAlgebra/TotallyReal/Complex.lean`), and rests on
`TauCeti.LinearMap.lsmul_restrictScalars_prodMap` (`TauCeti/LinearAlgebra/Prod.lean`), which says
that multiplication by `i` on a product is the product map of the two multiplications.

The axiom is the additivity half of the standard list of properties of the Maslov index
(Robbin--Salamon, *The Maslov index for paths*, Topology **32** (1993); McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix C.3). It combines two loops that vary
independently: it is the statement needed whenever a totally real boundary condition, or a pair of
complex bundles, is a direct sum of two such conditions or bundles, each with its own loop of
totally real subspaces. Summing over the separate boundary components of a Cauchy--Riemann operator
on a surface, each of which carries a loop of its own, is a further step built on top of this one.

## Main declarations

* `TauCeti.IsMaximalTotallyReal.maslovPhase_prod`: the Maslov phase of a direct sum is the product
  of the two phases.
* `TauCeti.TotallyRealLoop.prod`: the loop of coordinate subspaces of a pair of loops.
* `TauCeti.TotallyRealLoop.maslovIndex_prod`: **the direct-sum axiom.**
* `TauCeti.TotallyRealLoop.maslovIndex_prod_rotation`: the two half-turns, taken in the two
  summands, have Maslov index the sum of the two complex dimensions.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), the axioms of
  the Maslov index of a loop of Lagrangian subspaces, one of which is the direct-sum axiom.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (the Maslov index of a loop of totally real
  subspaces, and the boundary Maslov index of a bundle pair).
-/

public section

open Module Real
open scoped ComplexConjugate unitInterval

namespace TauCeti

namespace IsMaximalTotallyReal

variable {E E' : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  {L : Submodule ℝ E}
  [AddCommGroup E'] [Module ℝ E'] [Module ℂ E'] [IsScalarTower ℝ ℂ E'] {M : Submodule ℝ E'}

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']

/-- **The Maslov phase of a direct sum is the product of the two phases:**
`ρ(L₀ ⊕ L₀', L ⊕ L') = ρ(L₀, L) ρ(L₀', L')`. -/
theorem maslovPhase_prod {L' : Submodule ℝ E} {M' : Submodule ℝ E'}
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
    (hM : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E' Complex.I).restrictScalars ℝ) M)
    (hL' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L')
    (hM' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E' Complex.I).restrictScalars ℝ) M') :
    (hL.isMaximalTotallyReal_prod hM).maslovPhase (hL'.isMaximalTotallyReal_prod hM')
      = hL.maslovPhase hL' * hM.maslovPhase hM' := by
  obtain ⟨A, hA⟩ := hL.exists_linearEquiv_map_eq hL'
  obtain ⟨B, hB⟩ := hM.exists_linearEquiv_map_eq hM'
  have hP : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (E × E') Complex.I).restrictScalars ℝ)
      (L.prod M) := hL.isMaximalTotallyReal_prod hM
  -- The block diagonal of `A` and `B` carries `L ⊕ M` onto `A L ⊕ B M`.
  have hsub : (L'.prod M') = (L.prod M).map
      ((LinearEquiv.prodCongr A B : (E × E') →ₗ[ℂ] (E × E')).restrictScalars ℝ) := by
    have h : ((LinearEquiv.prodCongr A B : (E × E') →ₗ[ℂ] (E × E')).restrictScalars ℝ :
        (E × E') →ₗ[ℝ] (E × E')) =
        LinearMap.prodMap (LinearMap.restrictScalars ℝ A.toLinearMap)
          (LinearMap.restrictScalars ℝ B.toLinearMap) := by
      apply LinearMap.ext (R := ℝ)
      intro x
      rcases x with ⟨x, y⟩
      simp
    rw [← hA, ← hB, h, LinearMap.prodMap_map_prod]
  -- The determinant of the block diagonal is the product of the two block determinants, which is
  -- `LinearEquiv.det_prodCongr` read through `LinearEquiv.coe_det`.
  have hdet : LinearMap.det ((LinearEquiv.prodCongr A B : (E × E') →ₗ[ℂ] (E × E'))) =
      LinearMap.det (A : E →ₗ[ℂ] E) * LinearMap.det (B : E' →ₗ[ℂ] E') := by
    rw [← LinearEquiv.coe_det, ← LinearEquiv.coe_det, ← LinearEquiv.coe_det,
      LinearEquiv.det_prodCongr, Units.val_mul]
  rw [hP.maslovPhase_congr (hL'.isMaximalTotallyReal_prod hM')
    (hP.map_linearEquiv (LinearEquiv.prodCongr A B)) hsub,
    hP.maslovPhase_map, hdet,
    hL.maslovPhase_congr hL' (hL.map_linearEquiv A) hA.symm,
    hM.maslovPhase_congr hM' (hM.map_linearEquiv B) hB.symm,
    hL.maslovPhase_map, hM.maslovPhase_map, map_mul]
  ring

end IsMaximalTotallyReal

namespace TotallyRealLoop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- The loop of coordinate subspaces of a pair of loops of maximal totally real subspaces: the
direct sum `Λ ⊕ Λ'` of `t ↦ Λ t` and `t ↦ Λ' t`, in the product of the ambient spaces. -/
noncomputable def prod (Λ : TotallyRealLoop E) (Λ' : TotallyRealLoop E') :
    TotallyRealLoop (E × E') where
  toFun t := (Λ t).prod (Λ' t)
  exists_frame := by
    obtain ⟨L₁, hL₁, A, hAc, hA⟩ := Λ.exists_frame
    obtain ⟨L₂, hL₂, B, hBc, hB⟩ := Λ'.exists_frame
    have hL₁₂ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (E × E') Complex.I).restrictScalars ℝ)
        (L₁.prod L₂) := hL₁.isMaximalTotallyReal_prod hL₂
    refine ⟨L₁.prod L₂, hL₁₂, fun t => ContinuousLinearEquiv.prodCongr (A t) (B t),
      Continuous.prod_map_equivL ℂ hAc hBc, ?_⟩
    intro t
    rw [hA t, hB t, ← LinearMap.prodMap_map_prod]
    -- The product of the two restricted block maps is the restriction of the blockwise product
    -- map; the two agree pointwise, not definitionally.
    have hmap : (((A t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ).prodMap
        (((B t).toLinearEquiv : E' →ₗ[ℂ] E').restrictScalars ℝ) =
        ((ContinuousLinearEquiv.prodCongr (A t) (B t) : (E × E') ≃ₗ[ℂ] (E × E')) :
          (E × E') →ₗ[ℂ] (E × E')).restrictScalars ℝ := by
      apply LinearMap.ext (R := ℝ)
      intro x
      rcases x with ⟨x, y⟩
      simp
    rw [hmap]
  toFun_zero_eq_toFun_one :=
    by rw [Λ.toFun_zero_eq_toFun_one, Λ'.toFun_zero_eq_toFun_one]

@[simp]
theorem prod_apply (Λ : TotallyRealLoop E) (Λ' : TotallyRealLoop E') (t : I) :
    Λ.prod Λ' t = (Λ t).prod (Λ' t) :=
  (rfl)

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']

/-- **The direct-sum axiom of the Maslov index.** The Maslov index of the direct sum of two loops
of maximal totally real subspaces is the sum of their Maslov indices. -/
@[simp]
theorem maslovIndex_prod (Λ : TotallyRealLoop E) (Λ' : TotallyRealLoop E') :
    (Λ.prod Λ').maslovIndex = Λ.maslovIndex + Λ'.maslovIndex := by
  have hL₁ := Λ.isMaximalTotallyReal 0
  have hL₂ := Λ'.isMaximalTotallyReal 0
  have hL₁₂ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (E × E') Complex.I).restrictScalars ℝ)
      ((Λ 0).prod (Λ' 0)) := hL₁.isMaximalTotallyReal_prod hL₂
  -- The phases of the two summands multiply to the phase of the direct sum.
  have hphase (t : I) :
      hL₁₂.maslovPhase ((Λ.prod Λ').isMaximalTotallyReal t)
        = hL₁.maslovPhase (Λ.isMaximalTotallyReal t)
          * hL₂.maslovPhase (Λ'.isMaximalTotallyReal t) := by
    exact IsMaximalTotallyReal.maslovPhase_prod hL₁ hL₂
      (Λ.isMaximalTotallyReal t) (Λ'.isMaximalTotallyReal t)
  have hμ₁ : Λ.maslovIndex = Circle.degree (Λ.maslovPhasePath) :=
    Λ.maslovIndex_eq_degree hL₁ (Λ.maslovPhasePath) fun _ => maslovPhasePath_apply _ _
  have hμ₂ : Λ'.maslovIndex = Circle.degree (Λ'.maslovPhasePath) :=
    Λ'.maslovIndex_eq_degree hL₂ (Λ'.maslovPhasePath) fun _ => maslovPhasePath_apply _ _
  -- Both loops of phases are based at `1`, so their pointwise product is again a loop, and it is
  -- the loop of phases of the direct sum.
  have hμ₃ : (Λ.prod Λ').maslovIndex = Circle.degree ((Λ.maslovPhasePath).mul
      (Λ'.maslovPhasePath)) := by
    refine (Λ.prod Λ').maslovIndex_eq_degree hL₁₂ _ fun t => ?_
    rw [Path.mul_apply, Circle.coe_mul, maslovPhasePath_apply, maslovPhasePath_apply, hphase]
  rw [hμ₃, hμ₁, hμ₂, Circle.degree_mul]

/-- The direct sum of the two half-turns has Maslov index the sum of the two complex dimensions. -/
theorem maslovIndex_prod_rotation {L₁ : Submodule ℝ E} {L₂ : Submodule ℝ E'}
    (hL₁ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₁)
    (hL₂ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E' Complex.I).restrictScalars ℝ) L₂) :
    (rotation hL₁ |>.prod (rotation hL₂)).maslovIndex = finrank ℂ E + finrank ℂ E' := by
  rw [maslovIndex_prod, maslovIndex_rotation, maslovIndex_rotation]

end TotallyRealLoop

end TauCeti

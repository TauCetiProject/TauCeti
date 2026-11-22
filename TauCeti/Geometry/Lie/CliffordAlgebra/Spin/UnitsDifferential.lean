/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitsRange
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.SpecialFunctions.Exponential

/-!
# Shared exponential-curve differentiation for Spin-to-SO projections

Both the compact real Spin projection and the nondegenerate complex Spin projection compute the
differential `d(spinToSpecialOrthogonal)` by comparing a one-parameter exponential curve
`exp (t • A)` in `SO(Q)` with the corresponding curve `exp (t • x)` in `Spin(Q)`.

This module extracts the field-independent core of that calculation over any finite-dimensional
normed field extension `𝕜` of `ℝ` with `2` invertible:

* `TauCeti.CliffordAlgebra.hasDerivAt_linearMap_exp_mulVec`: differentiates
  `t ↦ f (exp (t • A) *ᵥ v)` at `t = 0` for any `ℝ`-linear map `f` into a normed space.
* `TauCeti.CliffordAlgebra.ι_mulVec_eq_lie_of_spinToSpecialOrthogonal_exp_curve`: given an
  algebra identification `e : CliffordAlgebra Q ≃ₐ[ℝ] R` into a complete normed algebra `R` and a
  curve `u : ℝ → MonoidHom.range spinGroup.toUnits` whose Spin and matrix projections follow
  `NormedSpace.exp (t • e x)` and `NormedSpace.exp (t • A)`, deduces `ι Q (A *ᵥ v) = ⁅x, ι Q v⁆`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] NormedAlgebra.toNormedSpace
attribute [local instance] TauCeti.normedAlgebraRatOfReal

section ChainRule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [FiniteDimensional ℝ 𝕜]
  {m : Type*} [Fintype m] [DecidableEq m]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiating the linear evaluation `t ↦ f (NormedSpace.exp (t • A) *ᵥ v)` at `0`
yields `f (A *ᵥ v)`. -/
theorem hasDerivAt_linearMap_exp_mulVec
    (f : (m → 𝕜) →ₗ[ℝ] E) (A : Matrix m m 𝕜) (v : m → 𝕜) :
    HasDerivAt (fun t : ℝ ↦ f (NormedSpace.exp (t • A) *ᵥ v)) (f (A *ᵥ v)) 0 := by
  let _ : CompleteSpace 𝕜 := FiniteDimensional.completeSpace ℝ 𝕜
  let fLin : Matrix m m 𝕜 →ₗ[ℝ] E :=
    f.comp (((Matrix.mulVecBilin 𝕜 𝕜).flip v).restrictScalars ℝ)
  let fCLM : Matrix m m 𝕜 →L[ℝ] E :=
    ContinuousLinearMap.mk fLin fLin.continuous_of_finiteDimensional
  have hfCLM (M : Matrix m m 𝕜) : fCLM M = f (M *ᵥ v) := by
    simp only [fCLM, fLin, ContinuousLinearMap.coe_mk', LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, LinearMap.flip_apply, Matrix.mulVecBilin_apply]
  have h := fCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_exp_smul_const A (0 : ℝ))
  simpa only [Function.comp_def, hfCLM, zero_smul, NormedSpace.exp_zero, one_mul] using h

end ChainRule

section Commutator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [FiniteDimensional ℝ 𝕜] [Invertible (2 : 𝕜)]
  {m : Type*} [Fintype m] [DecidableEq m]
  {Q : QuadraticForm 𝕜 (m → 𝕜)}
  {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- **Spin–SO exponential-curve differentiation.** If a curve `u` in `MonoidHom.range
spinGroup.toUnits` has Clifford ambient coordinate `NormedSpace.exp (t • e x)` and projects under
`spinToSpecialOrthogonalUnitsRange` to `NormedSpace.exp (t • A)`, then `A` acts on embedded
vectors `v` by the Clifford Lie bracket with `x`. -/
theorem ι_mulVec_eq_lie_of_spinToSpecialOrthogonal_exp_curve
    [IsModuleTopology 𝕜 (m → 𝕜)] [ContinuousMul (CliffordAlgebra Q)]
    (e : CliffordAlgebra Q ≃ₐ[ℝ] R)
    (x : CliffordAlgebra Q) (A : Matrix m m 𝕜)
    (u : ℝ → MonoidHom.range (spinGroup.toUnits (Q := Q)))
    (hu : ∀ t : ℝ, e ((u t : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      NormedSpace.exp (t • e x))
    (hA : ∀ t : ℝ,
      (((spinToSpecialOrthogonalUnitsRange Q (u t) :
          MonoidHom.range Q.specialOrthogonalToGeneralLinear).val : (Matrix m m 𝕜)ˣ) :
        Matrix m m 𝕜) = NormedSpace.exp (t • A))
    (v : m → 𝕜) :
    ι Q (A *ᵥ v) = ⁅x, ι Q v⁆ := by
  have hconj : ∀ t : ℝ, e (ι Q (NormedSpace.exp (t • A) *ᵥ v)) =
      NormedSpace.exp (t • e x) * e (ι Q v) * NormedSpace.exp (t • (-e x)) := fun t ↦ by
    let s := (spinGroupContinuousMulEquivUnitsRange Q).symm (u t)
    have hmatrix : NormedSpace.exp (t • A) *ᵥ v = spinVectorAction Q s v := by
      rw [← hA t, spinToSpecialOrthogonalUnitsRange_apply,
        Q.specialOrthogonalContinuousMulEquivRange_apply]
      dsimp only
      rw [Q.specialOrthogonalToGeneralLinear_mulVec, coe_spinToSpecialOrthogonal_apply]
    have hs : e (s : CliffordAlgebra Q) = NormedSpace.exp (t • e x) := by
      rw [coe_spinGroupContinuousMulEquivUnitsRange_symm_apply, hu t]
    have hmul : (s : CliffordAlgebra Q) * star (s : CliffordAlgebra Q) = 1 :=
      spinGroup.coe_mul_star_self s
    have hstar : e (star (s : CliffordAlgebra Q)) = NormedSpace.exp (t • (-e x)) := by
      let _ := NormedSpace.invertibleExp (t • e x)
      have he : NormedSpace.exp (t • e x) * e (star (s : CliffordAlgebra Q)) = 1 := by
        rw [← hs, ← map_mul, hmul, map_one]
      rw [← invOf_eq_right_inv he, NormedSpace.invOf_exp, smul_neg]
    rw [hmatrix, ι_spinVectorAction_apply, map_mul, map_mul, hs, hstar]
  have hleft := hasDerivAt_linearMap_exp_mulVec
    (e.toLinearMap.comp ((ι Q).restrictScalars ℝ)) A v
  have hright := (TauCeti.hasDerivAt_exp_mul_const_mul_exp_neg
    (e x) (e (ι Q v))).congr_of_eventuallyEq (Filter.Eventually.of_forall hconj)
  have hderiv : e (ι Q (A *ᵥ v)) = e x * e (ι Q v) - e (ι Q v) * e x :=
    hleft.unique hright
  apply e.injective
  rw [Ring.lie_def, map_sub, map_mul, map_mul]
  exact hderiv

end Commutator

end TauCeti.CliffordAlgebra

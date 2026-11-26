/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Analysis.MvPolynomial.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Calculus.ImplicitFunction.Data
import TauCeti.LinearAlgebra.Matrix.MaximalMinor

/-!
# Implicit function charts for polynomial equations

At a zero of a polynomial family with an invertible Jacobian minor, the coordinates outside the
minor are local coordinates on the zero set. This is the implicit function theorem with the
coordinate projection as the complementary map.
-/

public section

open TauCeti

namespace MvPolynomial

variable {K ι σ : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  (p : σ → MvPolynomial ι K) {m : σ → ι}

/-- The projection onto the coordinates outside the Jacobian minor. -/
private def freeCoords : (ι → K) →L[K] ↥(Set.range m)ᶜ → K :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.val

section Fintype

variable [Fintype ι] [Fintype σ] [Fintype ↥(Set.range m)ᶜ]

/-- The implicit function data for the equations and complementary coordinate projection. -/
private noncomputable abbrev implicitData [DecidableEq σ] (hm : Function.Injective m) (x : ι → K)
    (hJ : IsUnit (((jacobiMatrixAt p x).submatrix id m).det)) :
    ImplicitFunctionData K (ι → K) (σ → K) (↥(Set.range m)ᶜ → K) := by
  classical
  let π : (ι → K) →L[K] ↥(Set.range m)ᶜ → K := freeCoords
  have hπ : π.toLinearMap = LinearMap.funLeft K K Subtype.val := by
    ext y i
    simp [π, freeCoords]
  have hD := fderiv_eval_family p x
  exact
    { leftFun := fun y j ↦ eval y (p j)
      leftDeriv := fderiv K (fun y j ↦ eval y (p j)) x
      rightFun := π
      rightDeriv := π
      pt := x
      hasStrictFDerivAt_leftFun := (analyticOnNhd_eval_family p _ trivial).hasStrictFDerivAt
      hasStrictFDerivAt_rightFun := π.hasStrictFDerivAt
      range_leftDeriv := by
        rw [hD, LinearMap.range_eq_top, Matrix.coe_mulVecLin]
        exact Matrix.mulVec_surjective_of_isUnit_det_submatrix _ hm hJ
      range_rightDeriv := by
        rw [hπ, LinearMap.range_eq_top]
        exact LinearMap.funLeft_surjective_of_injective K K _ Subtype.val_injective
      isCompl_ker := by
        rw [hD, hπ]
        exact Matrix.isCompl_ker_mulVecLin_ker_funLeft _ hm hJ }

end Fintype

/-- At a common zero of polynomial equations with an invertible Jacobian minor, evaluating
the coordinates outside the minor gives a chart on the zero set. -/
theorem exists_openPartialHomeomorph_zeroSet [Finite ι] [Fintype σ] [DecidableEq σ]
    (hm : Function.Injective m)
    (x : {y : ι → K | (fun j ↦ eval y (p j)) = 0})
    (hJ : IsUnit (((jacobiMatrixAt p x.val).submatrix id m).det)) :
    ∃ e : OpenPartialHomeomorph {y : ι → K | (fun j ↦ eval y (p j)) = 0}
        (↥(Set.range m)ᶜ → K),
      x ∈ e.source ∧ ∀ y i, e y i = y.val i := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite ↥(Set.range m)ᶜ
  let d := implicitData p hm x.val hJ
  refine ⟨d.levelSetChart x.property, d.mem_levelSetChart_source x.property, fun y i ↦ ?_⟩
  simp [d, implicitData, freeCoords]

end MvPolynomial

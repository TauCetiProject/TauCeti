/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Analysis.MvPolynomial.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Calculus.ImplicitFunction.Data
import TauCeti.LinearAlgebra.Matrix.MaximalMinor
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi.FunLeft

/-!
# Implicit function charts for polynomial equations

At a zero of a polynomial family, an invertible square Jacobian minor using every equation
row gives a chart on the common zero set. The chart projects onto the coordinates outside the
selected columns.

This construction is extracted from
`TauCeti.Topology.Algebra.PointTopology.Smooth.Chart`, using
`ImplicitFunctionData.levelSetChart` as its formal basis.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §4, p. 11.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, vol. 1,
  second edition, §3.1.
-/

public section

namespace TauCeti

open MvPolynomial

variable {K ι σ : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  (p : σ → MvPolynomial ι K) {m : σ → ι}

section Fintype

variable [Fintype ι] [Fintype σ] [Fintype ↥(Set.range m)ᶜ]

/-- The implicit function data for the equations and complementary coordinate projection. -/
private noncomputable abbrev implicitData [DecidableEq σ] (hm : Function.Injective m) (x : ι → K)
    (hJ : IsUnit (((jacobiMatrixAt p x).submatrix id m).det)) :
    ImplicitFunctionData K (ι → K) (σ → K) (↥(Set.range m)ᶜ → K) := by
  classical
  let π : (ι → K) →L[K] ↥(Set.range m)ᶜ → K := ContinuousLinearMap.funLeft K K Subtype.val
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
        rw [ContinuousLinearMap.toLinearMap_funLeft, LinearMap.range_eq_top]
        exact LinearMap.funLeft_surjective_of_injective K K _ Subtype.val_injective
      isCompl_ker := by
        rw [hD, ContinuousLinearMap.toLinearMap_funLeft]
        exact Matrix.isCompl_ker_mulVecLin_ker_funLeft _ hm hJ }

end Fintype

/-- At a common zero of polynomial equations, an invertible square Jacobian minor using every
equation row gives a chart on the zero set, projecting onto the coordinates outside its columns. -/
theorem exists_openPartialHomeomorph_zeroSet [Finite ι] [Fintype σ] [DecidableEq σ]
    (x : {y : ι → K | (fun j ↦ eval y (p j)) = 0})
    (hJ : IsUnit (((jacobiMatrixAt p x.val).submatrix id m).det)) :
    ∃ e : OpenPartialHomeomorph {y : ι → K | (fun j ↦ eval y (p j)) = 0}
        (↥(Set.range m)ᶜ → K),
      x ∈ e.source ∧ ∀ y i, e y i = y.val i := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite ↥(Set.range m)ᶜ
  have hm : Function.Injective m := by
    intro i j hij
    by_contra hne
    exact hJ.ne_zero (Matrix.det_zero_of_column_eq hne (fun a ↦ by
      simp only [Matrix.submatrix_apply, hij]))
  let d := implicitData p hm x.val hJ
  refine ⟨d.levelSetChart x.property, d.mem_levelSetChart_source x.property, fun y i ↦ ?_⟩
  simp [d, implicitData]

end TauCeti

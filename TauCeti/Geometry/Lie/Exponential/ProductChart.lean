/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph

/-!
# Complementary exponential-product charts

Let `p` and `q` be complementary linear subspaces of the Lie algebra of a finite-dimensional
real Lie group. The map

`(X, Y) ↦ lieExp X * lieExp Y`

is a local diffeomorphism at `(0, 0)`. Its derivative there is the addition equivalence
`p × q ≃ Lie(G)`, transported to the model space of the group.

This is the local product chart used to compare a subgroup with a linear complement of its
infinitesimal directions. The result is stated for arbitrary complementary subspaces, independently
of any subgroup.

## Main definitions

* `Submodule.lieExpMul`: the product of the exponentials of two linear coordinates.

## Main results

* `Submodule.mfderiv_lieExpMul_apply_zero`: the derivative is addition in Lie-algebra
  coordinates.
* `Submodule.isLocalDiffeomorphAt_lieExpMul_zero_of_isCompl`: complementary subspaces give a
  local exponential-product chart at the identity.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
-/

public section

noncomputable section

namespace Submodule

open Function Manifold
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree

/-- The product of the Lie exponentials of coordinates in two linear subspaces of a Lie
algebra. -/
def lieExpMul (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) : G :=
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  lieExp (I := I) (G := G) (z.1 : LeftInvariantDerivation I G) *
    lieExp (I := I) (G := G) (z.2 : LeftInvariantDerivation I G)

/-- The exponential-product map evaluates by exponentiating its two coordinates in order. -/
@[simp]
theorem lieExpMul_apply (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    lieExpMul (I := I) (G := G) p q z =
      lieExp (z.1 : LeftInvariantDerivation I G) *
        lieExp (z.2 : LeftInvariantDerivation I G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  dsimp only
  rfl

/-- The exponential-product map on two linear subspaces is smooth. -/
theorem contMDiff_lieExpMul (p q : Submodule ℝ (LeftInvariantDerivation I G)) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
      finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
    ContMDiff (modelWithCornersSelf ℝ (p × q)) I ∞
      (lieExpMul (I := I) (G := G) p q) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  dsimp only
  have hexp := contMDiff_lieExp (I := I) (G := G)
  have hp : ContMDiff (modelWithCornersSelf ℝ (p × q))
      (modelWithCornersSelf ℝ (LeftInvariantDerivation I G)) ∞
      (fun z : p × q => (z.1 : LeftInvariantDerivation I G)) :=
    p.subtypeL.contDiff.comp contDiff_fst |>.contMDiff
  have hq : ContMDiff (modelWithCornersSelf ℝ (p × q))
      (modelWithCornersSelf ℝ (LeftInvariantDerivation I G)) ∞
      (fun z : p × q => (z.2 : LeftInvariantDerivation I G)) :=
    q.subtypeL.contDiff.comp contDiff_snd |>.contMDiff
  exact ((hexp.comp hp).mul (hexp.comp hq)).congr fun _ => (lieExpMul_apply p q _).symm

private theorem fderiv_extChartAt_lieExpMul_zero_apply
    (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
      finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
    fderiv ℝ
        (fun w : p × q => extChartAt I (1 : G) (lieExpMul (I := I) (G := G) p q w)) 0 z =
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G) ((z.1 : LeftInvariantDerivation I G) + z.2) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  dsimp only
  let T := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  let F : p × q → E := fun w => extChartAt I (1 : G) (lieExpMul (I := I) (G := G) p q w)
  -- Differentiate the chart representative along the line through the prescribed direction.
  have hsource : lieExpMul (I := I) (G := G) p q 0 ∈ (chartAt H (1 : G)).source := by
    simp
  have hFdiff : DifferentiableAt ℝ F 0 := by
    have hsmooth := (contMDiff_lieExpMul (I := I) (G := G) p q).contMDiffAt (x := 0)
    have hcoord := (contMDiffAt_iff_target_of_mem_source
      (f := lieExpMul (I := I) (G := G) p q) (y := (1 : G)) hsource).mp hsmooth
    rw [contMDiffAt_iff_contDiffAt] at hcoord
    exact hcoord.2.differentiableAt (by simp)
  have hscale : HasDerivAt (fun t : ℝ => t • z) z 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const z)
  have hline := hFdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hscale (by simp)
  -- Compute the same curve through the established derivative formula for two invariant
  -- exponential curves, after translating between the two Lie-algebra models.
  have hcurve := hasFDerivAt_extChartAt_mulInvariantExp_smul_mul_mulInvariantExp_smul_zero
    (I := I) (G := G) (T z.1) (T z.2)
  have hfunctions :
      (fun t : ℝ => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G)
            (t • T z.1) *
          mulInvariantExp (I := I) (G := G)
            (t • T z.2))) =
      fun t : ℝ => F (t • z) := by
    funext t
    dsimp only [F]
    rw [lieExpMul_apply]
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul_of_tower]
    rw [lieExp_eq_mulInvariantExp, lieExp_eq_mulInvariantExp]
    dsimp only [T]
    simp only [map_smul]
  have hcurve' := hcurve.hasDerivAt
  rw [hfunctions] at hcurve'
  have hderiv := hline.unique hcurve'
  -- Unfold the local abbreviations to compare the two directional derivatives in model
  -- coordinates.
  rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hderiv
  rw [map_add, leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply,
    leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply]
  exact hderiv

/-- In canonical model coordinates, the derivative of the exponential-product map at the zero
pair sends `(X, Y)` to the coordinate of `X + Y`. -/
@[simp]
theorem mfderiv_lieExpMul_apply_zero
    (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
      finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
    groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)
        (mfderiv (modelWithCornersSelf ℝ (p × q)) I
          (lieExpMul (I := I) (G := G) p q) 0
          ((NormedSpace.fromTangentSpace (0 : p × q)).symm z)) =
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G) ((z.1 : LeftInvariantDerivation I G) + z.2) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  dsimp only
  have hzero : lieExpMul (I := I) (G := G) p q 0 = 1 := by simp
  rw [hzero]
  have hdiff := (contMDiff_lieExpMul (I := I) (G := G) p q).mdifferentiableAt
    (x := 0) (by simp)
  have hsource : lieExpMul (I := I) (G := G) p q 0 ∈
      (chartAt H (1 : G)).source := by
    rw [hzero]
    exact mem_chart_source H (1 : G)
  have hext := (mdifferentiableAt_extChartAt (I := I)
    (x := (1 : G)) hsource).hasMFDerivAt
  have hcomp := hext.comp 0 hdiff.hasMFDerivAt
  have hmf := hcomp.mfderiv
  -- Read the composite derivative as the Frechet derivative of the identity-chart
  -- representative.
  simp only [Function.comp_apply] at hmf
  rw [mfderiv_eq_fderiv] at hmf
  have happly := DFunLike.congr_fun hmf
    ((NormedSpace.fromTangentSpace (0 : p × q)).symm z)
  have hfderiv := fderiv_extChartAt_lieExpMul_zero_apply (I := I) (G := G) p q z
  have hresult := happly.symm.trans hfderiv
  rw [hzero, mfderiv_extChartAt_self] at hresult
  exact hresult

/-- Complementary linear subspaces of the Lie algebra give a local product chart at the group
identity by multiplying their exponentials in order. -/
theorem isLocalDiffeomorphAt_lieExpMul_zero_of_isCompl
    (p q : Submodule ℝ (LeftInvariantDerivation I G)) (h : IsCompl p q) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
      finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ (p × q)) I ∞
      (lieExpMul (I := I) (G := G) p q) 0 := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : ContMDiffMul I 1 G := ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  dsimp only
  let ht : Submodule.IsTopCompl p q :=
    Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional
      h p.closed_of_finiteDimensional
  let e₀ : (p × q) ≃L[ℝ] E :=
    (p.prodEquivOfIsTopCompl q ht).trans
      (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G)).toContinuousLinearEquiv
  have hzero : lieExpMul (I := I) (G := G) p q 0 = 1 := by simp
  let eTarget : E ≃L[ℝ] TangentSpace I (lieExpMul (I := I) (G := G) p q 0) := by
    rw [hzero]
    exact (groupLieAlgebraEquivModelVectorSpace
      (I := I) (G := G)).symm.toContinuousLinearEquiv
  let e : TangentSpace (modelWithCornersSelf ℝ (p × q)) (0 : p × q) ≃L[ℝ]
      TangentSpace I (lieExpMul (I := I) (G := G) p q 0) :=
    (NormedSpace.fromTangentSpace (0 : p × q)).trans (e₀.trans eTarget)
  apply TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq
      (s := Set.univ) (e := e)
      (contMDiff_lieExpMul (I := I) (G := G) p q).contMDiffOn
      isOpen_univ (Set.mem_univ 0)
      (BoundarylessManifold.isInteriorPoint :
        (modelWithCornersSelf ℝ (p × q)).IsInteriorPoint (0 : p × q))
      (by simp)
  apply ContinuousLinearMap.ext
  intro z
  have hm := mfderiv_lieExpMul_apply_zero (I := I) (G := G) p q
    (NormedSpace.fromTangentSpace (0 : p × q) z)
  dsimp only at hm
  rw [ContinuousLinearEquiv.symm_apply_apply] at hm
  have hm' := congrArg
    (groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).symm hm
  have hm'' := ((groupLieAlgebraEquivModelVectorSpace
    (I := I) (G := G)).symm_apply_apply
      (mfderiv (modelWithCornersSelf ℝ (p × q)) I
        (lieExpMul (I := I) (G := G) p q) 0 z)).symm.trans hm'
  rw [hzero]
  simp only [e, eTarget, e₀]
  exact hm''.symm

end Submodule

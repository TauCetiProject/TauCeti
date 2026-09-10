/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph
-- Non-public: topological complements are used only to package the derivative as a continuous
-- linear equivalence; the public hypothesis is the algebraic condition `IsCompl`.
import Mathlib.Analysis.Normed.Module.Complemented
import TauCeti.Geometry.Lie.Interior

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

* `TauCeti.Lie.lieExpMul`: the product of the exponentials of two linear coordinates.

## Main results

* `TauCeti.Lie.mfderiv_lieExpMul_zero_apply`: the derivative is addition in Lie-algebra
  coordinates.
* `TauCeti.Lie.isLocalDiffeomorphAt_lieExpMul_zero_of_isCompl`: complementary subspaces give a
  local exponential-product chart at the identity.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
-/

public section

noncomputable section

namespace TauCeti.Lie

open Function Manifold
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G] [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree

local instance productChartContMDiffMulOne : ContMDiffMul I 1 G :=
  ContMDiffMul.of_le (m := 1) (n := ∞) (by norm_num)

local instance productChartBoundarylessManifold : BoundarylessManifold I G :=
  ContMDiffMul.boundarylessManifold

local instance finiteDimensionalLeftInvariantDerivationProductChart :
    FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- The product of the Lie exponentials of coordinates in two linear subspaces of a Lie
algebra. -/
def lieExpMul (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) : G :=
  lieExp (I := I) (G := G) (z.1 : LeftInvariantDerivation I G) *
    lieExp (I := I) (G := G) (z.2 : LeftInvariantDerivation I G)

/-- The exponential-product map evaluates by exponentiating its two coordinates in order. -/
theorem lieExpMul_apply (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) :
    lieExpMul (I := I) (G := G) p q z =
      lieExp (z.1 : LeftInvariantDerivation I G) *
        lieExp (z.2 : LeftInvariantDerivation I G) := (rfl)

/-- The exponential-product map sends the zero pair to the group identity. -/
@[simp]
theorem lieExpMul_zero (p q : Submodule ℝ (LeftInvariantDerivation I G)) :
    lieExpMul (I := I) (G := G) p q 0 = 1 := by
  simp [lieExpMul]

/-- The exponential-product map on two linear subspaces is smooth. -/
theorem contMDiff_lieExpMul (p q : Submodule ℝ (LeftInvariantDerivation I G)) :
    ContMDiff (modelWithCornersSelf ℝ (p × q)) I ∞
      (lieExpMul (I := I) (G := G) p q) := by
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
    fderiv ℝ
        (fun w : p × q => extChartAt I (1 : G) (lieExpMul (I := I) (G := G) p q w)) 0 z =
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G) ((z.1 : LeftInvariantDerivation I G) + z.2) := by
  let L := leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)
  let F : p × q → E := fun w => extChartAt I (1 : G) (lieExpMul (I := I) (G := G) p q w)
  -- Differentiate the chart representative along the line through the prescribed direction.
  have hsource : lieExpMul (I := I) (G := G) p q 0 ∈ (chartAt H (1 : G)).source := by
    rw [lieExpMul_zero]
    exact mem_chart_source H 1
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
  have hcurve := hasFDerivAt_extChartAt_mulInvariantExp_smul_mul_mulInvariantExp_smul
    (I := I) (G := G)
    (L (z.1 : LeftInvariantDerivation I G) : GroupLieAlgebra I G)
    (L (z.2 : LeftInvariantDerivation I G) : GroupLieAlgebra I G)
  have hfunctions :
      (fun t : ℝ => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G)
            (t • (L (z.1 : LeftInvariantDerivation I G) : GroupLieAlgebra I G)) *
          mulInvariantExp (I := I) (G := G)
            (t • (L (z.2 : LeftInvariantDerivation I G) : GroupLieAlgebra I G)))) =
      fun t : ℝ => F (t • z) := by
    funext t
    dsimp only [F]
    rw [lieExpMul_apply]
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul_of_tower]
    rw [lieExp_eq_mulInvariantExp, lieExp_eq_mulInvariantExp]
    simp only [map_smul]
    rw [← leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply,
      ← leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply]
    dsimp only [L]
    rfl
  have hcurve' := hcurve.hasDerivAt
  have hcurve'' : HasDerivAt (fun t : ℝ => F (t • z))
      (((1 : ℝ →L[ℝ] ℝ).smulRight
        ((show E from (L (z.1 : LeftInvariantDerivation I G) : GroupLieAlgebra I G)) +
         (show E from (L (z.2 : LeftInvariantDerivation I G) : GroupLieAlgebra I G)))) 1) 0 := by
    rw [← hfunctions]
    exact hcurve'
  have hderiv := hline.unique hcurve''
  -- Unfold the local abbreviations to compare the two directional derivatives in model
  -- coordinates.
  change fderiv ℝ F 0 z = L ((z.1 : LeftInvariantDerivation I G) + z.2)
  rw [map_add]
  simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using hderiv

/-- At the zero pair, the derivative of the exponential-product map sends `(X, Y)` to the model
coordinate of `X + Y`. -/
theorem mfderiv_lieExpMul_zero_apply
    (p q : Submodule ℝ (LeftInvariantDerivation I G)) (z : p × q) :
    mfderiv (modelWithCornersSelf ℝ (p × q)) I
        (lieExpMul (I := I) (G := G) p q) 0 z =
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G) ((z.1 : LeftInvariantDerivation I G) + z.2) := by
  rw [lieExpMul_zero]
  apply (groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).injective
  have hdiff := (contMDiff_lieExpMul (I := I) (G := G) p q).mdifferentiableAt
    (x := 0) (by simp)
  have hsource : lieExpMul (I := I) (G := G) p q 0 ∈
      (chartAt H (1 : G)).source := by
    rw [lieExpMul_zero]
    exact mem_chart_source H 1
  have hext := (mdifferentiableAt_extChartAt (I := I)
    (x := (1 : G)) hsource).hasMFDerivAt
  have hcomp := hext.comp 0 hdiff.hasMFDerivAt
  have hmf := hcomp.mfderiv
  -- Read the composite derivative as the Fréchet derivative of the identity-chart
  -- representative.
  change mfderiv (modelWithCornersSelf ℝ (p × q)) (modelWithCornersSelf ℝ E)
      (fun w : p × q => extChartAt I (1 : G) (lieExpMul (I := I) (G := G) p q w)) 0 = _
      at hmf
  rw [mfderiv_eq_fderiv] at hmf
  have happly := DFunLike.congr_fun hmf z
  have hfderiv := fderiv_extChartAt_lieExpMul_zero_apply (I := I) (G := G) p q z
  have hresult := happly.symm.trans hfderiv
  rw [lieExpMul_zero, mfderiv_extChartAt_self] at hresult
  -- The target tangent space at the identity is definitionally the model space `E`.
  change (show E from mfderiv (modelWithCornersSelf ℝ (p × q)) I
    (lieExpMul (I := I) (G := G) p q) 0 z) = _
  exact hresult

/-- Complementary linear subspaces of the Lie algebra give a local product chart at the group
identity by multiplying their exponentials in order. -/
theorem isLocalDiffeomorphAt_lieExpMul_zero_of_isCompl
    (p q : Submodule ℝ (LeftInvariantDerivation I G)) (h : IsCompl p q) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ (p × q)) I ∞
      (lieExpMul (I := I) (G := G) p q) 0 := by
  let _ : CompleteSpace (LeftInvariantDerivation I G) :=
    FiniteDimensional.complete ℝ (LeftInvariantDerivation I G)
  let ht : Submodule.IsTopCompl p q := Submodule.IsCompl.isTopCompl_of_isClosed h
    p.closed_of_finiteDimensional q.closed_of_finiteDimensional
  let e₀ : (p × q) ≃L[ℝ] E :=
    (p.prodEquivOfIsTopCompl q ht).trans
      (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
        (I := I) (G := G)).toContinuousLinearEquiv
  let e : TangentSpace (modelWithCornersSelf ℝ (p × q)) (0 : p × q) ≃L[ℝ]
      TangentSpace I (lieExpMul (I := I) (G := G) p q 0) :=
    (tangentSpaceCastModel (M := p × q) (modelWithCornersSelf ℝ (p × q))
      (0 : p × q)).trans
      (e₀.trans (tangentSpaceCastModel I
        (lieExpMul (I := I) (G := G) p q 0)).symm)
  apply TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq
      (s := Set.univ) (e := e)
      (contMDiff_lieExpMul (I := I) (G := G) p q).contMDiffOn
      isOpen_univ (Set.mem_univ 0) (by simp)
  apply ContinuousLinearMap.ext
  intro z
  let z₀ : p × q := tangentSpaceCastModel (M := p × q)
    (modelWithCornersSelf ℝ (p × q)) (0 : p × q) z
  apply (tangentSpaceCastModel I (lieExpMul (I := I) (G := G) p q 0)).injective
  simp only [e]
  have hm := mfderiv_lieExpMul_zero_apply (I := I) (G := G) p q z₀
  -- Transport both sides through the source and target tangent-space casts; the remaining
  -- equality is exactly the application formula for the complement equivalence.
  change e₀ z₀ =
    tangentSpaceCastModel I (lieExpMul (I := I) (G := G) p q 0)
      (mfderiv (modelWithCornersSelf ℝ (p × q)) I
        (lieExpMul (I := I) (G := G) p q) 0 z)
  rw [show z = z₀ by rfl, hm]
  -- Unfold the complement equivalence only after the tangent-space casts have disappeared.
  change leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G) ((p.prodEquivOfIsTopCompl q ht) z₀) =
    leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G) ((z₀.1 : LeftInvariantDerivation I G) + z₀.2)
  rw [Submodule.prodEquivOfIsTopCompl_apply]

end TauCeti.Lie

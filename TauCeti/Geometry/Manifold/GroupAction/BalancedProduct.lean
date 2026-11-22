/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Topology.Covering.BalancedProduct.Basic
public import TauCeti.Algebra.GroupAction.DiagonalOrbits
public import TauCeti.Topology.Algebra.ProperAction.Basic

import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# The smooth structure of a balanced product `P ×_K Z`

Let `K` be a finite-dimensional real Lie group acting smoothly, freely and properly on a
boundaryless manifold `P`, and smoothly on a Hausdorff boundaryless manifold `Z`. The balanced
product `P ×_K Z = TauCeti.BalancedProduct K P Z` is the quotient of `P × Z` by the diagonal
action of `K`. This action is free and proper (`TauCeti.isCancelSMul_prod`,
`TauCeti.properSMul_prod`), so by the quotient manifold theorem `P ×_K Z` is a smooth manifold of
dimension `dim P + dim Z - dim K` (`TauCeti.BalancedProduct.chartedSpace`), for which
`(p, z) ↦ [p, z]` is a smooth submersion. Smoothness of maps out of `P ×_K Z` can therefore be
checked on representatives (`TauCeti.BalancedProduct.contMDiff_iff`), and the projection
`[p, z] ↦ [z]` onto `Z ⧸ K` is smooth when `K` acts freely and properly on `Z`. It is a submersion
for every manifold structure on `Z ⧸ K` for which the orbit projection of `Z` is a submersion.

The case `P = G` of a Lie group with right translation by a closed subgroup `K` is in
`TauCeti.Geometry.Lie.Subgroup.BalancedProduct`.

## Main definitions

* `TauCeti.BalancedProduct.chartedSpace`: the charts of the quotient manifold theorem on
  `P ×_K Z`.

## Main results

* `TauCeti.BalancedProduct.isManifold`, `TauCeti.BalancedProduct.isSubmersion_quotientMk`:
  `P ×_K Z` is a smooth manifold and the projection from `P × Z` is a smooth submersion.
* `TauCeti.BalancedProduct.contMDiff_iff`: a map out of `P ×_K Z` is smooth exactly when its
  composite with the projection is.
* `TauCeti.BalancedProduct.contMDiff_orbitProj`: the projection onto `Z ⧸ K` is smooth.
* `TauCeti.BalancedProduct.isSubmersion_orbitProj`: the projection onto `Z ⧸ K` is a submersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.10 (the
  quotient manifold theorem).
-/

public section

noncomputable section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti.BalancedProduct

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [FiniteDimensional ℝ EK]
  [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK} {K : Type*} [Group K] [TopologicalSpace K]
  [ChartedSpace HK K] [LieGroup IK ∞ K]
  {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless] {P : Type*}
  [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P] [MulAction K P]
  [ContMDiffSMul IK IP ∞ K P] [ProperSMul K P] [IsCancelSMul K P]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] {Z : Type*}
  [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z] [MulAction K Z]
  [ContMDiffSMul IK IZ ∞ K Z]

omit [FiniteDimensional ℝ EK] [LieGroup IK ∞ K] [FiniteDimensional ℝ EP]
  [IP.Boundaryless] [ChartedSpace HP P] [IsManifold IP ∞ P] [ContMDiffSMul IK IP ∞ K P]
  [IsCancelSMul K P] [FiniteDimensional ℝ EZ] [IZ.Boundaryless] [IsManifold IZ ∞ Z] in
include IK IZ in
/-- The hypotheses of the quotient manifold theorem for the diagonal action of `K` on `P × Z`,
other than those found by instance search. -/
private theorem quotient_hypotheses : ProperSMul K (P × Z) := by
  have := ContMDiffSMul.continuousSMul (I := IK) (I' := IZ) (G := K) (M := Z) ∞
  infer_instance

variable (IK K IP P IZ Z) in
/-- **The charts of the balanced product** `P ×_K Z`: the slice charts of the quotient manifold
theorem `ProperSMul.orbitRelQuotientChartedSpace` for the free and proper diagonal action of `K`
on `P × Z`, modelled on `ℝ^(dim P + dim Z - dim K)`. -/
@[instance_reducible]
def chartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace EK (EP × EZ)) (BalancedProduct K P Z) :=
  haveI := quotient_hypotheses (IK := IK) (IZ := IZ) (K := K) (P := P) (Z := Z)
  ProperSMul.orbitRelQuotientChartedSpace IK K (IP.prod IZ) (P × Z)

/-- **The balanced product is a smooth manifold**, for the charts
`TauCeti.BalancedProduct.chartedSpace`. -/
theorem isManifold :
    letI := chartedSpace IK K IP P IZ Z
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EP × EZ)) ∞ (BalancedProduct K P Z) := by
  have := quotient_hypotheses (IK := IK) (IZ := IZ) (K := K) (P := P) (Z := Z)
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- The projection `P × Z → P ×_K Z` is a smooth submersion. -/
theorem isSubmersion_quotientMk :
    letI := chartedSpace IK K IP P IZ Z
    IsSubmersion (IP.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EP × EZ)) ∞
      (Quotient.mk (MulAction.orbitRel K (P × Z))) := by
  have := quotient_hypotheses (IK := IK) (IZ := IZ) (K := K) (P := P) (Z := Z)
  exact ProperSMul.isSubmersion_quotientMk

/-- Smoothness descends from `P × Z` to `P ×_K Z`: a map out of the balanced product is `C^m`,
for `m ≤ ∞`, exactly when its composite with the projection is. -/
theorem contMDiff_iff {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N]
    [ChartedSpace HN N] {m : ℕ∞ω} (hm : m ≤ ∞) {f : BalancedProduct K P Z → N} :
    letI := chartedSpace IK K IP P IZ Z
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EP × EZ)) IN m f ↔
      ContMDiff (IP.prod IZ) IN m (f ∘ Quotient.mk (MulAction.orbitRel K (P × Z))) := by
  let _ := chartedSpace IK K IP P IZ Z
  exact ((isSubmersion_quotientMk (IK := IK) (IP := IP) (IZ := IZ)).contMDiff_comp_iff
    Quotient.mk_surjective hm).symm

/-- **The projection onto `Z ⧸ K` is smooth** when `K` acts freely and properly on `Z`, for the
charts `ProperSMul.orbitRelQuotientChartedSpace` of the quotient manifold theorem on `Z ⧸ K`. -/
theorem contMDiff_orbitProj [ProperSMul K Z] [IsCancelSMul K Z] :
    letI := chartedSpace IK K IP P IZ Z
    letI := ProperSMul.orbitRelQuotientChartedSpace IK K IZ Z
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EP × EZ))
      𝓘(ℝ, ProperSMul.QuotientModelSpace EK EZ) ∞
      (orbitProj : BalancedProduct K P Z → MulAction.orbitRel.Quotient K Z) := by
  let _ := chartedSpace IK K IP P IZ Z
  let _ := ProperSMul.orbitRelQuotientChartedSpace IK K IZ Z
  rw [contMDiff_iff (IK := IK) (IP := IP) (IZ := IZ) le_rfl]
  have hcomp : orbitProj ∘ Quotient.mk (MulAction.orbitRel K (P × Z)) =
      Quotient.mk (MulAction.orbitRel K Z) ∘ Prod.snd :=
    funext fun x ↦ orbitProj_mk x.1 x.2
  rw [hcomp]
  exact (ProperSMul.contMDiff_quotientMk (I := IK)).comp (contMDiff_snd (I := IP) (M := P))

/-- **The projection onto `Z ⧸ K` is a smooth submersion** for every manifold structure on `Z ⧸ K`
for which the orbit projection `Z → Z ⧸ K` is a submersion, such as the charts of the quotient
manifold theorem when `K` acts freely and properly on `Z` (`ProperSMul.isSubmersion_quotientMk`).
Its composite with the projection from `P × Z` is the submersion `(p, z) ↦ [z]`. -/
theorem isSubmersion_orbitProj {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
    [FiniteDimensional ℝ EQ] [TopologicalSpace HQ] {JQ : ModelWithCorners ℝ EQ HQ}
    [ChartedSpace HQ (MulAction.orbitRel.Quotient K Z)]
    [IsManifold JQ ∞ (MulAction.orbitRel.Quotient K Z)]
    (hq : IsSubmersion IZ JQ ∞ (Quotient.mk (MulAction.orbitRel K Z))) :
    letI := chartedSpace IK K IP P IZ Z
    IsSubmersion 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EP × EZ)) JQ ∞
      (orbitProj : BalancedProduct K P Z → MulAction.orbitRel.Quotient K Z) := by
  let _ := chartedSpace IK K IP P IZ Z
  have := isManifold (IK := IK) (IP := IP) (IZ := IZ) (K := K) (P := P) (Z := Z)
  have hπ := isSubmersion_quotientMk (IK := IK) (IP := IP) (IZ := IZ) (K := K) (P := P) (Z := Z)
  have hcomp : orbitProj ∘ Quotient.mk (MulAction.orbitRel K (P × Z)) =
      Quotient.mk (MulAction.orbitRel K Z) ∘ Prod.snd :=
    funext fun x ↦ orbitProj_mk x.1 x.2
  have hsnd : ContMDiff (IP.prod IZ) IZ ∞ (Prod.snd : P × Z → Z) := contMDiff_snd
  have hO : ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EP × EZ)) JQ ∞
      (orbitProj : BalancedProduct K P Z → MulAction.orbitRel.Quotient K Z) := by
    rw [contMDiff_iff (IK := IK) (IP := IP) (IZ := IZ) le_rfl, hcomp]
    exact hq.contMDiff.comp hsnd
  -- `orbitProj ∘ π = π_Z ∘ Prod.snd` is a submersion, as its differentials are surjective.
  have hZ : IsSubmersion (IP.prod IZ) JQ ∞
      (Quotient.mk (MulAction.orbitRel K Z) ∘ (Prod.snd : P × Z → Z)) := by
    refine ((hq.contMDiff.comp hsnd).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      fun x ↦ ?_).isSubmersion
    rw [mfderiv_comp x (hq.contMDiff.mdifferentiableAt (by simp))
      (hsnd.mdifferentiableAt (by simp)), mfderiv_snd]
    exact (hq.surjective_mfderiv (by simp) x.2).comp fun v ↦ ⟨(0, v), rfl⟩
  rw [← hcomp] at hZ
  exact hZ.of_comp hπ.contMDiff Quotient.mk_surjective hO (by simp)

end TauCeti.BalancedProduct

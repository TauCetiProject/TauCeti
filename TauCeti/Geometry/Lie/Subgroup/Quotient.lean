/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Lie.Basic
import TauCeti.Geometry.Manifold.Algebra.LieGroup

/-!
# Homogeneous spaces `G ⧸ K` of Lie groups

Let `K` be a closed subgroup of a finite-dimensional real Lie group `G`. By Cartan's
closed-subgroup theorem (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`) `K` is a Lie group
modelled on its Lie algebra `𝔨 = TauCeti.Lie.lieSubalgebraOfSubgroup K`. Its action on `G` by
right multiplication, `g ↦ g * k`, is smooth, free and proper, and its orbits are the left cosets
`g K`. The quotient manifold theorem (`ProperSMul.instIsManifoldOrbitRelQuotient`) therefore makes
the coset space `G ⧸ K` a smooth manifold of dimension `dim G - dim 𝔨` for which the projection
`G → G ⧸ K` is a smooth submersion.

Mathlib's coset space `G ⧸ K` is by definition the orbit space of the subgroup `K.op` of `Gᵐᵒᵖ`,
acting on `G` by `MulOpposite.op k • g = g * k`. So the acting group is `K.op`, which this file
charts by pulling back the charts of `K` along the continuous isomorphism
`K.op ≃ₜ* K`, `a ↦ (MulOpposite.unop a)⁻¹`. This is the left action `k • g = g * k⁻¹` of `K` on `G`,
transported to `K.op`.

## Main definitions

* `Subgroup.opChartedSpace`: the charts on `K.op` pulled back from the closed-subgroup charts
  of `K`.
* `Subgroup.quotientChartedSpace`: the slice charts on `G ⧸ K`.

## Main results

* `Subgroup.lieGroup_op`, `Subgroup.contMDiffSMul_op`: `K.op` is a Lie group acting smoothly on
  `G` by right multiplication.
* `Subgroup.instIsManifoldQuotient`: `G ⧸ K` is a smooth manifold.
* `Subgroup.isSubmersion_quotientMk`: the projection `G → G ⧸ K` is a smooth submersion; so a map
  out of `G ⧸ K` is smooth exactly when its composite with the projection is
  (`Manifold.IsSubmersion.contMDiff_comp_iff`).
* `Subgroup.ker_mfderiv_quotientMk`: the kernel of the differential of the projection at `g` is
  the orbit tangent space of the right action of `K` at `g`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.17.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §10.5.
-/

public section

noncomputable section

open Manifold MulOpposite TauCeti TauCeti.Lie
open scoped ContDiff Manifold

namespace Subgroup

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  (K : Subgroup G) [IsClosed (K : Set G)]

/-- The continuous isomorphism `K.op ≃ₜ* K`, `a ↦ (MulOpposite.unop a)⁻¹`, along which `K.op` is
charted. -/
private def opInvEquiv : K.op ≃ₜ* K :=
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  { toFun a := ⟨(unop (a : Gᵐᵒᵖ))⁻¹, K.inv_mem a.2⟩
    invFun k := ⟨op (k : G)⁻¹, K.inv_mem k.2⟩
    left_inv a := by ext; simp
    right_inv k := by ext; simp
    map_mul' a b := by ext; simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- The charts on `K.op` for a closed subgroup `K` of a Lie group: the closed-subgroup charts of
`K` (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`), modelled on its Lie algebra, pulled back
along `a ↦ (MulOpposite.unop a)⁻¹`. -/
@[instance_reducible]
def opChartedSpace :
    ChartedSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule K.op :=
  letI := (EmbeddedLieSubgroupData.ofIsClosed (I := I) (K := K) ‹_›).chartedSpace
  (opInvEquiv I K).toHomeomorph.pullbackChartedSpace

/-- The closed-subgroup data of `K` chosen by `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`. -/
private abbrev data :
    EmbeddedLieSubgroupData I K (lieSubalgebraOfSubgroup (I := I) K).toSubmodule :=
  EmbeddedLieSubgroupData.ofIsClosed (I := I) (K := K) ‹_›

/-- The map `a ↦ (MulOpposite.unop a)⁻¹` from `K.op` to `K` is smooth for `Subgroup.opChartedSpace`
and the closed-subgroup charts of `K`. -/
private theorem contMDiff_opInvEquiv :
    letI := opChartedSpace I K
    letI := (data I K).chartedSpace
    ContMDiff 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule)
      𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞ (opInvEquiv I K) := by
  let _ := opChartedSpace I K
  let _ := (data I K).chartedSpace
  let _ := (data I K).lieGroup
  have h := ((opInvEquiv I K).toHomeomorph.pullbackDiffeomorph
    𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞).contMDiff
  rw [Homeomorph.coe_pullbackDiffeomorph] at h
  exact h

/-- For a closed subgroup `K` of a Lie group, `K.op` is a Lie group for `Subgroup.opChartedSpace`.
-/
theorem lieGroup_op :
    letI := opChartedSpace I K
    LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞ K.op := by
  let _ := (data I K).chartedSpace
  let _ := (data I K).lieGroup
  exact (opInvEquiv I K).lieGroup_pullbackChartedSpace

/-- The right multiplication action `MulOpposite.op k • g = g * k` of a closed subgroup `K` on a
Lie group `G` is smooth for `Subgroup.opChartedSpace`. -/
theorem contMDiffSMul_op :
    letI := opChartedSpace I K
    ContMDiffSMul 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I ∞ K.op G := by
  let _ := opChartedSpace I K
  let _ := (data I K).chartedSpace
  refine ⟨?_⟩
  have hv := (data I K).contMDiff_subtypeVal.comp (contMDiff_opInvEquiv I K)
  have h : (fun p : K.op × G ↦ p.1 • p.2) =
      fun p ↦ p.2 * ((opInvEquiv I K p.1 : K) : G)⁻¹ := by
    funext p
    simp [opInvEquiv, Subgroup.smul_def]
  rw [h]
  exact contMDiff_snd.mul (hv.comp contMDiff_fst).inv

omit [TopologicalSpace G] [T2Space G] [IsClosed (K : Set G)] in
/-- The right multiplication action of a subgroup on its group is free. -/
private theorem isCancelSMul_op : IsCancelSMul K.op G :=
  isCancelSMul_iff_eq_one_of_smul_eq.2 fun a g h ↦ by
    ext
    simpa [Subgroup.smul_def] using h

variable (G) in
/-- **The charts of the homogeneous space `G ⧸ K`.** For a closed subgroup `K` of a
finite-dimensional real Lie group `G` with boundaryless model, the coset space `G ⧸ K` is the orbit
space of the free proper smooth right action of `K`, charted by transverse slices
(`ProperSMul.orbitRelQuotientChartedSpace`). The model is `ℝ^(dim G - dim 𝔨)`, for `𝔨` the Lie
algebra of `K`. -/
@[instance_reducible]
def quotientChartedSpace [I.Boundaryless] :
    ChartedSpace
      (ProperSMul.QuotientModelSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule E)
      (G ⧸ K) :=
  letI := opChartedSpace I K
  haveI := lieGroup_op I K
  haveI := contMDiffSMul_op I K
  haveI := isCancelSMul_op K
  haveI := topologicalGroup_of_lieGroup I ∞ (G := G)
  ProperSMul.orbitRelQuotientChartedSpace
    𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) K.op I G

variable [I.Boundaryless]

/-- **Homogeneous spaces are manifolds.** For a closed subgroup `K` of a finite-dimensional real
Lie group `G` with boundaryless model, the coset space `G ⧸ K` is a smooth manifold for the slice
charts `Subgroup.quotientChartedSpace`. -/
instance instIsManifoldQuotient :
    letI := quotientChartedSpace I G K
    IsManifold
      𝓘(ℝ, ProperSMul.QuotientModelSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule E) ∞
      (G ⧸ K) := by
  let _ := opChartedSpace I K
  have := lieGroup_op I K
  have := contMDiffSMul_op I K
  have := isCancelSMul_op K
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- **The projection `G → G ⧸ K` is a smooth submersion** for the slice charts on `G ⧸ K`. In
particular a map out of `G ⧸ K` is smooth exactly when its composite with the projection is
(`Manifold.IsSubmersion.contMDiff_comp_iff`). -/
theorem isSubmersion_quotientMk :
    letI := quotientChartedSpace I G K
    IsSubmersion I
      𝓘(ℝ, ProperSMul.QuotientModelSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule E) ∞
      (QuotientGroup.mk : G → G ⧸ K) := by
  let _ := opChartedSpace I K
  have := lieGroup_op I K
  have := contMDiffSMul_op I K
  have := isCancelSMul_op K
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact ProperSMul.isSubmersion_quotientMk

/-- **The projection `G → G ⧸ K` is smooth** for the slice charts on `G ⧸ K`. -/
theorem contMDiff_quotientMk :
    letI := quotientChartedSpace I G K
    ContMDiff I
      𝓘(ℝ, ProperSMul.QuotientModelSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule E) ∞
      (QuotientGroup.mk : G → G ⧸ K) := by
  let _ := quotientChartedSpace I G K
  exact (isSubmersion_quotientMk I K).contMDiff

omit [I.Boundaryless] in
/-- The map `MulOpposite.op k ↦ k` from `K.op` to `K` has surjective differential at `1`: it has
the smooth right inverse `k ↦ MulOpposite.op k`. -/
private theorem range_mfderiv_unop :
    letI := opChartedSpace I K
    letI := (data I K).chartedSpace
    (mfderiv 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule)
      𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule)
      (fun a : K.op ↦ (opInvEquiv I K a)⁻¹) 1).range = ⊤ := by
  let _ := opChartedSpace I K
  let _ := (data I K).chartedSpace
  let _ := (data I K).lieGroup
  have := lieGroup_op I K
  have hφ := (contMDiff_opInvEquiv I K).inv
  have hψ : ContMDiff 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule)
      𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞
      (fun k : K ↦ (opInvEquiv I K).symm k⁻¹) := by
    have h := ((opInvEquiv I K).toHomeomorph.pullbackDiffeomorph
      𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞).symm.contMDiff
    rw [Homeomorph.coe_pullbackDiffeomorph_symm] at h
    exact h.comp (contMDiff_inv _ _)
  let Φ : K.op ≃ₘ^∞⟮𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule),
      𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule)⟯ K :=
    { toEquiv := (opInvEquiv I K).toEquiv.trans (Equiv.inv K)
      contMDiff_toFun := hφ
      contMDiff_invFun := hψ }
  obtain ⟨L, hL⟩ := Φ.isInvertible_mfderiv (by simp) (x := 1)
  rw [LinearMap.range_eq_top, ContinuousLinearMap.coe_coe]
  exact hL ▸ L.surjective

/-- **The vertical directions of `G → G ⧸ K` are the left translates of `K`'s tangent space.** The
kernel of the differential at `g` of the projection is the image of the differential at `1` of
`k ↦ g * k` on `K`, for the closed-subgroup charts of `K`. -/
theorem ker_mfderiv_quotientMk (g : G) :
    letI := quotientChartedSpace I G K
    letI := (EmbeddedLieSubgroupData.ofIsClosed (I := I) (K := K) ‹_›).chartedSpace
    (mfderiv I
      𝓘(ℝ, ProperSMul.QuotientModelSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule E)
      (QuotientGroup.mk : G → G ⧸ K) g).ker =
      (mfderiv 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I
        (fun k : K ↦ g * k) 1).range := by
  let _ := opChartedSpace I K
  let _ := (data I K).chartedSpace
  let _ := (data I K).lieGroup
  have := lieGroup_op I K
  have := contMDiffSMul_op I K
  have := isCancelSMul_op K
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  rw [show (QuotientGroup.mk : G → G ⧸ K) = Quotient.mk (MulAction.orbitRel K.op G) from rfl,
    ProperSMul.ker_mfderiv_quotientMk, InfinitesimalAction.orbitTangent_eq_range]
  have heval : (InfinitesimalAction.fundamental
      𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) K.op I G).eval g =
      (mfderiv 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I
        (fun a : K.op ↦ a • g) 1).toLinearMap := by
    ext ξ
    rw [InfinitesimalAction.eval_apply, InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_apply]
    rfl
  have hL : ContMDiff 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I ∞
      (fun k : K ↦ g * (k : G)) :=
    contMDiff_const.mul (data I K).contMDiff_subtypeVal
  -- The orbit map `a ↦ a • g` of `K.op` is `k ↦ g * k` after `a ↦ MulOpposite.unop a`.
  have key : ∀ o : K.op → G, o = (fun k : K ↦ g * (k : G)) ∘ (fun a ↦ (opInvEquiv I K a)⁻¹) →
      ∀ y, (opInvEquiv I K 1)⁻¹ = y →
      (mfderiv 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I o 1).range =
        (mfderiv 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I
          (fun k : K ↦ g * (k : G)) y).range := by
    rintro o rfl y rfl
    rw [mfderiv_comp (1 : K.op) (hL.mdifferentiableAt (by simp))
      ((contMDiff_opInvEquiv I K).inv.mdifferentiableAt (by simp)),
      ContinuousLinearMap.toLinearMap_comp,
      LinearMap.range_comp_of_range_eq_top _ (range_mfderiv_unop I K)]
  rw [heval]
  exact key _ (by funext a; simp [opInvEquiv, Subgroup.smul_def]) 1 (by simp)

end Subgroup

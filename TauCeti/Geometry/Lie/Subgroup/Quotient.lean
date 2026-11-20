/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
public import TauCeti.Geometry.Lie.InvariantVectorField.Distribution
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.Algebra.Group.Quotient.RightRel
import TauCeti.Geometry.Lie.IntegralCurve
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Homogeneous spaces of Lie groups

Let `K` be a closed subgroup of a finite-dimensional real Lie group `G` with boundaryless model.
By the closed-subgroup theorem `K` is an embedded Lie subgroup, modelled on its Lie algebra `𝔨`
(`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`). This file makes the coset space `G ⧸ K` a
smooth manifold of dimension `dim G - dim K`, the **homogeneous space** of `G` by `K`:

* the charts (`Subgroup.quotientChartedSpaceOfIsClosed`) are modelled on
  `ℝ^(dim G - dim K)` and form a smooth manifold (`Subgroup.isManifold_quotientOfIsClosed`);
* the projection `G → G ⧸ K` is a smooth submersion (`Subgroup.isSubmersion_quotientMk`), so a
  map out of `G ⧸ K` is smooth exactly when its composite with the projection is;
* its vertical directions at `g` are the tangent space at `g` of the coset `g K`, the image of the
  differential of `k ↦ g k` at the identity of `K` (`Subgroup.ker_mfderiv_quotientMk`), that is,
  the left translate of the Lie algebra of `K`
  (`Subgroup.ker_mfderiv_quotientMk_eq_mulInvariantDistribution`);
* `G` acts smoothly on `G ⧸ K` by left multiplication (`Subgroup.contMDiffSMul_quotientOfIsClosed`).

The charts come from the quotient manifold theorem
(`ProperSMul.instIsManifoldOrbitRelQuotient`) for the action of `K` on `G` by left multiplication,
which is free, proper because `K` is closed, and smooth. Its orbits are the right cosets `K g`.
Inversion carries them to the left cosets, and Mathlib's bijection between the two coset spaces is
a homeomorphism (`QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel`); the charts of `G ⧸ K`
are pulled back along its inverse (`Homeomorph.pullbackChartedSpace`). The charts are a definition
rather than an instance, since their model depends on the closedness of `K`, which instance search
cannot supply.

Homogeneous spaces of this kind include the coadjoint orbits `G ⧸ G_ν` of a Lie group, whose
Kirillov–Kostant–Souriau forms make them symplectic manifolds, and the flag manifolds `K ⧸ T` of a
compact Lie group.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.17 (the
  homogeneous space construction theorem, proved from the quotient manifold theorem for the action
  of the closed subgroup by translations).
-/

public section

noncomputable section

open Function Set Manifold Module TauCeti
open scoped ContDiff Manifold

namespace Subgroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {K : Subgroup G}

variable (I K) in
/-- The model space `ℝ^(dim G - dim K)` of the homogeneous space `G ⧸ K`, where `dim K` is the
dimension of the Lie algebra of `K`. -/
abbrev QuotientModelSpace : Type :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  ProperSMul.QuotientModelSpace (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule E

/-! ### The right coset space -/

variable (I) in
/-- The charts of the quotient manifold theorem on the right coset space `K \ G`, the orbit space
of the action of `K` on `G` by left multiplication. -/
@[instance_reducible]
private def rightChartedSpace (hK : IsClosed (K : Set G)) :
    ChartedSpace (QuotientModelSpace I K)
      (Quotient (QuotientGroup.rightRel K)) :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  letI := d.chartedSpace
  letI := d.lieGroup
  haveI := d.contMDiffSMul
  haveI : IsClosed (K : Set G) := hK
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  ProperSMul.orbitRelQuotientChartedSpace
    𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule) K I G

variable (I) in
/-- By the quotient manifold theorem, the charts of the right coset space `K \ G` form a smooth
manifold, and the projection `G → K \ G` is a smooth submersion. -/
private theorem isManifold_and_isSubmersion_right (hK : IsClosed (K : Set G)) :
    letI := rightChartedSpace I hK
    IsManifold 𝓘(ℝ, QuotientModelSpace I K) ∞ (Quotient (QuotientGroup.rightRel K)) ∧
      IsSubmersion I 𝓘(ℝ, QuotientModelSpace I K) ∞ (Quotient.mk (QuotientGroup.rightRel K)) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  let _ := d.chartedSpace
  let _ := d.lieGroup
  have := d.contMDiffSMul
  have : IsClosed (K : Set G) := hK
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact ⟨ProperSMul.instIsManifoldOrbitRelQuotient, ProperSMul.isSubmersion_quotientMk⟩

/-! ### The homogeneous space -/

variable (I) in
/-- **The charts of the homogeneous space** `G ⧸ K` of a closed subgroup `K`, modelled on
`ℝ^(dim G - dim K)`. They are the charts of the quotient manifold theorem on the right coset space
`K \ G`, pulled back to `G ⧸ K` along the homeomorphism `[g] ↦ [g⁻¹]`. -/
@[instance_reducible]
def quotientChartedSpaceOfIsClosed (hK : IsClosed (K : Set G)) :
    ChartedSpace (QuotientModelSpace I K)
      (G ⧸ K) :=
  letI := rightChartedSpace I hK
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  (QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel K).symm.pullbackChartedSpace

/-- **The homogeneous space of a closed subgroup is a smooth manifold**, for the charts
`Subgroup.quotientChartedSpaceOfIsClosed`. -/
theorem isManifold_quotientOfIsClosed (hK : IsClosed (K : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hK
    IsManifold 𝓘(ℝ, QuotientModelSpace I K) ∞ (G ⧸ K) :=
  letI := rightChartedSpace I hK
  haveI := (isManifold_and_isSubmersion_right I hK).1
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  (QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel K).symm.pullback_isManifold _ _

/-- **The projection onto the homogeneous space is a smooth submersion.** It is the projection
onto the right coset space, a submersion by the quotient manifold theorem, after inversion of `G`
and the homeomorphism `K \ G ≃ₜ G ⧸ K`, both local diffeomorphisms. -/
theorem isSubmersion_quotientMk (hK : IsClosed (K : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hK
    IsSubmersion I 𝓘(ℝ, QuotientModelSpace I K) ∞
      (QuotientGroup.mk : G → G ⧸ K) := by
  let _ := rightChartedSpace I hK
  let _ := quotientChartedSpaceOfIsClosed I hK
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := (isManifold_and_isSubmersion_right I hK).1
  have := isManifold_quotientOfIsClosed (I := I) hK
  -- The homeomorphism `K \ G ≃ₜ G ⧸ K` is a diffeomorphism for the pulled-back charts.
  have he := ((QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel K).symm.pullbackDiffeomorph
    𝓘(ℝ, QuotientModelSpace I K) ∞).symm.isLocalDiffeomorph
  rw [Homeomorph.coe_pullbackDiffeomorph_symm, Homeomorph.symm_symm] at he
  have hF := (isManifold_and_isSubmersion_right I hK).2.isSubmersionOfComplement_complement
  -- The projection is inversion of `G`, then the projection onto `K \ G`, then the homeomorphism.
  have hmk : (QuotientGroup.mk : G → G ⧸ K) =
      QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel K ∘
        (Quotient.mk (QuotientGroup.rightRel K) ∘ Lie.invDiffeomorph I ∞ G) :=
    funext fun g ↦ by
      rw [comp_apply, comp_apply, Lie.invDiffeomorph_apply,
        QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel_mk, inv_inv]
  refine (isSubmersionOfComplement_iff
    (F := (isManifold_and_isSubmersion_right I hK).2.complement).2 fun g ↦ ?_).isSubmersion
  rw [hmk]
  exact (he _).comp_isSubmersionAtOfComplement
    (((Lie.invDiffeomorph I ∞ G).isLocalDiffeomorph g).isSubmersionAtOfComplement_comp
      (isSubmersionOfComplement_iff.1 hF _))

/-- The projection onto the homogeneous space is smooth. -/
theorem contMDiff_quotientMk (hK : IsClosed (K : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ContMDiff I 𝓘(ℝ, QuotientModelSpace I K) ∞
      (QuotientGroup.mk : G → G ⧸ K) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  exact (isSubmersion_quotientMk hK).contMDiff

variable (I K) in
/-- **The dimension of a homogeneous space.** The model space `ℝ^(dim G - dim K)` of `G ⧸ K` and
the Lie algebra `𝔨` of `K` have dimensions adding up to `dim G`. -/
theorem finrank_quotientModelSpace_add_finrank_lieSubalgebraOfSubgroup
    (hK : IsClosed (K : Set G)) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    finrank ℝ (QuotientModelSpace I K) +
      finrank ℝ (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule = finrank ℝ E := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  let _ := d.chartedSpace
  -- The differential of the inclusion embeds `𝔨` linearly in the model space `E` of `G`.
  have hle : finrank ℝ (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule ≤ finrank ℝ E :=
    LinearMap.finrank_le_finrank_of_injective (f := (mfderiv
      𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I (fun k : K ↦ (k : G))
        1).toLinearMap) (d.injective_mfderiv_subtypeVal 1)
  rw [finrank_euclideanSpace_fin]
  omega

/-- **The vertical directions of the projection onto a homogeneous space.** The kernel of the
differential at `g` of the projection `G → G ⧸ K` is the tangent space at `g` of the coset `g K`,
the image of the differential at the identity of `k ↦ g k`, for the closed-subgroup structure of
`K`. -/
theorem ker_mfderiv_quotientMk (hK : IsClosed (K : Set G)) (g : G) :
    letI := quotientChartedSpaceOfIsClosed I hK
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK).chartedSpace
    (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g).ker =
      (LinearMap.range (mfderiv 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I
        (fun k : K ↦ g * k) 1).toLinearMap : Submodule ℝ (TangentSpace I g)) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  let _ := d.chartedSpace
  have := isManifold_quotientOfIsClosed (I := I) hK
  have hπ := isSubmersion_quotientMk (I := I) hK
  -- `g = g * 1` is a regular point of the projection, which is constant on the coset `g K`, and
  -- the dimensions of `K` and `G ⧸ K` add up to that of `G`.
  have hreg : IsRegularPoint I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K)
      (g * ((1 : K) : G)) :=
    isRegularPoint_iff.2 (hπ.surjective_mfderiv (by simp) _)
  have h := hreg.range_mfderiv_eq_ker_mfderiv (g := fun k : K ↦ g * k) (y := (g : G ⧸ K))
    (.of_forall fun k ↦ QuotientGroup.eq.2 (by simp))
    (d.injective_mfderiv_mul_left_subtypeVal g 1)
    (by rw [add_comm]; exact finrank_quotientModelSpace_add_finrank_lieSubalgebraOfSubgroup I K hK)
  rw [OneMemClass.coe_one, mul_one] at h
  exact h.symm

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField in
/-- **Left-translated generators of one-parameter subgroups of `K` are vertical.** If the
one-parameter subgroup `t ↦ exp (t ξ)` lies in the closed subgroup `K`, the curve
`t ↦ g exp (t ξ)` stays in the coset `g K`, so its velocity `ξ^L(g)` at `t = 0` lies in the kernel
of the differential of the projection `G → G ⧸ K`. -/
theorem mfderiv_quotientMk_mulInvariantVectorField_eq_zero [T2Space G]
    (hK : IsClosed (K : Set G)) {ξ : GroupLieAlgebra I G}
    (hξ : ∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) ∈ K) (g : G) :
    letI := quotientChartedSpaceOfIsClosed I hK
    mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g
      (mulInvariantVectorField ξ g) = 0 := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have hπ := isSubmersion_quotientMk (I := I) hK
  -- The curve `t ↦ g exp (t ξ)` is the integral curve of `ξ^L` through `g`, and it stays in the
  -- coset `g K`, so the projection is constant along it.
  have hconst (t : ℝ) :
      (QuotientGroup.mk (mulInvariantIntegralCurve ξ g t) : G ⧸ K) = QuotientGroup.mk g := by
    rw [mulInvariantIntegralCurve_eq_const_mul]
    beta_reduce
    rw [← mulInvariantExp_smul]
    refine QuotientGroup.eq.2 ?_
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact K.inv_mem (hξ t)
  have h := ((isMIntegralCurve_mulInvariantIntegralCurve ξ g).isMIntegralCurveAt 0)
    |>.mfderiv_apply_eq_zero_of_eventuallyEq_const (J := 𝓘(ℝ, QuotientModelSpace I K))
      (hπ.contMDiff.mdifferentiableAt (by simp)) (Filter.Eventually.of_forall hconst)
  rwa [mulInvariantIntegralCurve_zero] at h

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField in
/-- **The vertical directions of the projection onto a homogeneous space are the left translates
of the Lie algebra of `K`.** The kernel of the differential at `g` of the projection `G → G ⧸ K`
is the value at `g` of the left-invariant distribution of the Lie algebra `𝔨` of the closed
subgroup `K`, read in `𝔤` by evaluating left-invariant derivations at the identity. -/
theorem ker_mfderiv_quotientMk_eq_mulInvariantDistribution [T2Space G]
    (hK : IsClosed (K : Set G)) (g : G) :
    letI := quotientChartedSpaceOfIsClosed I hK
    (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g).ker =
      mulInvariantDistribution ((Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule.map
        (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint).toLinearMap) g := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have hπ := isSubmersion_quotientMk (I := I) hK
  set e := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_mulInvariantDistribution.mp hv
    obtain ⟨X, hX, rfl⟩ := Submodule.mem_map.mp hw
    refine mfderiv_quotientMk_mulInvariantVectorField_eq_zero hK (fun t ↦ ?_) g
    rw [LinearEquiv.coe_toLinearMap, ← map_smul e, ← lieExp_eq_mulInvariantExp]
    exact Lie.lieExp_smul_mem_of_mem_lieSubalgebraOfSubgroup hK hX t
  -- Both sides have the dimension of `𝔨`: the kernel by rank-nullity for the surjective
  -- differential of the projection, the translate of `𝔨` because left translation is injective.
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g).toLinearMap
  rw [LinearMap.range_eq_top.2 (hπ.surjective_mfderiv (by simp) g), finrank_top] at hrn
  -- The tangent spaces of `G` and of `G ⧸ K` are their model spaces, so rank-nullity reads
  -- `dim (G ⧸ K) + dim ker = dim G`.
  have hker : finrank ℝ (QuotientModelSpace I K) +
      finrank ℝ (LinearMap.ker (mfderiv I 𝓘(ℝ, QuotientModelSpace I K)
        (QuotientGroup.mk : G → G ⧸ K) g).toLinearMap) = finrank ℝ E := hrn
  rw [finrank_mulInvariantDistribution, LinearEquiv.finrank_map_eq]
  exact Nat.add_left_cancel
    ((finrank_quotientModelSpace_add_finrank_lieSubalgebraOfSubgroup I K hK).trans hker.symm)

/-- **`G` acts smoothly on its homogeneous space** `G ⧸ K` by left multiplication. The action
lifts along the submersion `(g, h) ↦ (g, [h])` to the multiplication of `G`, followed by the
projection. -/
theorem contMDiffSMul_quotientOfIsClosed (hK : IsClosed (K : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hK
    ContMDiffSMul I 𝓘(ℝ, QuotientModelSpace I K) ∞ G (G ⧸ K) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have := isManifold_quotientOfIsClosed (I := I) hK
  have hπ := isSubmersion_quotientMk (I := I) hK
  refine ⟨((IsSubmersion.id.prodMap hπ).contMDiff_comp_iff
    (surjective_id.prodMap QuotientGroup.mk_surjective) le_rfl).1 ?_⟩
  -- On representatives the action is the multiplication of `G`.
  have hcomp : (fun p : G × (G ⧸ K) ↦ p.1 • p.2) ∘ Prod.map id QuotientGroup.mk =
      (QuotientGroup.mk : G → G ⧸ K) ∘ fun p : G × G ↦ p.1 * p.2 :=
    funext fun p ↦ MulAction.Quotient.smul_coe K p.1 p.2
  rw [hcomp]
  exact hπ.contMDiff.comp (contMDiff_mul I ∞)

end Subgroup


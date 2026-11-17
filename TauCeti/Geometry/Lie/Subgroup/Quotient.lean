/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.Algebra.Group.Quotient.RightRel
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
  differential of `k ↦ g k` at the identity of `K` (`Subgroup.ker_mfderiv_quotientMk`);
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

/-! ### The closed-subgroup structure of `K` -/

variable (I) in
/-- A closed subgroup `K`, with its closed-subgroup structure, acts smoothly on `G` by left
multiplication. -/
private theorem contMDiffSMul_ofIsClosed (hK : IsClosed (K : Set G)) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK).chartedSpace
    ContMDiffSMul 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I ∞ K G := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  let _ := d.chartedSpace
  exact ⟨ContMDiff.comp (contMDiff_mul I ∞) (d.contMDiff_subtypeVal.prodMap contMDiff_id)⟩

/-- The map `k ↦ g k` on a closed subgroup `K`, for its closed-subgroup structure, is
differentiable at the identity. -/
private theorem mdifferentiableAt_mul_left_subtypeVal (hK : IsClosed (K : Set G)) (g : G) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK).chartedSpace
    MDifferentiableAt 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I
      (fun k : K ↦ g * k) 1 := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  let _ := d.chartedSpace
  exact ((contMDiff_mul_left (I := I) (n := ∞)).comp d.contMDiff_subtypeVal 1).mdifferentiableAt
    (by simp)

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
  haveI := contMDiffSMul_ofIsClosed I hK
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
  have := contMDiffSMul_ofIsClosed I hK
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

/-- The differential of `k ↦ g k` at the identity of a closed subgroup `K`, for its
closed-subgroup structure, is injective: left translation by `g⁻¹` turns it into the differential
of the inclusion of `K`. -/
private theorem injective_mfderiv_mul_left_subtypeVal (hK : IsClosed (K : Set G)) (g : G) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK).chartedSpace
    Injective (mfderiv 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I
      (fun k : K ↦ g * k) 1) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  let _ := d.chartedSpace
  have hφ := mdifferentiableAt_mul_left_subtypeVal (I := I) hK g
  intro v w hvw
  apply d.injective_mfderiv_subtypeVal 1
  -- The inclusion is left translation by `g⁻¹` after `k ↦ g k`.
  have hcomp : (fun k : K ↦ (k : G)) = (g⁻¹ * ·) ∘ fun k : K ↦ g * k :=
    funext fun k ↦ by simp
  have hder (u) : mfderiv 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I
      (fun k : K ↦ (k : G)) 1 u =
        mfderiv I I (g⁻¹ * ·) (g * ((1 : K) : G))
          (mfderiv 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule) I
            (fun k : K ↦ g * k) 1 u) := by
    rw [hcomp]
    exact mfderiv_comp_apply (1 : K) mdifferentiableAt_mul_left hφ u
  rw [hder, hder, hvw]

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
    (.of_forall fun k ↦ QuotientGroup.eq.2 (by simp)) (injective_mfderiv_mul_left_subtypeVal hK g)
    (by rw [add_comm]; exact finrank_quotientModelSpace_add_finrank_lieSubalgebraOfSubgroup I K hK)
  rw [OneMemClass.coe_one, mul_one] at h
  exact h.symm

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


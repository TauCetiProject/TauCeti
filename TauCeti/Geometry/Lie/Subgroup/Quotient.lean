/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.InvariantVectorField.Distribution
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.Algebra.Group.Quotient.RightRel
import TauCeti.Geometry.Lie.RightInvariantVectorField
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
  differential of `k ↦ g k` at the identity of `K` (`Subgroup.ker_mfderiv_quotientMk`), or
  equivalently the left translate `d(L_g)(S)` of any subspace `S` of `𝔤` of dimension `dim K`
  whose one-parameter subgroups lie in `K`
  (`Subgroup.ker_mfderiv_quotientMk_eq_mulInvariantDistribution`);
* the projection sends the generators of left multiplication on `G` to those of the action on
  `G ⧸ K` (`Subgroup.mfderiv_quotientMk_fundamentalVectorField`), which therefore span every
  tangent space of `G ⧸ K` (`Subgroup.surjective_fundamentalVectorField`);
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

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

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

/-- **Left-invariant vertical directions.** If the one-parameter subgroup `t ↦ exp (t ξ)` lies in
`K`, the left-invariant vector field `ξ^L` is vertical for the projection `G → G ⧸ K`. -/
theorem mfderiv_quotientMk_mulInvariantVectorField [T2Space G] (hK : IsClosed (K : Set G))
    {ξ : GroupLieAlgebra I G} (hξ : ∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) ∈ K) (g : G) :
    letI := quotientChartedSpaceOfIsClosed I hK
    mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g
      (mulInvariantVectorField ξ g) = 0 := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  -- The curve `t ↦ g exp (t ξ)` has velocity `ξ^L(g)` at `0` and stays in the coset `g K`.
  have hL : HasMFDerivAt I I (g * ·) (mulInvariantExp (I := I) ((0 : ℝ) • ξ))
      (mfderiv I I (g * ·) 1) := by
    rw [zero_smul, mulInvariantExp_zero]
    exact ((contMDiff_mul_left (I := I) (n := ∞)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hc := hL.comp (0 : ℝ) (hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) ξ)
  have hconst : (QuotientGroup.mk : G → G ⧸ K) ∘
      ((g * ·) ∘ fun t : ℝ ↦ mulInvariantExp (I := I) (t • ξ)) = fun _ ↦ (g : G ⧸ K) :=
    funext fun t ↦ QuotientGroup.mk_mul_of_mem g (hξ t)
  have hπ : MDifferentiableAt I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g :=
    (contMDiff_quotientMk hK).mdifferentiableAt (by simp)
  have hy : ((g * ·) ∘ fun t : ℝ ↦ mulInvariantExp (I := I) (t • ξ)) 0 = g := by simp
  have h := mfderiv_comp_apply_of_eq (0 : ℝ) hπ hc.mdifferentiableAt hy (1 : ℝ)
  rw [hconst, mfderiv_const, hc.mfderiv] at h
  -- The composite applied to the unit tangent vector `1` of `ℝ` is `dπ_g (d(L_g)_1 (1 • ξ))`, and
  -- `d(L_g)_1 (1 • ξ)` is `(1 • ξ)^L(g)` by definition of the invariant vector field.
  have h' : mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g
      (mulInvariantVectorField ((1 : ℝ) • ξ) g) = 0 :=
    h.symm
  rwa [one_smul] at h'

/-- **The vertical directions of a homogeneous space as a left-invariant distribution.** Let `S` be
a subspace of `𝔤` whose one-parameter subgroups lie in `K` and whose dimension is that of the Lie
algebra of `K`. Then the kernel of the differential at `g` of the projection `G → G ⧸ K` is the
left translate `d(L_g)(S)`. -/
theorem ker_mfderiv_quotientMk_eq_mulInvariantDistribution [T2Space G]
    (hK : IsClosed (K : Set G))
    {S : Submodule ℝ (GroupLieAlgebra I G)}
    (hS : ∀ ξ ∈ S, ∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) ∈ K)
    (hdim : finrank ℝ S = finrank ℝ (Lie.lieSubalgebraOfSubgroup (I := I) K).toSubmodule)
    (g : G) :
    letI := quotientChartedSpaceOfIsClosed I hK
    (mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g).ker =
      mulInvariantDistribution S g := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  let _ := d.chartedSpace
  refine (Submodule.eq_of_le_of_finrank_eq (fun v hv ↦ ?_) ?_).symm
  · obtain ⟨ξ, hξ, rfl⟩ := mem_mulInvariantDistribution.1 hv
    exact mfderiv_quotientMk_mulInvariantVectorField hK (hS ξ hξ) g
  -- The kernel is the image of the injective differential of `k ↦ g k` on the Lie algebra of `K`.
  rw [finrank_mulInvariantDistribution, hdim, ker_mfderiv_quotientMk hK g]
  exact (LinearMap.finrank_range_of_inj (d.injective_mfderiv_mul_left_subtypeVal g 1)).symm

/-- The projection `G → G ⧸ K` sends the generator `ξ_G(g)` of the action of `G` on itself by left
multiplication to the generator `ξ_(G ⧸ K)([g])` of its action on the homogeneous space. -/
theorem mfderiv_quotientMk_fundamentalVectorField (hK : IsClosed (K : Set G)) (g : G)
    (ξ : GroupLieAlgebra I G) :
    letI := quotientChartedSpaceOfIsClosed I hK
    mfderiv I 𝓘(ℝ, QuotientModelSpace I K) (QuotientGroup.mk : G → G ⧸ K) g
        (fundamentalVectorField I ξ g) =
      fundamentalVectorField 𝓘(ℝ, QuotientModelSpace I K) ξ (g : G ⧸ K) := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  exact mfderiv_fundamentalVectorField_of_map_smul
    ((contMDiff_quotientMk hK).mdifferentiableAt (by simp))
    ((contMDiff_mul_right (I := I) (n := ∞)).mdifferentiableAt (by simp))
    (fun h ↦ (MulAction.Quotient.smul_coe K h g).symm) ξ

/-- **The generators span the tangent spaces of a homogeneous space.** Every tangent vector of
`G ⧸ K` at `x` is the value at `x` of the generator `ξ_(G ⧸ K)` of some `ξ` in the Lie algebra: the
projection `G → G ⧸ K` is a submersion, and the generators `ξ_G(g)` of left multiplication, the
right-invariant vector fields, exhaust `T_g G`. -/
theorem surjective_fundamentalVectorField (hK : IsClosed (K : Set G)) (x : G ⧸ K) :
    letI := quotientChartedSpaceOfIsClosed I hK
    Surjective fun ξ : GroupLieAlgebra I G ↦
      fundamentalVectorField 𝓘(ℝ, QuotientModelSpace I K) ξ x := by
  let _ := quotientChartedSpaceOfIsClosed I hK
  have : T2Space G := I.t2Space_of_lieGroup ∞
  intro v
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨u, rfl⟩ := (isSubmersion_quotientMk hK).surjective_mfderiv (by simp) g v
  obtain ⟨ξ, rfl⟩ := (bijective_mulRightInvariantVectorField (I := I) g).2 u
  refine ⟨ξ, ?_⟩
  dsimp only
  rw [← mfderiv_quotientMk_fundamentalVectorField hK g ξ,
    fundamentalVectorField_eq_mulRightInvariantVectorField]

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


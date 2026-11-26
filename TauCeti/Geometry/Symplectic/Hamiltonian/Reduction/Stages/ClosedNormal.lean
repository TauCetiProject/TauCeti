/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.NormalQuotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Stages.Residual

import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm

/-!
# The first stage of reduction by a closed normal subgroup

Let a Lie group `G` act properly on a symplectic manifold `(M, σ)` with a coadjoint-equivariant
moment map `μ : M → 𝔤*`, and let `N` be a closed normal subgroup of `G`, with its closed-subgroup
Lie group structure (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`) and the restricted moment
map `μ_N = μ ∘ dι` of the inclusion `ι : N → G`
(`IsEquivariantMomentMap.comp_subtype_ofIsClosed`). Reduction in stages by `N` first reduces by
`N` at `0`, and then by the residual group `G ⧸ N`. This file constructs the first stage and its
residual symmetry, the data that reduction in stages
(`IsEquivariantMomentMap.exists_diffeomorph_apply_eq_and_mpullback_eq_of_ker_le_range`, stated
for arbitrary presentations of the reduced spaces) takes as input.

* **The first-stage level.** The level `Z₁ = μ_N⁻¹(0)` is invariant under all of `G`, which acts
  on it by restriction (`IsEquivariantMomentMap.subtypeLevelMulAction`,
  `IsEquivariantMomentMap.coe_smul_subtypeLevelMulAction`): this is
  `IsEquivariantMomentMap.compMonoidHomLevelMulAction` for `N →ι G →π G ⧸ N`, whose Lie algebra
  hypotheses are the exactness of `𝔫 → 𝔤 → Lie(G ⧸ N)` (`Subgroup.ker_groupLieAlgebraMap_mk'`).
  For a regular level this action is smooth
  (`IsEquivariantMomentMap.contMDiffSMul_subtypeLevelMulAction`), it is proper if the action on
  `M` is (`IsEquivariantMomentMap.properSMul_subtypeLevelMulAction`), and `N` acts freely on `Z₁`
  if it does at the points of `Z₁` in `M`
  (`IsEquivariantMomentMap.isCancelSMul_subtypeLevelMulAction`).
* **The first-stage reduced space.** If `N` acts freely on `Z₁`, then `0` is a regular value of
  `μ_N`, the orbit space `Z₁ ⧸ N` is a manifold (`Subgroup.orbitRelQuotientChartedSpaceOfIsClosed`)
  and, for an `N`-invariant symplectic form `σ`, it carries a unique symplectic form `η₁` with
  `π₁^* η₁ = i₁^* σ` for the orbit projection `π₁` and the inclusion `i₁ : Z₁ → M`
  (`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_quotientMk_subtypeLevel`). The
  fibres of `π₁` are the `N`-orbits
  (`IsEquivariantMomentMap.quotientMk_eq_quotientMk_iff_subtypeLevel`), so its vertical directions
  are the orbit directions `𝔫 · z`, the kernel of `dπ₁`
  (`Subgroup.ker_mfderiv_orbitRelQuotientMkOfIsClosed`), which is what the descent of `i₁^* σ`
  (`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`) needs.
* **The residual moment map.** The quotient Lie group `G ⧸ N` acts smoothly on `Z₁ ⧸ N` by
  `[g] • [z] = [g • z]` (`Subgroup.contMDiffSMul_orbitRelQuotientOfIsClosed`), so `π₁` is
  equivariant (`IsEquivariantMomentMap.quotientMk_eq_smul_quotientMk_subtypeLevel`). For every form
  `η₁` with `π₁^* η₁ = i₁^* σ` there is a unique `μ₁ : Z₁ ⧸ N → Lie(G ⧸ N)*` with
  `μ₁ [z] ∘ dπ = μ z`, and it is a coadjoint-equivariant moment map of the residual action
  (`IsEquivariantMomentMap.existsUnique_comp_groupLieAlgebraMap_mk'_eq_and_isEquivariantMomentMap`,
  from the abstract residual moment map
  `IsEquivariantMomentMap.existsUnique_comp_groupLieAlgebraMap_eq_and_isEquivariantMomentMap`).

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

## References

* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 5 (reduction by a normal
  subgroup: the first-stage reduced space and the induced moment map of the residual group).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 24 (reduction in stages).
-/

public section

noncomputable section

open Module Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {N : Subgroup G} [N.Normal] {n₁ : ℕ}

variable (hN : IsClosed (N : Set G))

/-! ### The first-stage level -/

omit [I'.Boundaryless] [N.Normal] in
/-- **The restricted moment map of a closed subgroup.** For a closed subgroup `N` of `G` with its
closed-subgroup Lie group structure, `μ_N = μ ∘ dι` is a coadjoint-equivariant moment map of the
action of `N`, where `dι` is the differential at the identity of the inclusion `ι : N → G`. -/
theorem comp_subtype_ofIsClosed (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    σ.IsEquivariantMomentMap fun x ↦ (μ x).comp (N.subtype.groupLieAlgebraMap 𝓘(ℝ,
        (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule) I).toLinearMap :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
    (I'' := I') (M := M)
  hμ.comp_subtype
    ((Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiff_subtypeVal.mdifferentiableAt
      (by simp))

/-- **`G` acts on the first-stage level.** For a closed normal subgroup `N`, the level
`μ_N⁻¹(0)` of the restricted moment map is invariant under `G`, which acts on it by restricting
its action on `M`. -/
@[instance_reducible]
def subtypeLevelMulAction (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    MulAction G ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
    (I'' := I') (M := M)
  letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
  haveI := Subgroup.lieGroup_quotientOfIsClosed (I := I) hN
  hμ.compMonoidHomLevelMulAction
    ((Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiff_subtypeVal.mdifferentiableAt
      (by simp)) (fun _ _ ↦ rfl) (QuotientGroup.mk'_comp_subtype N)
    (Subgroup.ker_groupLieAlgebraMap_mk' hN _).le


omit [I'.Boundaryless] in
/-- The action of `G` on the first-stage level is the restriction of its action on `M`. -/
@[simp]
theorem coe_smul_subtypeLevelMulAction (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    letI := hμ.subtypeLevelMulAction hN
    ∀ (g : G) (z : (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0), ((g • z :
        (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) : M) = g • (z : M) :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
    (I'' := I') (M := M)
  letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
  haveI := Subgroup.lieGroup_quotientOfIsClosed (I := I) hN
  hμ.coe_smul_compMonoidHomLevelMulAction _ (fun _ _ ↦ rfl) (QuotientGroup.mk'_comp_subtype N)
    (Subgroup.ker_groupLieAlgebraMap_mk' hN _).le

omit [I'.Boundaryless] in
/-- The action of `N` on the first-stage level, as a subgroup of `G`, is the restriction of its
action on `M`. -/
@[simp]
theorem coe_smul_subtypeLevelMulAction_subgroup (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    letI := hμ.subtypeLevelMulAction hN
    ∀ (k : N) (z : (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0), ((k • z :
        (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) : M) = k • (z : M) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (I'' := I') (M := M)
  let _ := hμ.subtypeLevelMulAction hN
  intro k z
  rw [Subgroup.smul_def, Subgroup.smul_def, hμ.coe_smul_subtypeLevelMulAction hN]

/-- **`G` acts smoothly on the first-stage level**, for its regular-level manifold structure. -/
theorem contMDiffSMul_subtypeLevelMulAction (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    ∀ (hreg₁ : ∀ x, (μ x).comp (N.subtype.groupLieAlgebraMap 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
        (I := I) N).toSubmodule) I).toLinearMap = 0 →
        Surjective ((hμ.comp_subtype_ofIsClosed hN).differential x))
      (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
          N).toSubmodule) N) = n₁),
      letI := (hμ.comp_subtype_ofIsClosed hN).levelSubMulActionChartedSpace 0 hreg₁ hn₁
      letI := hμ.subtypeLevelMulAction hN
      ContMDiffSMul I 𝓘(ℝ, Fin n₁ → ℝ) ∞ G ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
    (I'' := I') (M := M)
  letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
  haveI := Subgroup.lieGroup_quotientOfIsClosed (I := I) hN
  fun hreg₁ hn₁ ↦ hμ.contMDiffSMul_compMonoidHomLevelMulAction _ (fun _ _ ↦ rfl)
    (QuotientGroup.mk'_comp_subtype N) (Subgroup.ker_groupLieAlgebraMap_mk' hN _).le hreg₁ hn₁

omit [I'.Boundaryless] in
/-- **`G` acts properly on the first-stage level** if it acts properly on `M`, the level being a
`G`-invariant subspace of `M`. -/
theorem properSMul_subtypeLevelMulAction [ProperSMul G M] (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    letI := hμ.subtypeLevelMulAction hN
    ProperSMul G ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
    (I'' := I') (M := M)
  letI := hμ.subtypeLevelMulAction hN
  Topology.IsEmbedding.subtypeVal.properSMul_of_isEmbedding Topology.IsEmbedding.id
    (hμ.coe_smul_subtypeLevelMulAction hN) fun g _ _ _ ↦ ⟨g, rfl⟩

omit [I'.Boundaryless] in
/-- **`N` acts freely on the first-stage level** if it acts freely at every point of the level. -/
theorem isCancelSMul_subtypeLevelMulAction (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    ∀ (_ : ∀ x, (μ x).comp (N.subtype.groupLieAlgebraMap 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
        N).toSubmodule) I).toLinearMap = 0 → MulAction.stabilizer N x = ⊥),
      letI := hμ.subtypeLevelMulAction hN
      IsCancelSMul N ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
  haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
    (I'' := I') (M := M)
  fun hfree ↦
  letI := hμ.subtypeLevelMulAction hN
  isCancelSMul_iff_stabilizer_eq_bot.2 fun z ↦ by
    rw [eq_bot_iff, ← hfree z ((hμ.comp_subtype_ofIsClosed hN).mem_levelSubMulAction.1 z.property)]
    intro n hn
    rw [MulAction.mem_stabilizer_iff] at hn ⊢
    exact (hμ.coe_smul_subtypeLevelMulAction_subgroup hN n z).symm.trans (congrArg Subtype.val hn)

/-! ### The first-stage reduced space -/

omit [I'.Boundaryless] in
/-- **The fibres of the first-stage projection** `μ_N⁻¹(0) → μ_N⁻¹(0) ⧸ N` are the `N`-orbits:
two points of the level have the same image exactly when an element of `N` carries the second to
the first in `M`. -/
theorem quotientMk_eq_quotientMk_iff_subtypeLevel (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    letI := hμ.subtypeLevelMulAction hN
    ∀ z z' : (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0, (Quotient.mk (MulAction.orbitRel
        N ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0))) z = (Quotient.mk
            (MulAction.orbitRel N ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction
                0))) z' ↔ ∃ k : N, k • (z' : M) = z := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (I'' := I') (M := M)
  let _ := hμ.subtypeLevelMulAction hN
  intro z z'
  rw [eq_comm, MulAction.quotientMk_eq_quotientMk_iff_exists_smul_eq]
  simp only [Subtype.ext_iff, hμ.coe_smul_subtypeLevelMulAction_subgroup hN]

/-- The vertical directions of the first-stage orbit projection `μ_N⁻¹(0) → μ_N⁻¹(0) ⧸ N` are
the vectors that the inclusion of the level carries into the orbit directions `𝔫 · z` of `N`. -/
private theorem ker_mfderiv_quotientMk_subtypeLevel [ProperSMul G M]
    (hμ : σ.IsEquivariantMomentMap μ) (hσ : σ.IsNondegenerate) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    ∀ (hfree : ∀ x, (μ x).comp (N.subtype.groupLieAlgebraMap 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
        (I := I) N).toSubmodule) I).toLinearMap = 0 → MulAction.stabilizer N x = ⊥)
      (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
          N).toSubmodule) N) = n₁),
      haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
      letI := (hμ.comp_subtype_ofIsClosed hN).levelSubMulActionChartedSpace 0
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot hσ
            hfree) hn₁
      letI := hμ.subtypeLevelMulAction hN
      haveI := (hμ.comp_subtype_ofIsClosed hN).isManifold_levelSubMulAction
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot hσ
            hfree) hn₁
      haveI := hμ.contMDiffSMul_subtypeLevelMulAction hN
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot hσ
            hfree) hn₁
      haveI := hμ.properSMul_subtypeLevelMulAction hN
      haveI : IsClosed (N : Set G) := hN
      haveI := hμ.isCancelSMul_subtypeLevelMulAction hN hfree
      letI := Subgroup.orbitRelQuotientChartedSpaceOfIsClosed I 𝓘(ℝ, Fin n₁ → ℝ)
        ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
      ∀ z : (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0,
        (mfderiv 𝓘(ℝ, Fin n₁ → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace (Lie.lieSubalgebraOfSubgroup
            (I := I) N).toSubmodule (Fin n₁ → ℝ)) (Quotient.mk (MulAction.orbitRel N
                ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0))) z).ker =
          ((lieAnnihilator ℝ (GroupLieAlgebra 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
              N).toSubmodule) N)
            (0 : Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
                N).toSubmodule) N))).toSubmodule.map
            ((InfinitesimalAction.fundamental 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
                N).toSubmodule) N I' M).eval z)).comap
            (mfderiv 𝓘(ℝ, Fin n₁ → ℝ) I' (Subtype.val : (hμ.comp_subtype_ofIsClosed
                hN).levelSubMulAction 0 → M) z).toLinearMap := by
  -- Install the instances of the statement.
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (I'' := I') (M := M)
  intro hfree hn₁
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hreg := (hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot
    hσ hfree
  let _ := (hμ.comp_subtype_ofIsClosed hN).levelSubMulActionChartedSpace 0 hreg hn₁
  let _ := hμ.subtypeLevelMulAction hN
  have := (hμ.comp_subtype_ofIsClosed hN).isManifold_levelSubMulAction hreg hn₁
  have := hμ.contMDiffSMul_subtypeLevelMulAction hN hreg hn₁
  have := hμ.properSMul_subtypeLevelMulAction hN
  have : IsClosed (N : Set G) := hN
  have := hμ.isCancelSMul_subtypeLevelMulAction hN hfree
  let _ := Subgroup.orbitRelQuotientChartedSpaceOfIsClosed I 𝓘(ℝ, Fin n₁ → ℝ)
    ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
  have := d.contMDiffSMul (I'' := 𝓘(ℝ, Fin n₁ → ℝ))
    (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0)
  have hsmul := hμ.coe_smul_subtypeLevelMulAction_subgroup hN
  intro z
  have hemb := (hμ.comp_subtype_ofIsClosed hN).isSmoothEmbedding_coe_levelSubMulAction hreg hn₁
  have hinj := hemb.isImmersion.mfderiv_injective (by simp) z
  -- The differential of the inclusion carries `ξ · z` in the level to `ξ · z` in `M`.
  have hξ (ξ : GroupLieAlgebra 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule) N) :
      mfderiv 𝓘(ℝ, Fin n₁ → ℝ) I' (Subtype.val : (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction
          0 → M) z
          (fundamentalVectorField 𝓘(ℝ, Fin n₁ → ℝ) ξ z) =
        fundamentalVectorField I' ξ (z : M) :=
    mfderiv_fundamentalVectorField_of_map_smul (hemb.contMDiff.mdifferentiableAt (by simp))
      ((ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
          N).toSubmodule)) (G := N) (I' := 𝓘(ℝ, Fin n₁ → ℝ))
        (n := ∞) z).mdifferentiableAt (by simp))
      (fun n ↦ hsmul n z) ξ
  -- The kernel of `dπ₁` is the orbit tangent space `𝔫 · z` of `N` acting on the level.
  rw [Subgroup.ker_mfderiv_orbitRelQuotientMkOfIsClosed (I := I) (I' := 𝓘(ℝ, Fin n₁ → ℝ)) hN z,
    lieAnnihilator_zero, LieSubalgebra.top_toSubmodule, Submodule.map_top,
    ← InfinitesimalAction.orbitTangent_eq_range]
  ext v
  simp only [Submodule.mem_comap, InfinitesimalAction.mem_orbitTangent_iff,
    InfinitesimalAction.fundamental_apply]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, (hξ ξ).symm⟩
  · rintro ⟨ξ, hv⟩
    exact ⟨ξ, hinj ((hξ ξ).trans hv)⟩

/-- **The first-stage reduced space.** Let `G` act properly on `(M, σ)` with coadjoint-equivariant
moment map `μ`, let the closed normal subgroup `N` act by symplectomorphisms, and let it act freely
on the level `μ_N⁻¹(0)` of the restricted moment map `μ_N = μ ∘ dι`, which is then a regular level.
Then the orbit space `μ_N⁻¹(0) ⧸ N` carries a unique symplectic form `η₁` with
`π₁^* η₁ = i₁^* σ`, for the orbit projection `π₁` and the inclusion `i₁ : μ_N⁻¹(0) → M`. -/
theorem existsUnique_isSymplectic_mpullback_quotientMk_subtypeLevel [ProperSMul G M]
    (hμ : σ.IsEquivariantMomentMap μ) (hσ : σ.IsSymplectic)
    (hσN : ∀ k : N, SmoothForm.mpullback (fun x : M ↦ (k : G) • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (k : G)) σ = σ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    ∀ (hfree : ∀ x, (μ x).comp (N.subtype.groupLieAlgebraMap 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
        (I := I) N).toSubmodule) I).toLinearMap = 0 → MulAction.stabilizer N x = ⊥)
      (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
          N).toSubmodule) N) = n₁),
      haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
      letI := (hμ.comp_subtype_ofIsClosed hN).levelSubMulActionChartedSpace 0
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot
            hσ.isNondegenerate hfree) hn₁
      letI := hμ.subtypeLevelMulAction hN
      haveI := (hμ.comp_subtype_ofIsClosed hN).isManifold_levelSubMulAction
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot
            hσ.isNondegenerate hfree) hn₁
      haveI := hμ.contMDiffSMul_subtypeLevelMulAction hN
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot
            hσ.isNondegenerate hfree) hn₁
      haveI := hμ.properSMul_subtypeLevelMulAction hN
      haveI : IsClosed (N : Set G) := hN
      haveI := hμ.isCancelSMul_subtypeLevelMulAction hN hfree
      letI := Subgroup.orbitRelQuotientChartedSpaceOfIsClosed I 𝓘(ℝ, Fin n₁ → ℝ)
        ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
      haveI := Subgroup.isManifold_orbitRelQuotientOfIsClosed (I := I)
        (I' := 𝓘(ℝ, Fin n₁ → ℝ)) (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
      ∃! η₁ : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace (Lie.lieSubalgebraOfSubgroup
          (I := I) N).toSubmodule (Fin n₁ → ℝ)) (MulAction.orbitRel.Quotient N
              ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0)),
        η₁.IsSymplectic ∧
          SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel N ((hμ.comp_subtype_ofIsClosed
              hN).levelSubMulAction 0))) (Subgroup.isSubmersion_orbitRelQuotientMkOfIsClosed
                  (I := I)
            (I' := 𝓘(ℝ, Fin n₁ → ℝ)) (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction
                0) hN).contMDiff η₁ =
            SmoothForm.mpullback Subtype.val ((hμ.comp_subtype_ofIsClosed
                hN).isSmoothEmbedding_coe_levelSubMulAction
              ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot
                  hσ.isNondegenerate hfree) hn₁).contMDiff σ := by
  -- Install the instances of the statement.
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (I'' := I') (M := M)
  intro hfree hn₁
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hreg := (hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot
    hσ.isNondegenerate hfree
  let _ := (hμ.comp_subtype_ofIsClosed hN).levelSubMulActionChartedSpace 0 hreg hn₁
  let _ := hμ.subtypeLevelMulAction hN
  have := (hμ.comp_subtype_ofIsClosed hN).isManifold_levelSubMulAction hreg hn₁
  have := hμ.contMDiffSMul_subtypeLevelMulAction hN hreg hn₁
  have := hμ.properSMul_subtypeLevelMulAction hN
  have : IsClosed (N : Set G) := hN
  have := hμ.isCancelSMul_subtypeLevelMulAction hN hfree
  let _ := Subgroup.orbitRelQuotientChartedSpaceOfIsClosed I 𝓘(ℝ, Fin n₁ → ℝ)
    ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
  have := Subgroup.isManifold_orbitRelQuotientOfIsClosed (I := I)
    (I' := 𝓘(ℝ, Fin n₁ → ℝ)) (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
  have := d.contMDiffSMul (I'' := 𝓘(ℝ, Fin n₁ → ℝ))
    (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0)
  have hfib := hμ.quotientMk_eq_quotientMk_iff_subtypeLevel hN
  have hsmul := hμ.coe_smul_subtypeLevelMulAction_subgroup hN
  -- `N` acts on the level through itself, so the abstract `φ : N → N` is the identity.
  exact (hμ.comp_subtype_ofIsClosed hN).existsUnique_isSymplectic_mpullback_eq_mpullback hσ hσN
    ((hμ.comp_subtype_ofIsClosed hN).isSmoothEmbedding_coe_levelSubMulAction hreg hn₁).contMDiff
    (fun z ↦ (hμ.comp_subtype_ofIsClosed hN).mem_levelSubMulAction.1 z.property)
    ((hμ.comp_subtype_ofIsClosed hN).range_mfderiv_coe_levelSubMulAction hreg hn₁)
    (Subgroup.isSubmersion_orbitRelQuotientMkOfIsClosed (I := I) (I' := 𝓘(ℝ, Fin n₁ → ℝ))
      (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN)
    Quotient.mk_surjective
    (hμ.ker_mfderiv_quotientMk_subtypeLevel hN hσ.isNondegenerate hfree hn₁)
    (fun k : N ↦ ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
        (I := I) N).toSubmodule)) k)
    (fun k z ↦ (hfib (k • z) z).2 ⟨k, (hsmul k z).symm⟩)
    (fun z z' h ↦ (hfib z' z).1 h.symm |>.imp fun k hk ↦ Subtype.ext ((hsmul k z).trans hk))
    (id : N → N) hsmul

/-! ### The residual moment map -/

omit [I'.Boundaryless] in
/-- **The first-stage projection is equivariant** for the residual action: it intertwines the
action of `G` on the level `μ_N⁻¹(0)` with the action of `G ⧸ N` on `μ_N⁻¹(0) ⧸ N`, so
`[g • z] = [g] • [z]`. -/
theorem quotientMk_eq_smul_quotientMk_subtypeLevel (hμ : σ.IsEquivariantMomentMap μ) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    letI := hμ.subtypeLevelMulAction hN
    ∀ (g : G) (z z' : (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0), (z' : M) = g • (z : M) →
      (Quotient.mk (MulAction.orbitRel N ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction
          0))) z' = QuotientGroup.mk' N g • (Quotient.mk (MulAction.orbitRel N
              ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0))) z := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (I'' := I') (M := M)
  let _ := hμ.subtypeLevelMulAction hN
  intro g z z' h
  rw [show z' = g • z from Subtype.ext (h.trans (hμ.coe_smul_subtypeLevelMulAction hN g z).symm)]
  exact (MulAction.orbitRel.Quotient.mk_smul_mk N g z).symm

/-- **The residual moment map.** In the setting of
`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_quotientMk_subtypeLevel`,
the quotient Lie group `G ⧸ N` acts smoothly on the first-stage space `μ_N⁻¹(0) ⧸ N` by
`[g] • [z] = [g • z]` (`Subgroup.contMDiffSMul_orbitRelQuotientOfIsClosed`). For every two-form
`η₁` on `μ_N⁻¹(0) ⧸ N` with `π₁^* η₁ = i₁^* σ`, such as the first-stage reduced form, there is a
unique map `μ₁ : μ_N⁻¹(0) ⧸ N → Lie(G ⧸ N)*` with `μ₁ [z] ∘ dπ = μ z` for every `z`, where `dπ` is
the differential at the identity of the projection `π : G → G ⧸ N`, and it is a
coadjoint-equivariant moment map of the action of `G ⧸ N` on `(μ_N⁻¹(0) ⧸ N, η₁)`. -/
theorem existsUnique_comp_groupLieAlgebraMap_mk'_eq_and_isEquivariantMomentMap [ProperSMul G M]
    (hμ : σ.IsEquivariantMomentMap μ) (hσ : σ.IsNondegenerate) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).contMDiffSMul
      (I'' := I') (M := M)
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hN
    haveI := Subgroup.lieGroup_quotientOfIsClosed (I := I) hN
    ∀ (hfree : ∀ x, (μ x).comp (N.subtype.groupLieAlgebraMap 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup
        (I := I) N).toSubmodule) I).toLinearMap = 0 → MulAction.stabilizer N x = ⊥)
      (hn₁ : finrank ℝ E' - finrank ℝ (GroupLieAlgebra 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I)
          N).toSubmodule) N) = n₁),
      haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
      letI := (hμ.comp_subtype_ofIsClosed hN).levelSubMulActionChartedSpace 0
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot hσ
            hfree) hn₁
      letI := hμ.subtypeLevelMulAction hN
      haveI := (hμ.comp_subtype_ofIsClosed hN).isManifold_levelSubMulAction
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot hσ
            hfree) hn₁
      haveI := hμ.contMDiffSMul_subtypeLevelMulAction hN
        ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot hσ
            hfree) hn₁
      haveI := hμ.properSMul_subtypeLevelMulAction hN
      haveI : IsClosed (N : Set G) := hN
      haveI := hμ.isCancelSMul_subtypeLevelMulAction hN hfree
      letI := Subgroup.orbitRelQuotientChartedSpaceOfIsClosed I 𝓘(ℝ, Fin n₁ → ℝ)
        ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
      haveI := Subgroup.isManifold_orbitRelQuotientOfIsClosed (I := I)
        (I' := 𝓘(ℝ, Fin n₁ → ℝ)) (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
      haveI := Subgroup.contMDiffSMul_orbitRelQuotientOfIsClosed (I := I)
        (I' := 𝓘(ℝ, Fin n₁ → ℝ)) (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
      ∀ η₁ : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace (Lie.lieSubalgebraOfSubgroup (I := I)
          N).toSubmodule (Fin n₁ → ℝ)) (MulAction.orbitRel.Quotient N ((hμ.comp_subtype_ofIsClosed
              hN).levelSubMulAction 0)),
        SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel N ((hμ.comp_subtype_ofIsClosed
            hN).levelSubMulAction 0))) (Subgroup.isSubmersion_orbitRelQuotientMkOfIsClosed (I := I)
          (I' := 𝓘(ℝ, Fin n₁ → ℝ)) (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction
              0) hN).contMDiff η₁ =
            SmoothForm.mpullback Subtype.val ((hμ.comp_subtype_ofIsClosed
                hN).isSmoothEmbedding_coe_levelSubMulAction
              ((hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot
                  hσ hfree) hn₁).contMDiff σ →
          ∃! μ₁ : (MulAction.orbitRel.Quotient N ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction
              0)) → Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, Subgroup.QuotientModelSpace I N) (G ⧸ N)),
            (∀ z, (μ₁ ((Quotient.mk (MulAction.orbitRel N ((hμ.comp_subtype_ofIsClosed
                hN).levelSubMulAction 0))) z)).comp ((QuotientGroup.mk' N).groupLieAlgebraMap I
                    𝓘(ℝ, Subgroup.QuotientModelSpace I
                        N)).toLinearMap = μ z) ∧ η₁.IsEquivariantMomentMap μ₁ := by
  -- Install the instances of the statement.
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (I'' := I') (M := M)
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hN
  have := Subgroup.lieGroup_quotientOfIsClosed (I := I) hN
  intro hfree hn₁
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hreg := (hμ.comp_subtype_ofIsClosed hN).forall_differential_surjective_of_stabilizer_eq_bot
    hσ hfree
  let _ := (hμ.comp_subtype_ofIsClosed hN).levelSubMulActionChartedSpace 0 hreg hn₁
  let _ := hμ.subtypeLevelMulAction hN
  have := (hμ.comp_subtype_ofIsClosed hN).isManifold_levelSubMulAction hreg hn₁
  have := hμ.contMDiffSMul_subtypeLevelMulAction hN hreg hn₁
  have := hμ.properSMul_subtypeLevelMulAction hN
  have : IsClosed (N : Set G) := hN
  have := hμ.isCancelSMul_subtypeLevelMulAction hN hfree
  let _ := Subgroup.orbitRelQuotientChartedSpaceOfIsClosed I 𝓘(ℝ, Fin n₁ → ℝ)
    ((hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
  have := Subgroup.isManifold_orbitRelQuotientOfIsClosed (I := I)
    (I' := 𝓘(ℝ, Fin n₁ → ℝ)) (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
  have := Subgroup.contMDiffSMul_orbitRelQuotientOfIsClosed (I := I)
    (I' := 𝓘(ℝ, Fin n₁ → ℝ)) (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN
  intro η₁ hη₁
  exact hμ.existsUnique_comp_groupLieAlgebraMap_eq_and_isEquivariantMomentMap
    (d.contMDiff_subtypeVal.mdifferentiableAt (by simp)) (fun _ _ ↦ rfl)
    (QuotientGroup.mk'_surjective N) (Subgroup.surjective_groupLieAlgebraMap_mk' hN)
    (QuotientGroup.mk'_comp_subtype N) (Subgroup.ker_groupLieAlgebraMap_mk' hN _).le hreg hn₁
    Quotient.mk_surjective (fun z z' ↦ (hμ.quotientMk_eq_quotientMk_iff_subtypeLevel hN z z').1)
    (hμ.quotientMk_eq_smul_quotientMk_subtypeLevel hN)
    (Subgroup.isSubmersion_orbitRelQuotientMkOfIsClosed (I := I) (I' := 𝓘(ℝ, Fin n₁ → ℝ))
      (M := (hμ.comp_subtype_ofIsClosed hN).levelSubMulAction 0) hN) hη₁

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap

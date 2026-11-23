/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.NoSmallSubgroups
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Basic
public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.RepresentationTheory.Compact.Faithful

import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Geometry.Lie.Representation

/-!
# Faithful unitary representations of compact Lie groups and the NSS characterization

This file connects the representation theory of compact Hausdorff groups with the smooth theory of
finite-dimensional real Lie groups in both directions:

1. **Smooth faithful unitary representations of compact Lie groups**
   (`TauCeti.Lie.exists_faithful_isUnitary_contMDiff`,
   `TauCeti.Lie.exists_injective_contMDiffMonoidMorphism_matrixUnitarySubgroup`): every compact
   finite-dimensional real Lie group has no small subgroups
   (`TauCeti.Lie.hasNoSmallSubgroups_of_lieGroup`), hence by Peter–Weyl admits a faithful unitary
   representation on `EuclideanSpace 𝕜 (Fin n)` (over `ℂ` or `ℝ`), which is automatically smooth
   (`ContRepresentation.contMDiff`), and embeds smoothly and closedly into the matrix unitary Lie
   group `unitarySubgroup (GL (Fin n) 𝕜)`.
2. **The Gleason–Montgomery–Zippin / Peter–Weyl characterization of compact Lie groups**
   (`TauCeti.Lie.HasNoSmallSubgroups.exists_lieGroup`,
   `TauCeti.Lie.hasNoSmallSubgroups_iff_exists_lieGroup`,
   `TauCeti.Lie.tfae_hasNoSmallSubgroups_compact`): a compact Hausdorff topological group `G`
   carries a smooth finite-dimensional Lie-group structure compatible with its topology if and only
   if `G` has no small subgroups. Indeed, a faithful continuous orthogonal representation embeds `G`
   as a closed subgroup `K` of `(EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ`;
   Cartan's closed-subgroup theorem makes `K` a smooth Lie group modelled on its Lie algebra, a
   linear equivalence transports the model to `EuclideanSpace ℝ (Fin d)` via
   `Diffeomorph.lieGroup_chartedSpaceComp`, and `ContinuousMulEquiv.lieGroup_pullbackChartedSpace`
   pulls the smooth Lie-group structure back to `G`.

## Main results

* `TauCeti.Lie.exists_faithful_isUnitary_contMDiff`: every compact finite-dimensional real Lie
  group admits a smooth faithful unitary representation on `EuclideanSpace 𝕜 (Fin n)`.
* `TauCeti.Lie.exists_injective_contMDiffMonoidMorphism_matrixUnitarySubgroup`: smooth closed
  embedding of a compact Lie group into `unitarySubgroup (GL (Fin n) 𝕜)`.
* `TauCeti.Lie.HasNoSmallSubgroups.exists_lieGroup`: every compact Hausdorff group with no small
  subgroups carries a smooth `LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G` structure.
* `TauCeti.Lie.hasNoSmallSubgroups_iff_exists_lieGroup`,
  `TauCeti.Lie.tfae_hasNoSmallSubgroups_compact`: equivalence of no small subgroups, faithful
  complex unitary representation, faithful real orthogonal representation, and smooth Lie-group
  structure on a compact Hausdorff group.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III, §4 (Theorem 4.4).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience (1963),
  Note 2 (Myers–Steenrod and compact groups with no small subgroups).
* T. Tao, *Hilbert's Fifth Problem and Related Topics*, AMS GSM 153 (2014), Theorem 1.2.5.
-/

public section

noncomputable section

open Filter Function Manifold Set
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator Topology

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace TauCeti.Lie

section CompactLieGroup

attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [CompactSpace G]

variable (𝕜 : Type*) [RCLike 𝕜] in
/-- **Every compact finite-dimensional real Lie group admits a smooth faithful finite-dimensional
unitary representation** (over `ℂ` or `ℝ`). -/
theorem exists_faithful_isUnitary_contMDiff :
    ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
      ContMDiff I 𝓘(ℝ, EuclideanSpace 𝕜 (Fin n) →L[𝕜] EuclideanSpace 𝕜 (Fin n)) ∞ π ∧
        π.IsUnitary ∧ Function.Injective π := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  have hG : HasNoSmallSubgroups G := hasNoSmallSubgroups_of_lieGroup I
  obtain ⟨n, π, hπc, hπu, hinj⟩ := hG.exists_faithful_isUnitary (𝕜 := 𝕜)
  exact ⟨n, π, π.contMDiff hπc, hπu, hinj⟩

section Matrix

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

variable (𝕜 : Type*) [RCLike 𝕜] in
/-- **Smooth faithful embedding of a compact Lie group into a matrix unitary group.** Every compact
finite-dimensional real Lie group embeds via a smooth injective monoid morphism (which is also a
closed topological embedding) into `unitarySubgroup (GL (Fin n) 𝕜)`. -/
theorem exists_injective_contMDiffMonoidMorphism_matrixUnitarySubgroup :
    ∃ (n : ℕ) (f : ContMDiffMonoidMorphism I
        𝓘(ℝ, (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜))
          (unitarySubgroup (GL (Fin n) 𝕜))).toSubmodule)
        ∞ G (unitarySubgroup (GL (Fin n) 𝕜))),
      Function.Injective f ∧ Topology.IsClosedEmbedding f := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  have hG : HasNoSmallSubgroups G := hasNoSmallSubgroups_of_lieGroup I
  obtain ⟨n, π, hπc, hπu, hinj⟩ := hG.exists_faithful_isUnitary (𝕜 := 𝕜)
  let ψ : G →ₜ* Matrix.unitaryGroup (Fin n) 𝕜 := hπu.toMatrixUnitaryGroupHom hπc
  let φ : G →ₜ* unitarySubgroup (GL (Fin n) 𝕜) :=
    { toMonoidHom :=
        (unitarySubgroupUnitsEquiv (M := Matrix (Fin n) (Fin n) 𝕜)).symm.toMonoidHom.comp
          ψ.toMonoidHom
      continuous_toFun :=
        ((TauCeti.unitarySubgroupUnitsHomeomorph (Matrix (Fin n) (Fin n) 𝕜)).symm.continuous.comp
          ψ.continuous).congr fun g ↦
          TauCeti.unitarySubgroupUnitsHomeomorph_symm_apply (ψ g) }
  have hφ_inj : Function.Injective φ :=
    (unitarySubgroupUnitsEquiv (M := Matrix (Fin n) (Fin n) 𝕜)).symm.injective.comp
      ((hπu.injective_toMatrixUnitaryGroupHom_iff hπc).mpr hinj)
  let f := φ.toContMDiffMonoidMorphism I
    𝓘(ℝ, (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜))
      (unitarySubgroup (GL (Fin n) 𝕜))).toSubmodule)
  exact ⟨n, f, by simpa [f] using hφ_inj,
    by simpa [f] using φ.continuous.isClosedEmbedding hφ_inj⟩

end Matrix

end CompactLieGroup

section Characterization

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T1Space G]

/-- **Every compact Hausdorff group with no small subgroups carries a smooth finite-dimensional
real Lie-group structure.** -/
theorem HasNoSmallSubgroups.exists_lieGroup (hG : HasNoSmallSubgroups G) :
    ∃ (d : ℕ) (atlas : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
      letI := atlas
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G := by
  obtain ⟨n, π, hπc, hπu, hinj⟩ := hG.exists_faithful_isUnitary (𝕜 := ℝ)
  let φ : G →ₜ* (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ :=
    ⟨π.toMonoidHom.toHomUnits, hπu.continuous_toHomUnits hπc⟩
  have hφ_inj : Function.Injective φ := fun _ _ h ↦ hinj (congrArg Units.val h)
  let K : Subgroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ :=
    φ.toMonoidHom.range
  have hK_closed :
      IsClosed (K : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ) :=
    (isCompact_range φ.continuous).isClosed
  -- `φ` restricts to a continuous multiplicative equivalence onto the closed subgroup `K`.
  let eMul : G ≃* K :=
    MulEquiv.ofBijective φ.toMonoidHom.rangeRestrict
      ⟨fun x y hxy ↦ hφ_inj (congrArg Subtype.val hxy), φ.toMonoidHom.rangeRestrict_surjective⟩
  let eHomeo : G ≃ₜ K :=
    (φ.continuous.subtype_mk (fun g ↦ ⟨g, rfl⟩)).homeoOfEquivCompactToT2 (f := eMul.toEquiv)
  let e : G ≃ₜ* K :=
    { eMul with
      continuous_toFun := eHomeo.continuous
      continuous_invFun := eHomeo.symm.continuous }
  -- Apply Cartan's closed-subgroup theorem to `K`, then transport its model space to `ℝ^d`.
  have _ : BoundarylessManifold
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ :=
    ContMDiffMul.boundarylessManifold
  let dK := EmbeddedLieSubgroupData.ofIsClosed
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) hK_closed
  let _ := dK.chartedSpace
  let _ := dK.lieGroup
  let L := (lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) K).toSubmodule
  obtain ⟨atlasK, hlieK⟩ := TauCeti.exists_chartedSpace_euclideanSpace_lieGroup (𝕜 := ℝ) (n := ∞)
    (E := L) K
  let _ := atlasK
  let _ := hlieK
  -- Pull back the Euclidean charts and smooth Lie-group structure along `e : G ≃ₜ* K`.
  exact ⟨Module.finrank ℝ L,
    e.toHomeomorph.pullbackChartedSpace (H := EuclideanSpace ℝ (Fin (Module.finrank ℝ L))),
    e.lieGroup_pullbackChartedSpace⟩

/-- **A compact Hausdorff group has no small subgroups if and only if it carries a smooth
finite-dimensional real Lie-group structure.** -/
theorem hasNoSmallSubgroups_iff_exists_lieGroup :
    HasNoSmallSubgroups G ↔
      ∃ (d : ℕ) (atlas : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
        letI := atlas
        LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G :=
  ⟨HasNoSmallSubgroups.exists_lieGroup, fun ⟨d, atlas, hlie⟩ ↦ by
    let _ := atlas
    let _ := hlie
    exact hasNoSmallSubgroups_of_lieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d))⟩

/-- **Equivalent characterizations of compact Lie groups among compact Hausdorff groups:**
1. `G` has no small subgroups (`TauCeti.HasNoSmallSubgroups G`);
2. `G` admits a faithful continuous complex unitary representation on `EuclideanSpace ℂ (Fin n)`;
3. `G` admits a faithful continuous real orthogonal representation on `EuclideanSpace ℝ (Fin n)`;
4. `G` carries a smooth `LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G` structure. -/
theorem tfae_hasNoSmallSubgroups_compact :
    List.TFAE
      [HasNoSmallSubgroups G,
       ∃ (n : ℕ) (π : ContRepresentation ℂ G (EuclideanSpace ℂ (Fin n))),
         Continuous π ∧ π.IsUnitary ∧ Function.Injective π,
       ∃ (n : ℕ) (π : ContRepresentation ℝ G (EuclideanSpace ℝ (Fin n))),
         Continuous π ∧ π.IsUnitary ∧ Function.Injective π,
       ∃ (d : ℕ) (atlas : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
         letI := atlas
         LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G] := by
  tfae_have 1 ↔ 2 := hasNoSmallSubgroups_iff_exists_faithful_isUnitary ℂ
  tfae_have 1 ↔ 3 := hasNoSmallSubgroups_iff_exists_faithful_isUnitary ℝ
  tfae_have 1 ↔ 4 := hasNoSmallSubgroups_iff_exists_lieGroup
  tfae_finish

end Characterization

end TauCeti.Lie

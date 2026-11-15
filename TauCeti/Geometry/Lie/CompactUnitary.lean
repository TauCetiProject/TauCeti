/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.NoSmallSubgroups
public import TauCeti.Geometry.Lie.Subgroup.Unitary
public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.RepresentationTheory.Compact.Faithful

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Faithful unitary representations of compact Lie groups and the NSS characterization

This file connects the representation theory of compact Hausdorff groups with the smooth theory of
finite-dimensional real Lie groups in both directions:

1. **Automatic smoothness of finite-dimensional continuous representations**
   (`ContRepresentation.contMDiff`, `ContRepresentation.contMDiff_apply`): every continuous
   representation of a finite-dimensional real Lie group on a finite-dimensional normed space over
   a finite-dimensional normed `ℝ`-algebra `𝕜` is smooth as an operator-valued map and acts
   smoothly on `G × V`.
2. **Smooth faithful unitary representations of compact Lie groups**
   (`TauCeti.Lie.exists_faithful_isUnitary_contMDiff`,
   `TauCeti.Lie.exists_injective_contMDiffMonoidMorphism_matrixUnitarySubgroup`): every compact
   finite-dimensional real Lie group has no small subgroups
   (`TauCeti.Lie.hasNoSmallSubgroups_of_lieGroup`), hence by Peter–Weyl admits a smooth faithful
   unitary representation on `EuclideanSpace 𝕜 (Fin n)` (over `ℂ` or `ℝ`), and embeds smoothly and
   closedly into the matrix unitary Lie group `unitarySubgroup (GL (Fin n) 𝕜)`.
3. **The Gleason–Montgomery–Zippin / Peter–Weyl characterization of compact Lie groups**
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

* `ContRepresentation.contMDiff`, `ContRepresentation.contMDiff_apply`: finite-dimensional
  continuous representations of real Lie groups are smooth.
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

namespace ContRepresentation

attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [FiniteDimensional ℝ 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass 𝕜 ℝ V]
  [IsScalarTower ℝ 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Every continuous finite-dimensional representation of a finite-dimensional real Lie group is
smooth.** -/
theorem contMDiff (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ContMDiff I 𝓘(ℝ, V →L[𝕜] V) ∞ π := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : FiniteDimensional ℝ V := Module.Finite.trans 𝕜 V
  let _ : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let _ : FiniteDimensional ℝ (V →L[𝕜] V) := Module.Finite.trans 𝕜 (V →L[𝕜] V)
  let _ : NormedAlgebra ℝ (V →L[𝕜] V) :=
    { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }
  have hhom : ContMDiff I 𝓘(ℝ, V →L[𝕜] V) ∞ (π.toUnitsContinuousMonoidHom hπ) :=
    TauCeti.Lie.contMDiff_of_continuous_monoidHom (π.toUnitsContinuousMonoidHom hπ)
      (π.toUnitsContinuousMonoidHom hπ).continuous
  simpa [Function.comp_def] using
    (Units.contMDiff_val (𝕜 := ℝ) (R := V →L[𝕜] V) (n := ∞)).comp hhom

/-- The joint action `(g, v) ↦ π g v` of a continuous finite-dimensional representation of a
finite-dimensional real Lie group is smooth. -/
theorem contMDiff_apply (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ContMDiff (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ (fun p : G × V ↦ π p.1 p.2) := by
  let _ : FiniteDimensional ℝ V := Module.Finite.trans 𝕜 V
  let _ : FiniteDimensional ℝ (V →L[𝕜] V) := Module.Finite.trans 𝕜 (V →L[𝕜] V)
  -- Push `π g` through `restrictScalars ℝ` and compose with bounded bilinear evaluation.
  let Rlin : (V →L[𝕜] V) →ₗ[ℝ] (V →L[ℝ] V) :=
    { toFun f := f.restrictScalars ℝ, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let R : (V →L[𝕜] V) →L[ℝ] (V →L[ℝ] V) := Rlin.toContinuousLinearMap
  have hR : ContMDiff I 𝓘(ℝ, V →L[ℝ] V) ∞ (fun g : G ↦ R (π g)) :=
    R.contDiff.contMDiff.comp (π.contMDiff hπ)
  have hcomp : ContMDiff (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞
      ((fun q : (V →L[ℝ] V) × V ↦ q.1 q.2) ∘ fun p : G × V ↦ (R (π p.1), p.2)) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := V)).contDiff.contMDiff.comp
      ((hR.comp contMDiff_fst).prodMk_space contMDiff_snd)
  have hfun :
      ((fun q : (V →L[ℝ] V) × V ↦ q.1 q.2) ∘ fun p : G × V ↦ (R (π p.1), p.2)) =
        fun p : G × V ↦ π p.1 p.2 :=
    funext fun p ↦ by simp [R, Rlin]; rfl
  rwa [hfun] at hcomp

end ContRepresentation

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
  let eMat : (EuclideanSpace 𝕜 (Fin n) →L[𝕜] EuclideanSpace 𝕜 (Fin n)) ≃⋆ₐ[𝕜]
      Matrix (Fin n) (Fin n) 𝕜 :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜)).symm
  have heMat_cont : Continuous eMat :=
    LinearMap.continuous_of_finiteDimensional eMat.toAlgEquiv.toLinearEquiv.toLinearMap
  let φGL : G →* GL (Fin n) 𝕜 :=
    (Units.map eMat.toRingHom.toMonoidHom).comp π.toUnitsMonoidHom
  have hval_φGL (g : G) : ((φGL g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) = eMat (π g) := by
    simp [φGL]
    rfl
  have hinv_φGL (g : G) :
      (((φGL g)⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) = eMat (π g⁻¹) := by
    simp [φGL, ← map_inv]
    rfl
  have hφGL_cont : Continuous φGL := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have h1 : (Units.val ∘ φGL) = fun g ↦ eMat (π g) := funext hval_φGL
      rw [h1]
      exact heMat_cont.comp hπc
    · have h2 : (fun g : G ↦ (((φGL g)⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜)) =
          fun g ↦ eMat (π g⁻¹) := funext hinv_φGL
      rw [h2]
      exact heMat_cont.comp (hπc.comp continuous_inv)
  have hφGL_mem : ∀ g : G, φGL g ∈ unitarySubgroup (GL (Fin n) 𝕜) := fun g ↦ by
    rw [mem_unitarySubgroup_iff, TauCeti.mem_unitary_units_iff, hval_φGL]
    exact Unitary.map_mem eMat (hπu.mem_unitary g)
  let φ : G →ₜ* unitarySubgroup (GL (Fin n) 𝕜) :=
    { toMonoidHom := φGL.codRestrict (unitarySubgroup (GL (Fin n) 𝕜)) hφGL_mem
      continuous_toFun := hφGL_cont.subtype_mk _ }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hval : ((φGL x : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) =
        ((φGL y : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) :=
      congrArg (fun u : unitarySubgroup (GL (Fin n) 𝕜) ↦ ((u : GL (Fin n) 𝕜) :
        Matrix (Fin n) (Fin n) 𝕜)) hxy
    rw [hval_φGL, hval_φGL] at hval
    exact hinj (eMat.injective hval)
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
    ⟨π.toUnitsMonoidHom, hπu.continuous_toUnitsMonoidHom hπc⟩
  have hφ_inj : Function.Injective φ := π.injective_toUnitsMonoidHom_iff.mpr hinj
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.AlgebraicTopology.UniversalCover.Countable
public import TauCeti.Geometry.Lie.Adjoint.Compact
public import TauCeti.Geometry.Lie.UniversalCover.Compact
public import TauCeti.Geometry.Lie.UniversalCover.Splitting
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv
public import TauCeti.Topology.Algebra.Group.Covering

/-!
# The semisimple factor of a simply connected cover of a compact group is compact

Let `G` be a simply connected Lie group whose Lie algebra `𝔤` is the direct sum of its centre `𝔷`
and its derived algebra `[𝔤, 𝔤]`. Then `G` is the product `A × K` of the commutative subgroup `A`
integrating `𝔷` and the subgroup `K` integrating `[𝔤, 𝔤]`
(`TauCeti.Lie.centerProdDerivedContinuousMulEquiv`). If `G` covers a compact group `C`, through a
surjective homomorphism `π : G →* C` that is a local homeomorphism, then `K` is compact
(`TauCeti.Lie.compactSpace_integralLeafSubgroupData_derivedSeries`). This applies to the
projection of the universal covering group of a compact connected Lie group, and is the
compactness of the factor `K` in the finite cover `T × K → G` of a compact connected Lie group by
a torus times a simply connected compact semisimple group.

The proof is Weyl's theorem, in the form
`Subgroup.compactSpace_of_le_center_of_derivedSeries_one_eq_top` (a connected Lie group with
perfect, centreless Lie algebra and a cocompact central subgroup is compact), applied to the
kernel of the composite

`f : K → G → C → C ⧸ π(A)`.

* The subgroup `A` is central in `G`: it is commutative, and it commutes with `K`
  (`TauCeti.Lie.integralLeafSubgroupData_center_toHom_mem_center`). So `π(A)` is central in `C`,
  and `C ⧸ π(A)` is a compact topological group.
* Since `π ∘ (A × K ≃ G)` sends `(a, k)` to `π(a) π(k)`, the map `f` is open, so `K ⧸ ker f` is
  compact.
* The kernel of `π` is discrete, hence central in the connected group `G`. An element of the
  kernel of `f` is therefore `a⁻¹` times a central element of `G`, so it is central in `K`.
* The Lie algebra `[𝔤, 𝔤]` of `K` has zero centre
  (`TauCeti.Lie.center_eq_bot_integralLeafSubgroupData_derivedSeries`) and is perfect
  (`TauCeti.Lie.derivedSeries_one_eq_top_integralLeafSubgroupData_derivedSeries`).

For the universal covering group of a compact Lie group the centre and the derived algebra are
complementary, since its Lie algebra is that of the compact group
(`TauCeti.UniversalCover.isCompl_center_derivedSeries_one`). So the universal cover of a compact
connected Lie group is the product of the subgroup integrating `𝔷` and a compact subgroup `K`
(`TauCeti.UniversalCover.compactSpace_integralLeafSubgroupData_derivedSeries`).

## Main results

* `TauCeti.Lie.compactSpace_integralLeafSubgroupData_derivedSeries`: the subgroup integrating
  `[𝔤, 𝔤]` is compact when `G` covers a compact group.
* `TauCeti.UniversalCover.isCompl_center_derivedSeries_one`: the Lie algebra of the universal
  covering group of a compact Lie group is the direct sum of its centre and derived algebra.
* `TauCeti.UniversalCover.compactSpace_integralLeafSubgroupData_derivedSeries`: the factor `K` of
  the universal covering group of a compact connected Lie group is compact.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter V, Theorem 8.1 and its proof.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Theorem 12.1.17.
-/

public section

noncomputable section

open Function Set LieAlgebra
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
namespace TauCeti.Lie

attribute [local instance] ImmersedLieSubgroupData.group
  ImmersedLieSubgroupData.topologicalSpace ImmersedLieSubgroupData.normedAddCommGroup
  ImmersedLieSubgroupData.normedSpace ImmersedLieSubgroupData.finiteDimensional
  ImmersedLieSubgroupData.modelTopology ImmersedLieSubgroupData.chartedSpace
  ImmersedLieSubgroupData.lieGroup ImmersedLieSubgroupData.connectedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [SecondCountableTopology G] [SimplyConnectedSpace G]

/-- The image of the subgroup integrating the centre under a surjective homomorphism is central. -/
private theorem range_comp_toHom_center_le_center
    (hc : IsCompl (center ℝ (LeftInvariantDerivation I G))
      (derivedSeries ℝ (LeftInvariantDerivation I G) 1))
    {C : Type*} [Group C] (π : G →* C) (hsurj : Surjective π) :
    (π.comp ((center ℝ (LeftInvariantDerivation I G) :
      LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
        (I := I)).toHom).range ≤ Subgroup.center C := by
  rintro _ ⟨a, rfl⟩
  exact Subgroup.map_center_le_center hsurj
    ⟨_, integralLeafSubgroupData_center_toHom_mem_center hc a, rfl⟩

/-- An element `k` of the subgroup integrating `[𝔤, 𝔤]` whose image under a local homeomorphism
`π` lies in the image of the subgroup `A` integrating the centre is central: `k = a * z` with
`a ∈ A` and `z ∈ ker π`, both central in `G`. -/
private theorem mem_center_of_map_mem_range
    (hc : IsCompl (center ℝ (LeftInvariantDerivation I G))
      (derivedSeries ℝ (LeftInvariantDerivation I G) 1))
    {C : Type*} [Group C] [TopologicalSpace C] (π : G →* C) (hπ : IsLocalHomeomorph π)
    {k : ((derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
      LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X}
    (hk : π (((derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
      LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).toHom k) ∈
      (π.comp ((center ℝ (LeftInvariantDerivation I G) :
        LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
          (I := I)).toHom).range) :
    k ∈ Subgroup.center ((derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
      LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hk
  have hz := π.ker_le_center_of_isLocalHomeomorph hπ ((π.eq_iff).mp ha.symm)
  have := Subgroup.mul_mem _ (integralLeafSubgroupData_center_toHom_mem_center hc a) hz
  rw [mul_inv_cancel_left] at this
  exact Subgroup.comap_center_le_center
    ((derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
      LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData
        (I := I)).injective this

/-- **The semisimple factor of a simply connected cover of a compact group is compact.** Let `G`
be a simply connected Lie group whose Lie algebra is the direct sum of its centre `𝔷` and its
derived algebra `[𝔤, 𝔤]`, and `π : G →* C` a surjective homomorphism onto a compact group that is
a local homeomorphism, for instance the projection of the universal covering group of a compact
connected Lie group. Then the subgroup `K` integrating `[𝔤, 𝔤]`, the second factor of
`TauCeti.Lie.centerProdDerivedContinuousMulEquiv`, is compact. -/
theorem compactSpace_integralLeafSubgroupData_derivedSeries
    (hc : IsCompl (center ℝ (LeftInvariantDerivation I G))
      (derivedSeries ℝ (LeftInvariantDerivation I G) 1))
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
    (π : G →* C) (hπ : IsLocalHomeomorph π) (hsurj : Surjective π) :
    CompactSpace ((derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
      LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)).X := by
  set A := (center ℝ (LeftInvariantDerivation I G) :
    LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)
  set D := (derivedSeries ℝ (LeftInvariantDerivation I G) 1 :
    LieSubalgebra ℝ (LeftInvariantDerivation I G)).integralLeafSubgroupData (I := I)
  set Φ := centerProdDerivedContinuousMulEquiv hc with hΦdef
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- The image `N = π(A)` is central in `C`, so `C ⧸ N` is a compact topological group.
  set N := (π.comp A.toHom).range
  have : N.Normal :=
    Subgroup.normal_of_le_center (range_comp_toHom_center_le_center hc π hsurj)
  set f : D.X →* C ⧸ N := (QuotientGroup.mk' N).comp (π.comp D.toHom)
  -- Through the splitting `Φ : A × K ≃ G`, the projection to `C ⧸ N` only sees the factor `K`.
  have hΦ (p : A.X × D.X) : (QuotientGroup.mk (π (Φ p)) : C ⧸ N) = f p.2 := by
    rw [hΦdef, centerProdDerivedContinuousMulEquiv_apply hc p, map_mul, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (π (A.toHom p.1))).mpr (MonoidHom.mem_range.mpr ⟨p.1, rfl⟩),
      one_mul]
    simp [f, D]
  have hopen : IsOpenMap f := fun U hU ↦ by
    have himage : f '' U = (fun p ↦ (QuotientGroup.mk (π (Φ p)) : C ⧸ N)) '' (univ ×ˢ U) := by
      ext y
      simp only [mem_image, mem_prod, mem_univ, true_and, Prod.exists, hΦ]
      exact ⟨fun ⟨k, hk, hky⟩ ↦ ⟨1, k, hk, hky⟩, fun ⟨_, k, hk, hky⟩ ↦ ⟨k, hk, hky⟩⟩
    rw [himage]
    exact (QuotientGroup.isOpenMap_coe.comp (hπ.isOpenMap.comp Φ.toHomeomorph.isOpenMap)) _
      (isOpen_univ.prod hU)
  -- So `K ⧸ ker f` is compact, `ker f` is central in `K`, and Weyl's theorem applies.
  have := f.compactSpace_quotient_ker_of_isOpenMap
    (QuotientGroup.continuous_mk.comp (hπ.continuous.comp D.contMDiff_toHom.continuous)) hopen
  exact f.ker.compactSpace_of_le_center_of_derivedSeries_one_eq_top
    (derivedSeries_one_eq_top_integralLeafSubgroupData_derivedSeries hc)
    (center_eq_bot_integralLeafSubgroupData_derivedSeries hc)
    fun _ hk ↦ mem_center_of_map_mem_range hc π hπ ((QuotientGroup.eq_one_iff _).mp hk)

end TauCeti.Lie

namespace TauCeti.UniversalCover

attribute [local instance] Lie.ImmersedLieSubgroupData.group
  Lie.ImmersedLieSubgroupData.topologicalSpace Lie.ImmersedLieSubgroupData.normedAddCommGroup
  Lie.ImmersedLieSubgroupData.normedSpace Lie.ImmersedLieSubgroupData.modelTopology
  Lie.ImmersedLieSubgroupData.chartedSpace

section Complement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [IsTopologicalGroup G] [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G]
  [CompactSpace G]

/-- The centre and the derived algebra of the Lie algebra of the universal covering group of a
compact Lie group are complementary: the Lie algebra is that of the compact group
(`TauCeti.UniversalCover.lieEquivProjHom`). -/
theorem isCompl_center_derivedSeries_one :
    IsCompl (center ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))))
      (derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1) :=
  (LieEquiv.isCompl_center_derivedSeries_iff (lieEquivProjHom I G)).mpr
    Lie.isCompl_center_derivedSeries_one_of_compactSpace

end Complement

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [IsTopologicalGroup G] [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G]
  [CompactSpace G]

/-- **The semisimple factor of the universal cover of a compact connected Lie group is compact.**
The universal covering group of a compact connected Lie group `G` is the product of the subgroup
integrating the centre of its Lie algebra and the subgroup `K` integrating the derived algebra
(`TauCeti.Lie.centerProdDerivedContinuousMulEquiv`), and `K` is compact. -/
theorem compactSpace_integralLeafSubgroupData_derivedSeries [SecondCountableTopology G]
    [ConnectedSpace G] :
    CompactSpace ((derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 :
      LieSubalgebra ℝ (LeftInvariantDerivation I (UniversalCover (1 : G)))).integralLeafSubgroupData
        (I := I)).X := by
  have hπ := (isCoveringMap_projHom (G := G)).isLocalHomeomorph
  have hsurj := proj_surjective_of_preconnectedSpace (1 : G)
  rw [← coe_projHom] at hsurj
  exact Lie.compactSpace_integralLeafSubgroupData_derivedSeries isCompl_center_derivedSeries_one
    (projHom : UniversalCover (1 : G) →ₜ* G).toMonoidHom hπ hsurj

end TauCeti.UniversalCover

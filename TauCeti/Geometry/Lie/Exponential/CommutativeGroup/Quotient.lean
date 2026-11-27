/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Isogeny
public import TauCeti.Geometry.Lie.Subgroup.NormalQuotient
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.Geometry.Lie.Exponential.Classification
import TauCeti.Geometry.Lie.Subgroup.Kernel
import TauCeti.Topology.Algebra.Group.Connected

/-!
# Period lattices of kernels and quotients of commutative Lie groups

Let `G` be a connected commutative finite-dimensional real Lie group, with Lie algebra `𝔤` and
period lattice `Λ_ℤ(G) = (2π)⁻¹ ker(exp)` (`TauCeti.periodLattice`), and let `N` be a closed
subgroup, with Lie algebra `𝔫`. This file relates the period lattices of `N`, `G` and the
quotient Lie group `G ⧸ N` through the Lie map `dι` of the inclusion and the Lie map `dπ` of the
projection. Informally, the sequence

`0 → Λ_ℤ(N) → Λ_ℤ(G) → Λ_ℤ(G ⧸ N) → π₀(N) → 0`

is exact; the results below give its exactness at `Λ_ℤ(G)` and the order of the cokernel of `dπ`:

* the period lattice of `N` is the part of `Λ_ℤ(G)` lying in `𝔫`
  (`TauCeti.Lie.EmbeddedLieSubgroupData.periodLattice_inf_eq_map_lieMapSubtypeVal`), so its image
  under `dι` is the kernel of `dπ` on `Λ_ℤ(G)`
  (`Subgroup.periodLattice_inf_ker_lieMap_quotientMkSmoothHom`);
* `dπ(Λ_ℤ(G))` has index in `Λ_ℤ(G ⧸ N)` the number of connected components of `N`, the index of
  its identity component `N₀` (`Subgroup.relIndex_map_lieMap_quotientMkSmoothHom_periodLattice`).

In particular, when `N` is connected, `dπ` maps `Λ_ℤ(G)` onto `Λ_ℤ(G ⧸ N)`
(`Subgroup.map_lieMap_quotientMkSmoothHom_periodLattice`): a quotient of a torus by a subtorus has
the quotient lattice `Λ_ℤ(G) / Λ_ℤ(N)` as its period lattice. For a disconnected `N` the lattice
of the quotient is strictly larger. For instance the quotient of the circle by `{±1}` is again a
circle, and `dπ` is multiplication by `2` on lattices `ℤ → ℤ`, of index `2 = |π₀({±1})|`.

These statements are proved for any continuous homomorphism `f : G → G'` of commutative Lie groups
with surjective Lie map `df`. Its kernel is a closed subgroup, and the exponential maps the kernel
of `df` onto the identity component of `ker f` (`ContinuousMonoidHom.image_lieExp_ker_lieMap`).
Indeed, `exp(ker df)` is connected and contained in `ker f`. Conversely, `ker f` is a commutative
Lie group by the closed-subgroup theorem, so its identity component is the image of its own
exponential, which is carried into `exp(ker df)` by the Lie map of the inclusion. With the index
formula `[Λ_ℤ(G') : df(Λ_ℤ(G))] = [ker f : exp(ker df)]`
(`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice_of_surjective`) this gives
`[Λ_ℤ(G') : df(Λ_ℤ(G))] = [ker f : (ker f)₀]`
(`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice_eq_index_connectedComponentOfOne`), and
`df(Λ_ℤ(G)) = Λ_ℤ(G')` when `ker f` is connected
(`ContinuousMonoidHom.map_lieMap_periodLattice_of_surjective`).

## Main results

* `ContinuousMonoidHom.image_lieExp_ker_lieMap`: `exp(ker df)` is the identity component of
  `ker f`.
* `ContinuousMonoidHom.relIndex_map_lieMap_periodLattice_eq_index_connectedComponentOfOne`,
  `ContinuousMonoidHom.map_lieMap_periodLattice_of_surjective`: for surjective `df`, the image of
  the period lattice has index the number of components of `ker f`, and is the whole period
  lattice of the target when `ker f` is connected.
* `TauCeti.Lie.EmbeddedLieSubgroupData.periodLattice_inf_eq_map_lieMapSubtypeVal`: the period
  lattice of a closed subgroup is the part of the ambient period lattice in its Lie algebra.
* `Subgroup.relIndex_map_lieMap_quotientMkSmoothHom_periodLattice`,
  `Subgroup.map_lieMap_quotientMkSmoothHom_periodLattice`,
  `Subgroup.periodLattice_inf_ker_lieMap_quotientMkSmoothHom`: the same statements for the
  quotient `G ⧸ N` by a closed subgroup.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
-/

public section

open Real
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace ContinuousMonoidHom

open TauCeti TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']
  [T2Space G] [BoundarylessManifold I G] [T2Space G'] [BoundarylessManifold I' G']
  [IsMulCommutative G]

/-- **The exponential image of the kernel of the Lie map is the identity component of the
kernel.** For a continuous homomorphism `f : G → G'` out of a commutative Lie group, the
exponential maps the kernel of the Lie map `df` onto the identity component of `ker f`. -/
theorem image_lieExp_ker_lieMap (f : G →ₜ* G') :
    let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    lieExp '' (LinearMap.ker (lieMap (I := I) (I' := I') f).toLinearMap :
        Set (LeftInvariantDerivation I G)) =
      ((Subgroup.connectedComponentOfOne f.ker).map f.ker.subtype : Set G) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have hcont := (contMDiff_lieExp (I := I) (G := G)).continuous
  have hK : IsClosed (f.ker : Set G) := f.isClosed_ker
  -- The kernel is a commutative Lie group by the closed-subgroup theorem.
  let d := EmbeddedLieSubgroupData.ofIsClosed (I := I) hK
  let _ := d.chartedSpace
  let _ := d.lieGroup
  ext g
  simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker, Subgroup.mem_map,
    LieHom.coe_toLinearMap]
  constructor
  · rintro ⟨X, hX, rfl⟩
    -- `t ↦ exp(t X)` is a path in `ker f` from `1` to `exp X`.
    have hmem := (lieMap_eq_zero_iff_forall_lieExp_smul_mem_ker f).1 hX
    let γ : ℝ → f.ker := fun t ↦ ⟨lieExp (t • X), hmem t⟩
    have hγ : Continuous γ := (hcont.comp (continuous_id.smul continuous_const)).subtype_mk _
    refine ⟨γ 1, ?_, by simp [γ]⟩
    have h := (isPreconnected_range hγ).subset_connectedComponent (x := γ 0) ⟨0, rfl⟩
      ⟨1, rfl⟩
    have h0 : γ 0 = 1 := Subtype.ext (by simp [γ, lieExp_zero])
    rwa [h0] at h
  · rintro ⟨n, hn, rfl⟩
    -- The identity component of the kernel is the image of its exponential.
    have hrange := range_lieExp (I := 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) f.ker).toSubmodule))
      (G := f.ker)
    obtain ⟨Y, rfl⟩ : n ∈ Set.range lieExp := by rw [hrange]; exact hn
    refine ⟨d.lieMapSubtypeVal Y, ?_, by rw [d.lieExp_lieMapSubtypeVal, Subgroup.coe_subtype]⟩
    -- `t ↦ exp(t dι Y)` lies in `ker f`, so `df(dι Y)` vanishes.
    refine (lieMap_eq_zero_iff_forall_lieExp_smul_mem_ker f).2 fun t ↦ ?_
    rw [← map_smul, d.lieExp_lieMapSubtypeVal]
    exact (lieExp (t • Y)).property

variable [IsMulCommutative G'] [PreconnectedSpace G]

/-- **The index of the period lattice under a homomorphism with surjective Lie map is the number of
components of the kernel.** Let `f : G → G'` be a continuous homomorphism of commutative Lie
groups, with `G` connected, whose Lie map `df` is surjective. Then the image `df(Λ_ℤ(G))` of the
period lattice of `G` has index `[ker f : (ker f)₀]` in the period lattice of `G'`. -/
theorem relIndex_map_lieMap_periodLattice_eq_index_connectedComponentOfOne (f : G →ₜ* G')
    (hf : Function.Surjective (lieMap (I := I) (I' := I') f)) :
    let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    ((periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom).relIndex
        (periodLattice I' G') = (Subgroup.connectedComponentOfOne f.ker).index := by
  intro _
  have hK₀ : (LinearMap.ker (lieMap (I := I) (I' := I') f).toLinearMap).toAddSubgroup.map
      (lieExpAddMonoidHom (I := I) (G := G)) =
      Subgroup.toAddSubgroup ((Subgroup.connectedComponentOfOne f.ker).map f.ker.subtype) := by
    ext x
    have h := Set.ext_iff.1 (image_lieExp_ker_lieMap (I := I) (I' := I') f) (Additive.toMul x)
    rw [Additive.mem_toAddSubgroup]
    refine Iff.trans ?_ (h.trans SetLike.mem_coe)
    simp only [AddSubgroup.mem_map, lieExpAddMonoidHom_apply, Set.mem_image, SetLike.mem_coe,
      Submodule.mem_toAddSubgroup]
    exact exists_congr fun X ↦ and_congr_right fun _ ↦
      ⟨fun h ↦ by rw [← h, toMul_ofMul], fun h ↦ by rw [h, ofMul_toMul]⟩
  rw [relIndex_map_lieMap_periodLattice_of_surjective f hf, hK₀, Subgroup.relIndex_toAddSubgroup,
    ← Subgroup.relIndex_top_right, ← Subgroup.relIndex_map_map_of_injective _ _
      f.ker.subtype_injective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **Homomorphisms with surjective Lie map and connected kernel map period lattices onto period
lattices.** Let `f : G → G'` be a continuous homomorphism of commutative Lie groups, with `G`
connected, whose Lie map `df` is surjective and whose kernel is connected. Then `df` maps the
period lattice of `G` onto the period lattice of `G'`. -/
theorem map_lieMap_periodLattice_of_surjective (f : G →ₜ* G')
    (hf : Function.Surjective (lieMap (I := I) (I' := I') f)) [PreconnectedSpace f.ker] :
    (periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom =
      periodLattice I' G' := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  refine le_antisymm ?_ (AddSubgroup.relIndex_eq_one.1 ?_)
  · rintro _ ⟨X, hX, rfl⟩
    exact lieMap_mem_periodLattice f hX
  · rw [relIndex_map_lieMap_periodLattice_eq_index_connectedComponentOfOne f hf,
      Subgroup.connectedComponentOfOne_eq_top, Subgroup.index_top]

end ContinuousMonoidHom

namespace TauCeti.Lie.EmbeddedLieSubgroupData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [T2Space G] [BoundarylessManifold I G] [IsMulCommutative G] {N : Subgroup G}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']

/-- **The period lattice of an embedded Lie subgroup.** For an embedded Lie subgroup `N` of a
commutative Lie group `G`, the Lie map of the inclusion identifies the period lattice of `N` with
the elements of the period lattice of `G` lying in the Lie algebra `𝔫` of `N`:
`dι(Λ_ℤ(N)) = Λ_ℤ(G) ∩ 𝔫`. -/
theorem periodLattice_inf_eq_map_lieMapSubtypeVal (d : EmbeddedLieSubgroupData I N E') :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    periodLattice I G ⊓ (lieSubalgebraOfSubgroup (I := I) N).toSubmodule.toAddSubgroup =
      (periodLattice 𝓘(ℝ, E') N).map d.lieMapSubtypeVal.toLinearMap.toAddMonoidHom := by
  intro _ _
  ext X
  simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, LieSubalgebra.mem_toSubmodule,
    AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap]
  constructor
  · rintro ⟨hX, hXN⟩
    obtain ⟨Y, rfl⟩ := (LieHom.mem_range _ _).1 (d.range_lieMapSubtypeVal_eq.symm ▸ hXN)
    refine ⟨Y, ?_, rfl⟩
    rw [mem_periodLattice] at hX ⊢
    apply Subtype.ext
    rw [← map_smul, d.lieExp_lieMapSubtypeVal] at hX
    rw [hX, OneMemClass.coe_one]
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨?_, d.range_lieMapSubtypeVal_eq ▸ LieHom.mem_range_self _ _⟩
    rw [mem_periodLattice] at hY ⊢
    rw [← map_smul, d.lieExp_lieMapSubtypeVal, hY, OneMemClass.coe_one]

end TauCeti.Lie.EmbeddedLieSubgroupData

namespace Subgroup

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [IsMulCommutative G] {N : Subgroup G}

/-- **The kernel of the quotient lattice map.** For a closed subgroup `N` of a commutative Lie
group `G`, the elements of the period lattice of `G` killed by the Lie map of the projection
`G → G ⧸ N` are the image of the period lattice of `N` under the Lie map of the inclusion, for the
Lie group structure of `N` given by the closed-subgroup theorem. -/
theorem periodLattice_inf_ker_lieMap_quotientMkSmoothHom (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    haveI : T2Space G := I.t2Space_of_lieGroup ∞
    letI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).chartedSpace
    haveI := (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I) hN).lieGroup
    periodLattice I G ⊓
        (LinearMap.ker (lieMap (quotientMkSmoothHom I hN)).toLinearMap).toAddSubgroup =
      (periodLattice 𝓘(ℝ, (Lie.lieSubalgebraOfSubgroup (I := I) N).toSubmodule) N).map
        (Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I)
          hN).lieMapSubtypeVal.toLinearMap.toAddMonoidHom := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  have : T2Space G := I.t2Space_of_lieGroup ∞
  rw [← Lie.EmbeddedLieSubgroupData.periodLattice_inf_eq_map_lieMapSubtypeVal]
  congr 1
  ext X
  rw [Submodule.mem_toAddSubgroup, LinearMap.mem_ker, LieHom.coe_toLinearMap,
    lieMap_quotientMkSmoothHom_eq_zero_iff, Submodule.mem_toAddSubgroup,
    LieSubalgebra.mem_toSubmodule]

omit [IsMulCommutative G] in
/-- The Lie map of the projection `G → G ⧸ N`, viewed as a continuous homomorphism, is the Lie map
of the smooth projection. -/
theorem lieMap_quotientMkContinuousMonoidHom [N.Normal] (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI : T2Space G := I.t2Space_of_lieGroup ∞
    ContinuousMonoidHom.lieMap (I := I) (I' := 𝓘(ℝ, QuotientModelSpace I N))
        (quotientMkContinuousMonoidHom N) =
      lieMap (quotientMkSmoothHom I hN) := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : T2Space G := I.t2Space_of_lieGroup ∞
  rw [ContinuousMonoidHom.lieMap_def]
  congr 1
  apply DFunLike.coe_injective
  rw [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism, coe_quotientMkSmoothHom]
  exact funext (quotientMkContinuousMonoidHom_apply N)

variable [PreconnectedSpace G]

/-- **The quotient lattice has index the number of components.** For a closed subgroup `N` of a
connected commutative Lie group `G`, the Lie map of the projection `π : G → G ⧸ N` maps the period
lattice of `G` onto a subgroup of index `[N : N₀]` of the period lattice of `G ⧸ N`, where `N₀` is
the identity component of `N`. -/
theorem relIndex_map_lieMap_quotientMkSmoothHom_periodLattice (hN : IsClosed (N : Set G)) :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    haveI : IsMulCommutative (G ⧸ N) := (QuotientGroup.mk'_surjective N).isMulCommutative
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI : T2Space G := I.t2Space_of_lieGroup ∞
    ((periodLattice I G).map
        (lieMap (quotientMkSmoothHom I hN)).toLinearMap.toAddMonoidHom).relIndex
      (periodLattice 𝓘(ℝ, QuotientModelSpace I N) (G ⧸ N)) =
      (connectedComponentOfOne N).index := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  have : IsMulCommutative (G ⧸ N) := (QuotientGroup.mk'_surjective N).isMulCommutative
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have hq := lieMap_quotientMkContinuousMonoidHom (I := I) hN
  rw [← hq, ContinuousMonoidHom.relIndex_map_lieMap_periodLattice_eq_index_connectedComponentOfOne
    _ (hq ▸ surjective_lieMap_quotientMkSmoothHom hN), ker_quotientMkContinuousMonoidHom N]

/-- **Quotients by connected subgroups use the quotient lattice.** For a closed connected
subgroup `N` of a connected commutative Lie group `G`, the Lie map of the projection
`π : G → G ⧸ N` maps the period lattice of `G` onto the period lattice of `G ⧸ N`. -/
theorem map_lieMap_quotientMkSmoothHom_periodLattice (hN : IsClosed (N : Set G))
    [PreconnectedSpace N] :
    letI := quotientChartedSpaceOfIsClosed I hN
    haveI := lieGroup_quotientOfIsClosed (I := I) hN
    haveI : IsMulCommutative (G ⧸ N) := (QuotientGroup.mk'_surjective N).isMulCommutative
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI : T2Space G := I.t2Space_of_lieGroup ∞
    (periodLattice I G).map (lieMap (quotientMkSmoothHom I hN)).toLinearMap.toAddMonoidHom =
      periodLattice 𝓘(ℝ, QuotientModelSpace I N) (G ⧸ N) := by
  let _ := quotientChartedSpaceOfIsClosed I hN
  have := lieGroup_quotientOfIsClosed (I := I) hN
  have : IsMulCommutative (G ⧸ N) := (QuotientGroup.mk'_surjective N).isMulCommutative
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : PreconnectedSpace (quotientMkContinuousMonoidHom N).ker := by
    rw [ker_quotientMkContinuousMonoidHom N]
    infer_instance
  have hq := lieMap_quotientMkContinuousMonoidHom (I := I) hN
  rw [← hq]
  exact ContinuousMonoidHom.map_lieMap_periodLattice_of_surjective _
    (hq ▸ surjective_lieMap_quotientMkSmoothHom hN)

end Subgroup

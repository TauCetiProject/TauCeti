/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Prod.Quotient
public import TauCeti.Geometry.Lie.UniversalCover.DerivedFactor

import TauCeti.Geometry.Lie.Subgroup.Center

/-!
# The finite cover of a compact connected Lie group by a torus times a compact group

Let `G` be a compact connected Lie group, `G'` its universal covering group and `𝔤` their common
Lie algebra. Since `𝔤` is the direct sum of its centre `𝔷` and its derived algebra `[𝔤, 𝔤]`,
the group `G'` is the product of the vector group `𝔷` with the subgroup `K` integrating `[𝔤, 𝔤]`
(`TauCeti.Lie.lieExpCenterProdDerivedContinuousMulEquiv`), and `K` is compact
(`TauCeti.UniversalCover.compactSpace_integralLeafSubgroupData_derivedSeries`). Followed by the
covering projection, this gives the covering homomorphism

`𝔷 × K → G`, `(z, k) ↦ π(exp z · k)`

(`TauCeti.UniversalCover.centerProdDerivedCover`). This file turns it into a finite covering
of `G` by the product of a torus and `K`.

* The group `K` is compact, simply connected, and its Lie algebra `[𝔤, 𝔤]` is perfect with trivial
  centre, so `K` has finite centre.
* The kernel `Γ` of `𝔷 × K → G` is discrete, hence central since `𝔷 × K` is connected
  (`TauCeti.UniversalCover.ker_centerProdDerivedCover_le_center`). So its image in `K` lies in the
  finite centre of `K`.
* The part `Λ = {z ∈ 𝔷 | π(exp z) = 1}` of `Γ` in `𝔷` (`TauCeti.UniversalCover.centerLattice`) is
  therefore a full lattice in `𝔷` (`TauCeti.UniversalCover.isZLattice_centerLattice`), because
  `(𝔷 × K) ⧸ Γ ≅ G` is compact, and the torus `T = 𝔷 ⧸ Λ` is compact. A `ℤ`-basis of `Λ`
  identifies `T` with a product of circles (`Module.Basis.quotientLatticeEquiv`).
* The homomorphism `T × K → G`, `([z], k) ↦ π(exp z · k)`
  (`TauCeti.UniversalCover.torusProdDerivedCover`), is the quotient map
  `(𝔷 ⧸ Λ) × K → (𝔷 × K) ⧸ Γ` of `Subgroup.prodQuotientMap` followed by the isomorphism
  `(𝔷 × K) ⧸ Γ ≅ G`. It is a surjective covering map
  (`TauCeti.UniversalCover.isCoveringMap_torusProdDerivedCover`) with finite fibres
  (`TauCeti.UniversalCover.finite_torusProdDerivedCover_preimage`).

For `G = U(n)` this is the cover `S¹ × SU(n) → U(n)`, `(z, A) ↦ z A`, of degree `n`; for a torus,
`K` is trivial and the cover is an isomorphism.

## Main definitions

* `TauCeti.UniversalCover.centerFactor`, `TauCeti.UniversalCover.derivedFactor`: the centre `𝔷`
  of the Lie algebra and the subgroup `K` integrating `[𝔤, 𝔤]`.
* `TauCeti.UniversalCover.centerProdDerivedCover`: the covering homomorphism `𝔷 × K → G`.
* `TauCeti.UniversalCover.centerLattice`: the lattice `Λ ⊆ 𝔷`.
* `TauCeti.UniversalCover.torusProdDerivedCover`: the finite covering homomorphism `T × K → G`.

## Main results

* `TauCeti.UniversalCover.isZLattice_centerLattice`: `Λ` is a full lattice in `𝔷`.
* `TauCeti.UniversalCover.isCoveringMap_torusProdDerivedCover`,
  `TauCeti.UniversalCover.torusProdDerivedCover_surjective`,
  `TauCeti.UniversalCover.finite_torusProdDerivedCover_preimage`: `T × K → G` is a surjective
  covering map with finite fibres.
* The instances `CompactSpace`, `SimplyConnectedSpace` and `Finite (Subgroup.center _)` for `K`,
  and `CompactSpace` for the torus `T`.

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

namespace TauCeti.UniversalCover

attribute [local instance] Lie.ImmersedLieSubgroupData.group
  Lie.ImmersedLieSubgroupData.topologicalSpace Lie.ImmersedLieSubgroupData.normedAddCommGroup
  Lie.ImmersedLieSubgroupData.normedSpace Lie.ImmersedLieSubgroupData.finiteDimensional
  Lie.ImmersedLieSubgroupData.modelTopology Lie.ImmersedLieSubgroupData.chartedSpace
  Lie.ImmersedLieSubgroupData.lieGroup Lie.ImmersedLieSubgroupData.connectedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [IsTopologicalGroup G] [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G]
  [T2Space G] [SecondCountableTopology G]

/-- The centre `𝔷` of the Lie algebra of the universal covering group of `G`, a real vector space.
It is the Lie algebra of the centre factor of the universal cover. -/
abbrev centerFactor : Type _ :=
  (center ℝ (LeftInvariantDerivation I (UniversalCover (1 : G)))).toSubmodule

/-- The subgroup `K` of the universal covering group of `G` integrating the derived algebra
`[𝔤, 𝔤]` of its Lie algebra, with its intrinsic Lie group structure. -/
abbrev derivedFactor : Type _ :=
  ((derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 :
    LieSubalgebra ℝ (LeftInvariantDerivation I (UniversalCover (1 : G)))).integralLeafSubgroupData
      (I := I)).X

variable [CompactSpace G]

/-- The covering homomorphism `𝔷 × K → G`, `(z, k) ↦ π(exp z · k)`: the splitting of the universal
covering group of the compact Lie group `G` along the centre and the derived algebra of its Lie
algebra (`TauCeti.Lie.lieExpCenterProdDerivedContinuousMulEquiv`), followed by the covering
projection. -/
def centerProdDerivedCover : Multiplicative (centerFactor I G) × derivedFactor I G →ₜ* G :=
  projHom.comp
    (ContinuousMonoidHom.toContinuousMonoidHom (Lie.lieExpCenterProdDerivedContinuousMulEquiv
      (I := I) isCompl_center_derivedSeries_one))

variable {I G}

/-- The covering homomorphism `𝔷 × K → G` sends `(z, k)` to `π(exp z · k)`. -/
@[simp]
theorem centerProdDerivedCover_apply (p : Multiplicative (centerFactor I G) × derivedFactor I G) :
    centerProdDerivedCover I G p =
      proj (lieExp (I := I) (p.1.toAdd : LeftInvariantDerivation I (UniversalCover (1 : G))) *
        (LieSubalgebra.integralLeafSubgroupData (I := I)
          (derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 :
            LieSubalgebra ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))))).toHom p.2) := by
  simp [centerProdDerivedCover, coe_projHom]

/-- `𝔷 × K → G` is a covering map: it is the covering projection of the universal cover,
precomposed with the isomorphism of `𝔷 × K` onto the universal covering group. -/
theorem isCoveringMap_centerProdDerivedCover : IsCoveringMap (centerProdDerivedCover I G) :=
  (isCoveringMap_projHom (G := G)).comp_homeomorph
    (Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
      isCompl_center_derivedSeries_one).toHomeomorph

/-- `𝔷 × K → G` is surjective when `G` is connected. -/
theorem centerProdDerivedCover_surjective [ConnectedSpace G] :
    Surjective (centerProdDerivedCover I G) := by
  have hsurj := proj_surjective_of_preconnectedSpace (1 : G)
  rw [← coe_projHom] at hsurj
  exact hsurj.comp (Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
      isCompl_center_derivedSeries_one).surjective

/-- `K` is a topological group, as a Lie group. -/
instance : IsTopologicalGroup (derivedFactor I G) :=
  topologicalGroup_of_lieGroup
    ((derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 :
      LieSubalgebra ℝ (LeftInvariantDerivation I (UniversalCover (1 : G)))).integralLeafSubgroupData
        (I := I)).I' ∞

/-- **The kernel `Γ` of `𝔷 × K → G` is central**: it is discrete, and `𝔷 × K` is connected. -/
theorem ker_centerProdDerivedCover_le_center :
    (centerProdDerivedCover I G).toMonoidHom.ker ≤ Subgroup.center _ := by
  have : ConnectedSpace (Multiplicative (centerFactor I G) × derivedFactor I G) :=
    ((Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
      isCompl_center_derivedSeries_one).toHomeomorph.connectedSpace_iff).mpr inferInstance
  exact MonoidHom.ker_le_center_of_isLocalHomeomorph _
    isCoveringMap_centerProdDerivedCover.isLocalHomeomorph

/-- The kernel `Γ` of `𝔷 × K → G` is discrete, as the kernel of a local homeomorphism. -/
instance : DiscreteTopology (centerProdDerivedCover I G).toMonoidHom.ker :=
  isDiscrete_iff_discreteTopology.mp <| MonoidHom.isDiscrete_ker_of_isLocalHomeomorph _
    isCoveringMap_centerProdDerivedCover.isLocalHomeomorph

/-- `K` is compact (Weyl's theorem). -/
instance [ConnectedSpace G] : CompactSpace (derivedFactor I G) :=
  compactSpace_integralLeafSubgroupData_derivedSeries

/-- `K` is simply connected, as a factor of the universal covering group. -/
instance : SimplyConnectedSpace (derivedFactor I G) :=
  Lie.simplyConnectedSpace_integralLeafSubgroupData_derivedSeries isCompl_center_derivedSeries_one

/-- `K` has finite centre: it is compact, and its Lie algebra has trivial centre. -/
instance [ConnectedSpace G] : Finite (Subgroup.center (derivedFactor I G)) :=
  Lie.finite_center_of_center_eq_bot
    (Lie.center_eq_bot_integralLeafSubgroupData_derivedSeries isCompl_center_derivedSeries_one)

/-- The image of `Γ` in `K` is finite, since it is central in `K`. -/
private instance [ConnectedSpace G] :
    Finite ((centerProdDerivedCover I G).toMonoidHom.ker.map
      (MonoidHom.snd _ (derivedFactor I G))) :=
  Subgroup.finite_map_snd_of_le_center _ ker_centerProdDerivedCover_le_center

/-- `(𝔷 × K) ⧸ Γ` is compact, since `𝔷 × K → G` is open. -/
private instance : CompactSpace
    ((Multiplicative (centerFactor I G) × derivedFactor I G) ⧸
      (centerProdDerivedCover I G).toMonoidHom.ker) :=
  MonoidHom.compactSpace_quotient_ker_of_isOpenMap _ (centerProdDerivedCover I G).continuous
    isCoveringMap_centerProdDerivedCover.isLocalHomeomorph.isOpenMap

variable (I G) in
/-- The lattice `Λ = {z ∈ 𝔷 | π(exp z) = 1}`, the part of the kernel `Γ` of `𝔷 × K → G` lying in
`𝔷` (`TauCeti.UniversalCover.mem_centerLattice_iff`). -/
abbrev centerLattice : Subgroup (Multiplicative (centerFactor I G)) :=
  (centerProdDerivedCover I G).toMonoidHom.ker.comap (MonoidHom.inl _ _)

/-- An element `z ∈ 𝔷` lies in `Λ` exactly when `π(exp z) = 1`. -/
theorem mem_centerLattice_iff (z : Multiplicative (centerFactor I G)) :
    z ∈ centerLattice I G ↔
      proj (lieExp (I := I) (z.toAdd : LeftInvariantDerivation I (UniversalCover (1 : G)))) =
        1 := by
  simp [centerProdDerivedCover_apply]

/-- **`Λ` is a full lattice in `𝔷`**: it is discrete, and it spans `𝔷` because `(𝔷 × K) ⧸ Γ` is
compact and the image of `Γ` in `K` is finite. -/
theorem isZLattice_centerLattice [ConnectedSpace G] :
    IsZLattice ℝ (centerLattice I G).toAddSubgroup'.toIntSubmodule :=
  Subgroup.isZLattice_toAddSubgroup'_comap_inl _

/-- The torus `T = 𝔷 ⧸ Λ` is compact, as the quotient of `𝔷` by a full lattice. -/
instance [ConnectedSpace G] :
    CompactSpace (Multiplicative (centerFactor I G) ⧸ centerLattice I G) :=
  Subgroup.compactSpace_quotient_comap_inl _

variable (I G) in
/-- **The finite cover `T × K → G`** of a compact connected Lie group by the product of the torus
`T = 𝔷 ⧸ Λ` and the compact simply connected group `K`: `([z], k) ↦ π(exp z · k)`
(`TauCeti.UniversalCover.torusProdDerivedCover_mk`). It is a surjective covering map with finite
fibres (`TauCeti.UniversalCover.isCoveringMap_torusProdDerivedCover`,
`TauCeti.UniversalCover.finite_torusProdDerivedCover_preimage`). -/
def torusProdDerivedCover :
    (Multiplicative (centerFactor I G) ⧸ centerLattice I G) × derivedFactor I G →ₜ* G where
  toMonoidHom := MonoidHom.noncommCoprod
      (QuotientGroup.lift (centerLattice I G)
        ((centerProdDerivedCover I G).toMonoidHom.comp (MonoidHom.inl _ _)) fun _ h ↦ h)
      ((centerProdDerivedCover I G).toMonoidHom.comp (MonoidHom.inr _ _))
      fun x k ↦ QuotientGroup.induction_on x fun z ↦
        (MonoidHom.commute_inl_inr z k).map (centerProdDerivedCover I G).toMonoidHom
  continuous_toFun :=
    (QuotientGroup.isOpenQuotientMap_mk.prodMap .id).isQuotientMap.continuous_iff.2 <|
      (centerProdDerivedCover I G).continuous.congr fun p ↦ by
        simp [-centerProdDerivedCover_apply, ← map_mul (centerProdDerivedCover I G)]

/-- `T × K → G` sends `([z], k)` to the image `π(exp z · k)` of `(z, k)` under `𝔷 × K → G`. -/
@[simp]
theorem torusProdDerivedCover_mk (z : Multiplicative (centerFactor I G)) (k : derivedFactor I G) :
    torusProdDerivedCover I G ((z : Multiplicative (centerFactor I G) ⧸ centerLattice I G), k) =
      centerProdDerivedCover I G (z, k) := by
  simp [torusProdDerivedCover, -centerProdDerivedCover_apply,
    ← map_mul (centerProdDerivedCover I G)]

variable [ConnectedSpace G]

/-- The isomorphism `(𝔷 × K) ⧸ Γ ≃ₜ* G` induced by the open surjection `𝔷 × K → G`. -/
private def quotientKerEquiv :
    (Multiplicative (centerFactor I G) × derivedFactor I G) ⧸
      (centerProdDerivedCover I G).toMonoidHom.ker ≃ₜ* G :=
  ContinuousMulEquiv.quotientKerEquivOfSurjective _
    (isCoveringMap_centerProdDerivedCover.isLocalHomeomorph.isOpenMap.isStrictMap
      (centerProdDerivedCover I G).continuous)
    centerProdDerivedCover_surjective

/-- `T × K → G` is `(𝔷 ⧸ Λ) × K → (𝔷 × K) ⧸ Γ` followed by `(𝔷 × K) ⧸ Γ ≃ₜ* G`. -/
private theorem quotientKerEquiv_comp_prodQuotientMap :
    ⇑(quotientKerEquiv (I := I) (G := G)) ∘
        (centerProdDerivedCover I G).toMonoidHom.ker.prodQuotientMap =
      torusProdDerivedCover I G := by
  ext ⟨x, k⟩
  induction x using QuotientGroup.induction_on with
  | H z =>
    simp only [comp_apply, Subgroup.prodQuotientMap_mk, quotientKerEquiv,
      ContinuousMulEquiv.quotientKerEquivOfSurjective_apply_mk]
    exact (torusProdDerivedCover_mk z k).symm

/-- **`T × K → G` is a covering map.** -/
theorem isCoveringMap_torusProdDerivedCover : IsCoveringMap (torusProdDerivedCover I G) :=
  quotientKerEquiv_comp_prodQuotientMap (I := I) (G := G) ▸
    (Subgroup.isCoveringMap_prodQuotientMap _).homeomorph_comp quotientKerEquiv.toHomeomorph

/-- `T × K → G` is surjective. -/
theorem torusProdDerivedCover_surjective : Surjective (torusProdDerivedCover I G) :=
  quotientKerEquiv_comp_prodQuotientMap (I := I) (G := G) ▸
    quotientKerEquiv.surjective.comp (Subgroup.surjective_prodQuotientMap _)

/-- **`T × K → G` has finite fibres**: each fibre is in bijection with the image of `Γ` in the
finite centre of `K`. -/
theorem finite_torusProdDerivedCover_preimage (g : G) :
    (torusProdDerivedCover I G ⁻¹' {g}).Finite := by
  have h : (quotientKerEquiv (I := I) (G := G)) ⁻¹' {g} = {quotientKerEquiv.symm g} := by
    ext x
    simp [ContinuousMulEquiv.eq_symm_apply]
  rw [← quotientKerEquiv_comp_prodQuotientMap (I := I) (G := G), preimage_comp, h]
  exact Subgroup.finite_prodQuotientMap_preimage _ _

end TauCeti.UniversalCover

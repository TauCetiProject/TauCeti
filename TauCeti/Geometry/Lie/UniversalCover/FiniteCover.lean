/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Prod.Quotient
public import TauCeti.Geometry.Lie.Subgroup.Center
public import TauCeti.Geometry.Lie.UniversalCover.DerivedFactor
public import TauCeti.Topology.Algebra.Group.Quotient.Prod

/-!
# The finite cover of a compact connected Lie group by a torus times a compact group

Let `G` be a compact connected Lie group, `U` its universal covering group, `𝔤` the Lie algebra
of `U` (which is that of `G`), `𝔷` its centre and `K` the subgroup of `U` integrating the derived
algebra `[𝔤, 𝔤]`. Then `(z, k) ↦ exp z * k` identifies `𝔷 × K` with `U`
(`TauCeti.Lie.lieExpCenterProdDerivedContinuousMulEquiv`), and `K` is compact
(`TauCeti.UniversalCover.compactSpace_integralLeafSubgroupData_derivedSeries`). Following it by the
covering projection gives a surjective covering homomorphism

`ψ : 𝔷 × K → G`, `(z, k) ↦ π(exp z * k)`

(`TauCeti.UniversalCover.centerProdDerivedProjHom`), whose kernel `Γ` is discrete and central. So
`G` is the quotient `(𝔷 × K) ⧸ Γ` as a topological group
(`TauCeti.UniversalCover.quotientKerCenterProdDerivedProjHom`).

The group `K` is simply connected, as a factor of `U`
(`TauCeti.Lie.simplyConnectedSpace_integralLeafSubgroupData_derivedSeries`), and its Lie algebra
`[𝔤, 𝔤]` is perfect and has trivial centre, so its centre is finite
(`TauCeti.UniversalCover.finite_center_integralLeafSubgroupData_derivedSeries`). Hence the image of
the central subgroup `Γ` in `K` is finite, and the part

`Λ = {z ∈ 𝔷 | exp z ∈ ker π}`

of `Γ` in `𝔷` (`TauCeti.UniversalCover.deckLattice`) is a full lattice in the vector space `𝔷`
(`TauCeti.UniversalCover.isZLattice_deckLattice`), so `T = 𝔷 ⧸ Λ` is a torus. The homomorphism
`ψ` descends to

`T × K → G`, `([z], k) ↦ π(exp z * k)`

(`TauCeti.UniversalCover.torusProdDerivedCover`), a surjective covering map with finite fibres
(`TauCeti.UniversalCover.isCoveringMap_torusProdDerivedCover`,
`TauCeti.UniversalCover.surjective_torusProdDerivedCover`,
`TauCeti.UniversalCover.finite_torusProdDerivedCover_preimage`): every compact connected Lie group
is finitely covered by the product of a torus and a compact simply connected group with
semisimple Lie algebra.

For `G = U(n)` this is the cover `S¹ × SU(n) → U(n)`, `(z, A) ↦ zA`, with `n` sheets; for a torus
`K` is trivial and the cover is the identity, while `𝔷 → G` itself is not a finite covering.

## Main definitions

* `TauCeti.UniversalCover.centerProdDerivedProjHom`: the covering homomorphism `𝔷 × K → G`.
* `TauCeti.UniversalCover.quotientKerCenterProdDerivedProjHom`: `(𝔷 × K) ⧸ Γ ≃ₜ* G`.
* `TauCeti.UniversalCover.deckLattice`: the lattice `Λ ⊆ 𝔷`.
* `TauCeti.UniversalCover.torusProdDerivedCover`: the finite covering `(𝔷 ⧸ Λ) × K → G`.

## Main results

* `TauCeti.UniversalCover.finite_center_integralLeafSubgroupData_derivedSeries`: `K` has finite
  centre.
* `TauCeti.UniversalCover.isZLattice_deckLattice`: `Λ` is a full lattice in `𝔷`.
* `TauCeti.UniversalCover.compactSpace_quotient_deckLattice`: the torus `𝔷 ⧸ Λ` is compact.
* The instances `IsTopologicalGroup`, `CompactSpace` and `SimplyConnectedSpace` for `K`.
* `TauCeti.UniversalCover.isCoveringMap_torusProdDerivedCover`,
  `TauCeti.UniversalCover.surjective_torusProdDerivedCover`,
  `TauCeti.UniversalCover.finite_torusProdDerivedCover_preimage`: `(𝔷 ⧸ Λ) × K → G` is a surjective
  covering map with finite fibres.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, Theorem 8.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.31).
-/

public section

open Function LieAlgebra
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
  [T2Space G] [SecondCountableTopology G] [CompactSpace G]

/-- The centre `𝔷` of the Lie algebra of the universal covering group `U` of `G`, a real vector
space. -/
noncomputable abbrev centerFactor :
    Submodule ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) :=
  (center ℝ (LeftInvariantDerivation I (UniversalCover (1 : G)))).toSubmodule

/-- The subgroup `K` of the universal covering group `U` of `G` integrating the derived algebra
`[𝔤, 𝔤]` of its Lie algebra, with its intrinsic Lie group structure. -/
abbrev derivedFactor : Type _ :=
  ((derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 :
    LieSubalgebra ℝ (LeftInvariantDerivation I (UniversalCover (1 : G)))).integralLeafSubgroupData
      (I := I)).X

/-- **The covering homomorphism `𝔷 × K → G`** of a compact connected Lie group `G`,
`(z, k) ↦ π(exp z * k)`: the splitting `𝔷 × K ≃ₜ* U` of the universal covering group
(`TauCeti.Lie.lieExpCenterProdDerivedContinuousMulEquiv`), where `𝔷` is the centre of the Lie
algebra of `U` and `K` the subgroup integrating its derived algebra, followed by the covering
projection `π : U → G`. -/
noncomputable def centerProdDerivedProjHom :
    Multiplicative (centerFactor I G) × derivedFactor I G →* G :=
  (projHom : UniversalCover (1 : G) →ₜ* G).toMonoidHom.comp
    (Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
      isCompl_center_derivedSeries_one).toMulEquiv.toMonoidHom

@[simp]
theorem centerProdDerivedProjHom_apply
    (p : Multiplicative (centerFactor I G) × derivedFactor I G) :
    centerProdDerivedProjHom I G p =
      (lieExp (I := I) (p.1.toAdd : LeftInvariantDerivation I (UniversalCover (1 : G))) *
        ((derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 :
          LieSubalgebra ℝ (LeftInvariantDerivation I
            (UniversalCover (1 : G)))).integralLeafSubgroupData (I := I)).toHom p.2).proj := by
  simp [centerProdDerivedProjHom]

/-- The homomorphism `𝔷 × K → G` is continuous. -/
theorem continuous_centerProdDerivedProjHom : Continuous (centerProdDerivedProjHom I G) :=
  (projHom : UniversalCover (1 : G) →ₜ* G).continuous.comp
    (Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
      isCompl_center_derivedSeries_one).continuous

/-- The homomorphism `𝔷 × K → G` is a covering map, as the universal covering projection read
through the splitting `𝔷 × K ≃ₜ* U`. -/
theorem isCoveringMap_centerProdDerivedProjHom :
    IsCoveringMap (centerProdDerivedProjHom I G) :=
  isCoveringMap_projHom.comp_homeomorph
    (Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
      isCompl_center_derivedSeries_one).toHomeomorph

omit [T2Space G] [CompactSpace G] in
/-- The group `K` integrating the derived algebra is a topological group, as a Lie group. -/
instance isTopologicalGroup_derivedFactor : IsTopologicalGroup (derivedFactor I G) :=
  topologicalGroup_of_lieGroup ((derivedSeries ℝ
    (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 :
      LieSubalgebra ℝ (LeftInvariantDerivation I (UniversalCover (1 : G)))).integralLeafSubgroupData
        (I := I)).I' ∞

omit [T2Space G] [CompactSpace G] in
/-- The group `K` integrating the derived algebra is simply connected, as a factor of the universal
covering group. -/
instance simplyConnectedSpace_derivedFactor : SimplyConnectedSpace (derivedFactor I G) :=
  Lie.simplyConnectedSpace_integralLeafSubgroupData_derivedSeries isCompl_center_derivedSeries_one

/-- The kernel of `𝔷 × K → G` is discrete. -/
instance discreteTopology_ker_centerProdDerivedProjHom :
    DiscreteTopology (centerProdDerivedProjHom I G).ker :=
  SetLike.isDiscrete_iff_discreteTopology.mp
    ((centerProdDerivedProjHom I G).isDiscrete_ker_of_isLocalHomeomorph
      (isCoveringMap_centerProdDerivedProjHom I G).isLocalHomeomorph)

/-- The kernel of `𝔷 × K → G` is central. -/
theorem ker_centerProdDerivedProjHom_le_center :
    (centerProdDerivedProjHom I G).ker ≤ Subgroup.center _ :=
  -- The source is preconnected, being homeomorphic to the universal cover.
  have := (Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
    (isCompl_center_derivedSeries_one (G := G))).symm.surjective.denseRange.preconnectedSpace
      (Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
        (isCompl_center_derivedSeries_one (G := G))).symm.continuous
  (centerProdDerivedProjHom I G).ker_le_center_of_isLocalHomeomorph
    (isCoveringMap_centerProdDerivedProjHom I G).isLocalHomeomorph

/-- **The deck lattice** `Λ = {z ∈ 𝔷 | π(exp z) = 1}` of a compact connected Lie group: the part of
the kernel of `𝔷 × K → G` lying in the centre `𝔷` of the Lie algebra. -/
noncomputable abbrev deckLattice : Subgroup (Multiplicative (centerFactor I G)) :=
  (centerProdDerivedProjHom I G).ker.comap (MonoidHom.inl _ _)

theorem mem_deckLattice_iff {z : Multiplicative (centerFactor I G)} :
    z ∈ deckLattice I G ↔
      (lieExp (I := I) (z.toAdd : LeftInvariantDerivation I (UniversalCover (1 : G)))).proj =
        1 := by
  simp [deckLattice]

/-- **The finite cover `(𝔷 ⧸ Λ) × K → G`** of a compact connected Lie group `G`,
`([z], k) ↦ π(exp z * k)`, by the product of the torus `𝔷 ⧸ Λ` of the deck lattice
(`TauCeti.UniversalCover.deckLattice`) and the compact group `K` integrating the derived algebra.
It is a surjective covering map with finite fibres
(`TauCeti.UniversalCover.isCoveringMap_torusProdDerivedCover`,
`TauCeti.UniversalCover.surjective_torusProdDerivedCover`,
`TauCeti.UniversalCover.finite_torusProdDerivedCover_preimage`). -/
noncomputable def torusProdDerivedCover :
    (Multiplicative (centerFactor I G) ⧸ deckLattice I G) × derivedFactor I G →* G :=
  MonoidHom.noncommCoprod
    (QuotientGroup.lift (deckLattice I G) ((centerProdDerivedProjHom I G).comp (MonoidHom.inl _ _))
      fun _ h ↦ h)
    ((centerProdDerivedProjHom I G).comp (MonoidHom.inr _ _))
    fun t k ↦ QuotientGroup.induction_on t fun z ↦
      (MonoidHom.commute_inl_inr z k).map (centerProdDerivedProjHom I G)

@[simp]
theorem torusProdDerivedCover_mk (z : Multiplicative (centerFactor I G)) (k : derivedFactor I G) :
    torusProdDerivedCover I G ((z : _ ⧸ deckLattice I G), k) =
      centerProdDerivedProjHom I G (z, k) := by
  rw [torusProdDerivedCover, MonoidHom.noncommCoprod_apply]
  -- The two factors are `ψ (z, 1)` and `ψ (1, k)`, whose product is `ψ (z, k)`.
  exact (map_mul (centerProdDerivedProjHom I G) (z, 1) (1, k)).symm.trans
    (by rw [Prod.mk_mul_mk, mul_one, one_mul])

variable [ConnectedSpace G]

/-- The homomorphism `𝔷 × K → G` is surjective when `G` is connected. -/
theorem surjective_centerProdDerivedProjHom :
    Surjective (centerProdDerivedProjHom I G) := by
  intro x
  obtain ⟨y, rfl⟩ := proj_surjective_of_preconnectedSpace (1 : G) x
  refine ⟨(Lie.lieExpCenterProdDerivedContinuousMulEquiv (I := I)
    isCompl_center_derivedSeries_one).symm y, ?_⟩
  simp [centerProdDerivedProjHom]

/-- **A compact connected Lie group is a quotient of `𝔷 × K`**: `(𝔷 × K) ⧸ Γ ≃ₜ* G` for the kernel
`Γ` of `TauCeti.UniversalCover.centerProdDerivedProjHom`. -/
noncomputable def quotientKerCenterProdDerivedProjHom :
    (Multiplicative (centerFactor I G) × derivedFactor I G) ⧸
      (centerProdDerivedProjHom I G).ker ≃ₜ* G :=
  ContinuousMulEquiv.quotientKerEquivOfSurjective (centerProdDerivedProjHom I G)
    ((isCoveringMap_centerProdDerivedProjHom I G).isOpenMap.isStrictMap
      (continuous_centerProdDerivedProjHom I G))
    (surjective_centerProdDerivedProjHom I G)

@[simp]
theorem quotientKerCenterProdDerivedProjHom_apply_mk
    (p : Multiplicative (centerFactor I G) × derivedFactor I G) :
    quotientKerCenterProdDerivedProjHom I G p = centerProdDerivedProjHom I G p :=
  ContinuousMulEquiv.quotientKerEquivOfSurjective_apply_mk _ _ _ p

/-- The inverse of `(𝔷 × K) ⧸ Γ ≃ₜ* G` sends `ψ p` to the class of `p`. -/
theorem quotientKerCenterProdDerivedProjHom_symm_apply
    (p : Multiplicative (centerFactor I G) × derivedFactor I G) :
    (quotientKerCenterProdDerivedProjHom I G).symm (centerProdDerivedProjHom I G p) = p :=
  ContinuousMulEquiv.quotientKerEquivOfSurjective_symm_apply _ _ _ p

/-- The quotient `(𝔷 × K) ⧸ Γ` is compact, being homeomorphic to `G`. -/
instance compactSpace_quotient_ker_centerProdDerivedProjHom :
    CompactSpace ((Multiplicative (centerFactor I G) × derivedFactor I G) ⧸
      (centerProdDerivedProjHom I G).ker) :=
  (quotientKerCenterProdDerivedProjHom I G).toHomeomorph.symm.compactSpace

omit [T2Space G] in
/-- The group `K` integrating the derived algebra is compact
(`TauCeti.UniversalCover.compactSpace_integralLeafSubgroupData_derivedSeries`). -/
instance compactSpace_derivedFactor : CompactSpace (derivedFactor I G) :=
  compactSpace_integralLeafSubgroupData_derivedSeries

omit [T2Space G] in
/-- **The semisimple factor `K` has finite centre.** Its Lie algebra `[𝔤, 𝔤]` has trivial centre
and it is compact (`TauCeti.UniversalCover.compactSpace_integralLeafSubgroupData_derivedSeries`). -/
instance finite_center_integralLeafSubgroupData_derivedSeries :
    Finite (Subgroup.center (derivedFactor I G)) :=
  Lie.finite_center_of_center_eq_bot
    (Lie.center_eq_bot_integralLeafSubgroupData_derivedSeries isCompl_center_derivedSeries_one)

/-- The image in `K` of the kernel of `𝔷 × K → G` is finite: it is central, and `K` has finite
centre. -/
instance finite_map_snd_ker_centerProdDerivedProjHom :
    Finite ((centerProdDerivedProjHom I G).ker.map (MonoidHom.snd _ _)) :=
  Subgroup.finite_map_snd_of_le_center _ (ker_centerProdDerivedProjHom_le_center I G)

/-- **The deck lattice is a full lattice** in the centre `𝔷` of the Lie algebra, so `𝔷 ⧸ Λ` is a
torus. -/
instance isZLattice_deckLattice :
    IsZLattice ℝ (deckLattice I G).toAddSubgroup'.toIntSubmodule :=
  Subgroup.isZLattice_toAddSubgroup'_comap_inl _

/-- **The torus `𝔷 ⧸ Λ` is compact**, as the quotient of `𝔷` by a full lattice. -/
instance compactSpace_quotient_deckLattice :
    CompactSpace (Multiplicative (centerFactor I G) ⧸ deckLattice I G) :=
  Subgroup.compactSpace_quotient_comap_inl _

/-- The cover `(𝔷 ⧸ Λ) × K → G` is the map `(𝔷 ⧸ Λ) × K → (𝔷 × K) ⧸ Γ` followed by the
identification `(𝔷 × K) ⧸ Γ ≃ₜ* G`. -/
private theorem coe_torusProdDerivedCover :
    ⇑(torusProdDerivedCover I G) =
      quotientKerCenterProdDerivedProjHom I G ∘
        (centerProdDerivedProjHom I G).ker.prodQuotientMap := by
  ext ⟨t, k⟩
  induction t using QuotientGroup.induction_on with | H z =>
  refine (torusProdDerivedCover_mk I G z k).trans ?_
  rw [Function.comp_apply, Subgroup.prodQuotientMap_mk,
    quotientKerCenterProdDerivedProjHom_apply_mk]

/-- **The cover `(𝔷 ⧸ Λ) × K → G` is a covering map.** -/
theorem isCoveringMap_torusProdDerivedCover : IsCoveringMap (torusProdDerivedCover I G) := by
  rw [coe_torusProdDerivedCover]
  exact (Subgroup.isCoveringMap_prodQuotientMap _).homeomorph_comp
    (quotientKerCenterProdDerivedProjHom I G).toHomeomorph

/-- The cover `(𝔷 ⧸ Λ) × K → G` is continuous. -/
theorem continuous_torusProdDerivedCover : Continuous (torusProdDerivedCover I G) :=
  (isCoveringMap_torusProdDerivedCover I G).continuous

/-- The cover `(𝔷 ⧸ Λ) × K → G` is surjective. -/
theorem surjective_torusProdDerivedCover : Surjective (torusProdDerivedCover I G) := by
  rw [coe_torusProdDerivedCover]
  exact (quotientKerCenterProdDerivedProjHom I G).surjective.comp
    (Subgroup.surjective_prodQuotientMap _)

/-- **The cover `(𝔷 ⧸ Λ) × K → G` has finite fibres**, in bijection with the image in `K` of the
kernel of `𝔷 × K → G`. -/
theorem finite_torusProdDerivedCover_preimage (x : G) :
    Finite (torusProdDerivedCover I G ⁻¹' {x}) := by
  obtain ⟨y, rfl⟩ := (quotientKerCenterProdDerivedProjHom I G).surjective x
  rw [coe_torusProdDerivedCover, Set.preimage_comp, ← Set.image_singleton,
    Set.preimage_image_eq _ (quotientKerCenterProdDerivedProjHom I G).injective]
  exact Subgroup.finite_prodQuotientMap_preimage _ _

end TauCeti.UniversalCover

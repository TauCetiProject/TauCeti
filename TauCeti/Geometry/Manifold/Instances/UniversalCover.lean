/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.AlgebraicTopology.UniversalCover.Group
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.AlgebraicTopology.UniversalCover.Countable
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.AlgebraicTopology.UniversalCover.Compact
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Geometry.Manifold.Algebra.LieGroup

/-!
# Universal covers of Lie groups and subgroup covers of manifolds

Let `X` be a charted space that is locally path-connected and semilocally simply connected. The
endpoint projection `UniversalCover.proj : UniversalCover x₀ → X` is a covering map, hence a local
homeomorphism, and pulling the charts of `X` back along it makes the universal cover a charted space
over the same model. When `X` is a `C^n` manifold, so is its universal cover, and the projection is
a `C^n` local diffeomorphism. A map into the universal cover is `C^n` exactly when it is continuous
and its composite with the projection is `C^n`. The same pulled-back atlas makes every
subgroup cover a `C^n` manifold, with a `C^n` local diffeomorphism to the base.
Universal covers and subgroup covers of boundaryless manifolds are boundaryless.

`TauCeti.Manifold.exists_universalCover` packages the universal cover of a connected, Hausdorff,
second-countable manifold as a simply connected, Hausdorff, second-countable covering manifold.
It includes the compact-cover finiteness consequence imported from
`TauCeti.AlgebraicTopology.UniversalCover.Compact`: closed points of the base suffice to make
compactness of the universal cover imply finiteness of the fundamental group.

For a Lie group `G`, the universal cover `UniversalCover (1 : G)` based at the identity is a group
under pointwise multiplication of paths, and its multiplication and inversion lie over those of
`G`. The criterion above therefore makes them `C^n`, so the universal cover is a Lie group, and the
covering homomorphism `UniversalCover.projHom`, whose underlying map is the projection, is a `C^n`
local diffeomorphism. This is the smooth half of the simply connected covering group of a connected
Lie group.

## Main results

* `TauCeti.UniversalCover.instChartedSpace`, `TauCeti.UniversalCover.instIsManifold`: the universal
  cover of a `C^n` manifold is a `C^n` manifold over the same model.
* `TauCeti.UniversalCover.isLocalDiffeomorph_proj`: the projection is a `C^n` local
  diffeomorphism.
* `TauCeti.UniversalCover.isInvertible_mfderiv_proj`: the differential of the projection is
  invertible at every point.
* `TauCeti.Manifold.exists_universalCover`: a connected, Hausdorff, second-countable manifold
  has a simply connected, Hausdorff, second-countable covering manifold.
* `TauCeti.UniversalCover.instChartedSpaceSubgroupQuotient`,
  `TauCeti.UniversalCover.instIsManifoldSubgroupQuotient`: the analogous atlas and manifold
  structure for an arbitrary subgroup cover.
* `TauCeti.UniversalCover.isLocalDiffeomorph_subgroupQuotientProj`: every subgroup-cover
  projection is a `C^n` local diffeomorphism.
* `TauCeti.UniversalCover.contMDiff_iff`: a map into the universal cover is `C^n` if and only if it
  is continuous and its composite with the projection is `C^n`.
* `TauCeti.UniversalCover.instLieGroup`: the universal cover of a Lie group is a Lie group.
* `TauCeti.UniversalCover.exists_contMDiff_smul_eq_add`: for a real homomorphism `P` of the
  fundamental group of a path-connected σ-compact manifold, a smooth function `F` on the universal
  cover with `F (g • p) = F p + P g`. It is the sum `∑ᶠ z, ρ_z (proj p) * P g_z(p)` over a smooth
  partition of unity `ρ_z` subordinate to local sections `s_z` of the projection, where
  `g_z(p) • s_z (proj p) = p` (`TauCeti.UniversalCover.fiberShift`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 4, "Smooth Covering Maps", and Chapter 7,
  "Covering Groups", Proposition 4.40 and Corollary 4.43.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

namespace TauCeti.UniversalCover

section Manifold

variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- The universal cover of a charted space carries the charts of the base pulled back along the
covering projection. -/
noncomputable instance instChartedSpace : ChartedSpace H (UniversalCover x₀) :=
  (isCoveringMap x₀).isLocalHomeomorph.chartedSpaceComap

/-- The universal cover of a `C^n` manifold is a `C^n` manifold. -/
instance instIsManifold [IsManifold I n X] : IsManifold I n (UniversalCover x₀) :=
  (isCoveringMap x₀).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The covering projection of the universal cover is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_proj : IsLocalDiffeomorph I I n (proj : UniversalCover x₀ → X) :=
  (isCoveringMap x₀).isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap

/-- The universal cover of a boundaryless manifold is boundaryless. -/
instance instBoundarylessManifold [BoundarylessManifold I X] :
    BoundarylessManifold I (UniversalCover x₀) :=
  (isLocalDiffeomorph_proj (I := I) (n := 1) x₀).boundarylessManifold one_ne_zero

/-- The covering projection of the universal cover is `C^n`. -/
theorem contMDiff_proj : ContMDiff I I n (proj : UniversalCover x₀ → X) :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiff_chartedSpaceComap

/-- The differential of the projection of the universal cover is invertible at every point. -/
theorem isInvertible_mfderiv_proj {x₀ : X} (z : UniversalCover x₀) :
    (mfderiv I I (proj : UniversalCover x₀ → X) z).IsInvertible :=
  (isLocalDiffeomorph_proj (I := I) (n := ∞) x₀).isInvertible_mfderiv (by simp) z

variable {x₀} {f : N → UniversalCover x₀} {s : Set N} {z : N}

/-- A map into the universal cover is `C^n` within `s` at `z` if and only if it is continuous
within `s` at `z` and its composite with the projection is `C^n` within `s` at `z`. -/
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I' I n f s z ↔ ContinuousWithinAt f s z ∧
      ContMDiffWithinAt I' I n (proj ∘ f) s z :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiffWithinAt_chartedSpaceComap_iff

/-- A map into the universal cover is `C^n` at `z` if and only if it is continuous at `z` and its
composite with the projection is `C^n` at `z`. -/
theorem contMDiffAt_iff :
    ContMDiffAt I' I n f z ↔ ContinuousAt f z ∧ ContMDiffAt I' I n (proj ∘ f) z :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiffAt_chartedSpaceComap_iff

/-- A map into the universal cover is `C^n` on `s` if and only if it is continuous on `s` and its
composite with the projection is `C^n` on `s`. -/
theorem contMDiffOn_iff :
    ContMDiffOn I' I n f s ↔ ContinuousOn f s ∧ ContMDiffOn I' I n (proj ∘ f) s :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiffOn_chartedSpaceComap_iff

/-- A map into the universal cover is `C^n` if and only if it is continuous and its composite with
the projection is `C^n`. -/
theorem contMDiff_iff :
    ContMDiff I' I n f ↔ Continuous f ∧ ContMDiff I' I n (proj ∘ f) :=
  (isCoveringMap x₀).isLocalHomeomorph.contMDiff_chartedSpaceComap_iff

end Manifold

section SubgroupQuotient

variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X) (K : Subgroup (FundamentalGroup X x₀))

/-- A subgroup cover carries the atlas pulled back from the base along its projection. -/
noncomputable instance instChartedSpaceSubgroupQuotient : ChartedSpace H (SubgroupQuotient x₀ K) :=
  (isCoveringMap_subgroupQuotientProj x₀ K).isLocalHomeomorph.chartedSpaceComap

/-- A subgroup cover of a `C^n` manifold is a `C^n` manifold. -/
instance instIsManifoldSubgroupQuotient [IsManifold I n X] :
    IsManifold I n (SubgroupQuotient x₀ K) :=
  (isCoveringMap_subgroupQuotientProj x₀ K).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The subgroup-cover projection is a `C^n` local diffeomorphism for the lifted atlas. -/
theorem isLocalDiffeomorph_subgroupQuotientProj :
    IsLocalDiffeomorph I I n (subgroupQuotientProj x₀ K) :=
  (isCoveringMap_subgroupQuotientProj x₀ K).isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap

/-- A subgroup cover of a boundaryless manifold is boundaryless. -/
instance instBoundarylessManifoldSubgroupQuotient [BoundarylessManifold I X] :
    BoundarylessManifold I (SubgroupQuotient x₀ K) :=
  (isLocalDiffeomorph_subgroupQuotientProj (I := I) (n := 1) x₀ K).boundarylessManifold one_ne_zero

end SubgroupQuotient

section LieGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace H G]
  [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G] [LieGroup I n G]

/-- The universal cover of a Lie group, based at the identity, is a Lie group: its multiplication
and inversion are continuous and lie over the `C^n` multiplication and inversion of `G`. -/
instance instLieGroup : LieGroup I n (UniversalCover (1 : G)) :=
  (isCoveringMap (1 : G)).isLocalHomeomorph.lieGroup_chartedSpaceComap proj_mul

end LieGroup

/-! ### Equivariant functions -/

section Equivariant

open Set Function

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]
  [IsManifold I ∞ M] [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
  [PathConnectedSpace M] [T2Space M] [SigmaCompactSpace M] {x₀ : M}

/-- **Equivariant functions on the universal cover.** For every homomorphism `P` from the
fundamental group of a path-connected σ-compact manifold to `ℝ`, there is a smooth function `F` on
the universal cover with `F (g • p) = F p + P g` for every deck transformation `g`. -/
theorem exists_contMDiff_smul_eq_add (P : Additive (FundamentalGroup M x₀) →+ ℝ) :
    ∃ F : UniversalCover x₀ → ℝ, ContMDiff I 𝓘(ℝ) ∞ F ∧
      ∀ (g : FundamentalGroup M x₀) (p : UniversalCover x₀),
        F (g • p) = F p + P (Additive.ofMul g) := by
  -- Local sections `σ z` of the projection: local inverses at points `p₀ z` over each `z`.
  choose p₀ hp₀ using proj_surjective (x₀ := x₀)
  have hproj := (isCoveringMap x₀).isLocalHomeomorph
  set σ : M → OpenPartialHomeomorph M (UniversalCover x₀) := fun z ↦ hproj.localInverseAt (p₀ z)
  set U : M → Set M := fun z ↦ (σ z).source
  have hUo (z : M) : IsOpen (U z) := (σ z).open_source
  have hzU (z : M) : z ∈ U z := by
    simpa only [hp₀] using hproj.apply_self_mem_localInverseAt_source (x := p₀ z)
  have hσp (z y : M) (hy : y ∈ U z) : (σ z y).proj = y := hproj.apply_localInverseAt_of_mem hy
  have hσc (z : M) : ContinuousOn (σ z) (U z) := (σ z).continuousOn
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hUo
    fun z _ ↦ mem_iUnion.mpr ⟨z, hzU z⟩
  -- The terms of the sum defining `F`, and the fact that they only matter over `U z`.
  set T : M → UniversalCover x₀ → ℝ := fun z p ↦ ρ z p.proj * fiberShift P p (σ z p.proj)
  have hmem {z : M} {y : M} (hy : ρ z y ≠ 0) : y ∈ U z := hρ z (subset_tsupport _ hy)
  refine ⟨fun p ↦ ∑ᶠ z, T z p, ?_, fun g p ↦ ?_⟩
  · refine contMDiff_finsum (fun z ↦ ?_) ?_
    · intro p
      by_cases hp : p.proj ∈ U z
      · -- Over `U z` the fiber shift factor is locally constant.
        have hσ : ContinuousAt (fun p : UniversalCover x₀ ↦ σ z p.proj) p :=
          ((hσc z).continuousAt ((hUo z).mem_nhds hp)).comp (continuous_proj x₀).continuousAt
        have hloc := eventually_fiberShift_eq P continuousAt_id hσ
          (((hUo z).preimage (continuous_proj x₀)).eventually_mem hp |>.mono
            fun p' hp' ↦ (hσp z _ hp').symm)
        refine (((ρ z).contMDiff.comp (contMDiff_proj (I := I) x₀)).contMDiffAt.mul
          (contMDiffAt_const (c := fiberShift P p (σ z p.proj)))).congr_of_eventuallyEq ?_
        filter_upwards [hloc] with p' hp'
        simp only [id_eq] at hp'
        simp only [T, Pi.mul_apply, comp_apply, hp']
      · -- Off `U z` the partition function vanishes near `p`.
        have hnot : p.proj ∉ tsupport (ρ z) := fun h ↦ hp (hρ z h)
        have hzero := (continuous_proj x₀).continuousAt.eventually
          (notMem_tsupport_iff_eventuallyEq.mp hnot)
        refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
        filter_upwards [hzero] with p' hp'
        simp [T, hp']
    · exact (ρ.locallyFinite.preimage_continuous (continuous_proj x₀)).subset
        fun z ↦ support_mul_subset_left _ _
  · -- Each term changes by `ρ z (proj p) * P g`, and the `ρ z` sum to one.
    have hT (z : M) : T z (g • p) = ρ z p.proj * P (Additive.ofMul g) + T z p := by
      by_cases hz : ρ z p.proj = 0
      · simp [T, hz]
      · simp only [T, proj_smul, fiberShift_smul_left P g (hσp z _ (hmem hz)).symm, mul_add]
    have hfin (f : M → ℝ) (hf : ∀ z, ρ z p.proj = 0 → f z = 0) : (support f).Finite :=
      (ρ.locallyFinite.point_finite p.proj).subset fun z hz ↦ fun h ↦ hz (hf z h)
    simp only [hT]
    rw [finsum_add_distrib (hfin _ fun z hz ↦ by simp [hz]) (hfin _ fun z hz ↦ by simp [T, hz]),
      ← finsum_mul, ρ.sum_eq_one (mem_univ _), one_mul, add_comm]

end Equivariant

end TauCeti.UniversalCover

section UniversalCoverExistence

open Topology

universe u

variable [NormedSpace ℝ E] (I) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- **The universal covering manifold.** Let `M` be a connected, Hausdorff, second-countable
`C^n` manifold and `x₀ ∈ M`. There is a simply connected, Hausdorff, second-countable `C^n`
manifold `Y` over the same model and a surjective covering map `p : Y → M` which is a `C^n` local
diffeomorphism, whose fibre over `x₀` is in bijection with the homotopy classes of loops at `x₀`,
and such that if `Y` is compact then the fundamental group of `M` is finite. The based-path
universal cover `TauCeti.UniversalCover x₀`, with the atlas pulled back along its projection, is
such a manifold. -/
theorem TauCeti.Manifold.exists_universalCover {n : WithTop ℕ∞} [IsManifold I n M] [T2Space M]
    [SecondCountableTopology M] [PreconnectedSpace M] (x₀ : M) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace H Y) (p : Y → M),
      IsManifold I n Y ∧ IsCoveringMap p ∧ Function.Surjective p ∧
        IsLocalDiffeomorph I I n p ∧ T2Space Y ∧ SecondCountableTopology Y ∧
          SimplyConnectedSpace Y ∧ Nonempty (p ⁻¹' {x₀} ≃ FundamentalGroup M x₀) ∧
            (CompactSpace Y → Finite (FundamentalGroup M x₀)) := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  exact ⟨TauCeti.UniversalCover x₀, inferInstance, inferInstance, TauCeti.UniversalCover.proj,
    inferInstance, TauCeti.UniversalCover.isCoveringMap x₀,
    TauCeti.UniversalCover.proj_surjective_of_preconnectedSpace x₀,
    TauCeti.UniversalCover.isLocalDiffeomorph_proj x₀, inferInstance, inferInstance,
    inferInstance, ⟨TauCeti.UniversalCover.fiberEquivFundamentalGroup x₀⟩,
    fun _ ↦ TauCeti.UniversalCover.finite_fundamentalGroup_of_compactSpace x₀⟩

end UniversalCoverExistence

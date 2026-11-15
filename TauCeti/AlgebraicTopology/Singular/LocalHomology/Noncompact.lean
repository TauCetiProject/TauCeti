/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.AlgebraicTopology.Singular.CompactSupport
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology
import TauCeti.Topology.Compactness.Compact

/-!
# Vanishing of top singular homology on noncompact manifolds

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary, and let `N` be a module over a ring `Λ`. This file
proves Hatcher's Proposition 3.29:

* `Hₖ(M; N) = 0` for every `k > n`, with no compactness or connectedness assumption on `M`
  (`TauCeti.isZero_singularHomology_of_lt`), extending
  `TauCeti.isZero_singularHomology_of_compactSpace` by removing compactness;
* `Hₖ(M; N) = 0` for every `k ≥ n` whenever no connected component of `M` is compact
  (`TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`), and in particular
  when `M` is preconnected and noncompact (`TauCeti.isZero_singularHomology_of_noncompactSpace`).

Contrapositively, if `M` is preconnected and `Hₖ(M; N)` is nonzero (or nontrivial) in some degree
`k ≥ n`, then `M` is compact (`TauCeti.compactSpace_of_not_isZero_singularHomology` and
`TauCeti.compactSpace_of_nontrivial_singularHomology`).

## Proof outline

Every class `z ∈ Hₖ(M; N)` comes from an open subset `U` contained in a compact subset `K` of `M`
(`TauCeti.exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq`). Suppose `z` maps to zero in
the local homology `Hₖ(M, M ∖ K; N)`. By exactness of the pair `(M, M ∖ K)`, `z` also comes from a
class `v ∈ Hₖ(M ∖ K; N)`. For `k ≥ n`, the compact set `K ∖ U` satisfies
`Hₖ₊₁(M, M ∖ (K ∖ U); N) = 0` (`TauCeti.isZero_localHomology_of_isCompact`), so the inclusion of
`(K ∖ U)ᶜ = U ∪ (M ∖ K)` into `M` induces a monomorphism `Hₖ(U ∪ (M ∖ K); N) ⟶ Hₖ(M; N)`. The
classes on the disjoint open subsets `U` and `M ∖ K` therefore agree in `Hₖ(U ∪ (M ∖ K); N)`, hence
vanish (`TauCeti.eq_zero_of_singularHomologyMap_inclusion_eq_of_disjoint`), so `z = 0`.

When `k > n`, the local homology `Hₖ(M, M ∖ K; N)` vanishes unconditionally. When `k = n` and no
connected component of `M` is compact, for each `x ∈ K` the connected component of `x` is closed,
hence cannot lie inside `K`, so it meets `M ∖ K` at a point `x₀`. Since `M` is locally path
connected, `x₀` and `x` lie in the same path component. Because `U ⊆ K ⊆ M ∖ {x₀}`, the local class
of `z` vanishes at `x₀`, hence at `x` by transport along a path (`TauCeti.localHomologySystemCone`),
and therefore `z` maps to zero in `Hₙ(M, M ∖ K; N)`
(`TauCeti.eq_zero_of_forall_localHomologyRestriction_eq_zero`).

## Main results

* `TauCeti.isZero_singularHomology_of_lt`: `Hₖ(M; N) = 0` for `k > n` on every Hausdorff
  `n`-manifold without boundary.
* `TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`: `Hₖ(M; N) = 0` for
  `k ≥ n` when no connected component of `M` is compact.
* `TauCeti.isZero_singularHomology_of_noncompactSpace`: Hatcher's Proposition 3.29, `Hₖ(M; N) = 0`
  for `k ≥ n` on a preconnected noncompact Hausdorff `n`-manifold without boundary.
* `TauCeti.compactSpace_of_not_isZero_singularHomology` and
  `TauCeti.compactSpace_of_nontrivial_singularHomology`: nonvanishing or nontriviality of
  `Hₖ(M; N)` for some `k ≥ n` on a preconnected Hausdorff `n`-manifold forces `CompactSpace M`.
* `ModuleCat.finrank_singularHomology_eq_zero_of_lt` and
  `ModuleCat.finrank_singularHomology_eq_zero_of_noncompactSpace`: the corresponding rank-vanishing
  statements.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29, p. 239.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Module Set TopCat Topology

universe w

namespace TauCeti

section SameUniverse

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) {n : ℕ}
  {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- A class `z ∈ Hₖ(M; N)` supported on an open subset `U` of a compact set `K ⊆ M` vanishes once
its image in `Hₖ(M, M ∖ K; N)` vanishes, provided `k ≥ n`: exactness lifts `z` to `M ∖ K`,
vanishing of `Hₖ₊₁(M, M ∖ (K ∖ U); N)` makes `Hₖ(U ∪ (M ∖ K); N) ⟶ Hₖ(M; N)` injective, and
disjointness of `U` and `M ∖ K` forces the common lift to vanish. -/
private lemma eq_zero_of_singularHomologyπ_compl_eq_zero (hn : finrank ℝ E = n) {k : ℕ}
    (hk : n ≤ k) {U K : Set M} (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    (u : ((toSSet.obj (of ↥U)).homology N k : ModuleCat.{w} Λ))
    (hz : (TopPair.ofSubset (Kᶜ : Set (of M))).singularHomologyπ N k
      (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N k u) = 0) :
    SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N k u = 0 := by
  set z := SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N k u with hz_def
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset (Kᶜ : Set (of M))).singularHomology_exact_space N k) z hz
  let v' : ((toSSet.obj (of ↥(Kᶜ : Set M))).homology N k : ModuleCat.{w} Λ) := v
  have hv' : SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal Kᶜ))) N k v' = z := hv
  have hLc : (U ∪ Kᶜ : Set (of M)) = ((K \ U)ᶜ : Set (of M)) := by
    rw [Set.sdiff_eq, compl_inter, compl_compl, union_comm]
  have hzeroL : IsZero ((TopPair.ofSubset (U ∪ Kᶜ : Set (of M))).singularHomology N (k + 1)) := by
    rw [hLc]
    exact isZero_localHomology_of_isCompact N hn (hK.diff hU) (by lia)
  let j := SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ Kᶜ)))) N k
  have hmono : Mono j :=
    (TopPair.ofSubset (U ∪ Kᶜ : Set (of M))).mono_homologyMap_map_of_isZero N hzeroL
  have hju : j (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
      (subset_union_left (s := U) (t := Kᶜ))))) N k u) = z := by
    dsimp only [j]
    rw [← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← toSSet.map_comp]
    exact hz_def.symm
  have hjv : j (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
      (subset_union_right (s := U) (t := Kᶜ))))) N k v') = z := by
    dsimp only [j]
    rw [← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← toSSet.map_comp]
    exact hv'
  have huv : SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
      (subset_union_left (s := U) (t := Kᶜ))))) N k u =
      SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
        (subset_union_right (s := U) (t := Kᶜ))))) N k v' :=
    ((ModuleCat.mono_iff_injective j).1 hmono) (hju.trans hjv.symm)
  have hu0 := eq_zero_of_singularHomologyMap_inclusion_eq_of_disjoint N hU hK.isClosed.isOpen_compl
    (disjoint_compl_right.mono_left hUK) u v' huv
  rw [← hju, hu0, map_zero]

private lemma localHomologySystemCone_π_app_singularHomologyπ (x : M) (k : ℕ)
    (z : ((toSSet.obj (of M)).homology N k : ModuleCat.{w} Λ)) :
    ((localHomologySystemCone N M E k).π.app (FundamentalGroupoid.mk x))
      ((TopPair.ofSubset ((univ : Set M)ᶜ : Set (of M))).singularHomologyπ N k z) =
    (TopPair.ofSubset ({x}ᶜ : Set (of M))).singularHomologyπ N k z := by
  have hmor : (TopPair.ofSubset ((univ : Set M)ᶜ : Set (of M))).singularHomologyπ N k ≫
      (localHomologySystemCone N M E k).π.app (FundamentalGroupoid.mk x) =
      (TopPair.ofSubset ({x}ᶜ : Set (of M))).singularHomologyπ N k := by
    rw [localHomologySystemCone_π_app, localHomologyRestriction_def]
    exact TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id N
      (X := of M) (compl_subset_compl.2 (subset_univ {x})) k
  exact ConcreteCategory.congr_hom hmor z

omit [T2Space M] in
private lemma localHomologyRestriction_singularHomologyπ {K : Set M} {x : M} (hx : x ∈ K) (k : ℕ)
    (z : ((toSSet.obj (of M)).homology N k : ModuleCat.{w} Λ)) :
    localHomologyRestriction N (singleton_subset_iff.2 hx) k
      ((TopPair.ofSubset (Kᶜ : Set (of M))).singularHomologyπ N k z) =
    (TopPair.ofSubset ({x}ᶜ : Set (of M))).singularHomologyπ N k z := by
  have hmor : (TopPair.ofSubset (Kᶜ : Set (of M))).singularHomologyπ N k ≫
      localHomologyRestriction N (singleton_subset_iff.2 hx) k =
      (TopPair.ofSubset ({x}ᶜ : Set (of M))).singularHomologyπ N k := by
    rw [localHomologyRestriction_def]
    exact TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id N
      (X := of M) (compl_subset_compl.2 (singleton_subset_iff.2 hx)) k
  exact ConcreteCategory.congr_hom hmor z

/-- If `z ∈ Hₙ(M; N)` comes from `U ⊆ K` with `K` compact and no connected component of `M` is
compact, then `z` maps to zero in `Hₙ(M, M ∖ K; N)`: for every `x ∈ K`, the component of `x`
leaves `K` at some `x₀`, where the local class vanishes and transports to zero at `x`. -/
private lemma singularHomologyπ_compl_eq_zero_of_forall_not_isCompact_connectedComponent
    (hn : finrank ℝ E = n) (hnc : ∀ x : M, ¬ IsCompact (connectedComponent x))
    {U K : Set M} (hK : IsCompact K) (hUK : U ⊆ K)
    (u : ((toSSet.obj (of ↥U)).homology N n : ModuleCat.{w} Λ)) :
    (TopPair.ofSubset (Kᶜ : Set (of M))).singularHomologyπ N n
      (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N n u) = 0 := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  let z : ((toSSet.obj (of M)).homology N n : ModuleCat.{w} Λ) :=
    SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N n u
  let γ : ((localHomologySystemCone N M E n).pt : ModuleCat.{w} Λ) :=
    (TopPair.ofSubset ((univ : Set M)ᶜ : Set (of M))).singularHomologyπ N n z
  refine eq_zero_of_forall_localHomologyRestriction_eq_zero N hn hK _ fun x hx ↦ ?_
  have hnot_sub : ¬ connectedComponent x ⊆ K :=
    fun hsub ↦ hnc x (hK.of_isClosed_subset isClosed_connectedComponent hsub)
  obtain ⟨x₀, hx₀c, hx₀K⟩ := not_subset.1 hnot_sub
  have hjoin : Joined x₀ x := by
    have hx₀p : x₀ ∈ pathComponent x := by rwa [pathComponent_eq_connectedComponent]
    exact hx₀p.symm
  let f : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x :=
    Path.Homotopic.Quotient.mk hjoin.somePath
  have hUx₀ : U ⊆ ({x₀}ᶜ : Set M) := fun y hy hxy ↦ hx₀K (mem_singleton_iff.1 hxy ▸ hUK hy)
  let P := TopPair.ofSubset ({x₀}ᶜ : Set (of M))
  let f_inc : of ↥U ⟶ P.snd := ofHom (ContinuousMap.inclusion hUx₀)
  have hmor : SSet.homologyMap (toSSet.map (f_inc ≫ P.map)) N n ≫ P.singularHomologyπ N n = 0 := by
    have h1 : SSet.homologyMap (toSSet.map (f_inc ≫ P.map)) N n =
        SSet.homologyMap (toSSet.map f_inc) N n ≫ SSet.homologyMap (toSSet.map P.map) N n := by
      rw [toSSet.map_comp, SSet.homologyMap_comp]
    exact (congrArg (· ≫ P.singularHomologyπ N n) h1).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (P.homologyMap_comp_singularHomologyπ N n)).trans comp_zero))
  have hx₀_zero : P.singularHomologyπ N n z = 0 := ConcreteCategory.congr_hom hmor u
  have hγx₀ : ((localHomologySystemCone N M E n).π.app (.mk x₀)) γ = 0 :=
    (localHomologySystemCone_π_app_singularHomologyπ N x₀ n z).trans hx₀_zero
  have hγx : ((localHomologySystemCone N M E n).π.app (.mk x)) γ = 0 :=
    (ConcreteCategory.congr_hom ((localHomologySystemCone N M E n).w f) γ).symm.trans
      (by rw [ConcreteCategory.comp_apply, hγx₀, map_zero])
  exact (localHomologyRestriction_singularHomologyπ N hx n z).trans
    ((localHomologySystemCone_π_app_singularHomologyπ N x n z).symm.trans hγx)

private lemma isZero_singularHomology_of_lt_aux (hn : finrank ℝ E = n) {k : ℕ} (hk : n < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun z₁ z₂ ↦ ?_⟩
  suffices h : ∀ z : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M), z = 0 from
    (h z₁).trans (h z₂).symm
  intro z
  obtain ⟨U, K, hU, hK, hUK, u, rfl⟩ :=
    exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq N k z
  rw [singularHomologyFunctor_obj_map]
  refine eq_zero_of_singularHomologyπ_compl_eq_zero N hn hk.le hU hK hUK u ?_
  exact (ModuleCat.subsingleton_of_isZero
    (isZero_localHomology_of_isCompact N hn hK hk)).elim _ 0

private lemma isZero_singularHomology_of_forall_not_isCompact_connectedComponent_aux
    (hn : finrank ℝ E = n) (hnc : ∀ x : M, ¬ IsCompact (connectedComponent x)) {k : ℕ}
    (hk : n ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) := by
  obtain rfl | hk := hk.eq_or_lt
  · have := ChartedSpace.locallyCompactSpace E M
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun z₁ z₂ ↦ ?_⟩
    suffices h : ∀ z : ((singularHomologyFunctor (ModuleCat.{w} Λ) n).obj N).obj (of M), z = 0 from
      (h z₁).trans (h z₂).symm
    intro z
    obtain ⟨U, K, hU, hK, hUK, u, rfl⟩ :=
      exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq N n z
    rw [singularHomologyFunctor_obj_map]
    exact eq_zero_of_singularHomologyπ_compl_eq_zero N hn le_rfl hU hK hUK u
      (singularHomologyπ_compl_eq_zero_of_forall_not_isCompact_connectedComponent N hn hnc hK
        hUK u)
  · exact isZero_singularHomology_of_lt_aux N hn hk

end SameUniverse

/-- Transport `ChartedSpace E M` from a model space `E` in any universe to the coordinate space
`ULift.{w} (Fin n) → ℝ` in the universe of `M`. -/
@[instance_reducible]
private def chartedSpacePiOfFinrankEq {M : Type w} [TopologicalSpace M] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {n : ℕ} (hn : finrank ℝ E = n) :
    ChartedSpace (ULift.{w} (Fin n) → ℝ) M :=
  let e : E ≃L[ℝ] (ULift.{w} (Fin n) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hn])
  letI : ChartedSpace (ULift.{w} (Fin n) → ℝ) E := e.toHomeomorph.symm.chartedSpace
  ChartedSpace.comp (ULift.{w} (Fin n) → ℝ) E M

section General

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) {n : ℕ}
  {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **The singular homology of a manifold vanishes above the dimension** (Hatcher,
Proposition 3.29(a)). For any Hausdorff space `M` modelled on a real normed space of dimension
`n`, `Hₖ(M; N) = 0` for `k > n`, without assuming compactness or connectedness. -/
theorem isZero_singularHomology_of_lt (hn : finrank ℝ E = n) {k : ℕ} (hk : n < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) :=
  letI := chartedSpacePiOfFinrankEq (M := M) hn
  isZero_singularHomology_of_lt_aux (E := ULift.{w} (Fin n) → ℝ) N (by simp) hk

/-- **Singular homology from the dimension on vanishes when no connected component is compact.**
For a Hausdorff space `M` modelled on a real normed space of dimension `n`, if no connected
component of `M` is compact, then `Hₖ(M; N) = 0` for all `k ≥ n`. -/
theorem isZero_singularHomology_of_forall_not_isCompact_connectedComponent (hn : finrank ℝ E = n)
    (hnc : ∀ x : M, ¬ IsCompact (connectedComponent x)) {k : ℕ} (hk : n ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) :=
  letI := chartedSpacePiOfFinrankEq (M := M) hn
  isZero_singularHomology_of_forall_not_isCompact_connectedComponent_aux
    (E := ULift.{w} (Fin n) → ℝ) N (by simp) hnc hk

/-- **Top singular homology of a noncompact manifold vanishes** (Hatcher, Proposition 3.29(b)).
For a preconnected noncompact Hausdorff space `M` modelled on a real normed space of dimension
`n`, `Hₖ(M; N) = 0` for every `k ≥ n`. -/
theorem isZero_singularHomology_of_noncompactSpace [PreconnectedSpace M] [NoncompactSpace M]
    (hn : finrank ℝ E = n) {k : ℕ} (hk : n ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) :=
  isZero_singularHomology_of_forall_not_isCompact_connectedComponent N hn
    not_isCompact_connectedComponent hk

/-- **Nonvanishing singular homology in degree at least the dimension forces compactness.** If `M`
is a preconnected Hausdorff space modelled on a real normed space of dimension `n` and `Hₖ(M; N)`
is nonzero for some `k ≥ n`, then `M` is compact. -/
theorem compactSpace_of_not_isZero_singularHomology [PreconnectedSpace M] (hn : finrank ℝ E = n)
    {k : ℕ} (hk : n ≤ k)
    (h : ¬ IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M))) :
    CompactSpace M := by
  by_contra hnc
  have := not_compactSpace_iff.1 hnc
  exact h (isZero_singularHomology_of_noncompactSpace N hn hk)

/-- **Nontrivial singular homology in degree at least the dimension forces compactness.** If `M` is
a preconnected Hausdorff space modelled on a real normed space of dimension `n` and `Hₖ(M; N)` is
nontrivial for some `k ≥ n`, then `M` is compact. -/
theorem compactSpace_of_nontrivial_singularHomology [PreconnectedSpace M] (hn : finrank ℝ E = n)
    {k : ℕ} (hk : n ≤ k)
    [h : Nontrivial (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M))] :
    CompactSpace M :=
  compactSpace_of_not_isZero_singularHomology N hn hk fun hz ↦
    @false_of_nontrivial_of_subsingleton _ h (ModuleCat.subsingleton_of_isZero hz)

end General

end TauCeti

namespace ModuleCat

open AlgebraicTopology TauCeti

variable {Λ : Type w} [Ring Λ] [StrongRankCondition Λ] (N : ModuleCat.{w} Λ) {n : ℕ}
  {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- Above the dimension of a Hausdorff manifold `M`, `Hₖ(M; N)` has rank zero. -/
theorem finrank_singularHomology_eq_zero_of_lt (hn : Module.finrank ℝ E = n) {k : ℕ}
    (hk : n < k) :
    Module.finrank Λ (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) = 0 := by
  have := (ModuleCat.isZero_iff_subsingleton).1 (isZero_singularHomology_of_lt (M := M) N hn hk)
  exact Module.finrank_zero_of_subsingleton

/-- On a preconnected noncompact Hausdorff `n`-manifold `M`, `Hₖ(M; N)` has rank zero for every
`k ≥ n`. -/
theorem finrank_singularHomology_eq_zero_of_noncompactSpace [PreconnectedSpace M]
    [NoncompactSpace M] (hn : Module.finrank ℝ E = n) {k : ℕ} (hk : n ≤ k) :
    Module.finrank Λ (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) = 0 := by
  have := (ModuleCat.isZero_iff_subsingleton).1
    (isZero_singularHomology_of_noncompactSpace (M := M) N hn hk)
  exact Module.finrank_zero_of_subsingleton

end ModuleCat

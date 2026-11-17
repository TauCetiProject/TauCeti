/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Ring.ULift
import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Top and higher singular homology of noncompact manifolds

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary, and let `N` be a module over a ring `Λ`. This file
proves that `Hₖ(M; N)` vanishes for every `k > n` without any compactness hypothesis on `M`
(`TauCeti.isZero_singularHomology_of_finrank_lt`), and that `Hₙ(M; N)` vanishes whenever no
connected component of `M` is compact
(`TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`). In particular, if
`M` is preconnected and noncompact then `Hₖ(M; N) = 0` for all `k ≥ n`
(`TauCeti.isZero_singularHomology_of_not_compactSpace`), so a preconnected boundaryless
`n`-manifold with nonzero homology in some degree `k ≥ n` is compact
(`TauCeti.compactSpace_of_not_isZero_singularHomology`). Likewise every proper open subset of a
preconnected `n`-manifold has vanishing homology in degrees `k ≥ n`
(`TauCeti.isZero_singularHomology_of_isOpen_ne_univ`). Consequently, any Hausdorff `n`-manifold
homotopy equivalent to `Sⁿ` is compact (`ContinuousMap.HomotopyEquiv.compactSpace_of_sphere`) and
second countable (`ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`), and neither a
noncompact `n`-manifold nor a proper open subset of a preconnected `n`-manifold can be homotopy
equivalent to `Sⁿ` (`TauCeti.isEmpty_homotopyEquiv_sphere_of_not_compactSpace`,
`TauCeti.isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ`).

The proof follows Hatcher's compact-exhaustion argument using local homology along compact sets,
followed by restriction of scalars to `ULift ℤ` so that `Λ` can live in any universe:

* **Detection on compact subsets.** Suppose `Hₖ₊₁(M, M ∖ D; N) = 0` for every compact `D ⊆ M`. Any
  class `α ∈ Hₖ(M; N)` comes from `Hₖ(K; N)` for some compact `K ⊆ M`
  (`TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq`). Choosing a compact neighbourhood
  `L` of `K` with interior `U ⊇ K`, if the image of `α` in `Hₖ(M, M ∖ L; N)` vanishes then `α`
  also comes from `Hₖ(M ∖ L; N)`. Inside `M ∖ (L ∖ U)`, the disjoint open sets `U` and `M ∖ L`
  cover the space, so Mayer–Vietoris makes `Hₖ(U; N) ⊞ Hₖ(M ∖ L; N) ⟶ Hₖ(M ∖ (L ∖ U); N)` a
  monomorphism, while `Hₖ₊₁(M, M ∖ (L ∖ U); N) = 0` makes `Hₖ(M ∖ (L ∖ U); N) ⟶ Hₖ(M; N)` a
  monomorphism. Comparing the lifts of `α` to `U` and to `M ∖ L` forces `α = 0`
  (`TauCeti.eq_zero_of_disjoint_isOpen_of_isZero_localHomology`,
  `TauCeti.eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero`).
* **Degrees above `n`.** By `TauCeti.isZero_localHomology_of_isCompact`, `Hₖ(M, M ∖ L; N)` and
  `Hₖ₊₁(M, M ∖ D; N)` both vanish for `k > n`, giving `Hₖ(M; N) = 0`.
* **Top degree on noncompact components.** A class `α` pushed forward from compact `K` vanishes in
  `Hₙ(M, M ∖ {x₀}; N)` at every point `x₀ ∉ K`
  (`TauCeti.singularHomologyToLocalHomology_map_subtypeVal_eq_zero_of_notMem`). If the connected
  component of `x` is noncompact, then since `M` is locally path-connected that component is a
  closed path component, so it cannot lie inside `K`; transporting vanishing along a path from a
  point `x₀ ∉ K` of the component to `x` via
  `TauCeti.singularHomologyToLocalHomology_eq_zero_of_joined` shows that `α` vanishes in
  `Hₙ(M, M ∖ {x}; N)` for every `x ∈ M`. Pointwise detection along compact sets
  (`TauCeti.eq_zero_of_forall_localHomologyRestriction_eq_zero`) then kills the image of `α` in
  `Hₙ(M, M ∖ L; N)` for every compact `L`, and the first step concludes `α = 0`.

## Main results

* `TauCeti.eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero`: in a locally compact Hausdorff
  space whose compact subsets have vanishing local homology in degree `k + 1`, a class in
  `Hₖ(M; N)` vanishing in `Hₖ(M, M ∖ L; N)` for all compact `L` is zero.
* `TauCeti.isZero_singularHomology_of_finrank_lt`: `Hₖ(M; N) = 0` for `k > n` on any Hausdorff
  boundaryless `n`-manifold.
* `TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`: `Hₖ(M; N) = 0` for
  `k ≥ n` when every connected component of `M` is noncompact.
* `TauCeti.isZero_singularHomology_of_not_compactSpace` and
  `TauCeti.compactSpace_of_not_isZero_singularHomology`: for preconnected `M`, noncompactness
  implies `Hₖ(M; N) = 0` for `k ≥ n`, and nonvanishing in some degree `k ≥ n` implies
  `CompactSpace M`.
* `TauCeti.isZero_singularHomology_of_isOpen_ne_univ`: for preconnected `M` and proper open
  `U ⊂ M`, `Hₖ(U; N) = 0` for `k ≥ n`.
* `ContinuousMap.HomotopyEquiv.compactSpace_of_sphere` and
  `ContinuousMap.HomotopyEquiv.secondCountableTopology_of_sphere`: any Hausdorff `n`-manifold
  homotopy equivalent to `Sⁿ` is compact and second countable.
* `TauCeti.isEmpty_homotopyEquiv_sphere_of_not_compactSpace` and
  `TauCeti.isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ`: no noncompact Hausdorff `n`-manifold
  and no proper open subset of a preconnected Hausdorff `n`-manifold is homotopy equivalent to
  `Sⁿ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology
open scoped ContinuousMap

universe w

namespace TauCeti

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)

section TopologicalSpace

variable {M : Type w} [TopologicalSpace M]

/-- **Compact-exhaustion vanishing criterion.** In a locally compact Hausdorff space `M` where
`Hₖ₊₁(M, M ∖ D; N) = 0` for every compact `D ⊆ M`, a class `α ∈ Hₖ(M; N)` whose image in
`Hₖ(M, M ∖ L; N)` vanishes for every compact `L ⊆ M` is zero. -/
theorem eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero
    [T2Space M] [WeaklyLocallyCompactSpace M] {k : ℕ}
    (hhigh : ∀ D : Set M, IsCompact D → IsZero (localHomology N D (k + 1)))
    (α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ))
    (hπ : ∀ L : Set M, IsCompact L →
      (TopPair.ofSubset (Lᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} Λ) N k α = 0) :
    α = 0 := by
  obtain ⟨K, hK, αK, hαK⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq (X := M) N k α
  -- `((singularHomologyFunctor _ k).obj N).obj X` and `.map f` are definitionally
  -- `(TopCat.toSSet.obj X).homology N k` and `SSet.homologyMap (TopCat.toSSet.map f) N k`.
  change ((TopCat.toSSet.obj (TopCat.of K)).homology N k : ModuleCat.{w} Λ) at αK
  change SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal K))) N k αK =
    α at hαK
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  have hDc : IsCompact (L \ interior L) := hL.inter_right isOpen_interior.isClosed_compl
  have hUVD : interior L ∪ Lᶜ = (L \ interior L)ᶜ := by
    rw [sdiff_eq, compl_inter, compl_compl, union_comm]
  obtain ⟨β, hβ⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset (Lᶜ : Set (TopCat.of M))).singularHomology_exact_space N k) α (hπ L hL)
  refine eq_zero_of_disjoint_isOpen_of_isZero_localHomology N isOpen_interior
    hL.isClosed.isOpen_compl
    (disjoint_left.2 fun _ hxU hxLc ↦ hxLc (interior_subset hxU)) hUVD (hhigh _ hDc)
    ⟨SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion hKL))) N k αK, ?_⟩
    ⟨β, hβ⟩
  rw [← hαK, ← ContinuousMap.subtypeVal_comp_inclusion hKL, TopCat.ofHom_comp]
  simp [SSet.homologyMap_comp]

end TopologicalSpace

section SameUniverseModel

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

private theorem isZero_singularHomology_of_finrank_lt_aux
    {Λ' : Type w} [Ring Λ'] (N' : ModuleCat.{w} Λ') {n k : ℕ} (hn : finrank ℝ E = n)
    (hk : n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ') k).obj N').obj
      (TopCat.of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  rw [singularHomologyFunctor_obj_obj, ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun α β ↦ sub_eq_zero.1 ?_⟩
  refine eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero N'
    (fun D hD ↦ isZero_localHomology_of_isCompact N' hn hD (Nat.lt_succ_of_lt hk)) (α - β)
    fun L hL ↦ (ModuleCat.subsingleton_of_isZero
      (isZero_localHomology_of_isCompact N' hn hL hk)).elim _ _

private theorem isZero_singularHomology_top_of_forall_not_isCompact_connectedComponent_aux
    {Λ' : Type w} [Ring Λ'] (N' : ModuleCat.{w} Λ') {n : ℕ}
    (hn : finrank ℝ E = n) (hcomp : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ') n).obj N').obj
      (TopCat.of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  have := ChartedSpace.locallyPathConnectedSpace E M
  rw [singularHomologyFunctor_obj_obj, ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun α β ↦ sub_eq_zero.1 ?_⟩
  let γ := α - β
  obtain ⟨K, hK, γK, hγK⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq (X := M) N' n γ
  -- Every point `x` can be joined to a point `x₀ ∉ K` because its closed path component is not
  -- compact, hence not contained in `K`.
  have hloc (x : M) : singularHomologyToLocalHomology N' x n γ = 0 := by
    have hnotSub : ¬ connectedComponent x ⊆ K :=
      fun hsub ↦ hcomp x (hK.of_isClosed_subset isClosed_connectedComponent hsub)
    obtain ⟨x₀, hx₀c, hx₀K⟩ := not_subset.1 hnotSub
    have hjoined : Joined x₀ x :=
      (mem_pathComponent_iff.1 (pathComponent_eq_connectedComponent x ▸ hx₀c)).symm
    refine singularHomologyToLocalHomology_eq_zero_of_joined N' E hjoined ?_
    rw [← hγK]
    exact singularHomologyToLocalHomology_map_subtypeVal_eq_zero_of_notMem N' hx₀K γK
  refine eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero N'
    (fun D hD ↦ isZero_localHomology_of_isCompact N' hn hD (Nat.lt_succ_self n)) γ fun L hL ↦ ?_
  refine eq_zero_of_forall_localHomologyRestriction_eq_zero N' hn hL _ fun x hx ↦ ?_
  rw [localHomologyRestriction_singularHomologyπ_apply N' (singleton_subset_iff.2 hx)]
  exact hloc x

end SameUniverseModel

section Manifold

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **Singular homology of a boundaryless manifold vanishes above the dimension.** For any
Hausdorff space `M` modelled on a real normed space `E` of finite dimension `n`, compact or not,
`Hₖ(M; N) = 0` for `k > n`. -/
theorem isZero_singularHomology_of_finrank_lt {n k : ℕ} (hn : finrank ℝ E = n) (hk : n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  let _ := ChartedSpace.compHomeomorph M (ContinuousLinearEquiv.ofFinrankEq
    (hn.trans (finrank_euclideanSpace_ulift_fin.{w} n).symm)).toHomeomorph
  let F := ModuleCat.restrictScalars.{w} ((Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom)
  have : ∀ T : Type w, PreservesColimitsOfShape (Discrete T) F :=
    fun _ ↦ ⟨fun {K} ↦ ModuleCat.preservesColimit_restrictScalars _ K⟩
  exact (F.isZero_singularHomology_obj_iff N k (TopCat.of M)).1 <|
    isZero_singularHomology_of_finrank_lt_aux (E := EuclideanSpace ℝ (ULift.{w} (Fin n))) _
      (finrank_euclideanSpace_ulift_fin.{w} n) hk

/-- **Top and higher homology vanish when every connected component is noncompact**
(Hatcher, Proposition 3.29). Let `M` be a Hausdorff space modelled on a real normed space of
dimension `n`. If no connected component of `M` is compact, then `Hₖ(M; N) = 0` for all `k ≥ n`. -/
theorem isZero_singularHomology_of_forall_not_isCompact_connectedComponent {n : ℕ}
    (hn : finrank ℝ E = n) (hcomp : ∀ x : M, ¬ IsCompact (connectedComponent x)) {k : ℕ}
    (hk : n ≤ k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  obtain rfl | hk := hk.eq_or_lt
  · let _ := ChartedSpace.compHomeomorph M (ContinuousLinearEquiv.ofFinrankEq
      (hn.trans (finrank_euclideanSpace_ulift_fin.{w} n).symm)).toHomeomorph
    let F := ModuleCat.restrictScalars.{w} ((Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom)
    have : ∀ T : Type w, PreservesColimitsOfShape (Discrete T) F :=
      fun _ ↦ ⟨fun {K} ↦ ModuleCat.preservesColimit_restrictScalars _ K⟩
    exact (F.isZero_singularHomology_obj_iff N n (TopCat.of M)).1 <|
      isZero_singularHomology_top_of_forall_not_isCompact_connectedComponent_aux
        (E := EuclideanSpace ℝ (ULift.{w} (Fin n))) _
        (finrank_euclideanSpace_ulift_fin.{w} n) hcomp
  · exact isZero_singularHomology_of_finrank_lt N hn hk

/-- **Top and higher homology of a preconnected noncompact manifold vanish** (Hatcher,
Proposition 3.29). For a preconnected noncompact Hausdorff space `M` modelled on a real normed
space of dimension `n`, `Hₖ(M; N) = 0` for every `k ≥ n`. -/
theorem isZero_singularHomology_of_not_compactSpace [PreconnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (hM : ¬ CompactSpace M) {k : ℕ} (hk : n ≤ k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  refine isZero_singularHomology_of_forall_not_isCompact_connectedComponent N hn (fun x hc ↦ hM ?_)
    hk
  rw [← isCompact_univ_iff, ← PreconnectedSpace.connectedComponent_eq_univ x]
  exact hc

/-- **Nonzero homology in degree at least the dimension forces compactness.** If a preconnected
Hausdorff space `M` modelled on a real normed space of dimension `n` has `Hₖ(M; N) ≠ 0` for some
`k ≥ n` and some module `N`, then `M` is compact. -/
theorem compactSpace_of_not_isZero_singularHomology [PreconnectedSpace M] {n k : ℕ}
    (hn : finrank ℝ E = n) (hk : n ≤ k)
    (h : ¬ IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M))) :
    CompactSpace M :=
  Classical.byContradiction fun hM ↦ h (isZero_singularHomology_of_not_compactSpace N hn hM hk)

/-- **Homology of a proper open subset of a preconnected manifold vanishes from the dimension on.**
Let `M` be a preconnected Hausdorff space modelled on a real normed space of dimension `n`, and let
`U ⊆ M` be a proper open subset (`U ≠ univ`). Then `Hₖ(U; N) = 0` for every `k ≥ n`, even if `U` is
disconnected. -/
theorem isZero_singularHomology_of_isOpen_ne_univ [PreconnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) {U : Set M} (hUo : IsOpen U) (hU : U ≠ univ) {k : ℕ} (hk : n ≤ k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of U)) := by
  rcases isEmpty_or_nonempty U with _ | _
  · exact isZero_singularHomologyFunctor_of_isEmpty N (TopCat.of U) k
  · let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hUo⟩
    have := ChartedSpace.locallyPathConnectedSpace E U
    refine isZero_singularHomology_of_forall_not_isCompact_connectedComponent (E := E) N hn
      (fun x hc ↦ hU ?_) hk
    have hOpenM : IsOpen (Subtype.val '' connectedComponent x) :=
      hUo.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_connectedComponent
    have hClosedM : IsClosed (Subtype.val '' connectedComponent x) :=
      (hc.image continuous_subtype_val).isClosed
    have hClopen : IsClopen (Subtype.val '' connectedComponent x) := ⟨hClosedM, hOpenM⟩
    have hUniv : Subtype.val '' connectedComponent x = univ :=
      hClopen.eq_univ ⟨x.1, x, mem_connectedComponent, rfl⟩
    exact univ_subset_iff.1 (hUniv ▸ image_subset_iff.2 fun y _ ↦ y.2)

end Manifold

end TauCeti

namespace ContinuousMap.HomotopyEquiv

section Manifold

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A Hausdorff `n`-manifold homotopy equivalent to `Sⁿ` is compact.** -/
theorem compactSpace_of_sphere {n : ℕ} (e : M ≃ₕ sphere (0 : F) 1) (hE : finrank ℝ E = n)
    (hF : finrank ℝ F = n + 1) :
    CompactSpace M := by
  rcases n with _ | m
  · have : Subsingleton E := Module.finrank_zero_iff.1 hE
    have : DiscreteTopology M := ChartedSpace.discreteTopology E M
    have : Finite (sphere (0 : F) 1) := TauCeti.finite_sphere_of_finrank_eq_one hF 0 1
    have : Finite (ZerothHomotopy (sphere (0 : F) 1)) :=
      Finite.of_surjective _ ZerothHomotopy.mk_surjective
    have : Finite (ZerothHomotopy M) := Finite.of_equiv _ e.zerothHomotopyCongr.symm
    have : Finite M :=
      Finite.of_injective _ ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace
    exact Finite.compactSpace
  · have : PathConnectedSpace M := (e.topCatSphere hF).symm.pathConnectedSpace
    let N : ModuleCat.{w} ℤ := ModuleCat.of ℤ (ULift.{w} ℤ)
    have hN : ¬ IsZero N := fun h ↦
      one_ne_zero (α := ULift.{w} ℤ) ((ModuleCat.subsingleton_of_isZero h).elim ⟨1⟩ ⟨0⟩)
    have hH : ¬ IsZero (((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{w} ℤ) (m + 1)).obj N).obj (TopCat.of M)) :=
      fun h ↦ hN (h.of_iso (e.singularHomologySphereIso N hF (Nat.succ_pos m)).symm)
    exact TauCeti.compactSpace_of_not_isZero_singularHomology N hE le_rfl hH

/-- **A Hausdorff `n`-manifold homotopy equivalent to `Sⁿ` is second countable.** -/
theorem secondCountableTopology_of_sphere {n : ℕ} (e : M ≃ₕ sphere (0 : F) 1)
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) :
    SecondCountableTopology M := by
  have := e.compactSpace_of_sphere hE hF
  exact ChartedSpace.secondCountable_of_sigmaCompact E M

end Manifold

end ContinuousMap.HomotopyEquiv

namespace TauCeti

section Obstructions

/-- **No noncompact Hausdorff `n`-manifold is homotopy equivalent to `Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_not_compactSpace {M : Type*} [TopologicalSpace M]
    [T2Space M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) (hM : ¬ CompactSpace M) :
    IsEmpty (M ≃ₕ sphere (0 : F) 1) :=
  ⟨fun e ↦ hM (e.compactSpace_of_sphere hE hF)⟩

/-- **No proper open subset of a preconnected Hausdorff `n`-manifold is homotopy equivalent to
`Sⁿ`.** -/
theorem isEmpty_homotopyEquiv_sphere_of_isOpen_ne_univ {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} (hE : finrank ℝ E = n) (hF : finrank ℝ F = n + 1) {U : Set M}
    (hUo : IsOpen U) (hU : U ≠ univ) :
    IsEmpty (U ≃ₕ sphere (0 : F) 1) := by
  refine ⟨fun e ↦ hU ?_⟩
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  have : Nonempty (sphere (0 : F) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨x⟩ := e.symm.nonempty
  let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hUo⟩
  have hUc : IsCompact U := isCompact_iff_compactSpace.2 (e.compactSpace_of_sphere hE hF)
  exact IsClopen.eq_univ ⟨hUc.isClosed, hUo⟩ ⟨x.1, x.2⟩

end Obstructions

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Skeleton
public import TauCeti.Topology.CWComplex.Classical.Zero

/-!
# The chains on the based path space over the zero-skeleton

Let `C` be a CW complex in a space `B`, and `b ∈ B`. Brown's semi-free model of the chains
`C_*(P_b B; R)` on the based Moore path space, over the chains `C_*(Ω_b B; R)` on the Moore loops,
is built along the filtration of `C_*(P_b B; R)` by the chains over the skeleta
(`TauCeti.pathFromChainSkeleton`), with one free generator for each cell. This file treats the
zero-cells, the first stage, where the generators are attached to nothing.

For each zero-cell `q`, with point `x_q`, choose a Moore path `τ_q` from `b` to `x_q`. The free
generator of `q` goes to the `0`-chain `[τ_q]` of `τ_q`, read in `C_*(P_b B; R)` by pushing it
forward along `TauCeti.MoorePathBetween.toMoorePathFrom`. So the free module on the zero-cells maps
to the chains over the zero-skeleton by `(α_q)_q ↦ ∑_q α_q · [τ_q]`, linearly over
`C_*(Ω_b B; R)`, and this map is a quasi-isomorphism
(`TauCeti.exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton`).
The statement is written as the relative cycles of the map being relative boundaries, modulo the
stage below the zero-skeleton, which is zero. In this form it is the hypothesis on the new
generators of the cell attachment step
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, with the stages `-1` and `0` of
the filtration.

The chains over the zero-skeleton split over the zero-cells. A cube of paths ending in the
zero-skeleton ends at a single zero-cell, since the cube is connected and the zero-skeleton is
discrete; so these chains are the sums of chains over the fibres `P_{b→x_q} B` of the end point
map (`TauCeti.restrictScalars_pathFromChainSkeleton_zero`), and the sum is direct, since the
fibres are disjoint
(`TauCeti.eq_zero_of_sum_cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom_eq_zero`).
Over the fibre of a single zero-cell, appending `τ_q` is a quasi-isomorphism
`C_*(Ω_b B) → C_*(P_{b→x_q} B)` of left modules
(`TauCeti.exists_cubicalChainDifferential_eq_and_smul_pathChainPoint_add_eq`).

## Main results

* `TauCeti.restrictScalars_pathFromChainSkeleton_zero`: the chains over the zero-skeleton are the
  sums of chains over the fibres of the zero-cells.
* `TauCeti.eq_zero_of_sum_cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom_eq_zero`:
  chains over distinct fibres are independent.
* `TauCeti.exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton`:
  the free module on the zero-cells is quasi-isomorphic to the chains over the zero-skeleton.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex Finsupp

namespace TauCeti

open MoorePathBetween (isEmbedding_toMoorePathFrom toMoorePathFrom toMoorePathFrom_smul)

universe u

variable {B : Type u} [TopologicalSpace B] [T2Space B] {b : B} {C : Set B} [CWComplex C]
  {H : Type*} {R : Type*} [CommRing R]

/-- A cube of paths ending in the zero-skeleton ends at a single zero-cell: the cube is connected
and the zero-skeleton is discrete. -/
private theorem exists_range_subset_preimage_zeroCellPoint {n : ℕ}
    {σ : SingularCube (MoorePathFrom B b) n}
    (hσ : range σ ⊆ preimageSkeleton C (MoorePathFrom.endpoint B b) 0) :
    ∃ q : cell C 0, range σ ⊆ MoorePathFrom.endpoint B b ⁻¹' {(zeroCellPoint C q : B)} := by
  have hσ' (t : Fin n → unitInterval) :
      MoorePathFrom.endpoint B b (σ t) ∈ skeletonLT C ((1 : ℕ) : ℕ∞) := by
    simpa using (mem_preimageSkeleton_iff _ _ _).1 (hσ ⟨t, rfl⟩)
  let e : (Fin n → unitInterval) → skeletonLT C ((1 : ℕ) : ℕ∞) :=
    fun t ↦ ⟨MoorePathFrom.endpoint B b (σ t), hσ' t⟩
  have he : Continuous e := ((map_continuous _).comp (map_continuous σ)).subtype_mk _
  refine ⟨(zeroCellEquiv C).symm (e 0), ?_⟩
  rintro _ ⟨t, rfl⟩
  rw [mem_preimage, mem_singleton_iff, ← zeroCellEquiv_apply, Equiv.apply_symm_apply,
    ← he.isConst_of_preconnectedSpace t 0]

/-- Distinct zero-cells have distinct points. -/
private theorem pairwise_disjoint_preimage_zeroCellPoint :
    Pairwise (Function.onFun Disjoint fun q : cell C 0 ↦
      MoorePathFrom.endpoint B b ⁻¹' {(zeroCellPoint C q : B)}) := by
  exact fun q q' hqq' ↦ Disjoint.preimage _
    (disjoint_singleton.2 fun h ↦ hqq' (zeroCellPoint_injective C (Subtype.ext h)))

/-- The chains over the fibre of a zero-cell lie over the zero-skeleton. -/
theorem cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom_mem_pathFromChainSkeleton_zero
    (q : cell C 0)
    (x : cubicalChainModule (MoorePathBetween B b (zeroCellPoint C q))
      (MooreLoopSpace B (zeroCellPoint C q)) R) :
    cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _) x ∈
      pathFromChainSkeleton b C H R 0 := by
  refine mem_pathFromChainSkeleton.2 <| cubicalChainModuleSupportedIn_mono ?_
    ((range_cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom (H := H) (R := R) _).le
      (LinearMap.mem_range_self _ x))
  intro γ hγ
  rw [mem_preimage, mem_singleton_iff] at hγ
  refine (mem_preimageSkeleton_iff _ _ _).2 ?_
  simpa [hγ] using (zeroCellPoint C q).property

variable (b C H R) in
/-- **The chains over the zero-skeleton split over the zero-cells**: over the ground ring, they
are the sums of the chains supported in the fibres of the end point map over the zero-cells. -/
theorem restrictScalars_pathFromChainSkeleton_zero :
    (pathFromChainSkeleton b C H R 0).restrictScalars R =
      ⨆ q : cell C 0, cubicalChainModuleSupportedIn H R
        (MoorePathFrom.endpoint B b ⁻¹' {(zeroCellPoint C q : B)}) := by
  refine le_antisymm ?_ (iSup_le fun q ↦ ?_)
  · rw [restrictScalars_pathFromChainSkeleton, cubicalChainModuleSupportedIn_eq_span,
      Submodule.span_le]
    rintro _ ⟨n, σ, hσ, rfl⟩
    obtain ⟨q, hq⟩ := exists_range_subset_preimage_zeroCellPoint hσ
    exact Submodule.mem_iSup_of_mem q
      (cubicalChainModuleLof_ofCube_mem_cubicalChainModuleSupportedIn hq)
  · rw [← range_cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom
      (G := MooreLoopSpace B (zeroCellPoint C q)) (H := H) (R := R)]
    rintro _ ⟨x, rfl⟩
    exact cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom_mem_pathFromChainSkeleton_zero
      q x

/-- **Chains over distinct zero-cells are independent**: if a finite sum of chains over the fibres
of distinct zero-cells vanishes, every term vanishes. -/
theorem eq_zero_of_sum_cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom_eq_zero
    {s : Finset (cell C 0)}
    {x : ∀ q : cell C 0, cubicalChainModule (MoorePathBetween B b (zeroCellPoint C q))
      (MooreLoopSpace B (zeroCellPoint C q)) R}
    (hx : ∑ q ∈ s,
      cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _) (x q) = 0)
    {q : cell C 0} (hq : q ∈ s) :
    x q = 0 :=
  cubicalChainModuleLinearMap_injective (H := H) isEmbedding_toMoorePathFrom.injective <| by
    rw [map_zero]
    exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1
      (iSupIndep_cubicalChainModuleSupportedIn pairwise_disjoint_preimage_zeroCellPoint) s _
      (fun q _ ↦
        (range_cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom (H := H) (R := R) _).le
          (LinearMap.mem_range_self _ (x q)))
      hx q hq

/-- A chain over the zero-skeleton is a finite sum of chains over the fibres of the zero-cells,
and the chains over the fibres vanish off the finite set. -/
private theorem exists_eq_sum_of_mem_pathFromChainSkeleton_zero
    {w : cubicalChainModule (MoorePathFrom B b) H R} (hw : w ∈ pathFromChainSkeleton b C H R 0) :
    ∃ (W : ∀ q : cell C 0, cubicalChainModule (MoorePathBetween B b (zeroCellPoint C q))
        (MooreLoopSpace B (zeroCellPoint C q)) R) (t : Finset (cell C 0)),
      (∀ q ∉ t, W q = 0) ∧ w = ∑ q ∈ t,
        cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _) (W q) := by
  have hw' : w ∈ ⨆ q : cell C 0, cubicalChainModuleSupportedIn H R
      (MoorePathFrom.endpoint B b ⁻¹' {(zeroCellPoint C q : B)}) := by
    rw [← restrictScalars_pathFromChainSkeleton_zero]
    exact hw
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hw'
  choose W hW using fun q ↦
    (range_cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom
      (G := MooreLoopSpace B (zeroCellPoint C q)) (H := H) (R := R) _).ge (hf q)
  refine ⟨W, f.support, fun q hq ↦
    cubicalChainModuleLinearMap_injective (H := H) isEmbedding_toMoorePathFrom.injective ?_,
    ?_⟩
  · rw [hW, map_zero, ← notMem_support_iff.1 hq]
  · simp only [Finsupp.sum, hW]

/-- **The free module on the zero-cells is quasi-isomorphic to the chains over the
zero-skeleton.** Choose a Moore path `τ q` from `b` to each zero-cell `q`, and send the free
generator of `q` to the `0`-chain `[τ q]`, read in `C_*(P_b B; R)`. Every relative cycle `(y, w)` of
the resulting map `(α_q)_q ↦ ∑_q α_q · [τ q]`, with `w` over the zero-skeleton, is a relative
boundary `(d y', ∑_q y'_q · [τ q] + d w')` with `w'` over the zero-skeleton, modulo the chains over
the stage `-1`, which are zero.

This is the hypothesis on the new generators in
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists` for the zero-cells, with the
stages `-1` and `0` of `TauCeti.pathFromChainSkeleton`. -/
theorem exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton
    (τ : ∀ q : cell C 0, MoorePathBetween B b (zeroCellPoint C q))
    (y : cell C 0 →₀ loopChainAlgebra B b R) (w : cubicalChainModule (MoorePathFrom B b) H R)
    (hy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    (hw : w ∈ pathFromChainSkeleton b C H R 0)
    (hyw : linearCombination (loopChainAlgebra B b R)
        (fun q ↦ cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _)
          (pathChainPoint R (τ q))) y -
      cubicalChainModuleDifferential (MoorePathFrom B b) H R w ∈
        pathFromChainSkeleton b C H R (-1)) :
    ∃ (y' : cell C 0 →₀ loopChainAlgebra B b R) (w' : cubicalChainModule (MoorePathFrom B b) H R),
      w' ∈ pathFromChainSkeleton b C H R 0 ∧
        mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y ∧
          linearCombination (loopChainAlgebra B b R)
              (fun q ↦ cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _)
                (pathChainPoint R (τ q))) y' +
            cubicalChainModuleDifferential (MoorePathFrom B b) H R w' - w ∈
              pathFromChainSkeleton b C H R (-1) := by
  classical
  have hbot : pathFromChainSkeleton b C H R (-1) = ⊥ :=
    pathFromChainSkeleton_eq_bot_of_neg (by norm_num)
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hyw
  rw [hbot]
  -- Split `w` over the zero-cells, on a finite set `s` that also carries `y`.
  obtain ⟨W, t, hWt, rfl⟩ := exists_eq_sum_of_mem_pathFromChainSkeleton_zero hw
  set s := t ∪ y.support
  have hws : ∑ q ∈ t, cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _) (W q) =
      ∑ q ∈ s, cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _) (W q) :=
    Finset.sum_subset Finset.subset_union_left fun q _ hq ↦ by rw [hWt q hq, map_zero]
  have hys : linearCombination (loopChainAlgebra B b R)
      (fun q ↦ cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _)
        (pathChainPoint R (τ q))) y =
        ∑ q ∈ s, cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _)
          (y q • pathChainPoint R (τ q)) := by
    rw [linearCombination_apply]
    simp_rw [← cubicalChainModuleLinearMap_smul _ toMoorePathFrom_smul]
    exact sum_of_support_subset _ Finset.subset_union_right _ fun q _ ↦ by rw [zero_smul, map_zero]
  -- Over each zero-cell, `y q · [τ q]` bounds `W q`, since chains over distinct fibres are
  -- independent.
  have heq (q : cell C 0) (hq : q ∈ s) : y q • pathChainPoint R (τ q) =
      cubicalChainModuleDifferential _ _ R (W q) := by
    refine sub_eq_zero.1
      (eq_zero_of_sum_cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom_eq_zero (H := H)
        (x := fun q ↦ y q • pathChainPoint R (τ q) - cubicalChainModuleDifferential _ _ R (W q))
        ?_ hq)
    simp only [map_sub, Finset.sum_sub_distrib, ← hys, ← cubicalChainModuleDifferential_linearMap,
      ← map_sum, ← hws, hyw, sub_self]
  -- Over each zero-cell, appending `τ q` is a quasi-isomorphism.
  choose! α' W' hα' hW' using fun q hq ↦
    exists_cubicalChainDifferential_eq_and_smul_pathChainPoint_add_eq (τ q)
      (by simpa using DFunLike.congr_fun hy q) (heq q hq)
  refine ⟨∑ q ∈ s, single q (α' q),
    ∑ q ∈ s, cubicalChainModuleLinearMap (G' := H) R (toMoorePathFrom b _) (W' q),
    Submodule.sum_mem _ fun q _ ↦
      cubicalChainModuleLinearMap_moorePathBetweenToMoorePathFrom_mem_pathFromChainSkeleton_zero
        q _,
    ?_, ?_⟩
  · refine Finsupp.ext fun q ↦ ?_
    simp only [map_sum, mapRange.linearMap_apply, mapRange_single, Finset.sum_apply',
      single_apply, Finset.sum_ite_eq']
    split_ifs with hq
    · exact hα' q hq
    · exact (notMem_support_iff.1 fun h ↦ hq (Finset.mem_union_right _ h)).symm
  · rw [Submodule.mem_bot, map_sum, map_sum, hws, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun q hq ↦ ?_
    rw [linearCombination_single, ← cubicalChainModuleLinearMap_smul _ toMoorePathFrom_smul,
      cubicalChainModuleDifferential_linearMap, ← map_add, hW' q hq, sub_self]

end TauCeti

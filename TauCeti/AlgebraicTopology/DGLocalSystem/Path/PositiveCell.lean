/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Cell
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Excision
import TauCeti.Algebra.Homology.ComplexShape.Basic

/-!
# The chains on the based path space over the cells of positive dimension

Let `C` be a relative CW complex in a space `B`, and `b ∈ B`. Brown's semi-free model of the chains
`C_*(P_b B; R)` on the based Moore path space, over the chains `C_*(Ω_b B; R)` on the Moore loops,
is built along the filtration of `C_*(P_b B; R)` by the chains over the skeleta
(`TauCeti.pathFromChainSkeleton`), with one free generator for each cell. The zero-cells are
treated in `TauCeti.AlgebraicTopology.DGLocalSystem.Path.ZeroCell`; this file treats the
`(m + 1)`-cells, the step from the stage `m` to the stage `m + 1`.

Choose a Moore path from `b` to the centre of each `(m + 1)`-cell `j`. Followed by the images of
the radial segments of the disk of `j`, it gives a family of Moore paths from `b` to the points of
the disk, an `(m + 1)`-cube of paths `cⱼ` whose end points lie in the closed cell and whose faces
end in its boundary (`TauCeti.cellSectionPathChain`). The free generator of `j` is sent to `cⱼ`,
so the free module on the `(m + 1)`-cells maps to the chains over the `(m + 1)`-skeleton by
`(α_j)_j ↦ ∑_j α_j · cⱼ`, linearly over `C_*(Ω_b B; R)`. This map is a quasi-isomorphism onto the
quotient of the `(m + 1)`-th stage by the `m`-th
(`TauCeti.exists_mapRange_eq_and_linearCombination_cellSectionPathChain_add_sub_mem`), written as
the relative cycles of the map being relative boundaries: the form of the hypothesis on the new
generators of the cell attachment step
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`.

The proof goes through the pullback `P` of the based path fibration to the disks of the cells, and
its part `∂P` over the boundary spheres. The relative chains of `(P, ∂P)` map quasi-isomorphically
onto the quotient of the two stages
(`TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`).
Their relative homology vanishes below degree `m + 1`
(`TauCeti.isZero_homology_cubicalChainComplex_ofSubset_sigmaCellMap`), and above it is a direct sum
of copies of the homology of the loop space, one for each cell, through the action on the section
cubes (`TauCeti.cellPathPullbackHomologyEquiv`). Read on chains, these say that a cycle of the free
module whose action on the section cubes bounds modulo `∂P` is itself a boundary, and that every
relative cycle of `(P, ∂P)` is, up to a relative boundary, the action of a cycle of the free module.

## Main definitions

* `TauCeti.cellSectionPathChain γ j`: the chain of the `(m + 1)`-cell `j` in the based path space.

## Main results

* `TauCeti.cellSectionPathChain_mem_pathFromChainSkeleton`,
  `TauCeti.cubicalChainModuleDifferential_cellSectionPathChain_mem_pathFromChainSkeleton`: the chain
  of a cell lies over the `(m + 1)`-skeleton, and its boundary over the `m`-skeleton.
* `TauCeti.exists_mapRange_eq_and_linearCombination_cellSectionPathChain_add_sub_mem`: the free
  module on the `(m + 1)`-cells is quasi-isomorphic to the quotient of the `(m + 1)`-th stage of the
  skeletal filtration by the `m`-th.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

variable {B : Type} [TopologicalSpace B] [T2Space B] {b : B} {C D : Set B} [RelCWComplex C D]
  {R : Type} [CommRing R]

section Homology

variable {m : ℕ} (γ : ∀ j : cell C (m + 1), MoorePathBetween B b (map (m + 1) j 0))

omit [T2Space B] in
/-- **Injectivity of `TauCeti.cellPathPullbackHomologyEquiv` on chains.** If `∑ⱼ aⱼ · cⱼ` is a
relative boundary of the pullback over the `(m + 1)`-cells, for `q`-cycles `aⱼ` of the Moore loops
and the section cubes `cⱼ`, then every `aⱼ` is a boundary. -/
private theorem exists_boundary_eq_of_sum_leftAct_sub_boundary_mem {q : ℕ}
    (s : Finset (cell C (m + 1)))
    (a : cell C (m + 1) → NormalizedCubicalChain (MooreLoopSpace B b) R q)
    (ha : ∀ j, ((normalizedCubicalChainComplex R).obj (_root_.TopCat.of (MooreLoopSpace B b))).d q
      (q - 1) (a j) = 0)
    (u : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R (q + (m + 1) + 1))
    (hu : ∑ j ∈ s, NormalizedCubicalChain.leftAct (MooreLoopSpace B b)
        (MoorePathPullback (sigmaCellMap C (m + 1)) b) R q (m + 1) (a j)
          (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)) -
        NormalizedCubicalChain.boundary _ R (q + (m + 1)) u ∈
      NormalizedCubicalChain.supportedIn R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) (q + (m + 1))) :
    ∀ j ∈ s, ∃ a' : NormalizedCubicalChain (MooreLoopSpace B b) R (q + 1),
      NormalizedCubicalChain.boundary _ R q a' = a j := by
  classical
  intro j hj
  set K := (normalizedCubicalChainComplex R).obj (_root_.TopCat.of (MooreLoopSpace B b))
  let z (j : cell C (m + 1)) : K.cycles q :=
    K.moduleCatCyclesMk (a j) (q - 1) (ChainComplex.next_nat q) (ha j)
  have hz (j : cell C (m + 1)) : K.iCycles q (z j) = a j := K.iCycles_moduleCatCyclesMk _ _ _ _ _
  have hrep := TopPair.IsCubicalRepresentative.sum (s := s) fun j _ ↦ by
    have h := isCubicalRepresentative_cellPathPullbackHomologyEquiv γ R q j (z j)
    rwa [normalizedCubicalChainComplexXEquiv_apply, hz] at h
  have h0 := hrep.eq_zero_iff.2 ⟨u, by
    have hd : ((normalizedCubicalChainComplex R).obj (cellPathPullbackPair b C (m + 1)).fst).d
        (q + (m + 1) + 1) (q + (m + 1)) u =
          NormalizedCubicalChain.boundary (cellPathPullbackPair b C (m + 1)).fst R
            (q + (m + 1)) u :=
      normalizedCubicalChainComplex_obj_d_apply (R := R) (cellPathPullbackPair b C (m + 1)).fst
        (q + (m + 1)) u
    rw [TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff, TopPair.range_ofSubset_map,
      normalizedCubicalChainComplexXEquiv_apply, hd]
    exact hu⟩
  rw [← map_sum, LinearEquiv.map_eq_zero_iff] at h0
  have hj0 : K.homologyπ q (z j) = 0 := by
    simpa [DirectSum.lof_eq_of, DirectSum.of_apply, hj] using congrArg (fun x ↦ x j) h0
  obtain ⟨a', ha'⟩ := (K.moduleCat_homologyπ_eq_zero_iff (m := q + 1) (by simp) (z j)).1 hj0
  refine ⟨a', ?_⟩
  have := congrArg (K.iCycles q) ha'
  rw [HomologicalComplex.moduleCat_iCycles_toCycles_apply, hz] at this
  exact (normalizedCubicalChainComplex_obj_d_apply _ q a').symm.trans this

omit [T2Space B] in
/-- **Surjectivity of `TauCeti.cellPathPullbackHomologyEquiv` on chains.** Every relative cycle of
dimension `q + m + 1` of the pullback over the `(m + 1)`-cells is, up to a relative boundary,
`∑ⱼ aⱼ · cⱼ` for `q`-cycles `aⱼ` of the Moore loops and the section cubes `cⱼ`. -/
private theorem exists_sub_sum_leftAct_sub_boundary_mem {q : ℕ}
    (u : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R (q + (m + 1)))
    (hu : NormalizedCubicalChain.boundary _ R (q + m) u ∈
      NormalizedCubicalChain.supportedIn R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) (q + m)) :
    ∃ (s : Finset (cell C (m + 1)))
      (a : cell C (m + 1) → NormalizedCubicalChain (MooreLoopSpace B b) R q),
      (∀ j, ((normalizedCubicalChainComplex R).obj (_root_.TopCat.of (MooreLoopSpace B b))).d q
        (q - 1) (a j) = 0) ∧
      ∃ v : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R
          (q + (m + 1) + 1),
        u - ∑ j ∈ s, NormalizedCubicalChain.leftAct (MooreLoopSpace B b)
            (MoorePathPullback (sigmaCellMap C (m + 1)) b) R q (m + 1) (a j)
              (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)) -
          NormalizedCubicalChain.boundary _ R (q + (m + 1)) v ∈
        NormalizedCubicalChain.supportedIn R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
          {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) (q + (m + 1)) := by
  classical
  set K := (normalizedCubicalChainComplex R).obj (_root_.TopCat.of (MooreLoopSpace B b))
  have hd : ((normalizedCubicalChainComplex R).obj (cellPathPullbackPair b C (m + 1)).fst).d
      (q + (m + 1)) (q + m) u =
        NormalizedCubicalChain.boundary (cellPathPullbackPair b C (m + 1)).fst R (q + m) u :=
    normalizedCubicalChainComplex_obj_d_apply (R := R) (cellPathPullbackPair b C (m + 1)).fst
      (q + m) u
  obtain ⟨μ, hμ⟩ := TopPair.exists_isCubicalRepresentative_of_d_mem
    (P := cellPathPullbackPair b C (m + 1)) (n := q + (m + 1)) u (by
      rw [show q + (m + 1) - 1 = q + m by omega,
        TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff, TopPair.range_ofSubset_map,
        normalizedCubicalChainComplexXEquiv_apply, hd]
      exact hu)
  set ν := (cellPathPullbackHomologyEquiv γ R q).symm μ
  choose z hz using fun j ↦ K.moduleCat_homologyπ_surjective q (ν j)
  have hrep := TopPair.IsCubicalRepresentative.sum (s := ν.support) fun j _ ↦
    isCubicalRepresentative_cellPathPullbackHomologyEquiv γ R q j (z j)
  have hsum : ∑ j ∈ ν.support, cellPathPullbackHomologyEquiv γ R q
      (DirectSum.lof R _ _ j (K.homologyπ q (z j))) = μ := by
    rw [← map_sum, ← (cellPathPullbackHomologyEquiv γ R q).apply_symm_apply μ]
    congr 1
    simp_rw [hz, DirectSum.lof_eq_of]
    exact DirectSum.sum_support_of ν
  rw [hsum] at hrep
  obtain ⟨v, hv⟩ := (hμ.sub hrep).eq_zero_iff.1 (sub_self μ)
  refine ⟨ν.support, fun j ↦ normalizedCubicalChainComplexXEquiv _ q (K.iCycles q (z j)),
    fun j ↦ K.moduleCat_d_iCycles_apply q _ (z j), v, ?_⟩
  have hd' : ((normalizedCubicalChainComplex R).obj (cellPathPullbackPair b C (m + 1)).fst).d
      (q + (m + 1) + 1) (q + (m + 1)) v =
        NormalizedCubicalChain.boundary (cellPathPullbackPair b C (m + 1)).fst R (q + (m + 1)) v :=
    normalizedCubicalChainComplex_obj_d_apply (R := R) (cellPathPullbackPair b C (m + 1)).fst
      (q + (m + 1)) v
  rw [TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff, TopPair.range_ofSubset_map,
    normalizedCubicalChainComplexXEquiv_apply, hd'] at hv
  exact hv

/-- **Relative cycles below the cell dimension bound.** A relative cycle of dimension `p < m + 1`
of the pullback over the `(m + 1)`-cells is a relative boundary. -/
private theorem exists_sub_boundary_mem_of_lt {p : ℕ} (hp : p < m + 1)
    (u : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R p)
    (hu : ((normalizedCubicalChainComplex R).obj (cellPathPullbackPair b C (m + 1)).fst).d p
        (p - 1) u ∈
      LinearMap.range (((normalizedCubicalChainComplex R).map
        (cellPathPullbackPair b C (m + 1)).map).f (p - 1)).hom) :
    ∃ v : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R (p + 1),
      u - NormalizedCubicalChain.boundary _ R p v ∈
        NormalizedCubicalChain.supportedIn R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
          {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) p := by
  obtain ⟨v, hv⟩ := TopPair.exists_d_sub_mem_range_of_isZero
    (isZero_homology_cubicalChainComplex_ofSubset_sigmaCellMap R b C hp) u hu
  refine ⟨v, ?_⟩
  have hd : ((normalizedCubicalChainComplex R).obj (cellPathPullbackPair b C (m + 1)).fst).d
      (p + 1) p v =
        NormalizedCubicalChain.boundary (cellPathPullbackPair b C (m + 1)).fst R p v :=
    normalizedCubicalChainComplex_obj_d_apply (R := R) (cellPathPullbackPair b C (m + 1)).fst p v
  rw [TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff, TopPair.range_ofSubset_map,
    normalizedCubicalChainComplexXEquiv_apply, hd] at hv
  exact hv

end Homology

section Chains

open Finsupp

variable {m : ℕ} (γ : ∀ j : cell C (m + 1), MoorePathBetween B b (map (m + 1) j 0)) {H : Type*}

/-- The **chain of the `(m + 1)`-cell `j` in the based path space**: the section cube
`TauCeti.cellSectionCube`, the radial Moore paths from `b` to the points of the disk of `j`, read
as an `(m + 1)`-chain of `P_b B`. In Brown's semi-free model of `C_*(P_b B; R)` over the chains on
the Moore loops, the free generator of `j` is sent to this chain
(`TauCeti.exists_mapRange_eq_and_linearCombination_cellSectionPathChain_add_sub_mem`). -/
def cellSectionPathChain (j : cell C (m + 1)) : cubicalChainModule (MoorePathFrom B b) H R :=
  cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom
    (cubicalChainModuleLof (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R (m + 1)
      (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)))

omit [T2Space B] in
/-- The chain of an `(m + 1)`-cell has dimension `m + 1`. -/
theorem cellSectionPathChain_mem_cubicalChainModuleGrading (j : cell C (m + 1)) :
    cellSectionPathChain (H := H) (R := R) γ j ∈
      cubicalChainModuleGrading (MoorePathFrom B b) H R (-((m + 1 : ℕ) : ℤ)) :=
  cubicalChainModuleLinearMap_mem _ (cubicalChainModuleLof_mem _)

/-- The chains of the pullback over the disks of the `(m + 1)`-cells lie over the
`(m + 1)`-skeleton. -/
private theorem cubicalChainModuleLinearMap_mem_pathFromChainSkeleton_succ
    (x : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R) :
    cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom x ∈
      pathFromChainSkeleton b C H R (m + 1 : ℕ) := by
  refine cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton (S := Set.univ)
    (fun d _ ↦ ?_) (by simp)
  rw [show ((((m + 1 : ℕ) : ℤ) + 1).toNat : ℕ∞) = ((m + 1 + 1 : ℕ) : ℕ∞) by norm_cast,
    sigmaCellMap_apply]
  exact map_mem_skeletonLT_succ d.1 (mem_closedBall_zero_iff.1 d.2.property)

/-- The chains of the pullback over the boundary spheres of the `(m + 1)`-cells lie over the
`m`-skeleton. -/
private theorem cubicalChainModuleLinearMap_mem_pathFromChainSkeleton_of_mem
    {x : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R}
    (hx : x ∈ cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1))
      b ⁻¹' {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom x ∈
      pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1) := by
  refine cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton (fun d hd ↦ ?_) hx
  rw [sub_add_cancel, Int.toNat_natCast, sigmaCellMap_apply]
  exact cellFrontier_subset_skeletonLT (m + 1) d.1
    ⟨_, mem_sphere_zero_iff_norm.2 hd, rfl⟩

/-- The chain of an `(m + 1)`-cell lies over the `(m + 1)`-skeleton. -/
theorem cellSectionPathChain_mem_pathFromChainSkeleton (j : cell C (m + 1)) :
    cellSectionPathChain (H := H) (R := R) γ j ∈ pathFromChainSkeleton b C H R (m + 1 : ℕ) :=
  cubicalChainModuleLinearMap_mem_pathFromChainSkeleton_succ _

omit [T2Space B] in
/-- The section cubes of the `(m + 1)`-cells, as chains of the pullback over their disks. -/
private def cellSectionChain (j : cell C (m + 1)) :
    cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R :=
  cubicalChainModuleLof (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R (m + 1)
    (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j))

omit [T2Space B] in
/-- The part of the pullback over the boundary spheres of the cells is invariant under the
concatenation of loops in front. -/
private theorem smul_mem_cellSphere (g : MooreLoopSpace B b)
    (x : MoorePathPullback (sigmaCellMap C (m + 1)) b)
    (hx : x ∈ MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
      {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) :
    g • x ∈ MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
      {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1} := by
  simpa [MoorePathPullback.smul_eq_leftAct, MoorePathPullback.proj_apply] using hx

omit [T2Space B] in
/-- The boundary of the section cube of a cell lies over the boundary sphere. -/
private theorem boundary_ofCube_cellSectionCube_mem (j : cell C (m + 1)) :
    NormalizedCubicalChain.boundary _ R m
        (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)) ∈
      NormalizedCubicalChain.supportedIn R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) m := by
  have hc : Set.MapsTo (cellSectionCube C (m + 1) γ j) (Cube.boundary (Fin (m + 1)))
      (Set.range (cellPathPullbackPair b C (m + 1)).map) := by
    intro d hd
    refine TopPair.range_ofSubset_map.ge ?_
    have h : MoorePathPullback.proj (sigmaCellMap C (m + 1)) b (cellSectionCube C (m + 1) γ j d) ∈
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1} := by
      rw [MoorePathPullback.proj_apply, point_cellSectionCube, cellCubeMap_apply,
        Set.mem_ofPred_eq, norm_cubeHomeomorphClosedBall_eq_one_iff]
      exact hd
    exact h
  have h : NormalizedCubicalChain.boundary (cellPathPullbackPair b C (m + 1)).fst R m
      (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)) ∈
        NormalizedCubicalChain.supportedIn R
          (Set.range (cellPathPullbackPair b C (m + 1)).map) m := by
    rw [← NormalizedCubicalChain.range_map_eq_supportedIn_range R
      (cellPathPullbackPair b C (m + 1)).isEmbedding_map.isInducing]
    exact ⟨_, TopPair.map_cubicalBoundaryChainOfCube R _ hc⟩
  rw [TopPair.range_ofSubset_map] at h
  exact h

/-- The boundary of the chain of an `(m + 1)`-cell lies over the `m`-skeleton: it is the chain of
the radial paths to the points of the boundary sphere of the cell. -/
theorem cubicalChainModuleDifferential_cellSectionPathChain_mem_pathFromChainSkeleton
    (j : cell C (m + 1)) :
    cubicalChainModuleDifferential (MoorePathFrom B b) H R
        (cellSectionPathChain (H := H) (R := R) γ j) ∈
      pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1) := by
  rw [cellSectionPathChain, cubicalChainModuleDifferential_linearMap,
    cubicalChainModuleDifferential_lof_succ]
  exact cubicalChainModuleLinearMap_mem_pathFromChainSkeleton_of_mem
    (cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn
      (boundary_ofCube_cellSectionCube_mem γ j))

omit [T2Space B] in
/-- On a finite sum of generators with coefficients of a single dimension `q`, acting on the
section cubes is the left action of the coefficients on the section cubes, in dimension
`q + m + 1`. -/
private theorem linearCombination_sum_single {q : ℕ} (s : Finset (cell C (m + 1)))
    (a : cell C (m + 1) → NormalizedCubicalChain (MooreLoopSpace B b) R q) :
    linearCombination (loopChainAlgebra B b R)
        (cellSectionChain (H := H) (R := R) γ)
        (∑ j ∈ s, single j (cubicalChainLof (MooreLoopSpace B b) R q (a j))) =
      cubicalChainModuleLof (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R (q + m + 1)
        (∑ j ∈ s, NormalizedCubicalChain.leftAct (MooreLoopSpace B b)
          (MoorePathPullback (sigmaCellMap C (m + 1)) b) R q (m + 1) (a j)
            (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j))) := by
  simp only [map_sum, linearCombination_single, cellSectionChain, lof_smul_cubicalChainModuleLof]
  rfl

omit [T2Space B] in
/-- The graded Leibniz rule for the action on a section cube holds modulo the chains over the
boundary spheres, which contain the boundary of the section cube. -/
private theorem differential_smul_sub_mem {p : ℤ} {a : loopChainAlgebra B b R}
    (ha : a ∈ cubicalChainGrading (MooreLoopSpace B b) R p) (j : cell C (m + 1)) :
    cubicalChainModuleDifferential _ H R
        (a • cubicalChainModuleLof (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R (m + 1)
          (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j))) -
      cubicalChainDifferential _ R a •
        cubicalChainModuleLof (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R (m + 1)
          (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)) ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  rw [(cubicalChainModule_isDGLeftModule (MooreLoopSpace B b)
    (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R).leibniz ha, add_sub_cancel_left,
    Units.smul_def]
  refine zsmul_mem (smul_mem_cubicalChainModuleSupportedIn smul_mem_cellSphere a ?_) _
  rw [cubicalChainModuleDifferential_lof_succ]
  exact cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn
    (boundary_ofCube_cellSectionCube_mem γ j)

omit [T2Space B] in
/-- Acting on the section cubes commutes with the differentials modulo the chains over the
boundary spheres, on coefficients of a single degree. -/
private theorem differential_linearCombination_sub_mem {p : ℤ}
    {y : cell C (m + 1) →₀ loopChainAlgebra B b R}
    (hy : ∀ j, y j ∈ cubicalChainGrading (MooreLoopSpace B b) R p) :
    cubicalChainModuleDifferential _ H R (linearCombination (loopChainAlgebra B b R)
        (cellSectionChain (H := H) (R := R) γ) y) -
      linearCombination (loopChainAlgebra B b R)
        (cellSectionChain (H := H) (R := R) γ)
        (mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y) ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  rw [linearCombination_apply, linearCombination_apply, mapRange.linearMap_apply,
    sum_mapRange_index (h := fun j a ↦ a • cellSectionChain (H := H) (R := R) γ j)
      (fun _ ↦ zero_smul _ _), map_finsuppSum, ← Finsupp.sum_sub, Finsupp.sum]
  exact sum_mem fun j _ ↦ differential_smul_sub_mem γ (hy j) j

omit [T2Space B] in
/-- Pushing forward to the based path space carries the action on the section cubes to the action
on the chains of the cells. -/
private theorem cubicalChainModuleLinearMap_linearCombination
    (y : cell C (m + 1) →₀ loopChainAlgebra B b R) :
    cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom
        (linearCombination (loopChainAlgebra B b R)
          (cellSectionChain (H := H) (R := R) γ) y) =
      linearCombination (loopChainAlgebra B b R) (cellSectionPathChain (H := H) (R := R) γ) y := by
  simp only [linearCombination_apply, map_finsuppSum, cellSectionPathChain]
  refine Finsupp.sum_congr fun j _ ↦ cubicalChainModuleLinearMap_smul _ (fun ω x ↦ ?_) _ _
  rw [MoorePathPullback.smul_eq_leftAct]
  exact MoorePathPullback.toMoorePathFrom_leftAct ω x

omit [T2Space B] in
/-- **Injectivity on the free module over the loop algebra.** If acting on the section cubes with
a cycle `y` of the free module on the `(m + 1)`-cells gives a relative boundary of the pullback over
the cells, then `y` is a boundary. -/
private theorem exists_mapRange_eq_of_linearCombination_sub_differential_mem {i : ℤ}
    {y : cell C (m + 1) →₀ loopChainAlgebra B b R}
    (hy : ∀ j, y j ∈ cubicalChainGrading (MooreLoopSpace B b) R (i + (m + 1 : ℕ)))
    (hdy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    {u : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R}
    (hu : u ∈ cubicalChainModuleGrading _ H R (i - 1))
    (hyu : linearCombination (loopChainAlgebra B b R)
        (cellSectionChain (H := H) (R := R) γ) y -
        cubicalChainModuleDifferential _ H R u ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    ∃ y' : cell C (m + 1) →₀ loopChainAlgebra B b R,
      (∀ j, y' j ∈ cubicalChainGrading (MooreLoopSpace B b) R (i - 1 + (m + 1 : ℕ))) ∧
        mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y := by
  classical
  rcases lt_or_ge 0 (i + (m + 1 : ℕ)) with hi | hi
  · refine ⟨0, fun _ ↦ zero_mem _, Finsupp.ext fun j ↦ ?_⟩
    rw [map_zero, Finsupp.coe_zero, Pi.zero_apply,
      eq_zero_of_mem_cubicalChainGrading_of_pos _ _ hi (hy j)]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = -(i + (m + 1 : ℕ)) :=
    ⟨(-(i + (m + 1 : ℕ))).toNat, Int.toNat_of_nonneg (by omega)⟩
  choose a ha using fun j ↦ exists_cubicalChainLof_eq (hy j) q hq
  have hy' : y = ∑ j ∈ y.support, single j (cubicalChainLof (MooreLoopSpace B b) R q (a j)) := by
    simp_rw [ha]
    exact (Finsupp.sum_single y).symm
  have hcyc (j : cell C (m + 1)) :
      ((normalizedCubicalChainComplex R).obj (_root_.TopCat.of (MooreLoopSpace B b))).d q
        (q - 1) (a j) = 0 := by
    rw [normalizedCubicalChainComplex_d_eq_zero_iff, ha]
    simpa using DFunLike.congr_fun hdy j
  obtain ⟨u, rfl⟩ := exists_cubicalChainModuleLof_eq hu (q + m + 1 + 1) (by push_cast; omega)
  rw [hy', linearCombination_sum_single, cubicalChainModuleDifferential_lof_succ, ← map_sub,
    cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff] at hyu
  choose! c hc using exists_boundary_eq_of_sum_leftAct_sub_boundary_mem γ y.support a hcyc u hyu
  refine ⟨∑ j ∈ y.support, single j (cubicalChainLof (MooreLoopSpace B b) R (q + 1) (c j)),
    fun j ↦ ?_, ?_⟩
  · rw [Finsupp.finsetSum_apply]
    refine sum_mem fun k _ ↦ ?_
    rw [single_apply]
    split_ifs
    · convert cubicalChainLof_mem (MooreLoopSpace B b) R (c k) using 2
      push_cast
      omega
    · exact zero_mem _
  · conv_rhs => rw [hy']
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [mapRange.linearMap_apply, mapRange_single, cubicalChainDifferential_lof_succ, hc j hj]

/-- **Surjectivity onto the relative cycles of the pullback over the cells.** Every relative cycle
of the pullback over the `(m + 1)`-cells is, up to a relative boundary, the action of a cycle of
the free module on the cells on the section cubes. -/
private theorem exists_sub_linearCombination_sub_differential_mem {i : ℤ}
    {r : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R}
    (hr : r ∈ cubicalChainModuleGrading _ H R i)
    (hdr : cubicalChainModuleDifferential _ H R r ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    ∃ (z : cell C (m + 1) →₀ loopChainAlgebra B b R)
      (v : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R),
      mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) z = 0 ∧
        r - linearCombination (loopChainAlgebra B b R)
            (cellSectionChain (H := H) (R := R) γ) z -
          cubicalChainModuleDifferential _ H R v ∈
        cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
          {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  classical
  rcases lt_or_ge 0 i with hi | hi
  · refine ⟨0, 0, map_zero _, ?_⟩
    rw [eq_zero_of_mem_cubicalChainModuleGrading hr hi, map_zero, map_zero, sub_zero, sub_zero]
    exact zero_mem _
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = -i := ⟨(-i).toNat, Int.toNat_of_nonneg (by omega)⟩
  rcases lt_or_ge p (m + 1) with hpm | hpm
  · obtain ⟨r, rfl⟩ := exists_cubicalChainModuleLof_eq hr p hp
    obtain ⟨v, hv⟩ := exists_sub_boundary_mem_of_lt hpm r (by
      rcases p with _ | p
      · rw [HomologicalComplex.shape _ 0 (0 - 1) (by simp)]
        exact zero_mem _
      · have hd : ((normalizedCubicalChainComplex R).obj (cellPathPullbackPair b C (m + 1)).fst).d
            (p + 1) p r =
              NormalizedCubicalChain.boundary (cellPathPullbackPair b C (m + 1)).fst R p r :=
          normalizedCubicalChainComplex_obj_d_apply (R := R) (cellPathPullbackPair b C (m + 1)).fst
            p r
        rw [Nat.add_sub_cancel, TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff,
          TopPair.range_ofSubset_map, normalizedCubicalChainComplexXEquiv_apply, hd]
        rw [cubicalChainModuleDifferential_lof_succ,
          cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff] at hdr
        exact hdr)
    refine ⟨0, cubicalChainModuleLof _ H R (p + 1) v, map_zero _, ?_⟩
    rw [map_zero, sub_zero, cubicalChainModuleDifferential_lof_succ, ← map_sub]
    exact cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn hv
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + (m + 1) := ⟨p - (m + 1), by omega⟩
    obtain ⟨r, rfl⟩ := exists_cubicalChainModuleLof_eq hr (q + m + 1) (by push_cast; omega)
    rw [cubicalChainModuleDifferential_lof_succ,
      cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff] at hdr
    obtain ⟨s, a, ha, v, hv⟩ := exists_sub_sum_leftAct_sub_boundary_mem γ r hdr
    refine ⟨∑ j ∈ s, single j (cubicalChainLof _ R q (a j)),
      cubicalChainModuleLof _ H R (q + m + 1 + 1) v, ?_, ?_⟩
    · rw [map_sum]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [mapRange.linearMap_apply, mapRange_single,
        (normalizedCubicalChainComplex_d_eq_zero_iff (a j)).1 (ha j), single_zero]
    · rw [linearCombination_sum_single, cubicalChainModuleDifferential_lof_succ, ← map_sub,
        ← map_sub]
      exact cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn hv

end Chains

section Model

open Finsupp

variable {m : ℕ} (γ : ∀ j : cell C (m + 1), MoorePathBetween B b (map (m + 1) j 0)) {H : Type*}

/-- For a relative cycle `(y, w)` of a single degree `i`, the quasi-isomorphism from the relative
chains of the pullback over the cells onto the quotient of the filtration
(`TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`) gives a chain `u₀` of the
pullback, of degree `i - 1`, bounding the action of `y` on the section cubes modulo the boundary
spheres, and a chain `v₀` of the `(m + 1)`-th stage with `π u₀ + d v₀ ≡ w` modulo the `m`-th. -/
private theorem exists_differential_sub_mem_of_homogeneous {i : ℤ}
    {y : cell C (m + 1) →₀ loopChainAlgebra B b R}
    (hy : ∀ j, y j ∈ cubicalChainGrading (MooreLoopSpace B b) R (i + (m + 1 : ℕ)))
    (hdy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    {w : cubicalChainModule (MoorePathFrom B b) H R}
    (hwi : w ∈ cubicalChainModuleGrading _ H R (i - 1))
    (hw : w ∈ pathFromChainSkeleton b C H R (m + 1 : ℕ))
    (hyw : linearCombination (loopChainAlgebra B b R) (cellSectionPathChain (H := H) (R := R) γ)
        y - cubicalChainModuleDifferential (MoorePathFrom B b) H R w ∈
      pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1)) :
    ∃ u₀ ∈ cubicalChainModuleGrading (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R (i - 1),
      ∃ v₀ ∈ pathFromChainSkeleton b C H R (m + 1 : ℕ),
        linearCombination (loopChainAlgebra B b R) (cellSectionChain (H := H) (R := R) γ) y -
            cubicalChainModuleDifferential _ H R u₀ ∈
          cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
            {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) ∧
        cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom u₀ +
            cubicalChainModuleDifferential _ H R v₀ - w ∈
          pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1) := by
  classical
  have hdP := cubicalChainModuleDifferential_isHomogeneous
    (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R
  have hdN := cubicalChainModuleDifferential_isHomogeneous (MoorePathFrom B b) H R
  have hπ : LinearMap.IsHomogeneous (cubicalChainModuleLinearMap (G' := H) R
      (MoorePathPullback.toMoorePathFrom (f := sigmaCellMap C (m + 1)) (b := b)))
      (cubicalChainModuleGrading _ H R) (cubicalChainModuleGrading _ H R) 0 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
      rw [add_zero]
      exact cubicalChainModuleLinearMap_mem _ hx
  have hx := differential_linearCombination_sub_mem (H := H) γ hy
  rw [hdy, map_zero, sub_zero] at hx
  obtain ⟨u, v, hv, hu, huv⟩ := exists_add_differential_sub_mem_pathFromChainSkeleton (H := H)
    (n := m + 1) hx hw (by rwa [cubicalChainModuleLinearMap_linearCombination])
  have hΦy : linearCombination (loopChainAlgebra B b R) (cellSectionChain (H := H) (R := R) γ) y ∈
      cubicalChainModuleGrading _ H R i :=
    linearCombination_mem_of_mem_rowFiniteTotalGrading (ind := fun _ ↦ ((m + 1 : ℕ) : ℤ))
      (fun _ ↦ cubicalChainModuleLof_mem _) ((mem_rowFiniteTotalGrading_iff _ _).2 hy)
  -- Keep the components of `u` and `v` of the degrees of `y` and `w`.
  refine ⟨_, SetLike.coe_mem (DirectSum.decompose (cubicalChainModuleGrading _ H R) u (i - 1)),
    _, isHomogeneous_pathFromChainSkeleton b C H R _ (i - 1 - 1) hv, ?_, ?_⟩
  · have h := neg_mem (isHomogeneous_cubicalChainModuleSupportedIn _ i hu)
    rwa [DirectSum.decompose_sub, DirectSum.sub_apply, AddSubgroupClass.coe_sub,
      DirectSum.decompose_of_mem_same _ hΦy, ← sub_add_cancel i 1, ← hdP.map_decompose,
      neg_sub] at h
  · have h := isHomogeneous_pathFromChainSkeleton b C H R _ (i - 1) huv
    rwa [DirectSum.decompose_sub, DirectSum.decompose_add, DirectSum.sub_apply,
      DirectSum.add_apply, AddSubgroupClass.coe_sub, AddMemClass.coe_add,
      DirectSum.decompose_of_mem_same _ hwi, ← add_zero (i - 1), ← hπ.map_decompose (i - 1) u,
      add_zero, ← sub_add_cancel (i - 1) 1, ← hdN.map_decompose (i - 1 - 1) v, sub_add_cancel] at h

/-- The quasi-isomorphism of
`TauCeti.exists_mapRange_eq_and_linearCombination_cellSectionPathChain_add_sub_mem`, for a relative
cycle `(y, w)` of a single degree. -/
private theorem exists_mapRange_eq_and_add_sub_mem_of_homogeneous {i : ℤ}
    {y : cell C (m + 1) →₀ loopChainAlgebra B b R}
    (hy : ∀ j, y j ∈ cubicalChainGrading (MooreLoopSpace B b) R (i + (m + 1 : ℕ)))
    (hdy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    {w : cubicalChainModule (MoorePathFrom B b) H R}
    (hwi : w ∈ cubicalChainModuleGrading _ H R (i - 1))
    (hw : w ∈ pathFromChainSkeleton b C H R (m + 1 : ℕ))
    (hyw : linearCombination (loopChainAlgebra B b R) (cellSectionPathChain (H := H) (R := R) γ)
        y - cubicalChainModuleDifferential (MoorePathFrom B b) H R w ∈
      pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1)) :
    ∃ (y' : cell C (m + 1) →₀ loopChainAlgebra B b R)
      (w' : cubicalChainModule (MoorePathFrom B b) H R),
      w' ∈ pathFromChainSkeleton b C H R (m + 1 : ℕ) ∧
        mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y ∧
          linearCombination (loopChainAlgebra B b R) (cellSectionPathChain (H := H) (R := R) γ)
              y' + cubicalChainModuleDifferential (MoorePathFrom B b) H R w' - w ∈
            pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1) := by
  obtain ⟨u₀, hu₀i, v₀, hv₀, hu₀, huv₀⟩ :=
    exists_differential_sub_mem_of_homogeneous γ hy hdy hwi hw hyw
  -- `y` is a boundary `d y'`, and `u₀ - Φ y'` is a relative cycle.
  obtain ⟨y', hy'i, hy'⟩ :=
    exists_mapRange_eq_of_linearCombination_sub_differential_mem γ hy hdy hu₀i hu₀
  have hr : cubicalChainModuleDifferential _ H R
      (u₀ - linearCombination (loopChainAlgebra B b R) (cellSectionChain (H := H) (R := R) γ) y') ∈
        cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
          {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
    have h := add_mem (differential_linearCombination_sub_mem (H := H) γ hy'i) hu₀
    rw [hy'] at h
    convert neg_mem h using 1
    rw [map_sub]
    abel
  -- That relative cycle is the action of a cycle `z`, up to a relative boundary `d u''`.
  obtain ⟨z, u'', hz, hzu⟩ := exists_sub_linearCombination_sub_differential_mem γ
    (sub_mem hu₀i (linearCombination_mem_of_mem_rowFiniteTotalGrading
      (ind := fun _ ↦ ((m + 1 : ℕ) : ℤ)) (fun _ ↦ cubicalChainModuleLof_mem _)
        ((mem_rowFiniteTotalGrading_iff _ _).2 hy'i))) hr
  refine ⟨y' + z, cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom u'' +
    v₀, add_mem (cubicalChainModuleLinearMap_mem_pathFromChainSkeleton_succ _) hv₀,
    by rw [map_add, hy', hz, add_zero], ?_⟩
  have key : linearCombination (loopChainAlgebra B b R) (cellSectionPathChain (H := H) (R := R) γ)
        (y' + z) + cubicalChainModuleDifferential (MoorePathFrom B b) H R
          (cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom u'' + v₀) -
            w =
      (cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom u₀ +
        cubicalChainModuleDifferential _ H R v₀ - w) -
      cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom
        (u₀ - linearCombination (loopChainAlgebra B b R) (cellSectionChain (H := H) (R := R) γ) y' -
          linearCombination (loopChainAlgebra B b R) (cellSectionChain (H := H) (R := R) γ) z -
          cubicalChainModuleDifferential _ H R u'') := by
    rw [map_add, map_add, cubicalChainModuleDifferential_linearMap,
      ← cubicalChainModuleLinearMap_linearCombination,
      ← cubicalChainModuleLinearMap_linearCombination]
    simp only [map_sub]
    abel
  rw [key]
  exact sub_mem huv₀ (cubicalChainModuleLinearMap_mem_pathFromChainSkeleton_of_mem hzu)

/-- **The free module on the `(m + 1)`-cells is quasi-isomorphic to the `(m + 1)`-th quotient of
the skeletal filtration of the chains on the based path space.** Choose a Moore path from `b` to
the centre of each `(m + 1)`-cell, and send the free generator of the cell `j` to the chain `cⱼ` of
the radial paths to the points of its disk (`TauCeti.cellSectionPathChain`). Every relative cycle
`(y, w)` of the resulting map `(α_j)_j ↦ ∑_j α_j · cⱼ`, with `w` over the `(m + 1)`-skeleton, is a
relative boundary `(d y', ∑_j y'_j · cⱼ + d w')` with `w'` over the `(m + 1)`-skeleton, modulo the
chains over the `m`-skeleton.

This is the hypothesis on the new generators in
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists` for the `(m + 1)`-cells, with
the stages `m` and `m + 1` of `TauCeti.pathFromChainSkeleton`. For the zero-cells it is
`exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton`. -/
theorem exists_mapRange_eq_and_linearCombination_cellSectionPathChain_add_sub_mem
    (y : cell C (m + 1) →₀ loopChainAlgebra B b R) (w : cubicalChainModule (MoorePathFrom B b) H R)
    (hy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    (hw : w ∈ pathFromChainSkeleton b C H R (m + 1 : ℕ))
    (hyw : linearCombination (loopChainAlgebra B b R) (cellSectionPathChain (H := H) (R := R) γ)
        y - cubicalChainModuleDifferential (MoorePathFrom B b) H R w ∈
      pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1)) :
    ∃ (y' : cell C (m + 1) →₀ loopChainAlgebra B b R)
      (w' : cubicalChainModule (MoorePathFrom B b) H R),
      w' ∈ pathFromChainSkeleton b C H R (m + 1 : ℕ) ∧
        mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y ∧
          linearCombination (loopChainAlgebra B b R) (cellSectionPathChain (H := H) (R := R) γ)
              y' + cubicalChainModuleDifferential (MoorePathFrom B b) H R w' - w ∈
            pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1) := by
  -- Split the relative cycle into homogeneous pieces, and treat each one.
  obtain ⟨y', w', hw', hy', hyw'⟩ := exists_relative_boundary_of_forall_homogeneous
    (𝒢 := rowFiniteTotalGrading (cubicalChainGrading (MooreLoopSpace B b) R)
      fun _ : cell C (m + 1) ↦ ((m + 1 : ℕ) : ℤ))
    (Φ := (linearCombination (loopChainAlgebra B b R)
      (cellSectionPathChain (H := H) (R := R) γ)).restrictScalars R)
    (A := ⊥) (S := (pathFromChainSkeleton b C H R (((m + 1 : ℕ) : ℤ) - 1)).restrictScalars R)
    (T := (pathFromChainSkeleton b C H R (m + 1 : ℕ)).restrictScalars R)
    (dM := mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R))
    (dN := cubicalChainModuleDifferential (MoorePathFrom B b) H R)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hy ↦ (mem_rowFiniteTotalGrading_iff _ _).2 fun j ↦ by
      rw [mapRange.linearMap_apply, mapRange_apply, add_right_comm]
      exact cubicalChainDifferential_mem _ _ ((mem_rowFiniteTotalGrading_iff _ _).1 hy j))
    (cubicalChainModuleDifferential_isHomogeneous _ H R)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hy ↦
      (isHomogeneous_linearCombination (A := loopChainAlgebra B b R)
        (cellSectionPathChain_mem_cubicalChainModuleGrading γ)).map_mem hy)
    (fun _ _ hx ↦ by
      rw [Submodule.mem_bot] at hx ⊢
      rw [hx, DirectSum.decompose_zero, DFinsupp.zero_apply, ZeroMemClass.coe_zero])
    (isHomogeneous_pathFromChainSkeleton b C H R _)
    (isHomogeneous_pathFromChainSkeleton b C H R _)
    (fun i y hy w hw hdy hwT hyw ↦ by
      obtain ⟨y', w', hw', hy', hyw'⟩ := exists_mapRange_eq_and_add_sub_mem_of_homogeneous γ
        ((mem_rowFiniteTotalGrading_iff _ _).1 hy) ((Submodule.mem_bot R).1 hdy) hw hwT hyw
      exact ⟨y', w', hw', (Submodule.mem_bot R).2 (sub_eq_zero.2 hy'), hyw'⟩)
    ((Submodule.mem_bot R).2 hy) hw hyw
  exact ⟨y', w', hw', sub_eq_zero.1 ((Submodule.mem_bot R).1 hy'), hyw'⟩

end Model

end TauCeti

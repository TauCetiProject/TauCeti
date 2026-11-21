/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Cell
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Excision
import TauCeti.Algebra.Module.GradedModule.Internal
import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Relative.Basic

/-!
# The stages of positive dimension of Brown's model of the based path chains

Let `C ⊆ B` be a relative CW complex and `b ∈ B`. Brown's semi-free model of the chains
`C_*(P_b B; R)` on the based Moore path space, over the chains `C_*(Ω_b B; R)` on the Moore loops,
is built along the filtration of `C_*(P_b B; R)` by the chains over the skeleta
(`TauCeti.pathFromChainSkeleton`), with one free generator for each cell. The zero-cells are
treated in `TauCeti.AlgebraicTopology.DGLocalSystem.Path.ZeroCell`. This file treats the cells of
every positive dimension `m + 1`: it supplies the hypothesis on the new generators in the cell
attachment step `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, with the stages
`m` and `m + 1` of the filtration.

Choose a Moore path `γ j` from `b` to the centre of each `(m + 1)`-cell `j`. Let `P` be the pullback
of the based path fibration to the disks of the `(m + 1)`-cells and `∂P` its part over the boundary
spheres. The radial paths after `γ j` give the section cube of `j`
(`TauCeti.cellSectionCube`), a singular `(m + 1)`-cube of `P`; as a chain it is the **section
chain** `cⱼ` (`TauCeti.cellSectionChain`), a relative cycle of `(P, ∂P)`
(`TauCeti.cubicalChainModuleDifferential_cellSectionChain_mem_cubicalChainModuleSupportedIn`). The
free generator of `j` goes to the image `c₀ j` of `cⱼ` in `C_*(P_b B; R)`, which has dimension
`m + 1`, lies over the `(m + 1)`-skeleton and has boundary over the `m`-skeleton.

The main result is that the map `(y_j)_j ↦ ∑_j y_j · c₀ j` from the free module on the
`(m + 1)`-cells is a quasi-isomorphism onto the chains over the `(m + 1)`-skeleton modulo those over
the `m`-skeleton, written as in `TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`:
every relative cycle is a relative boundary
(`exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton_succ`).
It is the composite of two quasi-isomorphisms.

* The map `(y_j)_j ↦ ∑_j y_j · cⱼ` into the relative chains of `(P, ∂P)`
  (`TauCeti.exists_mapRange_eq_and_linearCombination_cellSectionChain_add_differential_sub_mem`).
  This is the chain-level form of `TauCeti.cellPathPullbackHomologyEquiv`, which identifies
  `⨁ⱼ H_q(Ω_b B)` with `H_{q+m+1}(P, ∂P)` through the section cubes, together with the vanishing of
  `Hⱼ(P, ∂P)` for `j ≤ m` (`TauCeti.isZero_cubicalHomology_cellPathPullbackPair_of_lt`). Relative
  classes are read on chains through `TopPair.IsCubicalRepresentative`, and the statement for all
  chains follows from the homogeneous ones
  (`TauCeti.exists_relative_boundary_of_forall_homogeneous`).
* The push-forward from `(P, ∂P)` onto the quotient of the stage `m + 1` of the skeletal filtration
  by the stage `m` (`TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`).

## Main definitions

* `TauCeti.cellSectionChain H R γ j`: the section chain of the `(m + 1)`-cell `j`, in `C_*(P; R)`.

## Main results

* `TauCeti.exists_mapRange_eq_and_linearCombination_cellSectionChain_add_differential_sub_mem`:
  the free module on the `(m + 1)`-cells is quasi-isomorphic to the relative chains of `(P, ∂P)`.
* `TauCeti.cubicalChainModuleLinearMap_cellSectionChain_mem_cubicalChainModuleGrading`,
  `TauCeti.cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton_succ`,
  `cubicalChainModuleDifferential_toMoorePathFrom_cellSectionChain_mem_pathFromChainSkeleton`:
  the image of a section chain in `C_*(P_b B; R)` has dimension `m + 1`, lies over the
  `(m + 1)`-skeleton and has boundary over the `m`-skeleton.
* `exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton_succ`:
  the free module on the `(m + 1)`-cells is quasi-isomorphic to the chains over the
  `(m + 1)`-skeleton modulo those over the `m`-skeleton.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex Finsupp CategoryTheory HomologicalComplex

namespace TauCeti

variable {B : Type} [TopologicalSpace B] {b : B} {C D : Set B} [RelCWComplex C D] {m : ℕ}
  {H : Type*} {R : Type} [CommRing R]
  (γ : ∀ j : cell C (m + 1), MoorePathBetween B b (map (m + 1) j 0))

variable (H R) in
/-- The **section chain** of the `(m + 1)`-cell `j`: the section cube `TauCeti.cellSectionCube`
of `j`, as a chain of dimension `m + 1` on the pullback `P` of the based Moore path fibration
`P_b B → B` to the disks of the `(m + 1)`-cells. -/
def cellSectionChain (j : cell C (m + 1)) :
    cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R :=
  cubicalChainModuleLof _ H R (m + 1)
    (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j))

/-- The section chain of a cell is the chain of its section cube. -/
theorem cellSectionChain_def (j : cell C (m + 1)) :
    cellSectionChain H R γ j = cubicalChainModuleLof _ H R (m + 1)
      (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)) :=
  (rfl)

/-- The section chain of a cell has dimension `m + 1`. -/
theorem cellSectionChain_mem_cubicalChainModuleGrading (j : cell C (m + 1)) :
    cellSectionChain H R γ j ∈
      cubicalChainModuleGrading (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R
        (-((m : ℤ) + 1)) :=
  mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨m + 1, _, by push_cast; ring, rfl⟩)

/-- The section cube of a cell sends the boundary of the cube over the boundary sphere. -/
private theorem mapsTo_cellSectionCube (j : cell C (m + 1)) :
    MapsTo (cellSectionCube C (m + 1) γ j) (Cube.boundary (Fin (m + 1)))
      (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := fun d hd ↦ by
  simpa [point_cellSectionCube, norm_cubeHomeomorphClosedBall_eq_one_iff] using hd

/-- **The section chain of a cell is a relative cycle**: its boundary lies over the boundary
sphere. -/
theorem cubicalChainModuleDifferential_cellSectionChain_mem_cubicalChainModuleSupportedIn
    (j : cell C (m + 1)) :
    cubicalChainModuleDifferential _ H R (cellSectionChain H R γ j) ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  rw [cellSectionChain_def, cubicalChainModuleDifferential_lof_succ,
    cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff,
    NormalizedCubicalChain.boundary_ofCube]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
    refine NormalizedCubicalChain.ofCube_mem_supportedIn R ?_ <;>
    rintro _ ⟨y, rfl⟩ <;>
    rw [SingularCube.face_apply] <;>
    exact mapsTo_cellSectionCube γ j ⟨i, by simp⟩

/-! ### Relative chains of the pullback over the cells -/

/-- **Relative cycles of the pullback over the cells are relative boundaries modulo the section
cubes.** For a relative cycle `x` of dimension `p + m + 1` of the pullback `P` over the disks of
the `(m + 1)`-cells, relative to its part over the boundary spheres, there are finitely many cells
`j` and `p`-cycles `zⱼ` of the Moore loops at `b` such that `x - ∑ⱼ zⱼ · cⱼ` is a relative
boundary, with `cⱼ` the section cubes. This is surjectivity of
`TauCeti.cellPathPullbackHomologyEquiv`, on chains. -/
private theorem exists_sub_sum_leftAct_sub_boundary_mem (p : ℕ)
    (x : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R (p + (m + 1)))
    (hx : NormalizedCubicalChain.boundary _ R (p + m) x ∈ NormalizedCubicalChain.supportedIn R
      (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) (p + m)) :
    ∃ (s : Finset (cell C (m + 1)))
      (z : cell C (m + 1) →
        ((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace B b))).cycles p)
      (v : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R
        (p + (m + 1) + 1)),
      x - ∑ j ∈ s, NormalizedCubicalChain.leftAct (MooreLoopSpace B b) _ R p (m + 1)
          (normalizedCubicalChainComplexXEquiv _ p
            (((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace B b))).iCycles p
              (z j)))
          (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)) -
        NormalizedCubicalChain.boundary _ R (p + (m + 1)) v ∈
        NormalizedCubicalChain.supportedIn R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
          {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) (p + (m + 1)) := by
  classical
  obtain ⟨μ, hμ⟩ :=
    (cellPathPullbackPair b C (m + 1)).exists_isCubicalRepresentative_of_boundary_mem
      R (n := p + m) x (by rw [range_cellPathPullbackPair_map]; exact hx)
  choose z hz using fun j ↦
    HomologicalComplex.moduleCat_homologyπ_surjective
      ((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace B b))) p
      ((cellPathPullbackHomologyEquiv γ R p).symm μ j)
  refine ⟨((cellPathPullbackHomologyEquiv γ R p).symm μ).support, z, ?_⟩
  -- The sum of the `zⱼ · cⱼ` represents `μ`, so `x` minus it represents zero.
  have hsum := TopPair.IsCubicalRepresentative.sum
    ((cellPathPullbackHomologyEquiv γ R p).symm μ).support fun j _ ↦
      isCubicalRepresentative_cellPathPullbackHomologyEquiv γ R p j (z j)
  simp only [hz, DirectSum.lof_eq_of, ← map_sum, DirectSum.sum_support_of,
    LinearEquiv.apply_symm_apply] at hsum
  obtain ⟨v, hv⟩ := ((cellPathPullbackPair b C (m + 1)).isCubicalRepresentative_zero_iff R _).1
    (by simpa using hμ.sub hsum)
  exact ⟨v, by rwa [range_cellPathPullbackPair_map] at hv⟩

/-- **The section cubes are independent on relative homology.** If `∑ⱼ zⱼ · cⱼ`, for finitely many
`(m + 1)`-cells `j` and `q`-cycles `zⱼ` of the Moore loops at `b`, is a relative boundary of the
pullback over the cells, then every `zⱼ` is a boundary. This is injectivity of
`TauCeti.cellPathPullbackHomologyEquiv`, on chains. -/
private theorem homologyπ_eq_zero_of_sum_leftAct_sub_boundary_mem (q : ℕ)
    (s : Finset (cell C (m + 1)))
    (z : cell C (m + 1) →
      ((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace B b))).cycles q)
    (v : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R
      (q + (m + 1) + 1))
    (h : ∑ j ∈ s, NormalizedCubicalChain.leftAct (MooreLoopSpace B b) _ R q (m + 1)
          (normalizedCubicalChainComplexXEquiv _ q
            (((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace B b))).iCycles q
              (z j)))
          (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j)) -
        NormalizedCubicalChain.boundary _ R (q + (m + 1)) v ∈
        NormalizedCubicalChain.supportedIn R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
          {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) (q + (m + 1)))
    {j : cell C (m + 1)} (hj : j ∈ s) :
    ((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace B b))).homologyπ q (z j) =
      0 := by
  classical
  have h₀ := ((cellPathPullbackPair b C (m + 1)).isCubicalRepresentative_zero_iff R _).2
    ⟨v, by rw [range_cellPathPullbackPair_map]; exact h⟩
  have hsum := TopPair.IsCubicalRepresentative.sum s fun j _ ↦
    isCubicalRepresentative_cellPathPullbackHomologyEquiv γ R q j (z j)
  have hz := hsum.unique h₀
  rw [← map_sum, LinearEquiv.map_eq_zero_iff] at hz
  have hzj := congrArg (fun x ↦ x j) hz
  simpa [DirectSum.lof_eq_of, DirectSum.sum_apply, DirectSum.of_apply, hj] using hzj

/-! ### The free module on the cells and the relative chains of the pullback -/

/-- The loops act on the pullback over the disks of the cells without moving the points of the
disks, so they preserve the part over the boundary spheres. -/
private theorem smul_mem_cellBoundary (ω : MooreLoopSpace B b)
    (x : MoorePathPullback (sigmaCellMap C (m + 1)) b)
    (hx : x ∈ MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
      {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) :
    ω • x ∈ MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
      {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1} := by
  simpa using hx

/-- **Acting on the section chains commutes with the differentials, up to chains over the boundary
spheres.** -/
private theorem differential_linearCombination_sub_mem
    (y : cell C (m + 1) →₀ loopChainAlgebra B b R) :
    cubicalChainModuleDifferential _ H R
        (linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) y) -
      linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ)
        (mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y) ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' =>
    convert add_mem hy hy' using 1
    simp only [map_add]
    abel
  | single j a =>
    simp only [mapRange.linearMap_apply, mapRange_single, linearCombination_single]
    induction a using DirectSum.induction_on with
    | zero => simp
    | of n a =>
      rw [← DirectSum.lof_eq_of R, cellSectionChain_def, cubicalChainModuleDifferential_lof_smul,
        add_sub_cancel_left]
      refine Submodule.smul_of_tower_mem _ _ (smul_mem_cubicalChainModuleSupportedIn
        smul_mem_cellBoundary _ ?_)
      exact cubicalChainModuleDifferential_cellSectionChain_mem_cubicalChainModuleSupportedIn γ j
    | add a a' ha ha' =>
      convert add_mem ha ha' using 1
      simp only [map_add, add_smul]
      abel

include γ in
/-- **Below the dimension of the cells, relative cycles of the pullback are relative
boundaries.** -/
private theorem exists_differential_sub_mem_of_lt {i : ℤ} (hi : -((m : ℤ) + 1) < i)
    {x : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R}
    (hxi : x ∈ cubicalChainModuleGrading _ H R i)
    (hx : cubicalChainModuleDifferential _ H R x ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    ∃ v, cubicalChainModuleDifferential _ H R v - x ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  rcases mem_cubicalChainModuleGrading_iff.1 hxi with rfl | ⟨e, x, he, rfl⟩
  · exact ⟨0, by simp⟩
  -- The relative homology vanishes in dimension `e < m + 1`, so the class of `x` is zero.
  obtain ⟨μ, hμ⟩ : ∃ μ, (cellPathPullbackPair b C (m + 1)).IsCubicalRepresentative R x μ := by
    cases e with
    | zero =>
      exact (cellPathPullbackPair b C (m + 1)).exists_isCubicalRepresentative_of_dim_zero R x
    | succ e =>
      rw [cubicalChainModuleDifferential_lof_succ,
        cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff] at hx
      exact (cellPathPullbackPair b C (m + 1)).exists_isCubicalRepresentative_of_boundary_mem R x
        (by rw [range_cellPathPullbackPair_map]; exact hx)
  obtain rfl : μ = 0 := (ModuleCat.isZero_iff_subsingleton.1
    (isZero_cubicalHomology_cellPathPullbackPair_of_lt γ R (j := e) (by omega))).elim _ _
  obtain ⟨v, hv⟩ : ∃ v : NormalizedCubicalChain (MoorePathPullback (sigmaCellMap C (m + 1)) b) R
      (e + 1), x - NormalizedCubicalChain.boundary _ R e v ∈ NormalizedCubicalChain.supportedIn R
        (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
          {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) e := by
    rw [← range_cellPathPullbackPair_map]
    exact ((cellPathPullbackPair b C (m + 1)).isCubicalRepresentative_zero_iff R x).1 hμ
  refine ⟨cubicalChainModuleLof _ H R (e + 1) v, ?_⟩
  rw [cubicalChainModuleDifferential_lof_succ, ← map_sub,
    cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff, ← neg_sub]
  exact neg_mem hv

/-- **Relative cycles of the pullback of dimension `p + m + 1` come from the free module on the
cells**, up to relative boundaries. -/
private theorem exists_linearCombination_add_differential_sub_mem (p : ℕ)
    {x : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R}
    (hxi : x ∈ cubicalChainModuleGrading _ H R (-((p : ℤ) + (m + 1))))
    (hx : cubicalChainModuleDifferential _ H R x ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    ∃ (z : cell C (m + 1) →₀ loopChainAlgebra B b R)
      (v : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R),
      mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) z = 0 ∧
        linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) z +
            cubicalChainModuleDifferential _ H R v - x ∈
          cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
            {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  classical
  obtain ⟨x, rfl⟩ := exists_cubicalChainModuleLof_eq hxi (p + (m + 1)) (by push_cast; ring)
  -- `p + (m + 1)` is `p + m + 1` by definition, which exhibits `x` as a chain of a successor
  -- dimension
  replace hx : NormalizedCubicalChain.boundary _ R (p + m) x ∈ NormalizedCubicalChain.supportedIn R
      (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) (p + m) := by
    rw [← cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff (H := H),
      ← cubicalChainModuleDifferential_lof_succ]
    exact hx
  obtain ⟨s, z, v, hv⟩ := exists_sub_sum_leftAct_sub_boundary_mem γ p x hx
  refine ⟨∑ j ∈ s, single j (cubicalChainLof (MooreLoopSpace B b) R p
      (normalizedCubicalChainComplexXEquiv _ p
        (((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace B b))).iCycles p
          (z j)))),
    cubicalChainModuleLof _ H R _ v, ?_, ?_⟩
  · simp only [map_sum, mapRange.linearMap_apply, mapRange_single]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [cubicalChainDifferential_lof_iCycles, single_zero]
  · simp only [map_sum, linearCombination_single, cellSectionChain_def,
      lof_smul_cubicalChainModuleLof]
    rw [← map_sum, cubicalChainModuleDifferential_lof_succ, ← map_add, ← map_sub,
      cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff]
    convert neg_mem hv using 1
    abel

/-- **The free module on the cells injects into the relative homology of the pullback.** If the
image of a cycle `y` of degree `q` is a relative boundary, then `y` is a boundary. -/
private theorem exists_mapRange_eq_of_linearCombination_sub_differential_mem (q : ℕ) {n : ℤ}
    (hn : n + ((m : ℤ) + 1) = -q) {y : cell C (m + 1) →₀ loopChainAlgebra B b R}
    (hyi : y ∈ rowFiniteTotalGrading (cubicalChainGrading (MooreLoopSpace B b) R)
      (fun _ ↦ (m : ℤ) + 1) n)
    (hy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    {w : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R}
    (hwi : w ∈ cubicalChainModuleGrading _ H R (n - 1))
    (hyw : linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) y -
        cubicalChainModuleDifferential _ H R w ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    ∃ y' : cell C (m + 1) →₀ loopChainAlgebra B b R,
      y' ∈ rowFiniteTotalGrading (cubicalChainGrading (MooreLoopSpace B b) R)
        (fun _ ↦ (m : ℤ) + 1) (n - 1) ∧
      mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y := by
  classical
  -- The coefficients of `y` are cycles of dimension `q`.
  choose z hz using fun j ↦ exists_iCycles_eq_of_mem_cubicalChainGrading q
    (by simpa [hn] using (mem_rowFiniteTotalGrading_iff _ _).1 hyi j)
    (by simpa using DFunLike.congr_fun hy j)
  -- The relative boundary `∑ⱼ zⱼ · cⱼ - ∂w`, on chains.
  obtain ⟨w, rfl⟩ := exists_cubicalChainModuleLof_eq hwi (q + (m + 1) + 1) (by push_cast; omega)
  have hsum : linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) y =
      cubicalChainModuleLof _ H R _ (∑ j ∈ y.support,
        NormalizedCubicalChain.leftAct (MooreLoopSpace B b) _ R q (m + 1)
          (normalizedCubicalChainComplexXEquiv _ q
            (((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace B b))).iCycles q
              (z j)))
          (NormalizedCubicalChain.ofCube _ R (cellSectionCube C (m + 1) γ j))) := by
    rw [linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hz j, cellSectionChain_def, lof_smul_cubicalChainModuleLof]
  rw [hsum, cubicalChainModuleDifferential_lof_succ, ← map_sub,
    cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff] at hyw
  -- Each `zⱼ` is a boundary.
  have hb (j : cell C (m + 1)) (hj : j ∈ y.support) :
      ∃ c : NormalizedCubicalChain (MooreLoopSpace B b) R (q + 1),
        cubicalChainDifferential _ R (cubicalChainLof (MooreLoopSpace B b) R (q + 1) c) = y j := by
    obtain ⟨c, hc⟩ := (HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _ (m := q + 1)
      (by simp) (z j)).1
        (homologyπ_eq_zero_of_sum_leftAct_sub_boundary_mem γ q y.support z w hyw hj)
    refine ⟨normalizedCubicalChainComplexXEquiv _ (q + 1) c, ?_⟩
    rw [cubicalChainDifferential_lof_succ, ← hz j, ← hc, moduleCat_iCycles_toCycles_apply,
      normalizedCubicalChainComplexXEquiv_d_apply]
  choose! c hc using hb
  refine ⟨∑ j ∈ y.support, single j (cubicalChainLof (MooreLoopSpace B b) R (q + 1) (c j)), ?_, ?_⟩
  · refine (mem_rowFiniteTotalGrading_iff _ _).2 fun j ↦ ?_
    simp only [Finset.sum_apply', single_apply, Finset.sum_ite_eq']
    split_ifs
    · exact (mem_cubicalChainGrading_iff _ R).2 (Or.inr ⟨q + 1, c j, by push_cast; omega, rfl⟩)
    · exact zero_mem _
  · refine Finsupp.ext fun j ↦ ?_
    simp only [map_sum, mapRange.linearMap_apply, mapRange_single, Finset.sum_apply',
      single_apply, Finset.sum_ite_eq']
    split_ifs with hj
    · exact hc j hj
    · exact (notMem_support_iff.1 hj).symm

/-- **Homogeneous relative cycles of the map from the free module on the cells are relative
boundaries.** This is the comparison of the free module on the `(m + 1)`-cells with the relative
chains of the pullback, for homogeneous pairs `(y, u)` of degrees `i` and `i - 1`. -/
private theorem exists_mapRange_eq_and_add_differential_sub_mem_of_mem (i : ℤ)
    {y : cell C (m + 1) →₀ loopChainAlgebra B b R}
    (hyi : y ∈ rowFiniteTotalGrading (cubicalChainGrading (MooreLoopSpace B b) R)
      (fun _ ↦ (m : ℤ) + 1) i)
    {u : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R}
    (hui : u ∈ cubicalChainModuleGrading _ H R (i - 1))
    (hy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    (hyu : linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) y -
        cubicalChainModuleDifferential _ H R u ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    ∃ (y' : cell C (m + 1) →₀ loopChainAlgebra B b R)
      (u' : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R),
      mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y ∧
        linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) y' +
            cubicalChainModuleDifferential _ H R u' - u ∈
          cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
            {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  rcases le_or_gt (i + ((m : ℤ) + 1)) 0 with h | h
  · -- The coefficients of `y` are cycles of dimension `q`, hence boundaries of some `y''`, and
    -- `u` minus the image of `y''` is a relative cycle of dimension `q + 1 + (m + 1)`.
    obtain ⟨q, hq⟩ : ∃ q : ℕ, i + ((m : ℤ) + 1) = -q := ⟨(-(i + ((m : ℤ) + 1))).toNat, by omega⟩
    obtain ⟨y'', hy''i, hy''⟩ :=
      exists_mapRange_eq_of_linearCombination_sub_differential_mem γ q hq hyi hy hui hyu
    have hdeg : i - 1 = -(((q + 1 : ℕ) : ℤ) + ((m : ℤ) + 1)) := by push_cast; omega
    have h₁ := differential_linearCombination_sub_mem (H := H) γ y''
    rw [hy''] at h₁
    obtain ⟨z, v, hz, hzv⟩ := exists_linearCombination_add_differential_sub_mem γ (q + 1)
      (x := u - linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) y'')
      (hdeg ▸ sub_mem hui (linearCombination_mem_of_mem_rowFiniteTotalGrading
        (cellSectionChain_mem_cubicalChainModuleGrading γ) hy''i))
      (by convert neg_mem (add_mem hyu h₁) using 1; rw [map_sub]; abel)
    refine ⟨y'' + z, v, by rw [map_add, hz, add_zero, hy''], ?_⟩
    convert hzv using 1
    rw [map_add]
    abel
  · -- The coefficients of `y` would have negative dimension, so `y = 0` and `u` is a relative
    -- cycle of dimension at most `m + 1`.
    obtain rfl : y = 0 := Finsupp.ext fun j ↦ by
      rcases (mem_cubicalChainGrading_iff _ R).1 ((mem_rowFiniteTotalGrading_iff _ _).1 hyi j)
        with h' | ⟨n, _, hn, _⟩
      · exact h'
      · omega
    rw [map_zero, zero_sub, neg_mem_iff] at hyu
    rcases eq_or_lt_of_le (show -(m : ℤ) ≤ i by omega) with rfl | hi
    · exact exists_linearCombination_add_differential_sub_mem γ 0
        (by convert hui using 2; push_cast; ring) hyu
    · obtain ⟨v, hv⟩ := exists_differential_sub_mem_of_lt γ (i := i - 1) (by omega) hui hyu
      exact ⟨0, v, map_zero _, by simpa using hv⟩

/-- **The free module on the `(m + 1)`-cells is quasi-isomorphic to the relative chains of the
pullback over the cells.** Let `P` be the pullback of the based Moore path fibration `P_b B → B` to
the disks of the `(m + 1)`-cells and `∂P` its part over the boundary spheres, and send the free
generator of each cell `j`, a free module over `C_*(Ω_b B; R)`, to its section chain `cⱼ`
(`TauCeti.cellSectionChain`). Every relative cycle `(y, u)` of the resulting map, with `y` a cycle
and `∑ⱼ yⱼ · cⱼ - ∂u` a chain over `∂P`, is a relative boundary `(d y', ∑ⱼ y'ⱼ · cⱼ + ∂u')`
modulo the chains over `∂P`.

This is the chain-level form of `TauCeti.cellPathPullbackHomologyEquiv`, together with the
vanishing of the relative homology of `(P, ∂P)` below degree `m + 1`
(`TauCeti.isZero_cubicalHomology_cellPathPullbackPair_of_lt`). -/
theorem exists_mapRange_eq_and_linearCombination_cellSectionChain_add_differential_sub_mem
    (y : cell C (m + 1) →₀ loopChainAlgebra B b R)
    (u : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R)
    (hy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    (hyu : linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) y -
        cubicalChainModuleDifferential _ H R u ∈
      cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    ∃ (y' : cell C (m + 1) →₀ loopChainAlgebra B b R)
      (u' : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R),
      mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y ∧
        linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) y' +
            cubicalChainModuleDifferential _ H R u' - u ∈
          cubicalChainModuleSupportedIn H R (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
            {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1}) := by
  obtain ⟨y', u', -, hy', hu'⟩ := exists_relative_boundary_of_forall_homogeneous
    (𝒢 := rowFiniteTotalGrading (cubicalChainGrading (MooreLoopSpace B b) R)
      (fun _ : cell C (m + 1) ↦ (m : ℤ) + 1))
    (𝒩 := cubicalChainModuleGrading _ H R)
    (dM := mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R))
    (dN := cubicalChainModuleDifferential _ H R)
    (Φ := (linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ)).restrictScalars R)
    (A := ⊥) (T := ⊤)
    (LinearMap.isHomogeneous_def.mpr fun i y hy ↦ (mem_rowFiniteTotalGrading_iff _ _).2 fun j ↦ by
      rw [mapRange.linearMap_apply, mapRange_apply,
        show i + 1 + ((m : ℤ) + 1) = i + ((m : ℤ) + 1) + 1 by ring]
      exact cubicalChainDifferential_mem _ R ((mem_rowFiniteTotalGrading_iff _ _).1 hy j))
    (cubicalChainModuleDifferential_isHomogeneous _ H R)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦
      (isHomogeneous_linearCombination (A := loopChainAlgebra B b R)
        (cellSectionChain_mem_cubicalChainModuleGrading γ)).map_mem hx)
    (fun _ _ hx ↦ by rw [Submodule.mem_bot] at hx ⊢; simp [hx])
    (isHomogeneous_cubicalChainModuleSupportedIn _) (fun _ _ _ ↦ Submodule.mem_top)
    (fun i y hyi u hui hy _ hyu ↦ by
      obtain ⟨y', u', hy', hu'⟩ := exists_mapRange_eq_and_add_differential_sub_mem_of_mem γ i hyi
        hui ((Submodule.mem_bot R).1 hy) hyu
      exact ⟨y', u', Submodule.mem_top, by rw [hy', sub_self]; exact zero_mem _, hu'⟩)
    (x := y) (y := u) (by rw [hy]; exact zero_mem _) Submodule.mem_top hyu
  exact ⟨y', u', sub_eq_zero.1 ((Submodule.mem_bot R).1 hy'), hu'⟩

/-! ### The section chains in the skeletal filtration of the based path space -/

/-- The image of the section chain of a cell in `C_*(P_b B; R)` has dimension `m + 1`. -/
theorem cubicalChainModuleLinearMap_cellSectionChain_mem_cubicalChainModuleGrading
    (j : cell C (m + 1)) :
    cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom (cellSectionChain H R γ j) ∈
      cubicalChainModuleGrading (MoorePathFrom B b) H R (-((m : ℤ) + 1)) :=
  cubicalChainModuleLinearMap_mem _ (cellSectionChain_mem_cubicalChainModuleGrading γ j)

section Skeleton

variable [T2Space B]

/-- **Chains on the pullback over the `(m + 1)`-cells lie over the `(m + 1)`-skeleton**: their
images in `C_*(P_b B; R)` lie in the stage `m + 1` of the skeletal filtration. -/
theorem cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton_succ
    (x : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R) :
    cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom x ∈
      pathFromChainSkeleton b C H R ((m : ℤ) + 1) := by
  refine cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton (S := univ)
    (fun d _ ↦ ?_)
    (by rw [preimage_univ, cubicalChainModuleSupportedIn_univ]; exact Submodule.mem_top)
  rw [show (((m : ℤ) + 1 + 1).toNat : ℕ∞) = ((m + 1 + 1 : ℕ) : ℕ∞) by congr 1, sigmaCellMap_apply]
  exact map_mem_skeletonLT_succ d.1 (mem_closedBall_zero_iff.1 d.2.property)

/-- **Chains over the boundary spheres of the `(m + 1)`-cells lie over the `m`-skeleton**: their
images in `C_*(P_b B; R)` lie in the stage `m` of the skeletal filtration. -/
theorem cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton_of_mem
    {x : cubicalChainModule (MoorePathPullback (sigmaCellMap C (m + 1)) b) H R}
    (hx : x ∈ cubicalChainModuleSupportedIn H R
      (MoorePathPullback.proj (sigmaCellMap C (m + 1)) b ⁻¹'
        {q | ‖(q.2 : Fin (m + 1) → ℝ)‖ = 1})) :
    cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom x ∈
      pathFromChainSkeleton b C H R m := by
  refine cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton
    (fun d hd ↦ ?_) hx
  rw [show (((m : ℤ) + 1).toNat : ℕ∞) = ((m + 1 : ℕ) : ℕ∞) by congr 1, sigmaCellMap_apply]
  exact cellFrontier_subset_skeletonLT (m + 1) d.1 ⟨d.2, mem_sphere_zero_iff_norm.2 hd, rfl⟩

/-- The boundary of the image of the section chain of a cell in `C_*(P_b B; R)` lies over the
`m`-skeleton. -/
theorem cubicalChainModuleDifferential_toMoorePathFrom_cellSectionChain_mem_pathFromChainSkeleton
    (j : cell C (m + 1)) :
    cubicalChainModuleDifferential _ H R
        (cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom
          (cellSectionChain H R γ j)) ∈
      pathFromChainSkeleton b C H R m := by
  rw [cubicalChainModuleDifferential_linearMap]
  exact cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton_of_mem
    (cubicalChainModuleDifferential_cellSectionChain_mem_cubicalChainModuleSupportedIn γ j)

/-- **The free module on the `(m + 1)`-cells is quasi-isomorphic to the chains on the based path
space over the `(m + 1)`-skeleton, modulo those over the `m`-skeleton.** Choose a Moore path `γ j`
from `b` to the centre of each `(m + 1)`-cell `j`, and send the free generator of `j` to the image
`c₀ j` in `C_*(P_b B; R)` of its section chain (`TauCeti.cellSectionChain`). Every relative cycle
`(y, w)` of the resulting map `(y_j)_j ↦ ∑_j y_j · c₀ j`, with `w` over the `(m + 1)`-skeleton, is a
relative boundary `(d y', ∑_j y'_j · c₀ j + d w')` with `w'` over the `(m + 1)`-skeleton, modulo the
chains over the `m`-skeleton.

This is the hypothesis on the new generators in
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists` for the `(m + 1)`-cells, with the
stages `m` and `m + 1` of `TauCeti.pathFromChainSkeleton`. -/
theorem exists_mapRange_eq_and_linearCombination_add_differential_sub_mem_pathFromChainSkeleton_succ
    (y : cell C (m + 1) →₀ loopChainAlgebra B b R) (w : cubicalChainModule (MoorePathFrom B b) H R)
    (hy : mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y = 0)
    (hw : w ∈ pathFromChainSkeleton b C H R ((m : ℤ) + 1))
    (hyw : linearCombination (loopChainAlgebra B b R)
        (fun j ↦ cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom
          (cellSectionChain H R γ j)) y -
      cubicalChainModuleDifferential (MoorePathFrom B b) H R w ∈ pathFromChainSkeleton b C H R m) :
    ∃ (y' : cell C (m + 1) →₀ loopChainAlgebra B b R)
      (w' : cubicalChainModule (MoorePathFrom B b) H R),
      w' ∈ pathFromChainSkeleton b C H R ((m : ℤ) + 1) ∧
        mapRange.linearMap (cubicalChainDifferential (MooreLoopSpace B b) R) y' = y ∧
          linearCombination (loopChainAlgebra B b R)
              (fun j ↦ cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom
                (cellSectionChain H R γ j)) y' +
            cubicalChainModuleDifferential (MoorePathFrom B b) H R w' - w ∈
              pathFromChainSkeleton b C H R m := by
  -- The map out of the free module factors through the chains on the pullback over the cells.
  have hΦ (z : cell C (m + 1) →₀ loopChainAlgebra B b R) :
      linearCombination (loopChainAlgebra B b R)
          (fun j ↦ cubicalChainModuleLinearMap (G' := H) R MoorePathPullback.toMoorePathFrom
            (cellSectionChain H R γ j)) z =
        cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom
          (linearCombination (loopChainAlgebra B b R) (cellSectionChain H R γ) z) := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']
    | single j a =>
      rw [linearCombination_single, linearCombination_single,
        cubicalChainModuleLinearMap_smul _ MoorePathPullback.toMoorePathFrom_leftAct]
  have hm : ((m + 1 : ℕ) : ℤ) - 1 = m := by push_cast; ring
  -- The image of `y` in the chains on the pullback is a relative cycle, which the excision
  -- quasi-isomorphism lifts to a relative cycle `(y, u)` on the pullback.
  have hx := differential_linearCombination_sub_mem (H := H) γ y
  rw [hy, map_zero, sub_zero] at hx
  obtain ⟨u, v, hv, hu, huv⟩ := exists_add_differential_sub_mem_pathFromChainSkeleton (n := m + 1)
    hx (by exact_mod_cast hw) (by rw [hm, ← hΦ]; exact hyw)
  rw [hm] at huv
  -- The comparison on the pullback bounds `(y, u)`.
  obtain ⟨y', u', hy', hu'⟩ :=
    exists_mapRange_eq_and_linearCombination_cellSectionChain_add_differential_sub_mem γ y u hy
      (by rw [← neg_sub]; exact neg_mem hu)
  refine ⟨y', cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom u' + v,
    add_mem (cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton_succ u')
      (by exact_mod_cast hv), hy', ?_⟩
  convert add_mem (cubicalChainModuleLinearMap_toMoorePathFrom_mem_pathFromChainSkeleton_of_mem hu')
    huv using 1
  rw [hΦ, map_add, cubicalChainModuleDifferential_linearMap, map_sub, map_add]
  abel

end Skeleton

end TauCeti

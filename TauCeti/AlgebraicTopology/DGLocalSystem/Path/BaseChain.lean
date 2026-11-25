/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.SemifreeModel

/-!
# Brown models pushed to the base

Let `B` be a space with a point `b`, and `R` a commutative ring. A Brown model
(`TauCeti.BrownModel`) of the chains `C_*(P_b B; R)` on the Moore paths from `b` is a semi-free
module `K_m` over the loop chains `C_*(Ω_b B; R)`, on generators `x` with rows `m_{x,y}`, with a
quasi-isomorphism `g : K_m → C_*(P_b B; R)` linear over the loop chains. This file reads it on the
base `B`, through the end point map `P_b B → B`.

The end point does not see a loop concatenated in front of a path, so pushing chains forward along
it is linear over the augmentation `ε : C_*(Ω_b B; R) → R`
(`TauCeti.cubicalChainModuleLinearMap_endpoint_smul`): a loop chain of positive dimension acts by
families of paths with the same end point, which become degenerate cubes, and a `0`-chain acts
through the sum of its coefficients. The **base chain** of a generator `x`
(`TauCeti.BrownModel.baseChain`) is the push-forward `e_x` of `g x` to `B`. Applying the end point
to the equation `g(m_x) = ∂ (g x)` of the model gives

`∂ e_x = ∑_y ε(m_{x,y}) e_y`

(`TauCeti.BrownModel.cubicalChainModuleDifferential_baseChain`): the augmented rows of a Brown
model are the boundary coefficients of its base chains. So `x ↦ e_x` is a chain map to `C_*(B; R)`
from the free `R`-module on the generators, with the differential given by the augmented rows,
which is the twisted complex `R ⊗_{C_*(Ω_b B; R)} K_m` of the ground ring.

For Brown's model of a CW complex `C` (`TauCeti.brownModel`), the generator of an `n`-cell `j` goes
to a chain over the `n`-skeleton congruent to the chain of the cell modulo the
`(n - 1)`-skeleton. Pushed to `B`, the chain of the cell is its **characteristic cube**
(`TauCeti.cellCube`), the characteristic map of `j` read on the cube `Iⁿ`
(`TauCeti.cubicalChainModuleLinearMap_endpoint_cellPathChain`). Hence the base chain of `j` lies
over the `n`-skeleton and is congruent to the characteristic cube of `j` modulo the
`(n - 1)`-skeleton, and the boundary of the base chain of an `n`-cell `x` is, modulo the chains
over the `(n - 2)`-skeleton, the combination of the characteristic cubes of the `(n - 1)`-cells `y`
with the coefficients `ε(m_{x,y})`. In the relative cubical homology of the pair of skeleta
`(Bⁿ⁻¹, Bⁿ⁻²)` this reads

`∂ [χ_x] = ∑_y ε(m_{x,y}) [χ_y]`:

the augmentations of the degree-one rows of Brown's cocycle are the coefficients of the cellular
boundary of the characteristic cubes. This is the cellular reduction of Brown's twisting cocycle;
the comparison of the classes of the characteristic cubes with the generators of the cellular
chain groups is not made here.

## Main definitions

* `TauCeti.BrownModel.baseChain M x`: the base chain of the generator `x` of a Brown model `M`.
* `TauCeti.cellCube C n j`: the characteristic map of the `n`-cell `j`, read on the cube.

## Main results

* `TauCeti.cubicalChainModuleLinearMap_endpoint_smul`: the end point map is linear over the
  augmentation of the loop chains.
* `TauCeti.BrownModel.cubicalChainModuleDifferential_baseChain`: `∂ e_x = ∑_y ε(m_{x,y}) e_y`.
* `TauCeti.cubicalChainModuleLinearMap_endpoint_cellPathChain`: the end point of the chain of a
  cell is its characteristic cube.
* `TauCeti.brownModel_baseChain_mem_cubicalChainModuleSupportedIn`,
  `TauCeti.brownModel_baseChain_sub_mem_cubicalChainModuleSupportedIn`: in Brown's model of a CW
  complex, the base chain of an `n`-cell lies over the `n`-skeleton and is its characteristic cube
  modulo the `(n - 1)`-skeleton.
* `TauCeti.brownModel_cubicalChainModuleDifferential_baseChain_sub_mem`: modulo the
  `(n - 2)`-skeleton, the boundary of the base chain of an `n`-cell is the combination
  of the characteristic cubes with the augmented row as coefficients.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex Finsupp

universe uB uR

namespace TauCeti

section Endpoint

variable {B : Type uB} [TopologicalSpace B] {b : B} {H H' : Type*} {R : Type uR} [CommRing R]

/-- **The end point map is linear over the augmentation of the loop chains**: pushing a chain on
the based path space forward to `B` along the end point, `ev_* (a · m) = ε(a) ev_* m` for a chain
`a` on the Moore loops at `b`. -/
theorem cubicalChainModuleLinearMap_endpoint_smul (a : loopChainAlgebra B b R)
    (m : cubicalChainModule (MoorePathFrom B b) H R) :
    cubicalChainModuleLinearMap (G' := H') R (MoorePathFrom.endpoint B b) (a • m) =
      loopChainAugmentation B b R a •
        cubicalChainModuleLinearMap R (MoorePathFrom.endpoint B b) m := by
  rw [loopChainAugmentation_def]
  exact cubicalChainModuleLinearMap_smul_of_apply_smul _ MoorePathFrom.endpoint_leftAct a m

namespace BrownModel

variable {P : Type*} {ind : P → ℤ} (M : BrownModel B b H R P ind)

/-- The **base chain** of a generator `x` of a Brown model: the push-forward to `B`, along the end
point map `P_b B → B`, of the image of `x` in the chains on the based path space. -/
def baseChain (x : P) : cubicalChainModule B H R :=
  cubicalChainModuleLinearMap R (MoorePathFrom.endpoint B b) (M.comparison x)

theorem baseChain_def (x : P) :
    M.baseChain x = cubicalChainModuleLinearMap R (MoorePathFrom.endpoint B b) (M.comparison x) :=
  (rfl)

/-- The base chain of a generator of index `n` has dimension `n`. -/
theorem baseChain_mem_cubicalChainModuleGrading (x : P) :
    M.baseChain x ∈ cubicalChainModuleGrading B H R (-ind x) :=
  cubicalChainModuleLinearMap_mem _ (M.comparison_mem x)

/-- **The augmented rows of a Brown model are the boundary coefficients of its base chains**:
`∂ e_x = ∑_y ε(m_{x,y}) e_y`, where `e_x` is the base chain of `x` and `ε` the augmentation of the
loop chains. -/
theorem cubicalChainModuleDifferential_baseChain (x : P) :
    cubicalChainModuleDifferential B H R (M.baseChain x) =
      (M.cocycle.m x).sum fun y a ↦ loopChainAugmentation B b R a • M.baseChain y := by
  rw [baseChain, cubicalChainModuleDifferential_linearMap, ← M.linearCombination_comparison_m,
    linearCombination_apply, map_finsuppSum]
  simp only [cubicalChainModuleLinearMap_endpoint_smul, baseChain]

end BrownModel

end Endpoint

section CW

variable {B : Type} [TopologicalSpace B] [T2Space B] {b : B} {C : Set B} [CWComplex C]
  {H : Type*} {R : Type} [CommRing R]

variable (C) in
/-- The **characteristic cube** of an `n`-cell `j`: its characteristic map, read on the cube `Iⁿ`
through `TauCeti.cubeHomeomorphClosedBall`. -/
def cellCube (n : ℕ) (j : cell C n) : SingularCube B n :=
  (sigmaCellMap C n).comp (cellCubeMap C n j)

omit [T2Space B] in
@[simp]
theorem cellCube_apply (n : ℕ) (j : cell C n) (d : Fin n → unitInterval) :
    cellCube C n j d = map n j (cubeHomeomorphClosedBall (Fin n) d) := by
  rw [cellCube, ContinuousMap.comp_apply, cellCubeMap_apply, sigmaCellMap_apply]

omit [T2Space B] in
/-- The characteristic cube of a `0`-cell is the `0`-cube at the point of the cell. -/
theorem cellCube_zero (j : cell C 0) : cellCube C 0 j = SingularCube.point (map 0 j 0) := by
  rw [SingularCube.eq_point (cellCube C 0 j), cellCube_apply]
  congr 2
  exact Subsingleton.elim _ _

omit [T2Space B] in
/-- **The end point of the chain of a cell is its characteristic cube**: pushed forward to `B` along
the end point map, the chain `TauCeti.cellPathChain τ n j` of the `n`-cell `j` on the based path
space becomes the characteristic cube of `j`. -/
theorem cubicalChainModuleLinearMap_endpoint_cellPathChain
    (τ : ∀ (n : ℕ) (j : cell C n), MoorePathBetween B b (map n j 0)) (n : ℕ) (j : cell C n) :
    cubicalChainModuleLinearMap R (MoorePathFrom.endpoint B b) (cellPathChain H R τ n j) =
      cubicalChainModuleLof B H R n (NormalizedCubicalChain.ofCube B R (cellCube C n j)) := by
  cases n with
  | zero =>
    rw [cellPathChain_zero, ← LinearMap.comp_apply, ← cubicalChainModuleLinearMap_comp,
      pathChainPoint_def, cubicalChainModuleLinearMap_lof, NormalizedCubicalChain.map_ofCube,
      cellCube_zero]
    congr 2
    ext
    simp
  | succ m =>
    rw [cellPathChain_succ, cellSectionPathChain_def, ← LinearMap.comp_apply,
      ← cubicalChainModuleLinearMap_comp, cubicalChainModuleLinearMap_lof,
      NormalizedCubicalChain.map_ofCube]
    congr 2
    ext d
    simp [cellCube]

/-- The chains of `B` over the `q`-skeleton of `C`, read through the identity of `B`, are the chains
supported over the preimage of the `q`-skeleton under the end point map, pushed forward. -/
private theorem cubicalChainModuleLinearMap_endpoint_mem {q : ℤ}
    {x : cubicalChainModule (MoorePathFrom B b) H R} (hx : x ∈ pathFromChainSkeleton b C H R q) :
    cubicalChainModuleLinearMap (G' := H) R (MoorePathFrom.endpoint B b) x ∈
      cubicalChainModuleSupportedIn H R (preimageSkeleton C id q) :=
  cubicalChainModuleLinearMap_mem_cubicalChainModuleSupportedIn
    (mapsTo_preimageSkeleton _ (fun _ ↦ rfl) q) (mem_pathFromChainSkeleton.1 hx)

variable (τ : ∀ (n : ℕ) (j : cell C n), MoorePathBetween B b (map n j 0)) (hC : pathComponent b ⊆ C)

/-- **In Brown's model of a CW complex, the base chain of an `n`-cell lies over the
`n`-skeleton.** -/
theorem brownModel_baseChain_mem_cubicalChainModuleSupportedIn (x : Σ n, cell C n) :
    (brownModel H R τ hC).baseChain x ∈
      cubicalChainModuleSupportedIn H R (preimageSkeleton C id x.1) :=
  cubicalChainModuleLinearMap_endpoint_mem
    (brownModel_comparison_mem_pathFromChainSkeleton τ hC x)

/-- **In Brown's model of a CW complex, the base chain of an `n`-cell is its characteristic cube
modulo the `(n - 1)`-skeleton.** -/
theorem brownModel_baseChain_sub_mem_cubicalChainModuleSupportedIn (x : Σ n, cell C n) :
    (brownModel H R τ hC).baseChain x -
        cubicalChainModuleLof B H R x.1 (NormalizedCubicalChain.ofCube B R (cellCube C x.1 x.2)) ∈
      cubicalChainModuleSupportedIn H R (preimageSkeleton C id ((x.1 : ℤ) - 1)) := by
  rw [BrownModel.baseChain, ← cubicalChainModuleLinearMap_endpoint_cellPathChain τ, ← map_sub]
  exact cubicalChainModuleLinearMap_endpoint_mem
    (brownModel_comparison_sub_cellPathChain_mem_pathFromChainSkeleton τ hC x)

/-- **The augmented rows of Brown's cocycle are the cellular boundary coefficients of the
characteristic cubes.** In Brown's model of a CW complex, the boundary of the base chain of an
`n`-cell `x` is, modulo the chains over the `(n - 2)`-skeleton, the combination
`∑_y ε(m_{x,y}) χ_y` of the characteristic cubes of the cells `y` with the augmentations of the row
of `x` as coefficients. Since the base chain of `x` is its characteristic cube `χ_x` modulo the
`(n - 1)`-skeleton (`TauCeti.brownModel_baseChain_sub_mem_cubicalChainModuleSupportedIn`), this
says `∂ [χ_x] = ∑_y ε(m_{x,y}) [χ_y]` in the relative homology of the skeleta `(Bⁿ⁻¹, Bⁿ⁻²)`. -/
theorem brownModel_cubicalChainModuleDifferential_baseChain_sub_mem (x : Σ n, cell C n) :
    cubicalChainModuleDifferential B H R ((brownModel H R τ hC).baseChain x) -
        ((brownModel H R τ hC).cocycle.m x).sum (fun y a ↦ loopChainAugmentation B b R a •
          cubicalChainModuleLof B H R y.1
            (NormalizedCubicalChain.ofCube B R (cellCube C y.1 y.2))) ∈
      cubicalChainModuleSupportedIn H R (preimageSkeleton C id ((x.1 : ℤ) - 2)) := by
  rw [BrownModel.cubicalChainModuleDifferential_baseChain, ← Finsupp.sum_sub]
  refine Submodule.finsuppSum_mem _ _ _ _ fun y hy ↦ ?_
  -- The row of an `n`-cell only involves cells `y` of dimension `< n`, and the base chain of `y`
  -- is its characteristic cube modulo the `(dim y - 1)`-skeleton, inside the `(n - 2)`-skeleton.
  have hlt : y.1 < x.1 :=
    brownModel_cocycle_m_mem_supported (H := H) τ hC x (Finsupp.mem_support_iff.2 hy)
  rw [← smul_sub]
  refine Submodule.smul_mem _ _ (cubicalChainModuleSupportedIn_mono ?_
    (brownModel_baseChain_sub_mem_cubicalChainModuleSupportedIn τ hC y))
  exact monotone_preimageSkeleton _ (by omega)

end CW

end TauCeti

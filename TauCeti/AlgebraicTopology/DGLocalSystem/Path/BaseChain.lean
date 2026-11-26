/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.CharacteristicCube
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.SemifreeModel

/-!
# Brown's model of a CW complex pushed to the base

Let `B` be a space with a point `b`, and `R` a commutative ring. The base chain `e_x` of a
generator `x` of a Brown model (`TauCeti.BrownModel.baseChain`) is the push-forward to `B`, along
the end point map `P_b B → B`, of the image of `x` in the chains `C_*(P_b B; R)` on the Moore paths
from `b`, and `∂ e_x = ∑_y ε(m_{x,y}) e_y`
(`TauCeti.BrownModel.cubicalChainModuleDifferential_baseChain`), where `ε` is the augmentation of
the loop chains. This file reads these base chains in Brown's model of a CW complex.

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

the augmentations of the entries `m_{x,y}` of index difference one (chains of degree zero) of
Brown's cocycle are the coefficients of the cellular boundary of the characteristic cubes. This is
the cellular reduction of Brown's twisting cocycle.

**The cellular comparison.** Read in relative singular homology, the class of the characteristic
cube of an `n`-cell `j` in `Hₙ(Bⁿ, Bⁿ⁻¹)` is `(-1) ^ (n choose 2)` times the cellular basis vector
of `j` (`TauCeti.singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_cellularChainBasis`), and the
cellular differential is the cubical connecting morphism read in singular homology. Taking
cellular coordinates in the formula above, and using `(n + 1) choose 2 = n + (n choose 2)`, gives

`ε(m_{x,y}) = (-1) ^ n [x : y]`

for an `(n + 1)`-cell `x` and an `n`-cell `y`, where `[x : y]` is the cellular incidence
coefficient `TauCeti.cellularIncidence` of `y` in the boundary of `x`
(`TauCeti.brownModel_loopChainAugmentation_cocycle_m_eq_neg_one_pow_mul_cellularIncidence`). So
the twisted complex of Brown's cocycle with coefficients in the ground ring, with differential
`x ↦ ∑_y ε(m_{x,y}) y`, is the cellular chain complex of `B` up to the signs `(-1) ^ (n choose 2)`
on the generators of dimension `n`.

## Main results

* `TauCeti.cubicalChainModuleLinearMap_endpoint_cellPathChain`: the end point of the chain of a
  cell is its characteristic cube.
* `TauCeti.brownModel_baseChain_mem_cubicalChainModuleSupportedIn`,
  `TauCeti.brownModel_baseChain_sub_cellCube_mem_cubicalChainModuleSupportedIn`: in Brown's model
  of a CW complex, the base chain of an `n`-cell lies over the `n`-skeleton and is its
  characteristic cube modulo the `(n - 1)`-skeleton.
* Modulo the `(n - 2)`-skeleton, the boundary of the base chain of an `n`-cell is the combination
  of the characteristic cubes with the augmented row as coefficients
  (`brownModel_cubicalChainModuleDifferential_baseChain_sub_mem_cubicalChainModuleSupportedIn`).
* `TauCeti.brownModel_loopChainAugmentation_cocycle_m_eq_neg_one_pow_mul_cellularIncidence`: the
  augmented entries of Brown's cocycle of index difference one are the cellular incidence
  coefficients, up to the sign `(-1) ^ n`.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
* A. Hatcher, *Algebraic Topology*, Section 2.2, the cellular chain complex.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex Finsupp

namespace TauCeti

section CW

variable {B : Type} [TopologicalSpace B] [T2Space B] {b : B} {C : Set B} [CWComplex C]
  {H : Type*} {R : Type} [CommRing R]

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
    simp

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
      cubicalChainModuleSupportedIn H R (preimageSkeleton C id x.1) := by
  rw [BrownModel.baseChain_def]
  exact cubicalChainModuleLinearMap_endpoint_mem
    (brownModel_comparison_mem_pathFromChainSkeleton τ hC x)

/-- **In Brown's model of a CW complex, the base chain of an `n`-cell is its characteristic cube
modulo the `(n - 1)`-skeleton.** -/
theorem brownModel_baseChain_sub_cellCube_mem_cubicalChainModuleSupportedIn (x : Σ n, cell C n) :
    (brownModel H R τ hC).baseChain x -
        cubicalChainModuleLof B H R x.1 (NormalizedCubicalChain.ofCube B R (cellCube C x.1 x.2)) ∈
      cubicalChainModuleSupportedIn H R (preimageSkeleton C id ((x.1 : ℤ) - 1)) := by
  rw [BrownModel.baseChain_def, ← cubicalChainModuleLinearMap_endpoint_cellPathChain τ, ← map_sub]
  exact cubicalChainModuleLinearMap_endpoint_mem
    (brownModel_comparison_sub_cellPathChain_mem_pathFromChainSkeleton τ hC x)

/-- **The augmented rows of Brown's cocycle are the cellular boundary coefficients of the
characteristic cubes.** In Brown's model of a CW complex, the boundary of the base chain of an
`n`-cell `x` is, modulo the chains over the `(n - 2)`-skeleton, the combination
`∑_y ε(m_{x,y}) χ_y` of the characteristic cubes of the cells `y` with the augmentations of the row
of `x` as coefficients. Since the base chain of `x` is its characteristic cube `χ_x` modulo the
`(n - 1)`-skeleton
(`TauCeti.brownModel_baseChain_sub_cellCube_mem_cubicalChainModuleSupportedIn`), this says
`∂ [χ_x] = ∑_y ε(m_{x,y}) [χ_y]` in the relative homology of the skeleta `(Bⁿ⁻¹, Bⁿ⁻²)`. -/
theorem brownModel_cubicalChainModuleDifferential_baseChain_sub_mem_cubicalChainModuleSupportedIn
    (x : Σ n, cell C n) :
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
    (brownModel_baseChain_sub_cellCube_mem_cubicalChainModuleSupportedIn τ hC y))
  exact monotone_preimageSkeleton _ (by omega)

/-! ### The cellular comparison -/

variable (H R) in
/-- The `n`-cells in the row of an `(n + 1)`-cell `x` of Brown's cocycle. -/
private abbrev rowCells (n : ℕ) (x : cell C (n + 1)) : Finset (cell C n) :=
  ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩).support.preimage (Sigma.mk n)
    sigma_mk_injective.injOn

/-- In the row of an `(n + 1)`-cell, the augmented entries vanish off the `n`-cells, so the
combination of characteristic cubes with the augmented row as coefficients is a chain of
dimension `n`. -/
private lemma sum_loopChainAugmentation_smul_cellCube (n : ℕ) (x : cell C (n + 1)) :
    ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩).sum (fun y a ↦ loopChainAugmentation B b R a •
        cubicalChainModuleLof B H R y.1 (NormalizedCubicalChain.ofCube B R (cellCube C y.1 y.2))) =
      cubicalChainModuleLof B H R n (∑ y ∈ rowCells H R τ hC n x,
        loopChainAugmentation B b R ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ ⟨n, y⟩) •
          NormalizedCubicalChain.ofCube B R (cellCube C n y)) := by
  rw [map_sum, Finsupp.sum]
  simp_rw [map_smul]
  refine (Finset.sum_preimage (Sigma.mk n) _ _ (fun y ↦ loopChainAugmentation B b R
    ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ y) • cubicalChainModuleLof B H R y.1
      (NormalizedCubicalChain.ofCube B R (cellCube C y.1 y.2))) fun ⟨k, j⟩ hy hyn ↦ ?_).symm
  -- An entry off the `n`-cells lies on a cell of dimension `< n`, in negative degree.
  have hlt : k < n + 1 := brownModel_cocycle_m_mem_supported (H := H) τ hC ⟨n + 1, x⟩ hy
  have hne : k ≠ n := by
    rintro rfl
    exact hyn ⟨j, rfl⟩
  have hg := (brownModel H R τ hC).cocycle.mem_graded ⟨n + 1, x⟩ ⟨k, j⟩
  -- The augmentation is a graded map to the ground ring, concentrated in degree `0`.
  have h₀ : loopChainAugmentation B b R ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ ⟨k, j⟩) = 0 :=
    ((mem_trivialGrading_iff R R).1 ((loopChainAugmentation B b R).map_mem hg)).resolve_left
      (by push_cast; omega)
  rw [h₀, zero_smul]

/-- **The boundary of a characteristic cube through Brown's model.** For an `(n + 1)`-cell `x`,
the boundary of its characteristic cube is, up to the boundary of a chain over the `n`-skeleton
and a chain over the `(n - 1)`-skeleton, the combination of the characteristic cubes of the
`n`-cells with the augmented row of `x` as coefficients. This is
`TauCeti.brownModel_cubicalChainModuleDifferential_baseChain_sub_mem_cubicalChainModuleSupportedIn`
read in dimension `n`. -/
private lemma exists_boundary_cellCube_add_sub_eq (n : ℕ) (x : cell C (n + 1)) :
    ∃ (v : NormalizedCubicalChain (skeletonLT C ((n + 1 : ℕ) : ℕ∞)) R (n + 1))
      (u : NormalizedCubicalChain (skeletonLT C (n : ℕ∞)) R n),
      NormalizedCubicalChain.boundary B R n
            (NormalizedCubicalChain.ofCube B R (cellCube C (n + 1) x)) +
          NormalizedCubicalChain.boundary B R n
            (NormalizedCubicalChain.map R (ContinuousMap.subtypeVal _) (n + 1) v) -
          ∑ y ∈ rowCells H R τ hC n x,
            loopChainAugmentation B b R ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ ⟨n, y⟩) •
              NormalizedCubicalChain.ofCube B R (cellCube C n y) =
        NormalizedCubicalChain.map R (ContinuousMap.subtypeVal _) n u := by
  obtain ⟨e, he⟩ := exists_cubicalChainModuleLof_eq
    ((brownModel H R τ hC).baseChain_mem_cubicalChainModuleGrading ⟨n + 1, x⟩) (n + 1) (by simp)
  have h₁ := brownModel_baseChain_sub_cellCube_mem_cubicalChainModuleSupportedIn (H := H) (R := R)
    τ hC ⟨n + 1, x⟩
  rw [← he, ← map_sub, cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff,
    preimageSkeleton_eq_preimage_skeletonLT id (n + 1) _ rfl, preimage_id,
    NormalizedCubicalChain.supportedIn_def] at h₁
  have h₂ :=
    brownModel_cubicalChainModuleDifferential_baseChain_sub_mem_cubicalChainModuleSupportedIn
      (H := H) (R := R) τ hC ⟨n + 1, x⟩
  rw [sum_loopChainAugmentation_smul_cellCube, ← he, cubicalChainModuleDifferential_lof_succ,
    ← map_sub, cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff,
    preimageSkeleton_eq_preimage_skeletonLT id n _ (by push_cast; ring), preimage_id,
    NormalizedCubicalChain.supportedIn_def] at h₂
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨u, hu⟩ := h₂
  refine ⟨v, u, ?_⟩
  rw [hv, hu, map_sub]
  abel

/-- Read on `B`, the boundary of the characteristic cube of an `(n + 1)`-cell, as a chain of the
`n`-skeleton, is the boundary of the characteristic cube of the cell. -/
private lemma map_cubicalBoundaryChainOfCube_characteristicCube (n : ℕ) (x : cell C (n + 1)) :
    NormalizedCubicalChain.map R (ContinuousMap.subtypeVal _ : C((skeletonPair C n).fst, B)) n
        (TopPair.cubicalBoundaryChainOfCube R (characteristicCube C (n + 1) x)
          (mapsTo_characteristicCube_boundary (n + 1) x)) =
      NormalizedCubicalChain.boundary B R n
        (NormalizedCubicalChain.ofCube B R (cellCube C (n + 1) x)) := by
  let ι₂ : C((skeletonPair C (n + 1)).fst, B) := ContinuousMap.subtypeVal _
  have hι₂ : ι₂.comp (skeletonPair C (n + 1)).map.hom = ContinuousMap.subtypeVal _ :=
    ContinuousMap.ext fun _ ↦ rfl
  calc _ = NormalizedCubicalChain.map R ι₂ n (NormalizedCubicalChain.map R
        (skeletonPair C (n + 1)).map.hom n (TopPair.cubicalBoundaryChainOfCube R
          (characteristicCube C (n + 1) x)
            (mapsTo_characteristicCube_boundary (n + 1) x))) := by
        rw [← hι₂]; exact LinearMap.congr_fun (NormalizedCubicalChain.map_comp R _ _ n) _
    _ = NormalizedCubicalChain.boundary B R n (NormalizedCubicalChain.map R ι₂ (n + 1)
        (NormalizedCubicalChain.ofCube _ R (characteristicCube C (n + 1) x))) := by
        rw [TopPair.map_cubicalBoundaryChainOfCube]
        exact LinearMap.congr_fun (NormalizedCubicalChain.map_boundary R ι₂ n)
          (NormalizedCubicalChain.ofCube _ R (characteristicCube C (n + 1) x))
    _ = _ := congrArg _ (map_ofCube_characteristicCube R (n + 1) x)

/-- **The cellular boundary of a characteristic cube, in cubical homology.** For an `(n + 1)`-cell
`x`, the connecting morphism of the skeletal pair `(Xⁿ⁺¹, Xⁿ)` followed by the map to the relative
homology of `(Xⁿ, Xⁿ⁻¹)` sends the class of the characteristic cube of `x` to the combination of the
classes of the characteristic cubes of the `n`-cells with the augmented row of `x` as
coefficients. -/
private lemma homologyMap_cubicalHomologyδ_eq_sum (n : ℕ) (x : cell C (n + 1))
    {μx : ((skeletonPair C (n + 1)).cubicalChainComplex R).homology (n + 1)}
    (hμx : (skeletonPair C (n + 1)).IsCubicalRepresentative R
      (NormalizedCubicalChain.ofCube _ R (characteristicCube C (n + 1) x)) μx)
    (μ : cell C n → ((skeletonPair C n).cubicalChainComplex R).homology n)
    (hμ : ∀ y, (skeletonPair C n).IsCubicalRepresentative R
      (NormalizedCubicalChain.ofCube _ R (characteristicCube C n y)) (μ y)) :
    HomologicalComplex.homologyMap
        (cokernel.π ((normalizedCubicalChainComplex R).map (skeletonPair C n).map)) n
        ((skeletonPair C (n + 1)).cubicalHomologyδ R (n + 1) n rfl μx) =
      ∑ y ∈ rowCells H R τ hC n x,
        loopChainAugmentation B b R ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ ⟨n, y⟩) • μ y := by
  set ε := fun y : cell C n ↦
    loopChainAugmentation B b R ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ ⟨n, y⟩)
  have hbd := mapsTo_characteristicCube_boundary (n + 1) x
  let w := TopPair.cubicalBoundaryCycleOfCube R (characteristicCube C (n + 1) x) hbd
  rw [hμx.cubicalHomologyδ_eq w (by
    rw [TopPair.iCycles_cubicalBoundaryCycleOfCube, TopPair.map_cubicalBoundaryChainOfCube])]
  let ι : C((skeletonPair C n).fst, B) := ContinuousMap.subtypeVal _
  let ι' : C((skeletonPair C n).snd, B) := ContinuousMap.subtypeVal _
  obtain ⟨v, u, hvu⟩ : ∃ (v : NormalizedCubicalChain (skeletonPair C n).fst R (n + 1))
      (u : NormalizedCubicalChain (skeletonPair C n).snd R n),
      NormalizedCubicalChain.boundary B R n
            (NormalizedCubicalChain.ofCube B R (cellCube C (n + 1) x)) +
          NormalizedCubicalChain.boundary B R n (NormalizedCubicalChain.map R ι (n + 1) v) -
          ∑ y ∈ rowCells H R τ hC n x, ε y • NormalizedCubicalChain.ofCube B R (cellCube C n y) =
        NormalizedCubicalChain.map R ι' n u :=
    exists_boundary_cellCube_add_sub_eq (H := H) (R := R) τ hC n x
  have hc := (TopPair.IsCubicalRepresentative.sum (s := rowCells H R τ hC n x)
    fun y _ ↦ (hμ y).smul (ε y)).sub (TopPair.isCubicalRepresentative_d v)
  rw [sub_zero] at hc
  refine (skeletonPair C n).homologyMap_homologyπ_eq_of_isCubicalRepresentative R w hc ⟨u, ?_⟩
  -- Read on `B`, through the inclusion of the `n`-skeleton, this is the equation `hvu`. Here `bc`
  -- is the boundary of the cube of `x`, as a chain of the `n`-skeleton.
  let bc : NormalizedCubicalChain (skeletonPair C n).fst R n :=
    TopPair.cubicalBoundaryChainOfCube R (characteristicCube C (n + 1) x) hbd
  have hbc : NormalizedCubicalChain.map R ι n bc = _ :=
    map_cubicalBoundaryChainOfCube_characteristicCube n x
  have hy (y : cell C n) : NormalizedCubicalChain.map R ι n
      (NormalizedCubicalChain.ofCube _ R (characteristicCube C n y)) =
        NormalizedCubicalChain.ofCube B R (cellCube C n y) :=
    map_ofCube_characteristicCube R n y
  have hv : NormalizedCubicalChain.map R ι n
      (NormalizedCubicalChain.boundary (skeletonPair C n).fst R n v) =
      NormalizedCubicalChain.boundary B R n (NormalizedCubicalChain.map R ι (n + 1) v) :=
    LinearMap.congr_fun (NormalizedCubicalChain.map_boundary R ι n) v
  have hu : NormalizedCubicalChain.map R ι n (NormalizedCubicalChain.map R
      (skeletonPair C n).map.hom n u) = NormalizedCubicalChain.map R ι' n u :=
    (LinearMap.congr_fun (NormalizedCubicalChain.map_comp R ι _ n) u).symm
  have hw : normalizedCubicalChainComplexXEquiv _ n
      (((normalizedCubicalChainComplex R).obj (skeletonPair C n).fst).iCycles n w) = bc :=
    TopPair.iCycles_cubicalBoundaryCycleOfCube R _ hbd
  have hd : ((normalizedCubicalChainComplex R).obj (skeletonPair C n).fst).d (n + 1) n v =
      NormalizedCubicalChain.boundary (skeletonPair C n).fst R n v :=
    normalizedCubicalChainComplex_obj_d_apply (skeletonPair C n).fst n v
  apply NormalizedCubicalChain.map_injective R ι Subtype.val_injective n
  rw [hu, ← hvu, hw, hd]
  -- Restate the chain as a normalized chain, rather than an element of the chain complex.
  change _ = NormalizedCubicalChain.map R ι n (bc - (∑ y ∈ rowCells H R τ hC n x,
    ε y • NormalizedCubicalChain.ofCube (skeletonPair C n).fst R (characteristicCube C n y) -
      NormalizedCubicalChain.boundary (skeletonPair C n).fst R n v))
  rw [map_sub, map_sub, map_sum, hbc, hv]
  simp_rw [map_smul, hy]
  abel

/-- **The augmented Brown cocycle is the cellular incidence matrix, up to sign.** In Brown's model
of a CW complex, the augmentation of the entry of Brown's twisting cocycle from an `(n + 1)`-cell
`x` to an `n`-cell `y` is `(-1) ^ n` times the cellular incidence coefficient of `y` in the
boundary of `x`. -/
theorem brownModel_loopChainAugmentation_cocycle_m_eq_neg_one_pow_mul_cellularIncidence (n : ℕ)
    (x : cell C (n + 1)) (y : cell C n) :
    loopChainAugmentation B b R ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ ⟨n, y⟩) =
      (-1) ^ n * cellularIncidence C R n y x := by
  set ε := fun y : cell C n ↦
    loopChainAugmentation B b R ((brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ ⟨n, y⟩)
  obtain ⟨μx, hμx⟩ :=
    exists_isCubicalRepresentative_characteristicCube R (n + 1) x
  choose μ hμ using fun y : cell C n ↦
    exists_isCubicalRepresentative_characteristicCube R n y
  -- The cellular differential is the cubical connecting morphism, read in singular homology.
  have hd := cellularDifferential_singularCubicalHomologyIso_inv R n μx
  rw [homologyMap_cubicalHomologyδ_eq_sum (H := H) τ hC n x hμx μ hμ, map_sum,
    singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_cellularChainBasis R hμx] at hd
  simp_rw [map_smul, singularCubicalHomologyIso_inv_eq_neg_one_pow_smul_cellularChainBasis R
    (hμ _)] at hd
  -- Read the coordinate of `y` in the cellular basis.
  have h := congrArg (fun z ↦ (cellularChainBasis C R n).repr z y) hd
  simp only [map_smul, map_sum, Finsupp.smul_apply, Finset.sum_apply',
    Module.Basis.repr_self, smul_eq_mul, ← cellularIncidence_def] at h
  -- Only the term of `y` contributes; off the row, the entry and its augmentation vanish.
  have h' : (-1 : R) ^ (n + 1).choose 2 * cellularIncidence C R n y x =
      ε y * (-1) ^ n.choose 2 := by
    rw [h, Finset.sum_eq_single y (fun k _ hk ↦ by simp [hk]) fun hy ↦ ?_]
    · simp [ε, mul_comm]
    · have hm : (brownModel H R τ hC).cocycle.m ⟨n + 1, x⟩ ⟨n, y⟩ = 0 := by
        simpa [rowCells] using hy
      simp [hm]
  -- `(n + 1) choose 2 = n + n choose 2`, and the sign `(-1) ^ (n choose 2)` is its own inverse.
  have hs : ((-1 : R) ^ n.choose 2) * (-1) ^ n.choose 2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [Nat.choose_succ_succ', Nat.choose_one_right, pow_add] at h'
  linear_combination (-(-1 : R) ^ n.choose 2) * h' +
    ((-1) ^ n * cellularIncidence C R n y x - ε y) * hs

end CW

end TauCeti

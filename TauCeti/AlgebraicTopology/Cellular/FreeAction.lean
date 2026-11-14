/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.AlgebraicTopology.Cellular.Augmentation
public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.RepresentationTheory.FreeOfBasis
public import TauCeti.Topology.CWComplex.Classical.OrbitSpace
import Mathlib.LinearAlgebra.Basis.SMul
import TauCeti.AlgebraicTopology.Cellular.LocalDegree
import TauCeti.AlgebraicTopology.Cellular.Permutation
import TauCeti.GroupTheory.GroupAction.Free

/-!
# Cellular chains of free cellular actions

Let a group `G` act continuously on a Hausdorff CW complex `C ⊆ E` so that every element carries
each open `n`-cell onto an open `n`-cell (`TauCeti.cellMulAction`). Unlike the lifted CW structure
of a covering map (`TauCeti.cwComplexPreimage`), translations need not preserve chosen
characteristic maps strictly: a translation carrying the open cell of `i` onto that of `g • i` sends
the cellular basis vector of `i` to a scalar multiple of the cellular basis vector of `g • i`. For a
group action, these scalars are units (`TauCeti.cellActionBasisUnit`), over `ℤ` the orientation
signs `±1` of the induced self-homeomorphisms of cells.

When `G` acts freely on the cells, rescaling the cellular basis along each orbit by the units from a
chosen representative produces a `G`-permuted basis. With coefficients in a commutative ring `R`,
each cellular chain group is therefore free over `R[G]`, with one generator for each `G`-orbit of
cells (`TauCeti.cellActionChainRepIsoFreeOfOrbits`), and — when `p : E → B` is a quotient covering
map giving `B` the orbit CW structure `IsQuotientCoveringMap.cwComplexQuotient` — with basis one
chosen lift of each cell of `B` (`TauCeti.quotientCellularChainRepIsoFree`).

When `C` is contractible, the equivariant cellular augmentation
(`TauCeti.cellActionChainComplexRepAugmentation`) is a quasi-isomorphism, packaging the cellular
chain complex of `C` as a projective resolution of the trivial representation `Rep.trivial R G R`
(`TauCeti.cellActionResolution`).

## Main definitions and results

* `TauCeti.cellularChainGroupMap_cellularChainBasis_eq_smul`: a cellular map sending a closed
  `n`-cell `i` into a closed `n`-cell `i'` sends the cellular basis vector of `i` to a scalar
  multiple of that of `i'`.
* `TauCeti.cellActionChainRepresentation` and `TauCeti.cellActionChainComplexRep`: the cellular
  chain groups and chain complex of a CW complex carrying a continuous open-cell-permuting monoid
  action, as representations and complexes in `Rep R G`.
* `TauCeti.cellActionBasisCoeff` and `TauCeti.cellActionBasisUnit`: the scalar (and unit, for a
  group action) by which `g` scales the cellular basis vector of `i` into that of `g • i`.
* `TauCeti.cellActionChainRepIsoFreeOfOrbits` and `TauCeti.quotientCellularChainRepIsoFree`: for a
  free cellular action, each cellular chain group is free over `R[G]` on the cell orbits (or on the
  cells of the orbit space `B`, given one chosen lift of each cell of `B`).
* `TauCeti.cellActionResolution`: for a contractible CW complex with a free cellular group action,
  its cellular chains form a `ProjectiveResolution (Rep.trivial R G R)`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Function Limits Metric Set Topology Topology.RelCWComplex
open scoped Pointwise

universe w

namespace TauCeti

section ClosedCellMap

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {D : Set X} {F : Set Y} (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' F]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f) (R : Type w) [Ring R]

/-- If a cellular map carries the closed `n`-cell `i` into the closed `n`-cell `i'`, then for any
other `n`-cell `k ≠ i'` of the target, the `k`-coordinate of the image of the cellular basis vector
of `i` vanishes: the image of the characteristic disk of `i` misses the interior of `k`, so it
vanishes in local homology there. -/
lemma cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_ne {n : ℕ}
    {i : cell C n} {i' k : cell C' n}
    (hi : ∀ x ∈ closedCell n i, ∀ hx : x ∈ C, (f ⟨x, hx⟩).1 ∈ closedCell n i') (hk : k ≠ i') :
    (cellularChainBasis C' R n).repr
      (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)) k = 0 := by
  have hy_open : map n k (0 : Fin n → ℝ) ∈ openCell n k :=
    ⟨0, mem_ball_zero_iff.2 (by simp), rfl⟩
  have hy_skel : map n k (0 : Fin n → ℝ) ∈ (skeletonLT C' ((n + 1 : ℕ) : ℕ∞) : Set Y) := by
    exact_mod_cast openCell_subset_skeletonLT n k hy_open
  let x' : skeletonObj C' (n + 1) := ⟨map n k 0, hy_skel⟩
  have hx' : (x' : Y) ∈ openCell n k := hy_open
  set v := cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)
  let locMap := TopPair.singularHomologyMap
    (skeletonPairToComplSingleton C' x' (notMem_skeletonLT_of_mem_openCell n hx'))
    (ModuleCat.of R R) n
  have hcoord : locMap v =
      ((cellularChainBasis C' R n).repr v k) • cellLocalClass C' (ModuleCat.of R R) x' hx' 1 := by
    conv_lhs => rw [← (cellularChainBasis C' R n).linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum, Finset.sum_eq_single k]
    · rw [map_smul, singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_self]
    · intro l _ hl
      rw [map_smul, singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_of_ne C' R
        x' hx' hl, smul_zero]
    · intro hk_mem
      rw [Finsupp.notMem_support_iff.1 hk_mem, zero_smul, map_zero]
  have hmiss : ∀ z : TopCat.disk.{w} n,
      (TopPair.Hom.fst (characteristicCellPairMap C i ≫ skeletonPairMap C C' hf n) z :
        skeletonObj C' (n + 1)) ≠ x' := by
    intro z hz
    have hmem_closed : (cellDiskHom i z : X) ∈ closedCell n i := by
      rw [coe_cellDiskHom_apply]
      exact ⟨_, (diskHomeomorphClosedBall n z).2, rfl⟩
    have hmem_C : (cellDiskHom i z : X) ∈ C :=
      closedCell_subset_complex n i hmem_closed
    have himg : (x' : Y) ∈ closedCell n i' := by
      rw [← hz]
      simp only [TopPair.Hom.fst_comp, characteristicCellPairMap_fst, skeletonPairMap_fst]
      have hs : ((skeletonMap C C' hf (n + 1) (cellDiskHom i z)) : Y) =
          (f ⟨(cellDiskHom i z : X), hmem_C⟩).1 :=
        congrArg Subtype.val (skeletonMap_apply C C' hf (n + 1) (cellDiskHom i z))
      exact hs ▸ hi _ hmem_closed hmem_C
    exact (disjoint_closedCell_openCell_of_ne n le_rfl
      (fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.1 h).2).symm)).notMem_of_mem_left himg hx'
  have hzero : locMap v = 0 := by
    have hv_eq : locMap v =
        ((singularHomologyDiskBoundaryPairIso (ModuleCat.of R R) n).inv ≫
          TopPair.singularHomologyMap
            (characteristicCellPairMap C i ≫ skeletonPairMap C C' hf n ≫
              skeletonPairToComplSingleton C' x' (notMem_skeletonLT_of_mem_openCell n hx'))
            (ModuleCat.of R R) n) 1 := by
      simp only [v, locMap, cellularChainBasis_apply, cellularChainGroupMap_def]
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Category.assoc,
        ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap,
        ← TopPair.singularHomologyMap_comp, Category.assoc, ← TopPair.singularHomologyMap_comp]
    rw [hv_eq, TopPair.singularHomologyMap_eq_zero_of_fac
      (characteristicCellPairMap C i ≫ skeletonPairMap C C' hf n ≫
        skeletonPairToComplSingleton C' x' _)
      (ModuleCat.of R R)
      (TopCat.ofHom ⟨fun z ↦
        ⟨TopPair.Hom.fst (characteristicCellPairMap C i ≫ skeletonPairMap C C' hf n) z, hmiss z⟩,
        (TopPair.Hom.fst (characteristicCellPairMap C i ≫
          skeletonPairMap C C' hf n)).hom.continuous.subtype_mk _⟩)
      (by
        ext z
        simp only [TopPair.Hom.fst_comp, skeletonPairToComplSingleton_fst]
        rfl),
      Limits.comp_zero]
    rfl
  have hsmul :
      ((cellularChainBasis C' R n).repr v k) • cellLocalClass C' (ModuleCat.of R R) x' hx' 1 = 0 :=
    hcoord.symm.trans hzero
  have hinv := congrArg (inv (cellLocalClass C' (ModuleCat.of R R) x' hx')) hsmul
  rw [map_zero, map_smul, ← ModuleCat.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply,
    smul_eq_mul, mul_one] at hinv
  exact hinv

/-- **A cellular map sending the closed `n`-cell `i` into the closed `n`-cell `i'` sends the
cellular basis vector of `i` to a scalar multiple of the cellular basis vector of `i'`.** -/
theorem cellularChainGroupMap_cellularChainBasis_eq_smul {n : ℕ} {i : cell C n} {i' : cell C' n}
    (hi : ∀ x ∈ closedCell n i, ∀ hx : x ∈ C, (f ⟨x, hx⟩).1 ∈ closedCell n i') :
    cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i) =
      ((cellularChainBasis C' R n).repr
        (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)) i') •
        cellularChainBasis C' R n i' := by
  set v := cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)
  conv_lhs => rw [← (cellularChainBasis C' R n).linearCombination_repr v]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_single i']
  · intro k _ hk
    rw [cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_ne C C' hf R hi hk, zero_smul]
  · intro hi'_mem
    rw [Finsupp.notMem_support_iff.1 hi'_mem, zero_smul]

end ClosedCellMap

section Action

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Monoid G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [Ring R]

/-- The representation of `G` on the `n`-th cellular chain group of a Hausdorff CW complex `C`
induced by a continuous action carrying open cells onto open cells of the same dimension. -/
def cellActionChainRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  cellularActionRepresentation C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R n

/-- An element `g` acts on the cellular chains of `C` by the cellular chain map of translation by
`g`. -/
@[simp]
theorem cellActionChainRepresentation_apply (n : ℕ) (g : G) :
    cellActionChainRepresentation C hcell R n g =
      (cellularChainGroupMap C C (isCellular_cellActionSMul C g (hcell g))
        (ModuleCat.of R R) n).hom := by
  unfold cellActionChainRepresentation
  exact cellularActionRepresentation_apply _ _ _ _ _ _ _ _

/-- The cellular differential of `C` as a morphism of representations of `G`. -/
def cellActionDifferentialRep (n : ℕ) :
    Rep.of (cellActionChainRepresentation C hcell R (n + 1)) ⟶
      Rep.of (cellActionChainRepresentation C hcell R n) :=
  cellularActionDifferential C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R n

/-- The underlying linear map of `TauCeti.cellActionDifferentialRep` is the cellular differential
of `C`. -/
@[simp]
theorem cellActionDifferentialRep_hom_toLinearMap (n : ℕ) :
    (cellActionDifferentialRep C hcell R n).hom.toLinearMap =
      (cellularDifferential C (ModuleCat.of R R) n).hom := by
  unfold cellActionDifferentialRep
  exact cellularActionDifferential_hom_toLinearMap _ _ _ _ _ _ _

/-- **The cellular chain complex of `C` as a chain complex in `Rep R G`** for a continuous action
permuting open cells. -/
def cellActionChainComplexRep : ChainComplex (Rep.{w} R G) ℕ :=
  cellularActionComplex C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R

/-- The terms of `TauCeti.cellActionChainComplexRep` are `TauCeti.cellActionChainRepresentation`. -/
@[simp]
theorem cellActionChainComplexRep_X (n : ℕ) :
    (cellActionChainComplexRep C hcell R).X n =
      Rep.of (cellActionChainRepresentation C hcell R n) := by
  unfold cellActionChainComplexRep cellActionChainRepresentation
  exact cellularActionComplex_X _ _ _ _ _ _ _

/-- The differentials of `TauCeti.cellActionChainComplexRep` are the equivariant cellular
differentials. -/
@[simp]
theorem cellActionChainComplexRep_d (n : ℕ) :
    (cellActionChainComplexRep C hcell R).d (n + 1) n =
      eqToHom (cellActionChainComplexRep_X C hcell R (n + 1)) ≫
        cellActionDifferentialRep C hcell R n ≫
          eqToHom (cellActionChainComplexRep_X C hcell R n).symm := by
  unfold cellActionChainComplexRep cellActionDifferentialRep
  exact cellularActionComplex_d _ _ _ _ _ _ n

/-- Forgetting the `G`-action on `TauCeti.cellActionChainComplexRep` recovers the cellular chain
complex of `C`. -/
def cellActionChainComplexRepForget₂Iso :
    ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).mapHomologicalComplex _).obj
        (cellActionChainComplexRep C hcell R) ≅
      cellularChainComplex C (ModuleCat.of R R) :=
  (cellularActionComplexForget₂Iso C (fun g ↦ cellActionSMul C g (hcell g))
    (fun g ↦ isCellular_cellActionSMul C g (hcell g))
    (cellActionSMul_one C (hcell 1))
    (fun g h ↦ cellActionSMul_mul C g h (hcell g) (hcell h) (hcell (g * h))) R).symm

/-- Components of `TauCeti.cellActionChainComplexRepForget₂Iso` are the canonical term
transports. -/
@[simp]
theorem cellActionChainComplexRepForget₂Iso_hom_f (n : ℕ) :
    (cellActionChainComplexRepForget₂Iso C hcell R).hom.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X,
          cellActionChainComplexRep_X]
        rfl) := by
  unfold cellActionChainComplexRepForget₂Iso
  exact cellularActionComplexForget₂Iso_inv_f _ _ _ _ _ _ _

/-- Inverse components of `TauCeti.cellActionChainComplexRepForget₂Iso` are the reverse term
transports. -/
@[simp]
theorem cellActionChainComplexRepForget₂Iso_inv_f (n : ℕ) :
    (cellActionChainComplexRepForget₂Iso C hcell R).inv.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularChainComplex_X,
          cellActionChainComplexRep_X]
        rfl) := by
  unfold cellActionChainComplexRepForget₂Iso
  exact cellularActionComplexForget₂Iso_hom_f _ _ _ _ _ _ _

/-- The scalar in `R` by which `g` multiplies the cellular basis vector of `i` into the cellular
basis vector of `g • i`. -/
def cellActionBasisCoeff {n : ℕ} (g : G) (i : cell C n) : R :=
  letI := cellMulAction hcell n
  (cellularChainBasis C R n).repr
    (cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i)) (g • i)

/-- **Translation by `g` sends the cellular basis vector of `i` to `cellActionBasisCoeff` times
that of `g • i`.** This is not a `simp` lemma because `simp` unfolds `TauCeti.cellularChainBasis`
first. -/
theorem cellActionChainRepresentation_cellularChainBasis {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellActionBasisCoeff C hcell R g i • cellularChainBasis C R n (g • i) := by
  let := cellMulAction hcell n
  have hi : ∀ x ∈ closedCell n i, ∀ hx : x ∈ C,
      (cellActionSMul C g (hcell g) ⟨x, hx⟩).1 ∈ closedCell n (g • i) := by
    intro x hx _
    rw [coe_cellActionSMul_apply, ← smul_closedCell hcell g i]
    exact smul_mem_smul_set hx
  simpa only [cellActionChainRepresentation_apply, cellActionBasisCoeff] using
    cellularChainGroupMap_cellularChainBasis_eq_smul C C
      (isCellular_cellActionSMul C g (hcell g)) R hi

/-- The identity element scales every cellular basis vector by `1`. -/
@[simp]
theorem cellActionBasisCoeff_one {n : ℕ} (i : cell C n) :
    cellActionBasisCoeff C hcell R (1 : G) i = 1 := by
  let := cellMulAction hcell n
  have h := cellActionChainRepresentation_cellularChainBasis C hcell R (1 : G) i
  rw [map_one, one_apply_eq_self, one_smul] at h
  have hrepr := congrArg (fun x ↦ (cellularChainBasis C R n).repr x i) h
  simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using hrepr.symm

/-- Cocycle law for `TauCeti.cellActionBasisCoeff` under composition of translations. -/
theorem cellActionBasisCoeff_mul {n : ℕ} (g h : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionBasisCoeff C hcell R (g * h) i =
      cellActionBasisCoeff C hcell R h i * cellActionBasisCoeff C hcell R g (h • i) := by
  let := cellMulAction hcell n
  have lhs := cellActionChainRepresentation_cellularChainBasis C hcell R (g * h) i
  rw [map_mul, mul_apply_eq_comp,
    cellActionChainRepresentation_cellularChainBasis C hcell R h i, map_smul,
    cellActionChainRepresentation_cellularChainBasis C hcell R g (h • i), smul_smul,
    ← mul_smul] at lhs
  have hrepr := congrArg (fun x ↦ (cellularChainBasis C R n).repr x ((g * h) • i)) lhs
  simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using hrepr.symm

/-- When translation by `g` carries the characteristic map of `i` strictly onto that of `g • i`
(as for lifted CW structures along coverings or ordered simplicial realizations), the scaling
coefficient `TauCeti.cellActionBasisCoeff` is `1`. -/
theorem cellActionBasisCoeff_eq_one_of_smul_map {n : ℕ} {g : G} {i : cell C n}
    (hmap : letI := cellMulAction hcell n
      ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, g • map n i x = map n (g • i) x) :
    cellActionBasisCoeff C hcell R g i = 1 := by
  let := cellMulAction hcell n
  have hstrict : cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellularChainBasis C R n (g • i) := by
    rw [cellActionChainRepresentation_apply]
    exact cellularChainGroupMap_cellularChainBasis C C
      (isCellular_cellActionSMul C g (hcell g)) R fun x hx hxC ↦
        (coe_cellActionSMul_apply C g (hcell g) ⟨map n i x, hxC⟩).trans (hmap x hx)
  rw [cellActionBasisCoeff, hstrict, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- The **augmentation** of `TauCeti.cellActionChainRepresentation` in degree `0` onto the trivial
representation, induced by naturality of the cellular augmentation under cellular translations. -/
def cellActionAugmentationRep :
    Rep.of (cellActionChainRepresentation C hcell R 0) ⟶ Rep.trivial R G R :=
  Rep.ofHom
    { toLinearMap := (cellularAugmentation C (ModuleCat.of R R)).hom
      isIntertwining' g := LinearMap.ext fun x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply,
          cellActionChainRepresentation_apply]
        exact ConcreteCategory.congr_hom (cellularChainGroupMap_comp_cellularAugmentation C C
          (isCellular_cellActionSMul C g (hcell g)) (ModuleCat.of R R)) x }

/-- The underlying linear map of `TauCeti.cellActionAugmentationRep` is the cellular augmentation
of `C`. -/
@[simp]
theorem cellActionAugmentationRep_hom_toLinearMap :
    (cellActionAugmentationRep C hcell R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom :=
  (rfl)

/-- The equivariant cellular augmentation vanishes on boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
theorem cellActionDifferentialRep_comp_cellActionAugmentationRep :
    cellActionDifferentialRep C hcell R 0 ≫ cellActionAugmentationRep C hcell R = 0 := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (cellularDifferential_comp_cellularAugmentation C (ModuleCat.of R R))) x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at h
  simpa [Rep.hom_comp] using h

/-- The **augmentation of `TauCeti.cellActionChainComplexRep`** as a chain map in `Rep R G` to the
trivial representation concentrated in degree `0`. -/
def cellActionChainComplexRepAugmentation :
    cellActionChainComplexRep C hcell R ⟶
      (ChainComplex.single₀ (Rep.{w} R G)).obj (Rep.trivial R G R) :=
  ((cellActionChainComplexRep C hcell R).toSingle₀Equiv _).symm
    ⟨eqToHom (cellActionChainComplexRep_X C hcell R 0) ≫ cellActionAugmentationRep C hcell R, by
      simp [cellActionChainComplexRep_d]⟩

/-- In degree `0`, `TauCeti.cellActionChainComplexRepAugmentation` is
`TauCeti.cellActionAugmentationRep`. -/
@[simp]
theorem cellActionChainComplexRepAugmentation_f_zero :
    (cellActionChainComplexRepAugmentation C hcell R).f 0 =
      eqToHom (cellActionChainComplexRep_X C hcell R 0) ≫ cellActionAugmentationRep C hcell R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end Action

section AugmentationQuasiIso

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Monoid G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type w) [CommRing R]

/-- **The augmented cellular chain complex of a contractible CW complex with a cellular action is
exact**: forgetting the `G`-action recovers the cellular chain augmentation of `C`. -/
theorem quasiIso_cellActionChainComplexRepAugmentation [ContractibleSpace C] :
    QuasiIso (cellActionChainComplexRepAugmentation C hcell R) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat R)),
    quasiIso_iff_of_arrow_mk_iso _
      (cellularChainComplexAugmentation C (ModuleCat.of R R)) ?_]
  · exact quasiIso_cellularChainComplexAugmentation _ _
  · refine Arrow.isoMk' _ _ (cellActionChainComplexRepForget₂Iso C hcell R)
      ((HomologicalComplex.singleMapHomologicalComplex _ _ 0).app _) ?_
    have h : (forget₂ (Rep R G) (ModuleCat R)).map (cellActionAugmentationRep C hcell R) =
        cellularAugmentation C (ModuleCat.of R R) := by
      rw [Rep.forget₂_moduleCat_map, cellActionAugmentationRep_hom_toLinearMap,
        ModuleCat.ofHom_hom]
    ext : 1
    simp [-Rep.forget₂_moduleCat_map, eqToHom_map, h]

end AugmentationQuasiIso

section GroupAction

variable {E : Type w} [TopologicalSpace E] [T2Space E] (C : Set E) [CWComplex C]
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)

section Units

variable (R : Type w) [Ring R]

/-- For a group action carrying open cells onto open cells, the scalar
`TauCeti.cellActionBasisCoeff` by which `g` multiplies the cellular basis vector of `i` is a unit in
`Rˣ`, with inverse the scalar of `g⁻¹` at `g • i`. -/
def cellActionBasisUnit {n : ℕ} (g : G) (i : cell C n) : Rˣ :=
  letI := cellMulAction hcell n
  { val := cellActionBasisCoeff C hcell R g i
    inv := cellActionBasisCoeff C hcell R g⁻¹ (g • i)
    val_inv := by
      rw [← cellActionBasisCoeff_mul, inv_mul_cancel, cellActionBasisCoeff_one]
    inv_val := by
      have h := cellActionBasisCoeff_mul C hcell R g g⁻¹ (g • i)
      rw [mul_inv_cancel, cellActionBasisCoeff_one, inv_smul_smul] at h
      exact h.symm }

/-- The underlying ring element of `TauCeti.cellActionBasisUnit` is
`TauCeti.cellActionBasisCoeff`. -/
@[simp]
theorem val_cellActionBasisUnit {n : ℕ} (g : G) (i : cell C n) :
    (cellActionBasisUnit C hcell R g i : R) = cellActionBasisCoeff C hcell R g i :=
  (rfl)

/-- The unit attached to the identity group element is `1`. -/
@[simp]
theorem cellActionBasisUnit_one {n : ℕ} (i : cell C n) :
    cellActionBasisUnit C hcell R (1 : G) i = 1 :=
  Units.ext (cellActionBasisCoeff_one C hcell R i)

/-- The inverse of `TauCeti.cellActionBasisUnit` at `(g, i)` is the unit of `g⁻¹` at `g • i`. -/
theorem cellActionBasisUnit_inv {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    (cellActionBasisUnit C hcell R g i)⁻¹ = cellActionBasisUnit C hcell R g⁻¹ (g • i) :=
  Units.ext rfl

/-- Translation by `g` acts on `cellularChainBasis` through the unit
`TauCeti.cellActionBasisUnit`. -/
theorem cellActionChainRepresentation_cellularChainBasis_unit {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n i) =
      cellActionBasisUnit C hcell R g i • cellularChainBasis C R n (g • i) :=
  cellActionChainRepresentation_cellularChainBasis C hcell R g i

/-- When translation by `g` carries the characteristic map of `i` strictly onto that of `g • i`,
the orientation unit `TauCeti.cellActionBasisUnit` is `1`. -/
theorem cellActionBasisUnit_eq_one_of_smul_map {n : ℕ} {g : G} {i : cell C n}
    (hmap : letI := cellMulAction hcell n
      ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, g • map n i x = map n (g • i) x) :
    cellActionBasisUnit C hcell R g i = 1 :=
  Units.ext (cellActionBasisCoeff_eq_one_of_smul_map C hcell R hmap)

end Units

section EquivariantBasis

variable (R : Type w) [CommRing R]

/-- Given an equivariant parametrization `e : (Σ _ : ι, G) ≃ cell C n` of the `n`-cells of `C`,
rescaling each cellular basis vector `e ⟨o, g⟩` by the unit of `g` at `e ⟨o, 1⟩` yields an `R`-basis
whose vectors are strictly permuted by `G`. -/
private def rescaledCellularChainBasis {n : ℕ} {ι : Type w} (e : (Σ _ : ι, G) ≃ cell C n) :
    Module.Basis (cell C n) R (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  (cellularChainBasis C R n).unitsSMul fun j ↦
    cellActionBasisUnit C hcell R (e.symm j).2 (e ⟨(e.symm j).1, 1⟩)

/-- At `e ⟨o, g⟩`, the rescaled cellular basis vector is the `g`-translate in the cellular chain
representation of the cellular basis vector of the chosen representative `e ⟨o, 1⟩`. -/
private theorem rescaledCellularChainBasis_apply_equiv {n : ℕ} {ι : Type w}
    (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • e ⟨o, 1⟩)
    (o : ι) (g : G) :
    rescaledCellularChainBasis C hcell R e (e ⟨o, g⟩) =
      cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (e ⟨o, 1⟩)) := by
  let := cellMulAction hcell n
  rw [rescaledCellularChainBasis, Module.Basis.unitsSMul_apply, Equiv.symm_apply_apply,
    Units.smul_def, val_cellActionBasisUnit, he g o,
    ← cellActionChainRepresentation_cellularChainBasis]

/-- `G` permutes `rescaledCellularChainBasis` strictly along left multiplication in the second
component of `e`. -/
private theorem cellActionChainRepresentation_rescaledCellularChainBasis {n : ℕ} {ι : Type w}
    (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • e ⟨o, 1⟩)
    (g h : G) (o : ι) :
    cellActionChainRepresentation C hcell R n g
        (rescaledCellularChainBasis C hcell R e (e ⟨o, h⟩)) =
      rescaledCellularChainBasis C hcell R e (e ⟨o, g * h⟩) := by
  rw [rescaledCellularChainBasis_apply_equiv C hcell R e he,
    rescaledCellularChainBasis_apply_equiv C hcell R e he, map_mul, mul_apply_eq_comp]

/-- Equivalence with the free representation associated to an equivariant parametrization of the
`n`-cells. -/
private def freeEquivCellActionChainRepresentation {n : ℕ} {ι : Type w}
    (e : (Σ _ : ι, G) ≃ cell C n)
    (he : letI := cellMulAction hcell n; ∀ (g : G) (o : ι), e ⟨o, g⟩ = g • e ⟨o, 1⟩) :
    (Representation.free R G ι).Equiv (cellActionChainRepresentation C hcell R n) :=
  (cellActionChainRepresentation C hcell R n).freeEquivOfBasis
    (rescaledCellularChainBasis C hcell R e) e
    (cellActionChainRepresentation_rescaledCellularChainBasis C hcell R e he)

end EquivariantBasis

section Free

variable (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

/-- The orbit parametrization `(Σ _ : orbitRel.Quotient G (cell C n), G) ≃ cell C n` attached to a
section `φ` of the orbit quotient. -/
private def orbitSigmaEquiv {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ) :
    (Σ _ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)), G) ≃
      cell C n :=
  letI := cellMulAction hcell n
  haveI := isCancelSMul_cell hcell hfree n
  (Equiv.sigmaEquivProd _ G).trans
    (MulAction.selfEquivOrbitsQuotientProd' hφ IsCancelSMul.stabilizer_eq_bot).symm

/-- **The cellular chains of a free cellular action are free over the group ring on the cell
orbits.** Given a choice `φ o` of representative in each `G`-orbit of `n`-cells of `C`, the `n`-th
cellular chain group of `C` is isomorphic in `Rep R G` to the free representation on the `G`-orbits
of `n`-cells, with `single o (single 1 1)` corresponding to the cellular basis vector of `φ o` and
`single o (single g r)` to `r` times its `g`-translate. -/
def cellActionChainRepIsoFreeOfOrbits {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ) :
    Rep.of (cellActionChainRepresentation C hcell R n) ≅
      Rep.free R G (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) :=
  (Rep.mkIso (freeEquivCellActionChainRepresentation C hcell R
    (orbitSigmaEquiv C hcell hfree φ hφ) fun g o ↦ by
      let := cellMulAction hcell n
      have := isCancelSMul_cell hcell hfree n
      simp [orbitSigmaEquiv])).symm

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the generator `single o (single g r)` of the
free representation maps to `r` times the `g`-translate of the cellular basis vector of the chosen
orbit representative `φ o`. -/
@[simp]
theorem cellActionChainRepIsoFreeOfOrbits_inv_hom_single {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) (r : R) :
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).inv.hom
        (Finsupp.single o (MonoidAlgebra.single g r)) =
      r • cellActionChainRepresentation C hcell R n g (cellularChainBasis C R n (φ o)) := by
  let := cellMulAction hcell n
  have := isCancelSMul_cell hcell hfree n
  have he : ∀ (g' : G) (o' : MulAction.orbitRel.Quotient G (cell C n)),
      orbitSigmaEquiv C hcell hfree φ hφ ⟨o', g'⟩ =
        g' • orbitSigmaEquiv C hcell hfree φ hφ ⟨o', 1⟩ := fun _ _ ↦ by simp [orbitSigmaEquiv]
  have ho : orbitSigmaEquiv C hcell hfree φ hφ ⟨o, 1⟩ = φ o := by simp [orbitSigmaEquiv]
  rw [cellActionChainRepIsoFreeOfOrbits, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact (Representation.freeEquivOfBasis_single (cellActionChainRepresentation C hcell R n)
    (rescaledCellularChainBasis C hcell R (orbitSigmaEquiv C hcell hfree φ hφ))
    (orbitSigmaEquiv C hcell hfree φ hφ) _ o g r).trans
      (by rw [rescaledCellularChainBasis_apply_equiv C hcell R _ he, ho])

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the cellular basis vector of the chosen
representative `φ o` corresponds to the generator `single o (single 1 1)`. This is not a `simp`
lemma because `simp` unfolds `TauCeti.cellularChainBasis` first. -/
theorem cellActionChainRepIsoFreeOfOrbits_hom_hom_cellularChainBasis {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) :
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).hom.hom
        (cellularChainBasis C R n (φ o)) =
      Finsupp.single o (MonoidAlgebra.single 1 1) := by
  have h := cellActionChainRepIsoFreeOfOrbits_inv_hom_single C hcell hfree R φ hφ o 1 1
  rw [map_one, one_apply_eq_self, one_smul] at h
  rw [← h, Rep.hom_inv_apply]

/-- Under `TauCeti.cellActionChainRepIsoFreeOfOrbits`, the cellular basis vector of a translated
representative `g • φ o` maps to `single o` weighted at `g` by the inverse orientation unit
`(cellActionBasisUnit C hcell R g (φ o))⁻¹`. -/
theorem cellActionChainRepIsoFreeOfOrbits_hom_hom_cellularChainBasis_smul {n : ℕ}
    (φ : (letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) → cell C n)
    (hφ : letI := cellMulAction hcell n; LeftInverse Quotient.mk'' φ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell C n)) (g : G) :
    letI := cellMulAction hcell n
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R φ hφ).hom.hom
        (cellularChainBasis C R n (g • φ o)) =
      Finsupp.single o
        (MonoidAlgebra.single g (↑(cellActionBasisUnit C hcell R g (φ o))⁻¹ : R)) := by
  let := cellMulAction hcell n
  have h := cellActionChainRepIsoFreeOfOrbits_inv_hom_single C hcell hfree R φ hφ o g
    (↑(cellActionBasisUnit C hcell R g (φ o))⁻¹ : R)
  rw [cellActionChainRepresentation_cellularChainBasis_unit, ← Units.smul_def, smul_smul,
    inv_mul_cancel, one_smul] at h
  rw [← h, Rep.hom_inv_apply]

include hfree in
/-- Every term of `TauCeti.cellActionChainComplexRep` for a free cellular group action is a
projective object of `Rep R G`. -/
theorem projective_cellActionChainComplexRep_X (n : ℕ) :
    Projective ((cellActionChainComplexRep C hcell R).X n) := by
  rw [cellActionChainComplexRep_X]
  exact Projective.of_iso
    (cellActionChainRepIsoFreeOfOrbits C hcell hfree R Quotient.out
      (letI := cellMulAction hcell n; Quotient.out_eq')).symm
    inferInstance

include hfree in
/-- **The cellular chains of a contractible CW complex with a free cellular group action form a
projective resolution** of the trivial representation `Rep.trivial R G R`. -/
def cellActionResolution [ContractibleSpace C] :
    ProjectiveResolution (Rep.trivial R G R) where
  complex := cellActionChainComplexRep C hcell R
  projective := projective_cellActionChainComplexRep_X C hcell hfree R
  π := cellActionChainComplexRepAugmentation C hcell R
  quasiIso := quasiIso_cellActionChainComplexRepAugmentation C hcell R

/-- The underlying chain complex of `TauCeti.cellActionResolution` is
`TauCeti.cellActionChainComplexRep`. -/
@[simp]
theorem cellActionResolution_complex [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).complex = cellActionChainComplexRep C hcell R :=
  (rfl)

-- Under `module`, the public statement cannot unfold the unexposed body of
-- `TauCeti.cellActionResolution`, so it transports along `cellActionResolution_complex`.
/-- The augmentation of `TauCeti.cellActionResolution` is
`TauCeti.cellActionChainComplexRepAugmentation`. -/
@[simp]
theorem cellActionResolution_π [ContractibleSpace C] :
    (cellActionResolution C hcell hfree R).π =
      eqToHom (cellActionResolution_complex C hcell hfree R) ≫
        cellActionChainComplexRepAugmentation C hcell R :=
  (Category.id_comp _).symm

end Free

end GroupAction

section QuotientCovering

variable {E B : Type w} [TopologicalSpace E] [T2Space E] [CWComplex (univ : Set E)]
  [TopologicalSpace B] {G : Type w} [Group G] [MulAction G E] {p : E → B}
  (hp : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  (R : Type w) [CommRing R]

/-- **The cellular chains of the total space of a free cellular quotient covering are free over the
group ring, with basis one chosen lift of each cell of the orbit space.** Given a lift `s b` of each
`n`-cell `b` of `B` (for the orbit CW structure `IsQuotientCoveringMap.cwComplexQuotient`), the
`n`-th cellular chain group of `E` is isomorphic in `Rep R G` to
`Rep.free R G (cell (univ : Set B) n)`, sending `single b (single 1 1)` to the cellular basis
vector of `s b` and `single b (single g r)` to `r` times its `g`-translate. -/
def quotientCellularChainRepIsoFree {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b) :
    haveI := hp.toContinuousConstSMul
    Rep.of (cellActionChainRepresentation (univ : Set E) hcell R n) ≅
      Rep.free R G (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :=
  haveI := hp.toContinuousConstSMul
  (Rep.mkIso (freeEquivCellActionChainRepresentation (univ : Set E) hcell R
    (hp.sigmaSMulQuotientLiftEquiv hcell hfree s hs) fun g b ↦ by
      let := cellMulAction hcell n
      rw [hp.sigmaSMulQuotientLiftEquiv_apply hcell hfree s hs,
        hp.sigmaSMulQuotientLiftEquiv_apply hcell hfree s hs, one_smul])).symm

/-- Under `TauCeti.quotientCellularChainRepIsoFree`, the generator `single b (single g r)` of the
free representation on the `n`-cells of `B` maps to `r` times the `g`-translate of the cellular
basis vector of the lifted cell `s b`. -/
@[simp]
theorem quotientCellularChainRepIsoFree_inv_hom_single {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) (r : R) :
    haveI := hp.toContinuousConstSMul
    (quotientCellularChainRepIsoFree hp hcell hfree R s hs).inv.hom
        (Finsupp.single b (MonoidAlgebra.single g r)) =
      r • cellActionChainRepresentation (univ : Set E) hcell R n g
        (cellularChainBasis (univ : Set E) R n (s b)) := by
  have := hp.toContinuousConstSMul
  let := hp.cwComplexQuotient hcell hfree
  let := cellMulAction hcell n
  have he : ∀ (g' : G) (b' : cell (univ : Set B) n),
      hp.sigmaSMulQuotientLiftEquiv hcell hfree s hs ⟨b', g'⟩ =
        g' • hp.sigmaSMulQuotientLiftEquiv hcell hfree s hs ⟨b', 1⟩ := fun g' b' ↦ by
    rw [hp.sigmaSMulQuotientLiftEquiv_apply hcell hfree s hs,
      hp.sigmaSMulQuotientLiftEquiv_apply hcell hfree s hs, one_smul]
  have hb : hp.sigmaSMulQuotientLiftEquiv hcell hfree s hs ⟨b, 1⟩ = s b := by
    rw [hp.sigmaSMulQuotientLiftEquiv_apply hcell hfree s hs, one_smul]
  rw [quotientCellularChainRepIsoFree, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact (Representation.freeEquivOfBasis_single
    (cellActionChainRepresentation (univ : Set E) hcell R n)
    (rescaledCellularChainBasis (univ : Set E) hcell R
      (hp.sigmaSMulQuotientLiftEquiv hcell hfree s hs))
    (hp.sigmaSMulQuotientLiftEquiv hcell hfree s hs) _ b g r).trans
      (by rw [rescaledCellularChainBasis_apply_equiv (univ : Set E) hcell R _ he, hb])

/-- Under `TauCeti.quotientCellularChainRepIsoFree`, the cellular basis vector of the chosen lift
`s b` corresponds to the generator `single b (single 1 1)`. This is not a `simp` lemma because
`simp` unfolds `TauCeti.cellularChainBasis` first. -/
theorem quotientCellularChainRepIsoFree_hom_hom_cellularChainBasis {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :
    haveI := hp.toContinuousConstSMul
    (quotientCellularChainRepIsoFree hp hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (s b)) =
      Finsupp.single b (MonoidAlgebra.single 1 1) := by
  have := hp.toContinuousConstSMul
  have h := quotientCellularChainRepIsoFree_inv_hom_single hp hcell hfree R s hs b 1 1
  rw [map_one, one_apply_eq_self, one_smul] at h
  rw [← h, Rep.hom_inv_apply]

/-- Under `TauCeti.quotientCellularChainRepIsoFree`, the cellular basis vector of the translated
lift `g • s b` maps to `single b` weighted at `g` by the inverse orientation unit
`(cellActionBasisUnit (univ : Set E) hcell R g (s b))⁻¹`. -/
theorem quotientCellularChainRepIsoFree_hom_hom_cellularChainBasis_smul {n : ℕ}
    (s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) → cell (univ : Set E) n)
    (hs : letI := hp.cwComplexQuotient hcell hfree; ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) :
    letI := cellMulAction hcell n
    haveI := hp.toContinuousConstSMul
    (quotientCellularChainRepIsoFree hp hcell hfree R s hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (g • s b)) =
      Finsupp.single b (MonoidAlgebra.single g
        (↑(cellActionBasisUnit (univ : Set E) hcell R g (s b))⁻¹ : R)) := by
  let := cellMulAction hcell n
  have := hp.toContinuousConstSMul
  have h := quotientCellularChainRepIsoFree_inv_hom_single hp hcell hfree R s hs b g
    (↑(cellActionBasisUnit (univ : Set E) hcell R g (s b))⁻¹ : R)
  rw [cellActionChainRepresentation_cellularChainBasis_unit, ← Units.smul_def, smul_smul,
    inv_mul_cancel, one_smul] at h
  rw [← h, Rep.hom_inv_apply]

end QuotientCovering

end TauCeti

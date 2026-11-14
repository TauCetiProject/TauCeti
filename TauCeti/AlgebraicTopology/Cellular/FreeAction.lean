/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import TauCeti.AlgebraicTopology.Cellular.Equivariant
public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.GroupTheory.GroupAction.Free
public import TauCeti.Topology.CWComplex.Classical.OrbitSpace
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RepresentationTheory.Rep.Iso
import TauCeti.AlgebraicTopology.Cellular.LocalDegree
import TauCeti.AlgebraicTopology.Cellular.Permutation
import TauCeti.RepresentationTheory.FreeOfBasis
import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor

/-!
# Cellular chains, resolutions, and coinvariants of free cellular group actions

Let a group `G` act continuously on a Hausdorff CW complex `C` so that every element carries each
open `n`-cell onto an open `n`-cell (`hcell`), without assuming compatibility with the chosen
characteristic maps. Translation by `g` restricts to a cellular self-map `TauCeti.cellularSMul`, so
with coefficients in a ring `R` the cellular chain groups carry representations
`TauCeti.cellularSMulRepresentation` assembling into an equivariant chain complex
`TauCeti.cellularSMulComplex`, with equivariant augmentation
`TauCeti.cellularSMulComplexAugmentation`.

Unlike a lifted CW structure along a covering map, translation by `g` need not preserve cell
orientations: it carries the closed `n`-cell `j` onto the closed `n`-cell `g • j`, so in the local
homology at a point of any other open `n`-cell its image vanishes
(`TauCeti.repr_cellularChainGroupMap_cellularChainBasis_eq_zero`), and on cellular chains it sends
the basis vector of `j` to a scalar multiple of the basis vector of `g • j`
(`TauCeti.cellularChainGroupMap_cellularChainBasis_of_mapsTo_closedCell`). Because `G` is a group,
these scalars satisfy a cocycle law and are units `TauCeti.cellularSMulUnit` in `Rˣ` (over `ℤ`,
the orientation signs `±1`).

When `G` acts freely on the open cells (`hfree`), rescaling the cellular basis along a transversal
`s : ι → cell C n` of the cell orbits by these orientation units produces an `R`-basis
`TauCeti.cellularSMulBasis` whose vectors on the orbit of `s i` are the actual `G`-translates of the
cellular basis vector of `s i`, and which `G` permutes freely without signs. Over a commutative
ring `R`, each cellular chain group is therefore isomorphic to `Rep.free R G ι`
(`TauCeti.cellularSMulRepIsoFree`), and when `C` is contractible the cellular chain complex of `C`
is a projective resolution of the trivial representation (`TauCeti.freeCellularResolution`).

When `C = univ : Set E` and `p : E → B` is the quotient covering map of the action
(`IsQuotientCoveringMap p G`), equipping `B` with the orbit CW structure
`IsQuotientCoveringMap.cwComplexQuotient`:

* for any family of lifts `s` of the `n`-cells of `B` with `p '' openCell n (s b) = openCell n b`,
  the `n`-th cellular chain group of `E` is free over `R[G]` on `cell (univ : Set B) n`
  (`IsQuotientCoveringMap.cellularSMulRepIsoFree`);
* the `G`-coinvariants of `TauCeti.cellularSMulComplex` identify canonically with the cellular chain
  complex of `B` (`IsQuotientCoveringMap.cellularSMulComplexCoinvariantsIso` and
  `IsQuotientCoveringMap.cellularSMulComplexCoinvariantsTensorIso`), deduced from a general
  coinvariants criterion for `G`-invariant cellular maps
  (`TauCeti.cellularActionComplexCoinvariantsIso`);
* when `E` is contractible, the cellular homology of the orbit CW complex `B` is isomorphic to
  Mathlib's group homology `groupHomology (Rep.trivial R G R) n`
  (`IsQuotientCoveringMap.cellularHomologyIsoGroupHomology`).

## Main definitions

* `TauCeti.cellularActionCoinvariantsIso`, `TauCeti.cellularActionComplexCoinvariantsIso`,
  `TauCeti.cellularActionComplexCoinvariantsTensorIso`: identification of the `G`-coinvariants of an
  equivariant cellular chain complex along a `G`-invariant cellular map admitting compatible cell
  lifts.
* `TauCeti.cellularSMulRepresentation`, `TauCeti.cellularSMulComplex`,
  `TauCeti.cellularSMulComplexAugmentation`: the equivariant cellular chain complex and augmentation
  of an open-cell-preserving continuous action.
* `TauCeti.cellularSMulUnit`: the unit in `Rˣ` by which `g` scales the cellular basis vector of `j`
  into that of `g • j`.
* `TauCeti.cellularSMulBasis`: the rescaled `R`-basis permuted without signs by a free cellular
  action.
* `TauCeti.cellularSMulRepIsoFree`, `TauCeti.cellularSMulRepIsoFreeOrbit`,
  `IsQuotientCoveringMap.cellularSMulRepIsoFree`: freeness over `R[G]` of the cellular chain groups
  of a free cellular action.
* `TauCeti.freeCellularResolution`: projective resolution of `Rep.trivial R G R` by the cellular
  chains of a contractible CW complex with a free cellular `G`-action.
* `IsQuotientCoveringMap.cellularSMulComplexCoinvariantsIso`,
  `IsQuotientCoveringMap.cellularSMulComplexCoinvariantsTensorIso`,
  `IsQuotientCoveringMap.cellularHomologyIsoGroupHomology`: coinvariants of the cellular chains of
  `E` are the cellular chains of the orbit CW complex `B`, computing `Hₙ(G, R)` when `E` is
  contractible.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections I.4 and II.4.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

section LocalVanishing

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {D : Set X} {E : Set Y} (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f) (R : Type u) [Ring R]

/-- **Local vanishing of cellular chain maps.** If a cellular map `f` sends the closed `n`-cell `j`
away from a point `x` of the open `n`-cell `i`, then the `i`-coordinate of the image of the cellular
basis vector of `j` vanishes. -/
theorem repr_cellularChainGroupMap_cellularChainBasis_eq_zero {n : ℕ} {j : cell C n}
    {i : cell C' n} (x : skeletonObj C' (n + 1)) (hx : (x : Y) ∈ openCell n i)
    (hmiss : ∀ z ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hz : map n j z ∈ C,
      (f ⟨map n j z, hz⟩).1 ≠ (x : Y)) :
    (cellularChainBasis C' R n).repr
      (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n j)) i = 0 := by
  set v := cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n j)
  set hx' := notMem_skeletonLT_of_mem_openCell n hx
  set loc := TopPair.singularHomologyMap (skeletonPairToComplSingleton C' x hx')
    (ModuleCat.of R R) n
  -- In the local homology at `x`, only the `i`-coordinate survives, as a multiple of the local
  -- class of `i` at `x`.
  have hcoord : loc v =
      ((cellularChainBasis C' R n).repr v i) • cellLocalClass C' (ModuleCat.of R R) x hx 1 := by
    conv_lhs => rw [← (cellularChainBasis C' R n).linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum, Finset.sum_eq_single i]
    · rw [map_smul, singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_self]
    · intro l _ hl
      rw [map_smul,
        singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_of_ne C' R x hx hl,
        smul_zero]
    · intro hi
      rw [Finsupp.notMem_support_iff.1 hi, zero_smul, map_zero]
  -- On the other hand, `f` carries the characteristic disk of `j` into `X'ⁿ ∖ {x}`, so `loc v = 0`.
  set gPair := characteristicCellPairMap C j ≫ skeletonPairMap C C' hf n ≫
    skeletonPairToComplSingleton C' x hx'
  have hmiss' (z : TopCat.disk.{u} n) :
      (TopPair.Hom.fst gPair z : skeletonObj C' (n + 1)) ≠ x := by
    intro hz
    set y : Fin n → ℝ := (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph
      ((z : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n))
    have hy : y ∈ closedBall 0 1 := by
      rw [mem_closedBall_zero_iff, ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff,
        ← mem_closedBall_zero_iff]
      exact (z : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down.2
    have hC : map n j y ∈ C := closedCell_subset_complex n j ⟨y, hy, rfl⟩
    set q : skeletonObj C (n + 1) := TopPair.Hom.fst (characteristicCellPairMap C j) z
    have hq : (q : X) = map n j y := coe_characteristicCellPairMap_fst_apply C j z
    have h1 : (TopPair.Hom.fst gPair z : skeletonObj C' (n + 1)) =
        skeletonMap C C' hf (n + 1) q := by
      simp only [gPair, TopPair.Hom.fst_comp, skeletonPairMap_fst,
        skeletonPairToComplSingleton_fst]
      rfl
    have h2 : (skeletonMap C C' hf (n + 1) q : Y) =
        (f ⟨q.1, (skeletonLT C _).subset_complex q.2⟩).1 :=
      congrArg Subtype.val (skeletonMap_apply C C' hf (n + 1) q)
    have h3 : (⟨q.1, (skeletonLT C _).subset_complex q.2⟩ : C) = ⟨map n j y, hC⟩ :=
      Subtype.ext hq
    have hval : (x : Y) = (f ⟨map n j y, hC⟩).1 :=
      (congrArg Subtype.val hz.symm).trans
        ((congrArg Subtype.val h1).trans (h2.trans (congrArg (fun w ↦ (f w).1) h3)))
    exact hmiss y hy hC hval.symm
  have hzero_hom : Sigma.ι (fun _ : cell C n ↦ ModuleCat.of R R) j ≫
      (cellularChainGroupIso C (ModuleCat.of R R) n).inv ≫
      cellularChainGroupMap C C' hf (ModuleCat.of R R) n ≫ loc = 0 := by
    rw [cellularChainGroupMap_def, ← TopPair.singularHomologyMap_comp,
      ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
      ← TopPair.singularHomologyMap_comp]
    change (singularHomologyDiskBoundaryPairIso (ModuleCat.of R R) n).inv ≫
      TopPair.singularHomologyMap gPair (ModuleCat.of R R) n = 0
    rw [TopPair.singularHomologyMap_eq_zero_of_fac gPair (ModuleCat.of R R)
      (TopCat.ofHom ⟨fun z ↦ ⟨TopPair.Hom.fst gPair z, hmiss' z⟩,
        (TopPair.Hom.fst gPair).hom.continuous.subtype_mk _⟩) (by ext z; rfl),
      Limits.comp_zero]
  have hzero : loc v = 0 := by
    change loc (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n j)) = 0
    rw [cellularChainBasis_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, hzero_hom]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  have hinv := congrArg (inv (cellLocalClass C' (ModuleCat.of R R) x hx)) (hcoord.symm.trans hzero)
  rw [map_smul, map_zero, ← ModuleCat.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply,
    smul_eq_mul, mul_one] at hinv
  exact hinv

/-- **Single-cell scaling of cellular chain maps.** If a cellular map `f` carries the closed
`n`-cell `j` into the closed `n`-cell `j'`, then on cellular chains it sends the basis vector of `j`
to its `j'`-coordinate times the basis vector of `j'`. -/
theorem cellularChainGroupMap_cellularChainBasis_of_mapsTo_closedCell {n : ℕ} {j : cell C n}
    {j' : cell C' n} (hclosed : ∀ x : C, x.1 ∈ closedCell n j → (f x).1 ∈ closedCell n j') :
    cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n j) =
      ((cellularChainBasis C' R n).repr
        (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n j)) j') •
      cellularChainBasis C' R n j' := by
  set v := cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n j)
  have hvanish (i : cell C' n) (hi : i ≠ j') : (cellularChainBasis C' R n).repr v i = 0 := by
    have hx_open : map n i (0 : Fin n → ℝ) ∈ openCell (C := C') n i :=
      mem_image_of_mem (map n i) (mem_ball_self zero_lt_one)
    have hx_skel : map n i (0 : Fin n → ℝ) ∈
        (skeletonLT C' ((n + 1 : ℕ) : ℕ∞) : Set Y) := by
      exact_mod_cast openCell_subset_skeletonLT n i hx_open
    refine repr_cellularChainGroupMap_cellularChainBasis_eq_zero C C' hf R ⟨map n i 0, hx_skel⟩
      hx_open fun z hz hC heq ↦ ?_
    have hmem : (f ⟨map n j z, hC⟩).1 ∈ closedCell n j' := hclosed ⟨map n j z, hC⟩ ⟨z, hz, rfl⟩
    exact (disjoint_closedCell_openCell_of_ne n le_rfl
      (fun h ↦ hi (eq_of_heq (Sigma.mk.inj_iff.1 h).2).symm)).notMem_of_mem_left hmem
      (heq ▸ hx_open)
  conv_lhs => rw [← (cellularChainBasis C' R n).linearCombination_repr v]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_single j']
  · intro i _ hi
    rw [hvanish i hi, zero_smul]
  · intro hj'
    rw [Finsupp.notMem_support_iff.1 hj', zero_smul]

end LocalVanishing

section CellularActionCoinvariants

variable {E B : Type u} [TopologicalSpace E] [T2Space E] [TopologicalSpace B] [T2Space B]
  (C : Set E) [CWComplex C] (C' : Set B) [CWComplex C']
  {G : Type u} [Group G] (ρ : G → (TopCat.of C ⟶ TopCat.of C))
  (hcell : ∀ g, IsCellular C C (ρ g))
  (hone : ρ 1 = 𝟙 _) (hmul : ∀ g h, ρ (g * h) = ρ h ≫ ρ g)
  {q : TopCat.of C ⟶ TopCat.of C'} (hq : IsCellular C C' q) (hqinv : ∀ g, ρ g ≫ q = q)
  (R : Type u) [CommRing R]

include hq hqinv

/-- The `G`-invariant cellular map `q` descends to a morphism from the `G`-coinvariants of the
equivariant `n`-th cellular chain group to the `n`-th cellular chain group of `C'`. -/
private def cellularActionCoinvariantsToChainGroup (n : ℕ) :
    (Rep.coinvariantsFunctor R G).obj
        (Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n)) ⟶
      cellularChainGroup C' (ModuleCat.of R R) n :=
  have hinv (g : G) :
      (cellularChainGroupMap C C' hq (ModuleCat.of R R) n).hom.comp
        (cellularActionRepresentation C ρ hcell hone hmul R n g) =
      (cellularChainGroupMap C C' hq (ModuleCat.of R R) n).hom :=
    LinearMap.ext fun x ↦ by
      rw [LinearMap.comp_apply, cellularActionRepresentation_apply]
      exact (ConcreteCategory.congr_hom
        (cellularChainGroupMap_comp C C (hcell g) C' hq (ModuleCat.of R R) n) x).symm.trans
        (ConcreteCategory.congr_hom
          (cellularChainGroupMap_congr C C' _ (ModuleCat.of R R) hq (hqinv g) n) x)
  ModuleCat.ofHom <| Representation.Coinvariants.lift
    (cellularActionRepresentation C ρ hcell hone hmul R n)
    (cellularChainGroupMap C C' hq (ModuleCat.of R R) n).hom hinv

private theorem cellularActionCoinvariantsToChainGroup_mk (n : ℕ)
    (x : (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R)) :
    cellularActionCoinvariantsToChainGroup C C' ρ hcell hone hmul hq hqinv R n
        (Representation.Coinvariants.mk
          (cellularActionRepresentation C ρ hcell hone hmul R n) x) =
      cellularChainGroupMap C C' hq (ModuleCat.of R R) n x :=
  rfl

private theorem isIso_cellularActionCoinvariantsToChainGroup {n : ℕ}
    (hlift : ∃ (e : Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ≅
        Rep.free R G (cell C' n)) (s : cell C' n → cell C n),
      (∀ b, e.inv.hom (Finsupp.single b (MonoidAlgebra.single 1 1)) =
        cellularChainBasis C R n (s b)) ∧
      ∀ b, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n (s b) x ∈ C,
        (q ⟨map n (s b) x, hx⟩).1 = map n b x) :
    IsIso (cellularActionCoinvariantsToChainGroup C C' ρ hcell hone hmul hq hqinv R n) := by
  obtain ⟨e, s, he, hs⟩ := hlift
  let eSrc : ModuleCat.of R (cell C' n →₀ R) ≅
      (Rep.coinvariantsFunctor R G).obj
        (Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n)) :=
    (Rep.coinvariantsFreeIso R G (cell C' n)).symm ≪≫ (Rep.coinvariantsFunctor R G).mapIso e.symm
  let eTgt : ModuleCat.of R (cell C' n →₀ R) ≅ cellularChainGroup C' (ModuleCat.of R R) n :=
    (cellularChainBasis C' R n).repr.symm.toModuleIso
  have hcomp :
      eSrc.hom ≫ cellularActionCoinvariantsToChainGroup C C' ρ hcell hone hmul hq hqinv R n =
        eTgt.hom := by
    refine ModuleCat.hom_ext <| Finsupp.lhom_ext' fun b ↦ LinearMap.ext_ring ?_
    change cellularActionCoinvariantsToChainGroup C C' ρ hcell hone hmul hq hqinv R n
        (Representation.Coinvariants.map _ _ e.inv.hom
          ((Rep.coinvariantsFreeIso R G (cell C' n)).inv (Finsupp.single b 1))) =
      (cellularChainBasis C' R n).repr.symm (Finsupp.single b 1)
    rw [Rep.coinvariantsFreeIso_inv_single, Representation.Coinvariants.map_mk, he b,
      cellularActionCoinvariantsToChainGroup_mk, Module.Basis.repr_symm_apply,
      Finsupp.linearCombination_single, one_smul]
    exact cellularChainGroupMap_cellularChainBasis C C' hq R (hs b)
  have : IsIso (eSrc.hom ≫
      cellularActionCoinvariantsToChainGroup C C' ρ hcell hone hmul hq hqinv R n) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left eSrc.hom _

/-- **Coinvariants of an equivariant cellular chain group along a `G`-invariant cellular map.** If
the `n`-th equivariant cellular chain group of `C` is free on `cell C' n` via lifts `s b` whose
characteristic maps project to those of `b` under `q`, then its `G`-coinvariants identify with the
`n`-th cellular chain group of `C'`. -/
def cellularActionCoinvariantsIso {n : ℕ}
    (hlift : ∃ (e : Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ≅
        Rep.free R G (cell C' n)) (s : cell C' n → cell C n),
      (∀ b, e.inv.hom (Finsupp.single b (MonoidAlgebra.single 1 1)) =
        cellularChainBasis C R n (s b)) ∧
      ∀ b, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n (s b) x ∈ C,
        (q ⟨map n (s b) x, hx⟩).1 = map n b x) :
    (Rep.coinvariantsFunctor R G).obj
        (Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n)) ≅
      cellularChainGroup C' (ModuleCat.of R R) n :=
  haveI := isIso_cellularActionCoinvariantsToChainGroup C C' ρ hcell hone hmul hq hqinv R hlift
  asIso (cellularActionCoinvariantsToChainGroup C C' ρ hcell hone hmul hq hqinv R n)

/-- Precomposing `TauCeti.cellularActionCoinvariantsIso` with the quotient map to coinvariants gives
the cellular chain map induced by `q`. -/
@[reassoc (attr := simp)]
theorem coinvariantsMk_comp_cellularActionCoinvariantsIso_hom {n : ℕ}
    (hlift : ∃ (e : Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ≅
        Rep.free R G (cell C' n)) (s : cell C' n → cell C n),
      (∀ b, e.inv.hom (Finsupp.single b (MonoidAlgebra.single 1 1)) =
        cellularChainBasis C R n (s b)) ∧
      ∀ b, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n (s b) x ∈ C,
        (q ⟨map n (s b) x, hx⟩).1 = map n b x) :
    (Rep.coinvariantsMk R G).app
        (Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n)) ≫
      (cellularActionCoinvariantsIso C C' ρ hcell hone hmul hq hqinv R hlift).hom =
      cellularChainGroupMap C C' hq (ModuleCat.of R R) n :=
  ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl

/-- On coinvariant classes, `TauCeti.cellularActionCoinvariantsIso` acts by the cellular chain map
induced by `q`. -/
-- Match before simplification changes the presentation of the coinvariants carrier.
@[simp↓]
theorem cellularActionCoinvariantsIso_hom_mk {n : ℕ}
    (hlift : ∃ (e : Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ≅
        Rep.free R G (cell C' n)) (s : cell C' n → cell C n),
      (∀ b, e.inv.hom (Finsupp.single b (MonoidAlgebra.single 1 1)) =
        cellularChainBasis C R n (s b)) ∧
      ∀ b, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n (s b) x ∈ C,
        (q ⟨map n (s b) x, hx⟩).1 = map n b x)
    (x : (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R)) :
    (cellularActionCoinvariantsIso C C' ρ hcell hone hmul hq hqinv R hlift).hom
        (Representation.Coinvariants.mk
          (cellularActionRepresentation C ρ hcell hone hmul R n) x) =
      cellularChainGroupMap C C' hq (ModuleCat.of R R) n x :=
  (rfl)

/-- **Coinvariants of an equivariant cellular chain complex along a `G`-invariant cellular map.**
If in every degree `n` the equivariant cellular chain group of `C` is free on `cell C' n` via cell
lifts projecting to the characteristic maps of `C'`, then the `G`-coinvariants of
`TauCeti.cellularActionComplex` identify with `TauCeti.cellularChainComplex` of `C'`. -/
def cellularActionComplexCoinvariantsIso
    (hlift : ∀ n : ℕ, ∃ (e : Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ≅
        Rep.free R G (cell C' n)) (s : cell C' n → cell C n),
      (∀ b, e.inv.hom (Finsupp.single b (MonoidAlgebra.single 1 1)) =
        cellularChainBasis C R n (s b)) ∧
      ∀ b, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n (s b) x ∈ C,
        (q ⟨map n (s b) x, hx⟩).1 = map n b x) :
    (((Rep.coinvariantsFunctor R G).mapHomologicalComplex _).obj
      (cellularActionComplex C ρ hcell hone hmul R)) ≅
      cellularChainComplex C' (ModuleCat.of R R) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦
      eqToIso (by rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X]) ≪≫
        cellularActionCoinvariantsIso C C' ρ hcell hone hmul hq hqinv R (hlift n) ≪≫
        eqToIso (cellularChainComplex_X C' (ModuleCat.of R R) n).symm)
    fun i j (hij : j + 1 = i) ↦ by
      subst hij
      have hcomm :
          (cellularActionCoinvariantsIso C C' ρ hcell hone hmul hq hqinv R (hlift (j + 1))).hom ≫
              cellularDifferential C' (ModuleCat.of R R) j =
            (Rep.coinvariantsFunctor R G).map
                (cellularActionDifferential C ρ hcell hone hmul R j) ≫
              (cellularActionCoinvariantsIso C C' ρ hcell hone hmul hq hqinv R (hlift j)).hom := by
        apply Rep.coinvariantsFunctor_hom_ext
        rw [coinvariantsMk_comp_cellularActionCoinvariantsIso_hom_assoc,
          ← (Rep.coinvariantsMk R G).naturality_assoc,
          coinvariantsMk_comp_cellularActionCoinvariantsIso_hom, Rep.forget₂_moduleCat_map,
          cellularActionDifferential_hom_toLinearMap, ModuleCat.ofHom_hom]
        exact cellularChainGroupMap_comp_cellularDifferential C C' hq (ModuleCat.of R R) j
      simp only [Functor.mapHomologicalComplex_obj_d, cellularActionComplex_d,
        cellularChainComplex_d, Iso.trans_hom, eqToIso.hom, Functor.map_comp, eqToHom_map,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, reassoc_of% hcomm]

/-- In degree `n`, `TauCeti.cellularActionComplexCoinvariantsIso` is
`TauCeti.cellularActionCoinvariantsIso` up to object transports. -/
@[simp]
theorem cellularActionComplexCoinvariantsIso_hom_f
    (hlift : ∀ n : ℕ, ∃ (e : Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ≅
        Rep.free R G (cell C' n)) (s : cell C' n → cell C n),
      (∀ b, e.inv.hom (Finsupp.single b (MonoidAlgebra.single 1 1)) =
        cellularChainBasis C R n (s b)) ∧
      ∀ b, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n (s b) x ∈ C,
        (q ⟨map n (s b) x, hx⟩).1 = map n b x)
    (n : ℕ) :
    (cellularActionComplexCoinvariantsIso C C' ρ hcell hone hmul hq hqinv R hlift).hom.f n =
      eqToHom (by rw [Functor.mapHomologicalComplex_obj_X, cellularActionComplex_X]) ≫
        (cellularActionCoinvariantsIso C C' ρ hcell hone hmul hq hqinv R (hlift n)).hom ≫
        eqToHom (cellularChainComplex_X C' (ModuleCat.of R R) n).symm :=
  (rfl)

/-- **Tensor coinvariants `(R ⊗ C_*(C))_G` along a `G`-invariant cellular map.** Composing
`TauCeti.cellularActionComplexCoinvariantsIso` with `Rep.coinvariantsTensorTrivialNatIso`
identifies `(cellularActionComplex ...).coinvariantsTensorObj (Rep.trivial R G R)` with the
cellular chain complex of `C'`. -/
def cellularActionComplexCoinvariantsTensorIso
    (hlift : ∀ n : ℕ, ∃ (e : Rep.of (cellularActionRepresentation C ρ hcell hone hmul R n) ≅
        Rep.free R G (cell C' n)) (s : cell C' n → cell C n),
      (∀ b, e.inv.hom (Finsupp.single b (MonoidAlgebra.single 1 1)) =
        cellularChainBasis C R n (s b)) ∧
      ∀ b, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n (s b) x ∈ C,
        (q ⟨map n (s b) x, hx⟩).1 = map n b x) :
    (cellularActionComplex C ρ hcell hone hmul R).coinvariantsTensorObj (Rep.trivial R G R) ≅
      cellularChainComplex C' (ModuleCat.of R R) :=
  (NatIso.mapHomologicalComplex (Rep.coinvariantsTensorTrivialNatIso R G) _).app
      (cellularActionComplex C ρ hcell hone hmul R) ≪≫
    cellularActionComplexCoinvariantsIso C C' ρ hcell hone hmul hq hqinv R hlift

end CellularActionCoinvariants

section CellularSMul

open scoped Pointwise

variable {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C] {G : Type u}

section Monoid

variable [Monoid G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type u) [Ring R]

/-- The representation of `G` on the `n`-th cellular chain group of `C` induced by continuous
translations preserving open cells. -/
def cellularSMulRepresentation (n : ℕ) :
    Representation R G (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  cellularActionRepresentation C (cellularSMul C hcell) (isCellular_cellularSMul C hcell)
    (cellularSMul_one C hcell) (cellularSMul_mul C hcell) R n

/-- An element `g` acts on cellular chains by the chain map of `TauCeti.cellularSMul`. -/
@[simp]
theorem cellularSMulRepresentation_apply (n : ℕ) (g : G) :
    cellularSMulRepresentation C hcell R n g =
      (cellularChainGroupMap C C (isCellular_cellularSMul C hcell g) (ModuleCat.of R R) n).hom :=
  cellularActionRepresentation_apply _ _ _ _ _ _ _ _

/-- The cellular differential as an equivariant morphism for
`TauCeti.cellularSMulRepresentation`. -/
def cellularSMulDifferential (n : ℕ) :
    Rep.of (cellularSMulRepresentation C hcell R (n + 1)) ⟶
      Rep.of (cellularSMulRepresentation C hcell R n) :=
  cellularActionDifferential C (cellularSMul C hcell) (isCellular_cellularSMul C hcell)
    (cellularSMul_one C hcell) (cellularSMul_mul C hcell) R n

/-- The underlying linear map of `TauCeti.cellularSMulDifferential` is the cellular differential. -/
@[simp]
theorem cellularSMulDifferential_hom_toLinearMap (n : ℕ) :
    (cellularSMulDifferential C hcell R n).hom.toLinearMap =
      (cellularDifferential C (ModuleCat.of R R) n).hom :=
  cellularActionDifferential_hom_toLinearMap _ _ _ _ _ _ _

/-- **The equivariant cellular chain complex of an open-cell-preserving continuous action.** -/
def cellularSMulComplex : ChainComplex (Rep.{u} R G) ℕ :=
  cellularActionComplex C (cellularSMul C hcell) (isCellular_cellularSMul C hcell)
    (cellularSMul_one C hcell) (cellularSMul_mul C hcell) R

/-- The objects of `TauCeti.cellularSMulComplex` are `TauCeti.cellularSMulRepresentation`. -/
@[simp]
theorem cellularSMulComplex_X (n : ℕ) :
    (cellularSMulComplex C hcell R).X n = Rep.of (cellularSMulRepresentation C hcell R n) :=
  cellularActionComplex_X _ _ _ _ _ _ _

/-- The differentials of `TauCeti.cellularSMulComplex` are `TauCeti.cellularSMulDifferential`. -/
@[simp]
theorem cellularSMulComplex_d (n : ℕ) :
    (cellularSMulComplex C hcell R).d (n + 1) n =
      eqToHom (cellularSMulComplex_X C hcell R (n + 1)) ≫
        cellularSMulDifferential C hcell R n ≫
        eqToHom (cellularSMulComplex_X C hcell R n).symm :=
  cellularActionComplex_d _ _ _ _ _ _ n

/-- Forgetting the `G`-action on `TauCeti.cellularSMulComplex` recovers the cellular chain complex
of `C`. -/
def cellularSMulComplexForget₂Iso :
    ((forget₂ (Rep.{u} R G) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
        (cellularSMulComplex C hcell R) ≅
      cellularChainComplex C (ModuleCat.of R R) :=
  (cellularActionComplexForget₂Iso C (cellularSMul C hcell) (isCellular_cellularSMul C hcell)
    (cellularSMul_one C hcell) (cellularSMul_mul C hcell) R).symm

/-- Components of `TauCeti.cellularSMulComplexForget₂Iso` are the canonical term transports. -/
@[simp]
theorem cellularSMulComplexForget₂Iso_hom_f (n : ℕ) :
    (cellularSMulComplexForget₂Iso C hcell R).hom.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularSMulComplex_X, cellularChainComplex_X]
        rfl) :=
  cellularActionComplexForget₂Iso_inv_f _ _ _ _ _ _ _

/-- Inverse components of `TauCeti.cellularSMulComplexForget₂Iso` are the reverse term
transports. -/
@[simp]
theorem cellularSMulComplexForget₂Iso_inv_f (n : ℕ) :
    (cellularSMulComplexForget₂Iso C hcell R).inv.f n =
      eqToHom (by
        rw [Functor.mapHomologicalComplex_obj_X, cellularSMulComplex_X, cellularChainComplex_X]
        rfl) :=
  cellularActionComplexForget₂Iso_hom_f _ _ _ _ _ _ _

/-- The cellular augmentation in degree `0` as a morphism from `TauCeti.cellularSMulRepresentation`
to the trivial representation. -/
def cellularSMulAugmentation :
    Rep.of (cellularSMulRepresentation C hcell R 0) ⟶ Rep.trivial R G R :=
  cellularActionAugmentation C (cellularSMul C hcell) (isCellular_cellularSMul C hcell)
    (cellularSMul_one C hcell) (cellularSMul_mul C hcell) R

/-- The underlying linear map of `TauCeti.cellularSMulAugmentation` is
`TauCeti.cellularAugmentation`. -/
@[simp]
theorem cellularSMulAugmentation_hom_toLinearMap :
    (cellularSMulAugmentation C hcell R).hom.toLinearMap =
      (cellularAugmentation C (ModuleCat.of R R)).hom :=
  cellularActionAugmentation_hom_toLinearMap _ _ _ _ _ _

/-- The equivariant augmentation vanishes on cellular boundaries. -/
@[reassoc (attr := simp)]
theorem cellularSMulDifferential_comp_cellularSMulAugmentation :
    cellularSMulDifferential C hcell R 0 ≫ cellularSMulAugmentation C hcell R = 0 :=
  cellularActionDifferential_comp_cellularActionAugmentation _ _ _ _ _ _

/-- The augmentation of `TauCeti.cellularSMulComplex` as a chain map to `Rep.trivial R G R` in
degree `0`. -/
def cellularSMulComplexAugmentation :
    cellularSMulComplex C hcell R ⟶
      (ChainComplex.single₀ (Rep.{u} R G)).obj (Rep.trivial R G R) :=
  cellularActionComplexAugmentation C (cellularSMul C hcell) (isCellular_cellularSMul C hcell)
    (cellularSMul_one C hcell) (cellularSMul_mul C hcell) R

/-- In degree `0`, `TauCeti.cellularSMulComplexAugmentation` is
`TauCeti.cellularSMulAugmentation`. -/
@[simp]
theorem cellularSMulComplexAugmentation_f_zero :
    (cellularSMulComplexAugmentation C hcell R).f 0 =
      eqToHom (cellularSMulComplex_X C hcell R 0) ≫ cellularSMulAugmentation C hcell R :=
  cellularActionComplexAugmentation_f_zero _ _ _ _ _ _

/-- When `C` is contractible, `TauCeti.cellularSMulComplexAugmentation` is a quasi-isomorphism. -/
theorem quasiIso_cellularSMulComplexAugmentation [ContractibleSpace C] :
    QuasiIso (cellularSMulComplexAugmentation C hcell R) :=
  quasiIso_cellularActionComplexAugmentation _ _ _ _ _ _

end Monoid

section Group

variable [Group G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (R : Type u) [Ring R]

/-- The scalar in `R` by which `g` multiplies the cellular basis vector of `j` to land in the
summand of `g • j`. -/
private def cellularSMulCoeff (n : ℕ) (g : G) (j : cell C n) : R :=
  letI := cellMulAction hcell n
  (cellularChainBasis C R n).repr
    (cellularSMulRepresentation C hcell R n g (cellularChainBasis C R n j)) (g • j)

private theorem cellularSMulRepresentation_cellularChainBasis_eq_coeff (n : ℕ) (g : G)
    (j : cell C n) :
    letI := cellMulAction hcell n
    cellularSMulRepresentation C hcell R n g (cellularChainBasis C R n j) =
      cellularSMulCoeff C hcell R n g j • cellularChainBasis C R n (g • j) := by
  let := cellMulAction hcell n
  have hclosed (x : C) (hx : x.1 ∈ closedCell n j) :
      (cellularSMul C hcell g x).1 ∈ closedCell n (g • j) := by
    rw [coe_cellularSMul_apply, ← smul_closedCell hcell g j]
    exact smul_mem_smul_set hx
  have h := cellularChainGroupMap_cellularChainBasis_of_mapsTo_closedCell C C
    (isCellular_cellularSMul C hcell g) R hclosed
  simpa only [cellularSMulCoeff, cellularSMulRepresentation_apply] using h

private theorem cellularSMulCoeff_one (n : ℕ) (j : cell C n) :
    cellularSMulCoeff C hcell R n 1 j = 1 := by
  classical
  let := cellMulAction hcell n
  rw [cellularSMulCoeff, map_one, one_smul, Module.End.one_eq_id, LinearMap.id_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same]

private theorem cellularSMulCoeff_mul (n : ℕ) (g h : G) (j : cell C n) :
    letI := cellMulAction hcell n
    cellularSMulCoeff C hcell R n (g * h) j =
      cellularSMulCoeff C hcell R n h j * cellularSMulCoeff C hcell R n g (h • j) := by
  classical
  let := cellMulAction hcell n
  have heq :
      cellularSMulRepresentation C hcell R n (g * h) (cellularChainBasis C R n j) =
        (cellularSMulCoeff C hcell R n h j * cellularSMulCoeff C hcell R n g (h • j)) •
          cellularChainBasis C R n ((g * h) • j) := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply,
      cellularSMulRepresentation_cellularChainBasis_eq_coeff C hcell R n h j, map_smul,
      cellularSMulRepresentation_cellularChainBasis_eq_coeff C hcell R n g (h • j),
      smul_smul, mul_smul g h j]
  have hrepr := congrArg (fun v ↦ (cellularChainBasis C R n).repr v ((g * h) • j)) heq
  rw [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_eq_same] at hrepr
  exact hrepr

/-- **Orientation unit of a cellular group action.** Because `g` and `g⁻¹` carry closed cells to
closed cells inverse to one another, `g` sends the cellular basis vector of `j` to a unit multiple
`TauCeti.cellularSMulUnit` of the cellular basis vector of `g • j`. Over `ℤ`, these units are the
orientation signs `±1`. -/
def cellularSMulUnit (n : ℕ) (g : G) (j : cell C n) : Rˣ :=
  letI := cellMulAction hcell n
  { val := cellularSMulCoeff C hcell R n g j
    inv := cellularSMulCoeff C hcell R n g⁻¹ (g • j)
    val_inv := by
      rw [← cellularSMulCoeff_mul C hcell R n g⁻¹ g j, inv_mul_cancel,
        cellularSMulCoeff_one]
    inv_val := by
      have h := cellularSMulCoeff_mul C hcell R n g g⁻¹ (g • j)
      rw [mul_inv_cancel, inv_smul_smul, cellularSMulCoeff_one] at h
      exact h.symm }

/-- Translation by `g` sends the cellular basis vector of `j` to `TauCeti.cellularSMulUnit` times
the cellular basis vector of `g • j`. This is not a `simp` lemma because `simp` unfolds
`TauCeti.cellularChainBasis` first. -/
theorem cellularSMulRepresentation_cellularChainBasis (n : ℕ) (g : G) (j : cell C n) :
    letI := cellMulAction hcell n
    cellularSMulRepresentation C hcell R n g (cellularChainBasis C R n j) =
      cellularSMulUnit C hcell R n g j • cellularChainBasis C R n (g • j) :=
  cellularSMulRepresentation_cellularChainBasis_eq_coeff C hcell R n g j

/-- The identity element acts with unit `1` on every cell. -/
@[simp]
theorem cellularSMulUnit_one (n : ℕ) (j : cell C n) :
    cellularSMulUnit C hcell R n 1 j = 1 :=
  Units.ext (cellularSMulCoeff_one C hcell R n j)

/-- Cocycle law for `TauCeti.cellularSMulUnit` over a possibly noncommutative ring `R`. -/
theorem cellularSMulUnit_mul (n : ℕ) (g h : G) (j : cell C n) :
    letI := cellMulAction hcell n
    cellularSMulUnit C hcell R n (g * h) j =
      cellularSMulUnit C hcell R n h j * cellularSMulUnit C hcell R n g (h • j) :=
  Units.ext (cellularSMulCoeff_mul C hcell R n g h j)

end Group

section FreeRing

variable [Group G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
  (R : Type u) [Ring R]

/-- **Rescaled cellular basis for a free cellular action.** Given a family `s : ι → cell C n`
meeting each `G`-orbit of `n`-cells in a unique index, rescaling the cellular basis vector of
`h • s i` by `TauCeti.cellularSMulUnit` produces an `R`-basis whose vector at `h • s i` is the
`G`-translate `h • e_{s i}` of the cellular basis vector of `s i`. -/
def cellularSMulBasis {n : ℕ} {ι : Type u} {s : ι → cell C n}
    (hs : Function.Bijective fun i ↦
      letI := cellMulAction hcell n
      (Quotient.mk'' (s i) : MulAction.orbitRel.Quotient G (cell C n))) :
    Module.Basis (cell C n) R (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  letI := cellMulAction hcell n
  haveI := isCancelSMul_cell hcell hfree n
  (cellularChainBasis C R n).unitsSMul fun k ↦
    cellularSMulUnit C hcell R n ((MulAction.sigmaSMulEquiv hs).symm k).2
      (s ((MulAction.sigmaSMulEquiv hs).symm k).1)

/-- At `h • s i`, `TauCeti.cellularSMulBasis` is the `h`-translate of the cellular basis vector of
`s i`. -/
theorem cellularSMulBasis_smul {n : ℕ} {ι : Type u} {s : ι → cell C n}
    (hs : Function.Bijective fun i ↦
      letI := cellMulAction hcell n
      (Quotient.mk'' (s i) : MulAction.orbitRel.Quotient G (cell C n)))
    (i : ι) (h : G) :
    letI := cellMulAction hcell n
    cellularSMulBasis C hcell hfree R hs (h • s i) =
      cellularSMulRepresentation C hcell R n h (cellularChainBasis C R n (s i)) := by
  let := cellMulAction hcell n
  have := isCancelSMul_cell hcell hfree n
  rw [cellularSMulBasis, Module.Basis.unitsSMul_apply, MulAction.sigmaSMulEquiv_symm_smul,
    ← cellularSMulRepresentation_cellularChainBasis]

/-- On the chosen representatives `s i`, `TauCeti.cellularSMulBasis` agrees with
`TauCeti.cellularChainBasis`. -/
theorem cellularSMulBasis_apply {n : ℕ} {ι : Type u} {s : ι → cell C n}
    (hs : Function.Bijective fun i ↦
      letI := cellMulAction hcell n
      (Quotient.mk'' (s i) : MulAction.orbitRel.Quotient G (cell C n)))
    (i : ι) :
    cellularSMulBasis C hcell hfree R hs (s i) = cellularChainBasis C R n (s i) := by
  let := cellMulAction hcell n
  have h := cellularSMulBasis_smul C hcell hfree R hs i 1
  rwa [one_smul, map_one, Module.End.one_eq_id, LinearMap.id_apply] at h

/-- `G` permutes `TauCeti.cellularSMulBasis` freely without orientation signs. -/
theorem cellularSMulRepresentation_cellularSMulBasis {n : ℕ} {ι : Type u} {s : ι → cell C n}
    (hs : Function.Bijective fun i ↦
      letI := cellMulAction hcell n
      (Quotient.mk'' (s i) : MulAction.orbitRel.Quotient G (cell C n)))
    (g h : G) (i : ι) :
    letI := cellMulAction hcell n
    haveI := isCancelSMul_cell hcell hfree n
    cellularSMulRepresentation C hcell R n g
        (cellularSMulBasis C hcell hfree R hs (MulAction.sigmaSMulEquiv hs ⟨i, h⟩)) =
      cellularSMulBasis C hcell hfree R hs (MulAction.sigmaSMulEquiv hs ⟨i, g * h⟩) := by
  let := cellMulAction hcell n
  have := isCancelSMul_cell hcell hfree n
  rw [MulAction.sigmaSMulEquiv_apply, MulAction.sigmaSMulEquiv_apply,
    cellularSMulBasis_smul, cellularSMulBasis_smul, map_mul, Module.End.mul_eq_comp,
    LinearMap.comp_apply]

end FreeRing

section FreeCommRing

variable [Group G] [MulAction G X] [ContinuousConstSMul G X]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n), ∃ j : cell C n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
  (R : Type u) [CommRing R]

include hfree

/-- **Freeness over `R[G]` of the cellular chains of a free cellular action.** Given a transversal
`s : ι → cell C n` of the `G`-orbits of `n`-cells, the `n`-th cellular chain group of `C` is
isomorphic in `Rep R G` to `Rep.free R G ι`, with `single i (single g r)` sent to `r` times the
`g`-translate of the cellular basis vector of `s i`. -/
def cellularSMulRepIsoFree {n : ℕ} {ι : Type u} {s : ι → cell C n}
    (hs : Function.Bijective fun i ↦
      letI := cellMulAction hcell n
      (Quotient.mk'' (s i) : MulAction.orbitRel.Quotient G (cell C n))) :
    Rep.of (cellularSMulRepresentation C hcell R n) ≅ Rep.free R G ι :=
  letI := cellMulAction hcell n
  haveI := isCancelSMul_cell hcell hfree n
  (Rep.mkIso ((cellularSMulRepresentation C hcell R n).freeEquivOfBasis
    (cellularSMulBasis C hcell hfree R hs) (MulAction.sigmaSMulEquiv hs)
    (cellularSMulRepresentation_cellularSMulBasis C hcell hfree R hs))).symm

/-- The inverse of `TauCeti.cellularSMulRepIsoFree` sends `single i (single g r)` to `r` times the
`g`-translate of the cellular basis vector of `s i`. -/
@[simp]
theorem cellularSMulRepIsoFree_inv_hom_single {n : ℕ} {ι : Type u} {s : ι → cell C n}
    (hs : Function.Bijective fun i ↦
      letI := cellMulAction hcell n
      (Quotient.mk'' (s i) : MulAction.orbitRel.Quotient G (cell C n)))
    (i : ι) (g : G) (r : R) :
    (cellularSMulRepIsoFree C hcell hfree R hs).inv.hom
        (Finsupp.single i (MonoidAlgebra.single g r)) =
      r • cellularSMulRepresentation C hcell R n g (cellularChainBasis C R n (s i)) := by
  let := cellMulAction hcell n
  have := isCancelSMul_cell hcell hfree n
  rw [cellularSMulRepIsoFree, Iso.symm_inv, Rep.mkIso_hom_hom_apply]
  exact (Representation.freeEquivOfBasis_single (cellularSMulRepresentation C hcell R n)
    (cellularSMulBasis C hcell hfree R hs) (MulAction.sigmaSMulEquiv hs)
    (cellularSMulRepresentation_cellularSMulBasis C hcell hfree R hs) i g r).trans
      (by rw [MulAction.sigmaSMulEquiv_apply, cellularSMulBasis_smul])

/-- `TauCeti.cellularSMulRepIsoFree` sends the cellular basis vector of the chosen representative
`s i` to `single i (single 1 1)`. -/
theorem cellularSMulRepIsoFree_hom_hom_cellularChainBasis {n : ℕ} {ι : Type u} {s : ι → cell C n}
    (hs : Function.Bijective fun i ↦
      letI := cellMulAction hcell n
      (Quotient.mk'' (s i) : MulAction.orbitRel.Quotient G (cell C n)))
    (i : ι) :
    (cellularSMulRepIsoFree C hcell hfree R hs).hom.hom (cellularChainBasis C R n (s i)) =
      Finsupp.single i (MonoidAlgebra.single 1 1) := by
  have h : (cellularSMulRepIsoFree C hcell hfree R hs).inv.hom
      (Finsupp.single i (MonoidAlgebra.single 1 1)) = cellularChainBasis C R n (s i) := by
    rw [cellularSMulRepIsoFree_inv_hom_single, one_smul, map_one, Module.End.one_eq_id,
      LinearMap.id_apply]
  rw [← h, Rep.hom_inv_apply]

/-- Without choosing an external indexing, the `n`-th cellular chain group of a free cellular
action is isomorphic to the free representation on the `G`-orbits of `n`-cells. -/
def cellularSMulRepIsoFreeOrbit (n : ℕ) :
    letI := cellMulAction hcell n
    Rep.of (cellularSMulRepresentation C hcell R n) ≅
      Rep.free R G (MulAction.orbitRel.Quotient G (cell C n)) :=
  letI := cellMulAction hcell n
  cellularSMulRepIsoFree C hcell hfree R (s := Quotient.out)
    ⟨fun a b h ↦ by
      dsimp only at h
      rwa [Quotient.out_eq', Quotient.out_eq'] at h,
      fun q ↦ ⟨q, Quotient.out_eq' q⟩⟩

/-- Every term of `TauCeti.cellularSMulComplex` for a free cellular action is projective in
`Rep R G`. -/
theorem projective_cellularSMulComplex_X (n : ℕ) :
    Projective ((cellularSMulComplex C hcell R).X n) := by
  let := cellMulAction hcell n
  rw [cellularSMulComplex_X]
  exact Projective.of_iso (cellularSMulRepIsoFreeOrbit C hcell hfree R n).symm inferInstance

/-- **Projective resolution of the trivial representation from a free cellular action on a
contractible CW complex.** -/
def freeCellularResolution [ContractibleSpace C] :
    ProjectiveResolution (Rep.trivial R G R) where
  complex := cellularSMulComplex C hcell R
  π := cellularSMulComplexAugmentation C hcell R
  projective := projective_cellularSMulComplex_X C hcell hfree R
  quasiIso := quasiIso_cellularSMulComplexAugmentation C hcell R

/-- The underlying chain complex of `TauCeti.freeCellularResolution` is
`TauCeti.cellularSMulComplex`. -/
@[simp]
theorem freeCellularResolution_complex [ContractibleSpace C] :
    (freeCellularResolution C hcell hfree R).complex = cellularSMulComplex C hcell R :=
  (rfl)

/-- The augmentation of `TauCeti.freeCellularResolution` is
`TauCeti.cellularSMulComplexAugmentation`. -/
@[simp]
theorem freeCellularResolution_π [ContractibleSpace C] :
    (freeCellularResolution C hcell hfree R).π =
      eqToHom (freeCellularResolution_complex C hcell hfree R) ≫
        cellularSMulComplexAugmentation C hcell R :=
  (Category.id_comp _).symm

end FreeCommRing

end CellularSMul

section OrbitSpace

open scoped Pointwise

variable {E B : Type u} [TopologicalSpace E] [T2Space E] [TopologicalSpace B]
  [CWComplex (univ : Set E)] {G : Type u} [Group G] [MulAction G E] {p : E → B}
  (hp : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  (R : Type u) [CommRing R]

private theorem bijective_mk_of_image_openCell_eq {n : ℕ}
    {s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) →
      cell (univ : Set E) n}
    (hs : letI := hp.cwComplexQuotient hcell hfree
      ∀ b, p '' openCell n (s b) = openCell n b) :
    letI := hp.cwComplexQuotient hcell hfree
    letI := cellMulAction hcell n
    Function.Bijective fun b ↦
      (Quotient.mk'' (s b) : MulAction.orbitRel.Quotient G (cell (univ : Set E) n)) := by
  let := hp.cwComplexQuotient hcell hfree
  let := cellMulAction hcell n
  have hfun : (fun b ↦ (Quotient.mk'' (s b) :
      MulAction.orbitRel.Quotient G (cell (univ : Set E) n))) =
      hp.cellQuotientEquiv hcell hfree n :=
    funext fun b ↦ (hp.image_openCell_eq_iff hcell hfree (s b) b).1 (hs b)
  rw [hfun]
  exact (hp.cellQuotientEquiv hcell hfree n).bijective

/-- **The cellular chains of a free cellular action are free over `R[G]` on the cells of the orbit
CW complex.** Given one chosen lift `s b` of each `n`-cell `b` of
`IsQuotientCoveringMap.cwComplexQuotient` satisfying `p '' openCell n (s b) = openCell n b`, the
`n`-th cellular chain group of `E` is isomorphic in `Rep R G` to
`Rep.free R G (cell (univ : Set B) n)`. -/
def _root_.IsQuotientCoveringMap.cellularSMulRepIsoFree {n : ℕ}
    {s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) →
      cell (univ : Set E) n}
    (hs : letI := hp.cwComplexQuotient hcell hfree
      ∀ b, p '' openCell n (s b) = openCell n b) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    Rep.of (cellularSMulRepresentation (univ : Set E) hcell R n) ≅
      Rep.free R G (cell (univ : Set B) n) :=
  letI := hp.cwComplexQuotient hcell hfree
  haveI := hp.toContinuousConstSMul
  TauCeti.cellularSMulRepIsoFree (univ : Set E) hcell hfree R
    (bijective_mk_of_image_openCell_eq hp hcell hfree hs)

/-- The inverse of `IsQuotientCoveringMap.cellularSMulRepIsoFree` sends `single b (single g r)` to
`r` times the `g`-translate of the cellular basis vector of the chosen lift `s b`. -/
@[simp]
theorem _root_.IsQuotientCoveringMap.cellularSMulRepIsoFree_inv_hom_single {n : ℕ}
    {s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) →
      cell (univ : Set E) n}
    (hs : letI := hp.cwComplexQuotient hcell hfree
      ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) (g : G) (r : R) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    (hp.cellularSMulRepIsoFree hcell hfree R hs).inv.hom
        (Finsupp.single b (MonoidAlgebra.single g r)) =
      r • cellularSMulRepresentation (univ : Set E) hcell R n g
        (cellularChainBasis (univ : Set E) R n (s b)) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.toContinuousConstSMul
  exact TauCeti.cellularSMulRepIsoFree_inv_hom_single (univ : Set E) hcell hfree R
    (bijective_mk_of_image_openCell_eq hp hcell hfree hs) b g r

/-- `IsQuotientCoveringMap.cellularSMulRepIsoFree` sends the cellular basis vector of `s b` to
`single b (single 1 1)`. -/
theorem _root_.IsQuotientCoveringMap.cellularSMulRepIsoFree_hom_hom_cellularChainBasis {n : ℕ}
    {s : (letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) →
      cell (univ : Set E) n}
    (hs : letI := hp.cwComplexQuotient hcell hfree
      ∀ b, p '' openCell n (s b) = openCell n b)
    (b : letI := hp.cwComplexQuotient hcell hfree; cell (univ : Set B) n) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.toContinuousConstSMul
    (hp.cellularSMulRepIsoFree hcell hfree R hs).hom.hom
        (cellularChainBasis (univ : Set E) R n (s b)) =
      Finsupp.single b (MonoidAlgebra.single 1 1) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.toContinuousConstSMul
  exact TauCeti.cellularSMulRepIsoFree_hom_hom_cellularChainBasis (univ : Set E) hcell hfree R
    (bijective_mk_of_image_openCell_eq hp hcell hfree hs) b

private theorem exists_orbit_lift (n : ℕ) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    haveI := hp.toContinuousConstSMul
    ∃ (e : Rep.of (cellularSMulRepresentation (univ : Set E) hcell R n) ≅
        Rep.free R G (cell (univ : Set B) n))
      (s : cell (univ : Set B) n → cell (univ : Set E) n),
      (∀ b, e.inv.hom (Finsupp.single b (MonoidAlgebra.single 1 1)) =
        cellularChainBasis (univ : Set E) R n (s b)) ∧
      ∀ b, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n (s b) x ∈ (univ : Set E),
        (hp.univMap ⟨map n (s b) x, hx⟩).1 = map n b x := by
  let := hp.cwComplexQuotient hcell hfree
  let := cellMulAction hcell n
  have := hp.t2Space_of_cwComplex hcell hfree
  have := hp.toContinuousConstSMul
  let s₀ : cell (univ : Set B) n → cell (univ : Set E) n :=
    fun b ↦ (hp.cellQuotientEquiv hcell hfree n b).out
  have hs₀ : ∀ b, p '' openCell n (s₀ b) = openCell n b := fun b ↦
    (hp.image_openCell_eq_iff hcell hfree (s₀ b) b).2 (Quotient.out_eq' _)
  refine ⟨hp.cellularSMulRepIsoFree hcell hfree R hs₀, s₀, fun b ↦ ?_, fun b x _ _ ↦ ?_⟩
  · rw [hp.cellularSMulRepIsoFree_inv_hom_single, one_smul, map_one, Module.End.one_eq_id,
      LinearMap.id_apply]
  · rw [hp.coe_univMap_apply]
    have h := (hp.map_cellQuotientEquiv_symm hcell hfree
      (hp.cellQuotientEquiv hcell hfree n b) x).symm
    rwa [Equiv.symm_apply_apply] at h

/-- **The `G`-coinvariants of the `n`-th cellular chain group of `E` identify with the `n`-th
cellular chain group of the orbit CW complex `B`.** -/
def _root_.IsQuotientCoveringMap.cellularSMulCoinvariantsIso (n : ℕ) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    haveI := hp.toContinuousConstSMul
    (Rep.coinvariantsFunctor R G).obj
        (Rep.of (cellularSMulRepresentation (univ : Set E) hcell R n)) ≅
      cellularChainGroup (univ : Set B) (ModuleCat.of R R) n :=
  letI := hp.cwComplexQuotient hcell hfree
  haveI := hp.t2Space_of_cwComplex hcell hfree
  haveI := hp.toContinuousConstSMul
  cellularActionCoinvariantsIso (univ : Set E) (univ : Set B)
    (cellularSMul (univ : Set E) hcell) (isCellular_cellularSMul (univ : Set E) hcell)
    (cellularSMul_one (univ : Set E) hcell) (cellularSMul_mul (univ : Set E) hcell)
    (hp.isCellular_cwComplexQuotient hcell hfree) (hp.cellularSMul_comp_univMap hcell) R
    (exists_orbit_lift hp hcell hfree R n)

/-- Precomposing `IsQuotientCoveringMap.cellularSMulCoinvariantsIso` with the coinvariants quotient
map gives the cellular chain map induced by the orbit covering map. -/
@[reassoc (attr := simp)]
theorem _root_.IsQuotientCoveringMap.coinvariantsMk_comp_cellularSMulCoinvariantsIso_hom (n : ℕ) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    haveI := hp.toContinuousConstSMul
    (Rep.coinvariantsMk R G).app
        (Rep.of (cellularSMulRepresentation (univ : Set E) hcell R n)) ≫
      (hp.cellularSMulCoinvariantsIso hcell hfree R n).hom =
      cellularChainGroupMap (univ : Set E) (univ : Set B)
        (hp.isCellular_cwComplexQuotient hcell hfree) (ModuleCat.of R R) n := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.t2Space_of_cwComplex hcell hfree
  have := hp.toContinuousConstSMul
  exact coinvariantsMk_comp_cellularActionCoinvariantsIso_hom _ _ _ _ _ _ _ _ R _

/-- On coinvariant classes, `IsQuotientCoveringMap.cellularSMulCoinvariantsIso` acts by the
cellular chain map induced by the orbit covering map. -/
-- Match before simplification changes the presentation of the coinvariants carrier.
@[simp↓]
theorem _root_.IsQuotientCoveringMap.cellularSMulCoinvariantsIso_hom_mk (n : ℕ)
    (x : (cellularChainGroup (univ : Set E) (ModuleCat.of R R) n : ModuleCat R)) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    haveI := hp.toContinuousConstSMul
    (hp.cellularSMulCoinvariantsIso hcell hfree R n).hom
        (Representation.Coinvariants.mk
          (cellularSMulRepresentation (univ : Set E) hcell R n) x) =
      cellularChainGroupMap (univ : Set E) (univ : Set B)
        (hp.isCellular_cwComplexQuotient hcell hfree) (ModuleCat.of R R) n x :=
  (rfl)

/-- **The `G`-coinvariants of the cellular chain complex of `E` identify with the cellular chain
complex of the orbit CW complex `B`.** -/
def _root_.IsQuotientCoveringMap.cellularSMulComplexCoinvariantsIso :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    haveI := hp.toContinuousConstSMul
    (((Rep.coinvariantsFunctor R G).mapHomologicalComplex _).obj
      (cellularSMulComplex (univ : Set E) hcell R)) ≅
      cellularChainComplex (univ : Set B) (ModuleCat.of R R) :=
  letI := hp.cwComplexQuotient hcell hfree
  haveI := hp.t2Space_of_cwComplex hcell hfree
  haveI := hp.toContinuousConstSMul
  cellularActionComplexCoinvariantsIso (univ : Set E) (univ : Set B)
    (cellularSMul (univ : Set E) hcell) (isCellular_cellularSMul (univ : Set E) hcell)
    (cellularSMul_one (univ : Set E) hcell) (cellularSMul_mul (univ : Set E) hcell)
    (hp.isCellular_cwComplexQuotient hcell hfree) (hp.cellularSMul_comp_univMap hcell) R
    (exists_orbit_lift hp hcell hfree R)

/-- In degree `n`, `IsQuotientCoveringMap.cellularSMulComplexCoinvariantsIso` is
`IsQuotientCoveringMap.cellularSMulCoinvariantsIso` up to object transports. -/
@[simp]
theorem _root_.IsQuotientCoveringMap.cellularSMulComplexCoinvariantsIso_hom_f (n : ℕ) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    haveI := hp.toContinuousConstSMul
    (hp.cellularSMulComplexCoinvariantsIso hcell hfree R).hom.f n =
      eqToHom (by rw [Functor.mapHomologicalComplex_obj_X, cellularSMulComplex_X]) ≫
        (hp.cellularSMulCoinvariantsIso hcell hfree R n).hom ≫
        eqToHom (cellularChainComplex_X (univ : Set B) (ModuleCat.of R R) n).symm :=
  (rfl)

/-- **The tensor coinvariants `(R ⊗ C_*^{\mathrm{cell}}(E))_G` identify with the cellular chain
complex of the orbit CW complex `B`.** -/
def _root_.IsQuotientCoveringMap.cellularSMulComplexCoinvariantsTensorIso :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    haveI := hp.toContinuousConstSMul
    (cellularSMulComplex (univ : Set E) hcell R).coinvariantsTensorObj (Rep.trivial R G R) ≅
      cellularChainComplex (univ : Set B) (ModuleCat.of R R) :=
  letI := hp.cwComplexQuotient hcell hfree
  haveI := hp.t2Space_of_cwComplex hcell hfree
  haveI := hp.toContinuousConstSMul
  cellularActionComplexCoinvariantsTensorIso (univ : Set E) (univ : Set B)
    (cellularSMul (univ : Set E) hcell) (isCellular_cellularSMul (univ : Set E) hcell)
    (cellularSMul_one (univ : Set E) hcell) (cellularSMul_mul (univ : Set E) hcell)
    (hp.isCellular_cwComplexQuotient hcell hfree) (hp.cellularSMul_comp_univMap hcell) R
    (exists_orbit_lift hp hcell hfree R)

/-- **The cellular homology of the orbit CW complex of a contractible free cellular `G`-space is
group homology.** When `E` is contractible, `TauCeti.freeCellularResolution` resolves
`Rep.trivial R G R` by free `R[G]`-modules whose coinvariants are the cellular chains of `B`. -/
def _root_.IsQuotientCoveringMap.cellularHomologyIsoGroupHomology [ContractibleSpace E] (n : ℕ) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    (cellularChainComplex (univ : Set B) (ModuleCat.of R R)).homology n ≅
      groupHomology (Rep.trivial R G R) n :=
  letI := hp.cwComplexQuotient hcell hfree
  haveI := hp.t2Space_of_cwComplex hcell hfree
  haveI := hp.toContinuousConstSMul
  haveI : ContractibleSpace (univ : Set E) := (Homeomorph.Set.univ E).contractibleSpace
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (hp.cellularSMulComplexCoinvariantsTensorIso hcell hfree R)).symm ≪≫
    (groupHomologyIso (Rep.trivial R G R) n
      (freeCellularResolution (univ : Set E) hcell hfree R)).symm

end OrbitSpace

end TauCeti

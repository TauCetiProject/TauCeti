/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.AlgebraicTopology.Cellular.Map
import TauCeti.AlgebraicTopology.Cellular.LocalDegree

/-!
# Action of cellular maps on cellular basis vectors

Let `f` be a cellular map between relative CW complexes.

* If `f` carries the base into the base and the characteristic map of `i` strictly onto that of `i'`
  (`f ∘ φᵢ = φᵢ'` on the closed unit ball), then on cellular chains it sends the summand of `i` in
  `Hₙ(Xⁿ, Xⁿ⁻¹)` identically onto the summand of `i'`
  (`TauCeti.ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap`), and with coefficients in a
  ring sends the cellular basis vector of `i` to that of `i'` with no sign
  (`TauCeti.cellularChainGroupMap_cellularChainBasis`). Deck transformations of a lifted CW
  structure along a covering map are of this kind.
* More generally, if `f` carries the closed `n`-cell `i` outside an open `n`-cell `k` of the target,
  its image misses the centre of `k` in local homology, so the `k`-coordinate of the image of the
  cellular basis vector of `i` vanishes
  (`TauCeti.cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_notMem_openCell`,
  `TauCeti.cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_ne`). Consequently, a cellular
  map sending the closed `n`-cell `i` into a closed `n`-cell `i'` sends the cellular basis vector of
  `i` to a scalar multiple of that of `i'`
  (`TauCeti.cellularChainGroupMap_cellularChainBasis_eq_smul`).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, cellular maps and cellular homology.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {D : Set X} {E : Set Y} (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]

variable {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **A map carrying the characteristic map of `i` onto that of `i'` sends the summand of `i` in
the cellular chain group onto the summand of `i'`.** -/
@[reassoc]
lemma ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap {n : ℕ}
    [HasExactColimitsOfShape (Discrete (cell C n)) A]
    [HasExactColimitsOfShape (Discrete (cell C' n)) A] {i : cell C n} {i' : cell C' n}
    (hi : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n i x ∈ C,
      (f ⟨map n i x, hx⟩).1 = map n i' x) :
    Sigma.ι (fun _ : cell C n ↦ R) i ≫ (cellularChainGroupIso C R n).inv ≫
        cellularChainGroupMap C C' hf R n =
      Sigma.ι (fun _ : cell C' n ↦ R) i' ≫ (cellularChainGroupIso C' R n).inv := by
  rw [ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
    ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap,
    cellularChainGroupMap_def,
    ← TopPair.singularHomologyMap_comp]
  congr 2
  refine TopPair.hom_ext_of_fst _ (TopCat.hom_ext (ContinuousMap.ext fun p ↦ Subtype.ext ?_))
  -- Both sides send a point of the Euclidean disk to the characteristic map of the respective
  -- cell, evaluated at the radial rescaling of that point.
  simp only [MorphismProperty.Comma.comp_right, skeletonPairMap_fst]
  have hs (q : skeletonObj C (n + 1)) : ((skeletonMap C C' hf (n + 1)) q).1 =
      (f ⟨q.1, (skeletonLT C _).subset_complex q.2⟩).1 :=
    congrArg Subtype.val (skeletonMap_apply C C' hf (n + 1) q)
  have hy : (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph
      ((p : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) ∈ closedBall 0 1 := by
    rw [mem_closedBall_zero_iff, ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff,
      ← mem_closedBall_zero_iff]
    exact (p : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down.2
  have hC : map n i _ ∈ C := closedCell_subset_complex n i ⟨_, hy, rfl⟩
  have key : ∀ (a b : X) (ha : a ∈ C) (hb : b ∈ C), a = b → (f ⟨a, ha⟩).1 = (f ⟨b, hb⟩).1 := by
    rintro a _ _ _ rfl
    rfl
  exact (hs _).trans ((key _ _ _ hC (coe_characteristicCellPairMap_fst_apply C i p)).trans
    ((hi _ hy hC).trans (coe_characteristicCellPairMap_fst_apply C' i' p).symm))

/-- **A map carrying the characteristic map of `i` onto that of `i'` sends the cellular basis
vector of `i` to the cellular basis vector of `i'`**, with coefficients in a ring. -/
lemma cellularChainGroupMap_cellularChainBasis (R : Type w) [Ring R] {n : ℕ} {i : cell C n}
    {i' : cell C' n} (hi : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n i x ∈ C,
      (f ⟨map n i x, hx⟩).1 = map n i' x) :
    cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i) =
      cellularChainBasis C' R n i' := by
  rw [cellularChainBasis_apply, cellularChainBasis_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap C C' hf _ hi]

/-- If a cellular map carries the closed `n`-cell `i` outside the open `n`-cell `k` of the target,
then the `k`-coordinate of the image of the cellular basis vector of `i` vanishes. -/
lemma cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_notMem_openCell (R : Type w) [Ring R]
    {n : ℕ} {i : cell C n} {k : cell C' n}
    (hk : ∀ x ∈ closedCell n i, ∀ hx : x ∈ C, (f ⟨x, hx⟩).1 ∉ openCell n k) :
    (cellularChainBasis C' R n).repr
      (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)) k = 0 := by
  have hy_open : map n k (0 : Fin n → ℝ) ∈ openCell n k := map_zero_mem_openCell n k
  have hy_skel : map n k (0 : Fin n → ℝ) ∈ (skeletonLT C' ((n + 1 : ℕ) : ℕ∞) : Set Y) := by
    exact_mod_cast openCell_subset_skeletonLT n k hy_open
  let x' : skeletonObj C' (n + 1) := ⟨map n k 0, hy_skel⟩
  have hx' : (x' : Y) ∈ openCell n k := hy_open
  -- Read off the `k`-coordinate in local homology at the centre `x'` of `openCell n k`.
  rw [cellularChainBasis_repr_eq_inv_cellLocalClass C' R x' hx']
  -- The image of the characteristic disk of `i` misses `x'`, so the pair map from `(Dⁿ, ∂Dⁿ)` into
  -- `(X'ⁿ, X'ⁿ ∖ {x'})` factors through `X'ⁿ ∖ {x'}` and vanishes on relative homology.
  have hmiss : ∀ z : TopCat.disk.{w} n,
      (TopPair.Hom.fst (characteristicCellPairMap C i ≫ skeletonPairMap C C' hf n) z :
        skeletonObj C' (n + 1)) ≠ x' := by
    intro z hz
    have hmem_closed : (cellDiskHom i z : X) ∈ closedCell n i := by
      rw [coe_cellDiskHom_apply]
      exact ⟨_, (diskHomeomorphClosedBall n z).2, rfl⟩
    have hmem_C : (cellDiskHom i z : X) ∈ C :=
      closedCell_subset_complex n i hmem_closed
    have hs : (x' : Y) = (f ⟨(cellDiskHom i z : X), hmem_C⟩).1 := by
      rw [← hz]
      simp only [TopPair.Hom.fst_comp, characteristicCellPairMap_fst, skeletonPairMap_fst]
      exact congrArg Subtype.val (skeletonMap_apply C C' hf (n + 1) (cellDiskHom i z))
    exact hk _ hmem_closed hmem_C (hs ▸ hx')
  have hv_eq : TopPair.singularHomologyMap
      (skeletonPairToComplSingleton C' x' (notMem_skeletonLT_of_mem_openCell n hx'))
      (ModuleCat.of R R) n
      (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)) =
      ((singularHomologyDiskBoundaryPairIso (ModuleCat.of R R) n).inv ≫
        TopPair.singularHomologyMap
          (characteristicCellPairMap C i ≫ skeletonPairMap C C' hf n ≫
            skeletonPairToComplSingleton C' x' (notMem_skeletonLT_of_mem_openCell n hx'))
          (ModuleCat.of R R) n) 1 := by
    simp only [cellularChainBasis_apply, cellularChainGroupMap_def]
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
  exact map_zero _

/-- If a cellular map carries the closed `n`-cell `i` into the closed `n`-cell `i'`, then for any
other `n`-cell `k ≠ i'` of the target, the `k`-coordinate of the image of the cellular basis vector
of `i` vanishes. -/
lemma cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_ne (R : Type w) [Ring R] {n : ℕ}
    {i : cell C n} {i' k : cell C' n}
    (hi : ∀ x ∈ closedCell n i, ∀ hx : x ∈ C, (f ⟨x, hx⟩).1 ∈ closedCell n i') (hk : k ≠ i') :
    (cellularChainBasis C' R n).repr
      (cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i)) k = 0 :=
  cellularChainBasis_repr_cellularChainGroupMap_eq_zero_of_notMem_openCell C C' hf R
    fun x hx hxC ↦ (disjoint_closedCell_openCell_of_ne n le_rfl
      (fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.1 h).2).symm)).notMem_of_mem_left (hi x hx hxC)

/-- **A cellular map sending the closed `n`-cell `i` into the closed `n`-cell `i'` sends the
cellular basis vector of `i` to a scalar multiple of the cellular basis vector of `i'`.** -/
theorem cellularChainGroupMap_cellularChainBasis_eq_smul (R : Type w) [Ring R] {n : ℕ}
    {i : cell C n} {i' : cell C' n}
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

end TauCeti

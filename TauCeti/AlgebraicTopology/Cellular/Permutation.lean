/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.AlgebraicTopology.Cellular.Map

/-!
# Maps carrying characteristic maps to characteristic maps act on cells

Let `f` be a map between relative CW complexes that carries the base into the base and the
characteristic map of every cell onto the characteristic map of a cell of the same dimension:
`f ∘ φᵢ = φᵢ'` on the closed unit ball. Such a map is cellular
(`TauCeti.isCellular_of_map_eq`, in `TauCeti.Topology.CWComplex.Classical.Map`), and on cellular
chains it relabels the cells: the summand of the cell `i` in the cellular chain group
`Hₙ(Xⁿ, Xⁿ⁻¹)` is sent identically onto the summand of `i'`
(`TauCeti.ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap`). With coefficients in a ring
this says that `f` sends each cellular basis vector to a cellular basis vector, with no sign
(`TauCeti.cellularChainGroupMap_cellularChainBasis`).

The deck transformations of the lift of a CW structure along a covering map are maps of this kind,
which is how the cellular chains of a free `G`-CW complex become modules over the group ring.
A map that only carries open cells onto open cells acts on the basis up to the local degrees
`±1` of the induced self-maps of the cells; the strict compatibility assumed here excludes signs.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, cellular maps and cellular homology.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Topology Topology.RelCWComplex

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

end TauCeti

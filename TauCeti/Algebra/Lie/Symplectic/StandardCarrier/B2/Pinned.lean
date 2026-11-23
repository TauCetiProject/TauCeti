/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Basic
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
import TauCeti.Algebra.Lie.Symplectic.Coordinates
import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.LieGeneration
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# The pinned type-B₂ algebra as four-by-four symplectic matrices

The rank-two symplectic Lie algebra `sp₄` cannot be instantiated at `TauCeti.SpStd.pinnedLieEquiv`
because `TauCeti.DynkinType.C 2` is excluded by `TauCeti.DynkinType.Valid` in favor of
`TauCeti.DynkinType.B 2`. In Bourbaki numbering, node `0` of `B₂` is long and node `1` is short,
whereas `TauCeti.SpStd` at `n = 1` numbers node `0` as short and node `1` as long.

`TauCeti.lengthPermRankTwo` exchanges those two Bourbaki nodes, and
`TauCeti.SpStd.b2PinnedLieEquiv` identifies the independently constructed rational Lie algebra of
type `B 2` with `sp (Fin 2) ℚ`, matching the Cartan, raising, and lowering generators across
`lengthPermRankTwo`. Thus the four-dimensional symplectic module and its standard integral
coordinate lattice become a representation of the pinned `B₂` algebra.

The construction applies `IsSerreSystem.submatrix` along `lengthPermRankTwo` to
`TauCeti.SpStd.isSerreSystem_rootGenerator 1`, rewrites the reindexed Cartan matrix via
`TauCeti.DynkinType.cartanMatrix_C_two_apply_eq_cartanMatrix_B_two`, and invokes
`TauCeti.DynkinType.lieEquivOfIsSerreSystem` using
`TauCeti.SpStd.lieSpan_range_rootGenerator_eq_top` and the dimension count `2 + 8 = 10`. This is a
rational Lie-algebra comparison; it does not assert an identification of group schemes or of their
points.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plates II and III.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, appendix.

The Serre-lift isomorphism construction, dimension-count bijectivity proof, and generator equations
adapt `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Pinned`.
-/

public section

namespace TauCeti.SpStd

open _root_.LieAlgebra.Symplectic

noncomputable section

private abbrev validB2 : (DynkinType.B 2).Valid := DynkinType.valid_B.mpr le_rfl

private theorem isSerreSystem_b2 :
    IsSerreSystem ℚ (DynkinType.B 2).cartanMatrix.transpose
      (fun i => cartanGenerator 1 (lengthPermRankTwo i))
      (fun i => rootGenerator 1 (.inl (lengthPermRankTwo i)))
      (fun i => rootGenerator 1 (.inr (lengthPermRankTwo i))) := by
  have h1 : IsSerreSystem ℚ (CartanMatrix.C 2).transpose
      (fun i : Fin 2 => cartanGenerator 1 i)
      (fun i : Fin 2 => rootGenerator 1 (.inl i))
      (fun i : Fin 2 => rootGenerator 1 (.inr i)) :=
    isSerreSystem_rootGenerator 1
  have h := h1.submatrix (f := lengthPermRankTwo) lengthPermRankTwo.injective
  have hCM : (CartanMatrix.C 2).transpose.submatrix lengthPermRankTwo lengthPermRankTwo =
      (CartanMatrix.B 2).transpose := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.transpose_apply]
    have hC := DynkinType.cartanMatrix_C_two_apply_eq_cartanMatrix_B_two
      (lengthPermRankTwo j) (lengthPermRankTwo i)
    rw [DynkinType.cartanMatrix_C, DynkinType.cartanMatrix_B] at hC
    exact hC.trans (by fin_cases i <;> fin_cases j <;> simp)
  simpa only [DynkinType.cartanMatrix_B, DynkinType.rank_B, hCM, Function.comp_def] using h

private theorem lieSpan_b2 :
    LieSubalgebra.lieSpan ℚ (sp (Fin 2) ℚ)
      (Set.range (fun i : Fin (DynkinType.B 2).rank =>
          rootGenerator 1 (.inl (lengthPermRankTwo i))) ∪
        Set.range (fun i : Fin (DynkinType.B 2).rank =>
          rootGenerator 1 (.inr (lengthPermRankTwo i)))) = ⊤ := by
  simp only [DynkinType.rank_B]
  have hpos : Set.range (fun i : Fin 2 => rootGenerator 1 (.inl (lengthPermRankTwo i))) =
      Set.range (fun i : Fin 2 => rootGenerator 1 (.inl i)) :=
    lengthPermRankTwo.surjective.range_comp (fun i => rootGenerator 1 (.inl i))
  have hneg : Set.range (fun i : Fin 2 => rootGenerator 1 (.inr (lengthPermRankTwo i))) =
      Set.range (fun i : Fin 2 => rootGenerator 1 (.inr i)) :=
    lengthPermRankTwo.surjective.range_comp (fun i => rootGenerator 1 (.inr i))
  rw [hpos, hneg]
  have htop :
      LieSubalgebra.lieSpan ℚ (sp (Fin 2) ℚ)
        (Set.range (fun k : Fin 2 ⊕ Fin 2 => rootGenerator 1 k)) = ⊤ :=
    lieSpan_range_rootGenerator_eq_top 1
  simpa only [Sum.range_eq, Function.comp_def] using htop

private theorem finrank_sp_two :
    Module.finrank ℚ (sp (Fin 2) ℚ) = (DynkinType.B 2).rank + (DynkinType.B 2).numRoots := by
  rw [TauCeti.LieAlgebra.Symplectic.finrank_sp, Fintype.card_fin,
    DynkinType.rank_B, DynkinType.numRoots_B]
  norm_num

/-- **The pinned rational type-`B₂` Lie algebra is the four-by-four symplectic Lie algebra**, with
the Cartan and positive and negative simple-root generators matched across
`TauCeti.lengthPermRankTwo`. -/
def b2PinnedLieEquiv :
    (DynkinType.B 2).lieAlgebra (DynkinType.valid_B.mpr le_rfl) ≃ₗ⁅ℚ⁆ sp (Fin 2) ℚ :=
  (DynkinType.B 2).lieEquivOfIsSerreSystem validB2 isSerreSystem_b2 lieSpan_b2 finrank_sp_two

/-- The comparison sends each pinned `B₂` Cartan generator to the standard simple coroot at the
swapped symplectic node. -/
@[simp]
theorem b2PinnedLieEquiv_lieBasis_h {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedLieEquiv (((DynkinType.B 2).lieBasis ht).h i) =
      cartanGenerator 1 (lengthPermRankTwo i) := by
  obtain rfl : ht = validB2 := Subsingleton.elim _ _
  exact (DynkinType.B 2).lieEquivOfIsSerreSystem_lieBasis_h validB2 isSerreSystem_b2 lieSpan_b2
    finrank_sp_two i

/-- The comparison sends each pinned `B₂` raising generator to the standard positive simple root at
the swapped symplectic node. -/
@[simp]
theorem b2PinnedLieEquiv_lieBasis_e {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedLieEquiv (((DynkinType.B 2).lieBasis ht).e i) =
      rootGenerator 1 (.inl (lengthPermRankTwo i)) := by
  obtain rfl : ht = validB2 := Subsingleton.elim _ _
  exact (DynkinType.B 2).lieEquivOfIsSerreSystem_lieBasis_e validB2 isSerreSystem_b2 lieSpan_b2
    finrank_sp_two i

/-- The comparison sends each pinned `B₂` lowering generator to the standard negative simple root
at the swapped symplectic node. -/
@[simp]
theorem b2PinnedLieEquiv_lieBasis_f {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedLieEquiv (((DynkinType.B 2).lieBasis ht).f i) =
      rootGenerator 1 (.inr (lengthPermRankTwo i)) := by
  obtain rfl : ht = validB2 := Subsingleton.elim _ _
  exact (DynkinType.B 2).lieEquivOfIsSerreSystem_lieBasis_f validB2 isSerreSystem_b2 lieSpan_b2
    finrank_sp_two i

/-- On the signed simple-root family, the comparison acts by `TauCeti.lengthPermRankTwo` on both
signs. -/
@[simp↓]
theorem b2PinnedLieEquiv_lieBasis_rootGenerator {ht : (DynkinType.B 2).Valid}
    (k : Fin (DynkinType.B 2).rank ⊕ Fin (DynkinType.B 2).rank) :
    b2PinnedLieEquiv (((DynkinType.B 2).lieBasis ht).rootGenerator k) =
      rootGenerator 1 (Sum.map lengthPermRankTwo lengthPermRankTwo k) := by
  cases k with
  | inl i => exact (congrArg b2PinnedLieEquiv
      (LieAlgebra.Basis.rootGenerator_inl _ i)).trans (b2PinnedLieEquiv_lieBasis_e i)
  | inr i => exact (congrArg b2PinnedLieEquiv
      (LieAlgebra.Basis.rootGenerator_inr _ i)).trans (b2PinnedLieEquiv_lieBasis_f i)

/-- The inverse comparison sends each standard symplectic simple coroot to the pinned `B₂` Cartan
generator at the swapped node. -/
@[simp]
theorem b2PinnedLieEquiv_symm_cartanGenerator (i : Fin 2) :
    b2PinnedLieEquiv.symm (cartanGenerator 1 i) =
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).h (lengthPermRankTwo i) := by
  rw [LieEquiv.symm_apply_eq, b2PinnedLieEquiv_lieBasis_h (lengthPermRankTwo i),
    lengthPermRankTwo_lengthPermRankTwo]

/-- The inverse comparison sends each standard positive simple root to the pinned `B₂` raising
generator at the swapped node. -/
@[simp]
theorem b2PinnedLieEquiv_symm_rootGenerator_inl (i : Fin 2) :
    b2PinnedLieEquiv.symm (rootGenerator 1 (.inl i)) =
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).e (lengthPermRankTwo i) := by
  rw [LieEquiv.symm_apply_eq, b2PinnedLieEquiv_lieBasis_e (lengthPermRankTwo i),
    lengthPermRankTwo_lengthPermRankTwo]

/-- The inverse comparison sends each standard negative simple root to the pinned `B₂` lowering
generator at the swapped node. -/
@[simp]
theorem b2PinnedLieEquiv_symm_rootGenerator_inr (i : Fin 2) :
    b2PinnedLieEquiv.symm (rootGenerator 1 (.inr i)) =
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).f (lengthPermRankTwo i) := by
  rw [LieEquiv.symm_apply_eq, b2PinnedLieEquiv_lieBasis_f (lengthPermRankTwo i),
    lengthPermRankTwo_lengthPermRankTwo]

/-- The inverse comparison sends the signed simple-root family of `sp₄` to the pinned `B₂` signed
simple-root family reindexed by `lengthPermRankTwo`. -/
theorem b2PinnedLieEquiv_symm_rootGenerator (k : Fin 2 ⊕ Fin 2) :
    b2PinnedLieEquiv.symm (rootGenerator 1 k) =
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).rootGenerator
        (Sum.map lengthPermRankTwo lengthPermRankTwo k) := by
  cases k with
  | inl i =>
      exact (b2PinnedLieEquiv_symm_rootGenerator_inl i).trans
        (LieAlgebra.Basis.rootGenerator_inl _ (lengthPermRankTwo i)).symm
  | inr i =>
      exact (b2PinnedLieEquiv_symm_rootGenerator_inr i).trans
        (LieAlgebra.Basis.rootGenerator_inr _ (lengthPermRankTwo i)).symm

end

end TauCeti.SpStd

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.LieGeneration
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Basis
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Symplectic.Coordinates

/-!
# The pinned type-C algebra on the standard symplectic module

`TauCeti.SpStd.pinnedLieEquiv` identifies the independently constructed rational Lie algebra
of type C with the native symplectic matrix Lie algebra. It matches the Cartan generators and
both signs of the simple-root generators in Bourbaki order, including the terminal long root.
Thus the standard symplectic representation can be read as a faithful representation of the
pinned algebra, with the same operators on its integral lattice.

The construction applies `TauCeti.DynkinType.lieEquivOfIsSerreSystem` to
`SpStd.isSerreSystem_rootGenerator`, `SpStd.lieSpan_range_rootGenerator_eq_top`, and the
native matrix-entry dimension `TauCeti.LieAlgebra.Symplectic.finrank_sp`. This is a
Lie-algebra comparison, not an identification of group schemes or of their points.

## References

* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, appendix.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plate III.
-/

public section

namespace TauCeti.SpStd

open _root_.LieAlgebra.Symplectic

noncomputable section

variable (n : ℕ) (ht : (DynkinType.C (n + 1)).Valid)

private theorem isSerreSystem_pinned :
    IsSerreSystem ℚ (DynkinType.C (n + 1)).cartanMatrix.transpose
      (cartanGenerator n) (fun i => rootGenerator n (.inl i))
      (fun i => rootGenerator n (.inr i)) := by
  simpa only [DynkinType.cartanMatrix_C, DynkinType.rank_C] using
    isSerreSystem_rootGenerator n

private theorem lieSpan_pinned :
    LieSubalgebra.lieSpan ℚ (sp (Fin (n + 1)) ℚ)
      (Set.range (fun i : Fin (DynkinType.C (n + 1)).rank => rootGenerator n (.inl i)) ∪
        Set.range (fun i : Fin (DynkinType.C (n + 1)).rank => rootGenerator n (.inr i))) = ⊤ := by
  simpa only [DynkinType.rank_C, Sum.range_eq, Function.comp_def] using
    lieSpan_range_rootGenerator_eq_top n

private theorem finrank_sp_eq_rank_add_numRoots :
    Module.finrank ℚ (sp (Fin (n + 1)) ℚ) =
      (DynkinType.C (n + 1)).rank + (DynkinType.C (n + 1)).numRoots := by
  rw [TauCeti.LieAlgebra.Symplectic.finrank_sp, Fintype.card_fin,
    DynkinType.rank_C, DynkinType.numRoots_C]
  ring

/-- The pinned rational type-C Lie algebra is the native symplectic Lie algebra, with the
numbered Cartan and positive and negative simple-root generators matched. -/
def pinnedLieEquiv :
    (DynkinType.C (n + 1)).lieAlgebra ht ≃ₗ⁅ℚ⁆ sp (Fin (n + 1)) ℚ :=
  (DynkinType.C (n + 1)).lieEquivOfIsSerreSystem ht (isSerreSystem_pinned n)
    (lieSpan_pinned n) (finrank_sp_eq_rank_add_numRoots n)

/-- The comparison sends each pinned Cartan generator to the standard simple coroot. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_h (i : Fin (n + 1)) :
    pinnedLieEquiv n ht (((DynkinType.C (n + 1)).lieBasis ht).h i) =
      cartanGenerator n i :=
  (DynkinType.C (n + 1)).lieEquivOfIsSerreSystem_lieBasis_h ht (isSerreSystem_pinned n)
    (lieSpan_pinned n) (finrank_sp_eq_rank_add_numRoots n) i

/-- The comparison sends each pinned raising generator to the standard positive simple root. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_e (i : Fin (n + 1)) :
    pinnedLieEquiv n ht (((DynkinType.C (n + 1)).lieBasis ht).e i) =
      rootGenerator n (.inl i) :=
  (DynkinType.C (n + 1)).lieEquivOfIsSerreSystem_lieBasis_e ht (isSerreSystem_pinned n)
    (lieSpan_pinned n) (finrank_sp_eq_rank_add_numRoots n) i

/-- The comparison sends each pinned lowering generator to the standard negative simple root. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_f (i : Fin (n + 1)) :
    pinnedLieEquiv n ht (((DynkinType.C (n + 1)).lieBasis ht).f i) =
      rootGenerator n (.inr i) :=
  (DynkinType.C (n + 1)).lieEquivOfIsSerreSystem_lieBasis_f ht (isSerreSystem_pinned n)
    (lieSpan_pinned n) (finrank_sp_eq_rank_add_numRoots n) i

/-- The comparison sends each pinned signed simple-root generator to the standard signed
simple-root generator with the same number. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_rootGenerator
    (k : Fin (DynkinType.C (n + 1)).rank ⊕ Fin (DynkinType.C (n + 1)).rank) :
    pinnedLieEquiv n ht (((DynkinType.C (n + 1)).lieBasis ht).rootGenerator k) =
      rootGenerator n k := by
  cases k with
  | inl i => exact (congrArg (pinnedLieEquiv n ht)
      (LieAlgebra.Basis.rootGenerator_inl _ i)).trans (pinnedLieEquiv_lieBasis_e n ht i)
  | inr i => exact (congrArg (pinnedLieEquiv n ht)
      (LieAlgebra.Basis.rootGenerator_inr _ i)).trans (pinnedLieEquiv_lieBasis_f n ht i)

/-- The inverse comparison recovers each numbered pinned Cartan generator. -/
@[simp]
theorem pinnedLieEquiv_symm_cartanGenerator (i : Fin (n + 1)) :
    (pinnedLieEquiv n ht).symm (cartanGenerator n i) =
      ((DynkinType.C (n + 1)).lieBasis ht).h i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_h]

/-- The inverse comparison recovers each numbered pinned raising generator. -/
@[simp]
theorem pinnedLieEquiv_symm_rootGenerator_inl (i : Fin (n + 1)) :
    (pinnedLieEquiv n ht).symm (rootGenerator n (.inl i)) =
      ((DynkinType.C (n + 1)).lieBasis ht).e i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_e]

/-- The inverse comparison recovers each numbered pinned lowering generator. -/
@[simp]
theorem pinnedLieEquiv_symm_rootGenerator_inr (i : Fin (n + 1)) :
    (pinnedLieEquiv n ht).symm (rootGenerator n (.inr i)) =
      ((DynkinType.C (n + 1)).lieBasis ht).f i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_f]

end

end TauCeti.SpStd

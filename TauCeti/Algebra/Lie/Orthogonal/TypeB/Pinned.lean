/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Basis
import TauCeti.Algebra.Lie.Orthogonal.TypeB.Killing
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# The pinned type-B Lie algebra as split odd orthogonal matrices

The rational pinned Lie algebra of type `B` and the native split odd orthogonal matrix Lie
algebra have the same numbered Serre presentation. This file identifies them, preserving the
Cartan, raising and lowering generators in Bourbaki order, including the terminal short root.
The inverse equations retain that pinning as well.

This identification allows representations of the native orthogonal algebra, in particular its
spin representation and admissible lattice, to be read as representations of the independently
pinned Lie algebra. It does not assert a comparison of the associated group schemes.

The construction uses `TauCeti.typeBLieBasis`, its nondegenerate Killing form, and
`TauCeti.DynkinType.lieEquivOfBasis`; injectivity is the existing Serre theorem for a Lie basis,
not a dimension assumption or a choice of a matrix realization.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4–6, Plate II.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, appendix.
-/

public section

open scoped Matrix

namespace TauCeti

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

/-- The independently pinned rational type-`Bₙ₊₁` Lie algebra is the split odd orthogonal
matrix Lie algebra, with the same numbered Cartan, raising and lowering generators. -/
def typeBPinnedLieEquiv (ht : (DynkinType.B (n + 1)).Valid) :
    (DynkinType.B (n + 1)).lieAlgebra ht ≃ₗ⁅ℚ⁆
      LieAlgebra.Orthogonal.typeB (Fin (n + 1)) ℚ :=
  (DynkinType.B (n + 1)).lieEquivOfBasis ht (typeBLieBasis (K := ℚ) n) (by simp)

variable (ht : (DynkinType.B (n + 1)).Valid)

/-- The pinned Cartan generator maps to the native simple coroot matrix. -/
@[simp]
theorem typeBPinnedLieEquiv_lieBasis_h (i : Fin (n + 1)) :
    typeBPinnedLieEquiv n ht (((DynkinType.B (n + 1)).lieBasis ht).h i) =
      typeBSimpleCorootGenerator i := by
  simpa only [typeBPinnedLieEquiv, typeBLieBasis_h] using
    (DynkinType.B (n + 1)).lieEquivOfBasis_lieBasis_h ht (typeBLieBasis (K := ℚ) n)
      (by simp) i

/-- The pinned raising generator maps to the native positive simple-root matrix. -/
@[simp]
theorem typeBPinnedLieEquiv_lieBasis_e (i : Fin (n + 1)) :
    typeBPinnedLieEquiv n ht (((DynkinType.B (n + 1)).lieBasis ht).e i) =
      typeBSimpleRootGenerator i := by
  simpa only [typeBPinnedLieEquiv, typeBLieBasis_e] using
    (DynkinType.B (n + 1)).lieEquivOfBasis_lieBasis_e ht (typeBLieBasis (K := ℚ) n)
      (by simp) i

/-- The pinned lowering generator maps to the native negative simple-root matrix. -/
@[simp]
theorem typeBPinnedLieEquiv_lieBasis_f (i : Fin (n + 1)) :
    typeBPinnedLieEquiv n ht (((DynkinType.B (n + 1)).lieBasis ht).f i) =
      typeBSimpleNegativeRootGenerator i := by
  simpa only [typeBPinnedLieEquiv, typeBLieBasis_f] using
    (DynkinType.B (n + 1)).lieEquivOfBasis_lieBasis_f ht (typeBLieBasis (K := ℚ) n)
      (by simp) i

/-- The inverse identification preserves each numbered simple coroot. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBSimpleCorootGenerator (i : Fin (n + 1)) :
    (typeBPinnedLieEquiv n ht).symm (typeBSimpleCorootGenerator i) =
      ((DynkinType.B (n + 1)).lieBasis ht).h i := by
  rw [LieEquiv.symm_apply_eq, typeBPinnedLieEquiv_lieBasis_h]

/-- The inverse identification preserves each numbered positive simple root. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBSimpleRootGenerator (i : Fin (n + 1)) :
    (typeBPinnedLieEquiv n ht).symm (typeBSimpleRootGenerator i) =
      ((DynkinType.B (n + 1)).lieBasis ht).e i := by
  rw [LieEquiv.symm_apply_eq, typeBPinnedLieEquiv_lieBasis_e]

/-- The inverse identification preserves each numbered negative simple root. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBSimpleNegativeRootGenerator (i : Fin (n + 1)) :
    (typeBPinnedLieEquiv n ht).symm (typeBSimpleNegativeRootGenerator i) =
      ((DynkinType.B (n + 1)).lieBasis ht).f i := by
  rw [LieEquiv.symm_apply_eq, typeBPinnedLieEquiv_lieBasis_f]

/-- The inverse identification sends the terminal short coroot to the pinned Cartan generator. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBShortCorootGenerator_last :
    (typeBPinnedLieEquiv n ht).symm (typeBShortCorootGenerator (Fin.last n)) =
      ((DynkinType.B (n + 1)).lieBasis ht).h (Fin.last n) := by
  simpa only [typeBSimpleCorootGenerator_last] using
    typeBPinnedLieEquiv_symm_typeBSimpleCorootGenerator n ht (Fin.last n)

/-- The inverse identification sends the terminal short root to the pinned raising generator. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBShortRootGenerator_last :
    (typeBPinnedLieEquiv n ht).symm (typeBShortRootGenerator (Fin.last n)) =
      ((DynkinType.B (n + 1)).lieBasis ht).e (Fin.last n) := by
  simpa only [typeBSimpleRootGenerator_last] using
    typeBPinnedLieEquiv_symm_typeBSimpleRootGenerator n ht (Fin.last n)

/-- The inverse identification sends the negative terminal short root to the pinned lowering
 generator. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBShortNegativeRootGenerator_last :
    (typeBPinnedLieEquiv n ht).symm (typeBShortNegativeRootGenerator (Fin.last n)) =
      ((DynkinType.B (n + 1)).lieBasis ht).f (Fin.last n) := by
  simpa only [typeBSimpleNegativeRootGenerator_last] using
    typeBPinnedLieEquiv_symm_typeBSimpleNegativeRootGenerator n ht (Fin.last n)

/-- The inverse identification sends an adjacent difference coroot to its pinned Cartan
 generator. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBDifferenceCorootGenerator_castSucc_succ
    (j : Fin n) (h : j.castSucc ≠ j.succ) :
    (typeBPinnedLieEquiv n ht).symm (typeBDifferenceCorootGenerator j.castSucc j.succ h) =
      ((DynkinType.B (n + 1)).lieBasis ht).h j.castSucc := by
  simpa only [typeBSimpleCorootGenerator_castSucc] using
    typeBPinnedLieEquiv_symm_typeBSimpleCorootGenerator n ht j.castSucc

/-- The inverse identification sends an adjacent difference root to its pinned raising
 generator. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBDifferenceRootGenerator_castSucc_succ
    (j : Fin n) (h : j.castSucc ≠ j.succ) :
    (typeBPinnedLieEquiv n ht).symm (typeBDifferenceRootGenerator j.castSucc j.succ h) =
      ((DynkinType.B (n + 1)).lieBasis ht).e j.castSucc := by
  simpa only [typeBSimpleRootGenerator_castSucc] using
    typeBPinnedLieEquiv_symm_typeBSimpleRootGenerator n ht j.castSucc

/-- The inverse identification sends a negative adjacent difference root to its pinned lowering
 generator. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_typeBDifferenceRootGenerator_succ_castSucc
    (j : Fin n) (h : j.succ ≠ j.castSucc) :
    (typeBPinnedLieEquiv n ht).symm (typeBDifferenceRootGenerator j.succ j.castSucc h) =
      ((DynkinType.B (n + 1)).lieBasis ht).f j.castSucc := by
  simpa only [typeBSimpleNegativeRootGenerator_castSucc] using
    typeBPinnedLieEquiv_symm_typeBSimpleNegativeRootGenerator n ht j.castSucc

end

end TauCeti

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

end

end TauCeti

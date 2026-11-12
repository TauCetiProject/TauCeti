/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Basis
import TauCeti.Algebra.Lie.Orthogonal.TypeB.Killing
import TauCeti.Algebra.Lie.Presentation.Serre.Injective
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
`TauCeti.DynkinType.serreLiftEquiv`; injectivity is the existing Serre theorem for a Lie basis,
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

private theorem typeBSerreSystem :
    IsSerreSystem ℚ (DynkinType.B (n + 1)).cartanMatrixᵀ
      (typeBLieBasis (K := ℚ) n).h (typeBLieBasis (K := ℚ) n).e
      (typeBLieBasis (K := ℚ) n).f := by
  rw [DynkinType.cartanMatrix_B, ← typeBLieBasis_A (K := ℚ) n]
  exact isSerreSystem_lieBasis (typeBLieBasis (K := ℚ) n)

private def typeBSerreEquiv :
    (DynkinType.B (n + 1)).SerreLieAlgebra ≃ₗ⁅ℚ⁆
      LieAlgebra.Orthogonal.typeB (Fin (n + 1)) ℚ := by
  let b := typeBLieBasis (K := ℚ) n
  have hS := typeBSerreSystem n
  -- Transport the Serre theorem at the matrix, keeping the target algebra and its generators
  -- fixed. This avoids casting the whole equivalence between different presentations.
  have hi : ∀ {CM : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ}, b.Aᵀ = CM →
      ∀ h : IsSerreSystem ℚ CM b.h b.e b.f, Function.Injective (serreLift h) := by
    rintro _ rfl _
    exact b.serreLift_injective
  exact LieEquiv.ofBijective (serreLift hS)
    ⟨hi (by simp [b]) hS, serreLift_surjective hS b.span_ef⟩

private theorem coe_typeBSerreEquiv :
    ⇑(typeBSerreEquiv n) = serreLift (typeBSerreSystem n) := by
  rfl

private theorem typeBSerreEquiv_h (i : Fin (n + 1)) :
    typeBSerreEquiv n (serreH ℚ (DynkinType.B (n + 1)).cartanMatrixᵀ i) =
      typeBSimpleCorootGenerator i := by
  rw [coe_typeBSerreEquiv]
  simpa only [typeBLieBasis_h] using
    serreLift_serreH (typeBSerreSystem n) i

private theorem typeBSerreEquiv_e (i : Fin (n + 1)) :
    typeBSerreEquiv n (serreE ℚ (DynkinType.B (n + 1)).cartanMatrixᵀ i) =
      typeBSimpleRootGenerator i := by
  rw [coe_typeBSerreEquiv]
  simpa only [typeBLieBasis_e] using
    serreLift_serreE (typeBSerreSystem n) i

private theorem typeBSerreEquiv_f (i : Fin (n + 1)) :
    typeBSerreEquiv n (serreF ℚ (DynkinType.B (n + 1)).cartanMatrixᵀ i) =
      typeBSimpleNegativeRootGenerator i := by
  rw [coe_typeBSerreEquiv]
  simpa only [typeBLieBasis_f] using
    serreLift_serreF (typeBSerreSystem n) i

/-- The independently pinned rational type-`Bₙ₊₁` Lie algebra is the split odd orthogonal
matrix Lie algebra, with the same numbered Cartan, raising and lowering generators. -/
def typeBPinnedLieEquiv (ht : (DynkinType.B (n + 1)).Valid) :
    (DynkinType.B (n + 1)).lieAlgebra ht ≃ₗ⁅ℚ⁆
      LieAlgebra.Orthogonal.typeB (Fin (n + 1)) ℚ :=
  ((DynkinType.B (n + 1)).serreLiftEquiv ht).symm.trans (typeBSerreEquiv n)

variable (ht : (DynkinType.B (n + 1)).Valid)

/-- The pinned Cartan generator maps to the native simple coroot matrix. -/
@[simp]
theorem typeBPinnedLieEquiv_h (i : Fin (n + 1)) :
    typeBPinnedLieEquiv n ht (((DynkinType.B (n + 1)).lieBasis ht).h i) =
      typeBSimpleCorootGenerator i := by
  exact (congrArg (typeBSerreEquiv n)
    ((DynkinType.B (n + 1)).serreLiftEquiv_symm_lieBasis_h ht i)).trans
      (typeBSerreEquiv_h n i)

/-- The pinned raising generator maps to the native positive simple-root matrix. -/
@[simp]
theorem typeBPinnedLieEquiv_e (i : Fin (n + 1)) :
    typeBPinnedLieEquiv n ht (((DynkinType.B (n + 1)).lieBasis ht).e i) =
      typeBSimpleRootGenerator i := by
  exact (congrArg (typeBSerreEquiv n)
    ((DynkinType.B (n + 1)).serreLiftEquiv_symm_lieBasis_e ht i)).trans
      (typeBSerreEquiv_e n i)

/-- The pinned lowering generator maps to the native negative simple-root matrix. -/
@[simp]
theorem typeBPinnedLieEquiv_f (i : Fin (n + 1)) :
    typeBPinnedLieEquiv n ht (((DynkinType.B (n + 1)).lieBasis ht).f i) =
      typeBSimpleNegativeRootGenerator i := by
  exact (congrArg (typeBSerreEquiv n)
    ((DynkinType.B (n + 1)).serreLiftEquiv_symm_lieBasis_f ht i)).trans
      (typeBSerreEquiv_f n i)

/-- The inverse identification preserves each numbered simple coroot. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_h (i : Fin (n + 1)) :
    (typeBPinnedLieEquiv n ht).symm (typeBSimpleCorootGenerator i) =
      ((DynkinType.B (n + 1)).lieBasis ht).h i := by
  rw [LieEquiv.symm_apply_eq, typeBPinnedLieEquiv_h]

/-- The inverse identification preserves each numbered positive simple root. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_e (i : Fin (n + 1)) :
    (typeBPinnedLieEquiv n ht).symm (typeBSimpleRootGenerator i) =
      ((DynkinType.B (n + 1)).lieBasis ht).e i := by
  rw [LieEquiv.symm_apply_eq, typeBPinnedLieEquiv_e]

/-- The inverse identification preserves each numbered negative simple root. -/
@[simp]
theorem typeBPinnedLieEquiv_symm_f (i : Fin (n + 1)) :
    (typeBPinnedLieEquiv n ht).symm (typeBSimpleNegativeRootGenerator i) =
      ((DynkinType.B (n + 1)).lieBasis ht).f i := by
  rw [LieEquiv.symm_apply_eq, typeBPinnedLieEquiv_f]

end

end TauCeti

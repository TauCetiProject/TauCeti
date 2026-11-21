/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Contraction
public import TauCeti.Analysis.InnerProductSpace.ProdL2

/-!
# The unitary dilation of a self-adjoint contraction

For an operator `F` on a complex Hilbert space `H`, the doubling operator
`ContinuousLinearMap.doublingOperator F` is the block operator
`[[F, √(1 - F²)], [√(1 - F²), -F]]` on the Hilbert direct sum `H ⊕ H`, whose upper left corner is
`F` (`ContinuousLinearMap.fstL_comp_doublingOperator_comp_inlL2`). When `F` is self-adjoint it
is self-adjoint (`ContinuousLinearMap.isSelfAdjoint_doublingOperator`), and when `F` is moreover
a contraction it is an involution (`ContinuousLinearMap.doublingOperator_mul_self`), because
`√(1 - F²)` commutes with `F` and `F² + √(1 - F²)² = 1`. So a self-adjoint contraction is the
compression of a self-adjoint unitary.

## References

* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), §8.3
  (Lemma 8.3.8).
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **doubling operator** of `F`: the operator `[[F, √(1 - F²)], [√(1 - F²), -F]]` on the
Hilbert direct sum `H ⊕ H`. For a self-adjoint contraction `F` it is a self-adjoint involution
(`ContinuousLinearMap.isSelfAdjoint_doublingOperator`,
`ContinuousLinearMap.doublingOperator_mul_self`) whose upper left corner is `F`. -/
def doublingOperator (F : H →L[ℂ] H) : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) :=
  WithLp.blockL2 F (CFC.sqrt (1 - F * F)) (CFC.sqrt (1 - F * F)) (-F)

/-- The block form of the doubling operator. -/
theorem doublingOperator_def (F : H →L[ℂ] H) :
    doublingOperator F =
      WithLp.blockL2 F (CFC.sqrt (1 - F * F)) (CFC.sqrt (1 - F * F)) (-F) :=
  (rfl)

/-- The upper left corner of the doubling operator of `F` is `F`. -/
@[simp]
theorem fstL_comp_doublingOperator_comp_inlL2 (F : H →L[ℂ] H) :
    WithLp.fstL 2 ℂ H H ∘L doublingOperator F ∘L WithLp.inlL2 ℂ H H = F :=
  WithLp.fstL_comp_blockL2_comp_inlL2 ..

/-- The doubling operator of a self-adjoint operator is self-adjoint. -/
theorem isSelfAdjoint_doublingOperator {F : H →L[ℂ] H} (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (doublingOperator F) := by
  have hS : IsSelfAdjoint (CFC.sqrt (1 - F * F)) := (CFC.sqrt_nonneg _).isSelfAdjoint
  simp [IsSelfAdjoint, doublingOperator, ← star_eq_adjoint, hS.star_eq, hF.star_eq]

/-- **The doubling operator is an involution.** For a self-adjoint contraction `F`,
`[[F, √(1 - F²)], [√(1 - F²), -F]]² = 1`. -/
theorem doublingOperator_mul_self {F : H →L[ℂ] H} (hF : IsSelfAdjoint F) (hF₁ : ‖F‖ ≤ 1) :
    doublingOperator F * doublingOperator F = 1 := by
  rw [doublingOperator, WithLp.blockL2_mul_blockL2, ← withLpProdMap_one (p := 2),
    ← WithLp.blockL2_zero_zero]
  set S := CFC.sqrt (1 - F * F)
  have hSS : S * S = 1 - F * F := CFC.sqrt_mul_sqrt_self _ (hF.one_sub_mul_self_nonneg hF₁)
  have hFS : F * S = S * F := (Commute.refl F).cfcSqrt_one_sub_mul_self.eq.symm
  simp only [← mul_def, mul_neg, neg_mul, neg_neg, hSS, hFS, WithLp.blockL2_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

end ContinuousLinearMap
